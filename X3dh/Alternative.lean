import Mathlib.Tactic

namespace X3DH

-- Registry of agent identities and key pairs
abbrev AgentName := String

inductive Kind where
 | pub : Kind
 | prv : Kind
 | sec : Kind
deriving Repr, DecidableEq

instance : ToString Kind where
  toString k :=
   match k with
   | .pub => "public"
   | .prv => "private"
   | .sec => "secret"

def Kind.rev : Kind → Kind
| .pub => .prv
| .prv => .pub
| .sec => .sec

-- a structure to hold a Key
structure Key where
  userName : String
  label : String
  kind : Kind
 deriving Repr, DecidableEq

instance : ToString Key where
  toString k := s!"{k.userName}_{k.label}_{k.kind}"

def match_key (k1 k2 : Key) : Bool :=
  k1.kind.rev = k2.kind
  ∧ k1.userName = k2.userName
  ∧ k1.label = k2.label


inductive ByteSequence where
 | encode : Key → ByteSequence
 | dh     : Key → Key → ByteSequence
 | append : ByteSequence → ByteSequence → ByteSequence
 | sig    : Key → ByteSequence → ByteSequence
 | ad     : ByteSequence → ByteSequence → ByteSequence
 | aead   : String → ByteSequence → ByteSequence → ByteSequence
 deriving Repr, DecidableEq


-- Define a simple abstract type for a Key Pair
structure KeyPair where
  privateKey : Key
  publicKey  : Key
 deriving Repr


-- The agent's full internal state
structure Agent where
  name          : AgentName
  IK            : KeyPair
  SPK           : KeyPair
  OPKs          : List KeyPair
  deriving Repr

def generateKeyPair (name : AgentName) (label : String) : KeyPair :=
  { privateKey := Key.mk name label Kind.prv,
    publicKey := Key.mk name label Kind.pub }

structure Registry where
  agents : List Agent

-- create a new agent
def createAgent (name : AgentName) : Agent :=
  let IK := generateKeyPair name "IK"
  let SPK := generateKeyPair name "SPK"
  let OPKs := (List.range 5).map (λ i => generateKeyPair name s!"OPK{i}")
  Agent.mk name IK SPK OPKs

-- find an agent by name
def getAgent? (reg : Registry) (name : AgentName) : Option Agent :=
  reg.agents.find? (·.name = name)

-- a bundle of public or private keys and signature
structure Bundle where
  IK    : Key
  SPK   : Key
  SPK_Signature : ByteSequence
  OPK   : Option Key
  deriving Repr

-- signature verification
def verify (b : Bundle) : Bool :=
  match b.SPK_Signature with
  | ByteSequence.sig privK enc =>
    match enc with
    | ByteSequence.encode s => match_key privK b.IK ∧ s = b.SPK
    | _ => False
  | _ => False


def toPublicBundle (agent : Agent) : Bundle :=
 { IK := agent.IK.publicKey,
   SPK := agent.SPK.publicKey,
   SPK_Signature := ByteSequence.sig
    agent.IK.privateKey (ByteSequence.encode agent.SPK.publicKey),
   OPK := agent.OPKs.head?.map (·.publicKey)
 }

def toPrivateBundle (agent : Agent) (opkUsed : Option Nat) : Bundle :=
 {
    IK := agent.IK.privateKey,
    SPK := agent.SPK.privateKey,
    SPK_Signature := { message := "dummy1" , signer := "dummy2"},
    OPK := opkUsed.bind (fun idx => agent.OPKs[idx]?.map (·.privateKey))
  }


-- Alice computes shared secret from her ephemeral key and Bob's bundle
def deriveSharedSecret (ik : Key) (ek : Key) (bundle : Bundle)
 : ByteSequence :=
  let DH1 := ByteSequence.dh ik bundle.SPK
  let DH2 := ByteSequence.dh ek bundle.IK
  let DH3 := ByteSequence.dh ek bundle.SPK
  let res := (DH1.append DH2).append DH3
  match bundle.OPK with
  | some opk => res.append (ByteSequence.dh ek opk)
  | none     => res


structure Message where
  senderName : AgentName
  senderIK   : Key
  senderEK   : Key
  opkUsed    : Option Nat
  ciphertext : ByteSequence
 deriving Repr

instance : ToString Message where
  toString m :=
    s!"PreKeyMessage({m.senderName}, IK={m.senderIK}, EK={m.senderEK}, OPK? = {toString m.opkUsed}, ICT: {m.initialCiphertext})"


def encrypt (plaintext : String) (key ad : ByteSequence)
  : ByteSequence :=
  ByteSequence.aead plaintext key ad


def decrypt (key ad : ByteSequence) (msg : Message)
  : Option String :=
  match msg.ciphertext with
  | .aead txt key ad =>
    sorry
  | _ => none


def makeMessage (alice : Agent) (EK_A : KeyPair)
  (opkUsedIdx : Option Nat) (ciphertext : ByteSequence)
  : Message :=
  {
    senderName := alice.name
    senderIK   := alice.IK.publicKey
    senderEK   := EK_A.publicKey
    opkUsed    := opkUsedIdx
    ciphertext := ciphertext
  }



def agentsRegistry :=
  Registry.mk [createAgent "Alice", createAgent "Bob"]


def simulateStep4 (r : Registry) : Except String Message :=

  let alice := getAgent? r "Alice"
  let bob := getAgent? r "Bob"

  match (alice, bob) with
  | (some a, some b) =>

    -- Bob publishes a set of elliptic curve public keys to the server
    let bundle := toPublicBundle b

    -- Alice verifies the prekey signature and aborts the protocol if
    -- verification fail
    if verify bundle then
      let EK_A := generateKeyPair a.name "EK"

      let sk := deriveSharedSecret a.IK.privateKey EK_A.privateKey bundle
      let ad := ByteSequence.ad
        (ByteSequence.encode a.IK.publicKey)
        (ByteSequence.encode b.IK.publicKey)

      let opkUsedIdx := if bundle.OPK.isSome then some 0 else none
      let plaintext := "Hello Bob!"
      let ciphertext := encrypt plaintext sk ad

      -- Alice sent the message
      let msg := makeMessage a EK_A opkUsedIdx ciphertext
      Except.ok msg
    else
      Except.error "Invalid SPK signature"
  | _ => Except.error "didnt find agents"


def simulateStep5 (r : Registry)
  (msg : Message) : Except String String :=
  match getAgent? r "Bob" with
  | some bob =>

      -- get message from alice
      let ikpub := msg.senderIK
      let ekpub := msg.senderEK

      let sk := deriveSharedSecret ikpub ekpub (toPrivateBundle bob msg.opkUsed)

      let ad := ByteSequence.ad
        (ByteSequence.encode ikpub)
        (ByteSequence.encode bob.IK.publicKey)

      match decrypt sk ad msg with
      | some s => Except.ok s
      | none => Except.error "not decrypted"

  | none => Except.error "Bob not found"


#eval simulateStep4 agentsRegistry

#eval let msg := simulateStep4 agentsRegistry
  match msg with
  | Except.ok m => simulateStep5 agentsRegistry m
  | Except.error s => Except.error s


end X3DH
