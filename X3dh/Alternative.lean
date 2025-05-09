

namespace X3DH

-- Registry of agent identities and key pairs
abbrev AgentName := String

-- Define a simple abstract type for keys
structure KeyPair where
  privateKey : String
  publicKey  : String
  deriving Repr

structure Signature where
  message : String
  signer : AgentName
  deriving Repr, BEq

-- The agent's full internal state
structure Agent where
  name          : AgentName
  IK            : KeyPair
  SPK           : KeyPair
  OPKs          : List KeyPair
  deriving Repr

abbrev AgentRegistry := List Agent

def generateKeyPair (label : String) : KeyPair :=
  { privateKey := label ++ "_priv", publicKey := label ++ "_pub" }

-- Register a new agent
def createAgent (reg : AgentRegistry) (name : AgentName) : AgentRegistry :=
  let IK := generateKeyPair (name ++ "_IK")
  let SPK := generateKeyPair (name ++ "_SPK")
  let OPKs := (List.range 5).map (λ i => generateKeyPair (s!"{name}_OPK_{i}"))
  Agent.mk name IK SPK OPKs :: reg

-- Get an agent by name
def getAgent? (reg : AgentRegistry) (name : AgentName) : Option Agent :=
  reg.find? (·.name = name)


-- Signature verification
def verify (reg : AgentRegistry)
  (sig : Signature) (message : String) (expectedPub : String) : Bool :=
  match getAgent? reg sig.signer with
  | some agent => sig.message = message && agent.IK.publicKey = expectedPub
  | none => false

-- Public bundle
structure Bundle where
  IK    : String
  SPK   : String
  SPK_Signature : Signature
  OPK   : Option String
  deriving Repr

def toPublicBundle (agent : Agent) : Bundle :=
 {
    IK := agent.IK.publicKey,
    SPK := agent.SPK.publicKey,
    SPK_Signature := {
      message := agent.SPK.publicKey,
      signer := agent.name : Signature },
    OPK := agent.OPKs.head?.map (·.publicKey)
  }

def toPrivateBundle (agent : Agent) (opkUsed : Option Nat) : Bundle :=
 {
    IK := agent.IK.privateKey,
    SPK := agent.SPK.privateKey,
    SPK_Signature := { message := "dummy1" , signer := "dummy2"},
    OPK := opkUsed.bind (fun idx => agent.OPKs[idx]?.map (·.privateKey))
  }


-- Fake Diffie-Hellman between priv and pub key
def dh (seq : Nat) (priv : String) (pub : String) : String :=
  s!"DH{seq}({priv},{pub})"

-- Fake key derivation function
def kdf (inputs : List String) : String :=
  s!"KDF({String.intercalate " || " inputs})"

-- Alice computes shared secret from her ephemeral key and Bob's bundle
def deriveSharedSecret (ik : String) (ek : String) (bundle : Bundle)
 : String :=
  let DH1 := dh 1 ik bundle.SPK
  let DH2 := dh 2 ek bundle.IK
  let DH3 := dh 3 ek bundle.SPK
  let DHs :=
    match bundle.OPK with
    | some opk => [DH1, DH2, DH3, dh 4 ek opk]
    | none     => [DH1, DH2, DH3]
  kdf DHs

-- Fake "associated data" byte sequence
def deriveAssociatedData (ika ikb : String) : String :=
  s!"AD({ika},{ikb})"


structure Message where
  senderName : AgentName
  senderIK   : String
  senderEK   : String
  opkUsed    : Option Nat
  initialCiphertext : String
 deriving Repr

instance : ToString Message where
  toString m :=
    s!"PreKeyMessage({m.senderName}, IK={m.senderIK}, EK={m.senderEK}, OPK? = {toString m.opkUsed}, ICT: {m.initialCiphertext})"


def aeadEncrypt (key ad plaintext : String) : String :=
  s!"AEAD({plaintext} | key={key}, ad={ad})"

def aeadDecrypt (key ad ciphertext : String) : String :=
  s!"DECRYPTED({ciphertext} | key={key}, ad={ad})"


def makeMessage (alice : Agent) (EK_A : KeyPair)
  (opkUsedIdx : Option Nat) (ciphertext : String) : Message :=
  {
    senderName := alice.name
    senderIK   := alice.IK.publicKey
    senderEK   := EK_A.publicKey
    opkUsed    := opkUsedIdx
    initialCiphertext := ciphertext
  }


def agentsRegistry :=
  let reg0 := []
  let reg1 := createAgent reg0 "Alice"
  let reg2 := createAgent reg1 "Bob"
  reg2


def simulateStep4 (r : AgentRegistry) : Except String Message :=

  let alice := getAgent? r "Alice"
  let bob := getAgent? r "Bob"

  match (alice, bob) with
  | (some a, some b) =>

      -- Bob publishes a set of elliptic curve public keys to the server
      let bundle := toPublicBundle b

      -- Alice verifies the prekey signature and aborts the protocol if verification fail
      let res := verify r bundle.SPK_Signature bundle.SPK bundle.IK

      if res then
        let EK_A := generateKeyPair "Alice_EK"

        let sk := deriveSharedSecret a.IK.privateKey EK_A.privateKey bundle
        let ad := deriveAssociatedData a.IK.publicKey b.IK.publicKey

        let opkUsedIdx := if bundle.OPK.isSome then some 0 else none
        let plaintext := "Hello Bob!"
        let ciphertext := aeadEncrypt sk ad plaintext

        -- Alice sent the message
        let msg := makeMessage a EK_A opkUsedIdx ciphertext

        Except.ok msg

      else
        Except.error "Invalid SPK signature"

  | _ => Except.error "didnt find agents"


def simulateStep5 (r : AgentRegistry)
  (msg : Message) : Except String String :=
  match getAgent? r "Bob" with
  | some bob =>

      -- get message from alice
      let ikpub := msg.senderIK
      let ekpub := msg.senderEK

      let sk := deriveSharedSecret ikpub ekpub (toPrivateBundle bob msg.opkUsed)

      let ad := deriveAssociatedData ikpub bob.IK.publicKey

      let plaintext := aeadDecrypt sk ad msg.initialCiphertext

      Except.ok plaintext

  | none => Except.error "Bob not found"


#eval simulateStep4 agentsRegistry

#eval let msg := simulateStep4 agentsRegistry
  match msg with
  | Except.ok m => simulateStep5 agentsRegistry m
  | Except.error s => Except.error s


end X3DH
