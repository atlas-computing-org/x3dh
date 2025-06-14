import Mathlib.Tactic

namespace X3DH

-- Registry of agent identities and key pairs
abbrev AgentName := String

inductive Kind where
 | pub : Kind
 | prv : Kind
deriving Repr, DecidableEq

instance : ToString Kind where
  toString k :=
   match k with
   | .pub => "public"
   | .prv => "private"

def Kind.rev : Kind → Kind
 | .pub => .prv
 | .prv => .pub

theorem Kind.rev_rev : ∀ k : Kind, k.rev.rev = k := by
  intro h
  cases h with
  | pub => rfl
  | prv => rfl

-- a structure to hold a Key
structure Key where
  userName : String
  label : String
  kind : Kind
 deriving Repr, DecidableEq

instance : ToString Key where
  toString k := s!"{k.userName}_{k.label}_{k.kind}"


def match_key (k1 k2 : Key) : Bool :=
  k1.userName = k2.userName
  ∧ k1.label = k2.label
  ∧ k1.kind.rev = k2.kind
  ∧ k1.kind = k2.kind.rev

inductive ByteSequence where
 | encode : Key → ByteSequence
 | dh     : Key → Key → ByteSequence
 | append : ByteSequence → ByteSequence → ByteSequence
 | sig    : Key → ByteSequence → ByteSequence
 | aead   : String → ByteSequence → ByteSequence → ByteSequence
 deriving Repr, DecidableEq

def ByteSequence.toString : ByteSequence → String
  | .encode k      => s!"enc({k})"
  | .dh k1 k2      => s!"dh({k1}, {k2})"
  | .append b1 b2  => s!"({b1.toString} || {b2.toString})"
  | .sig k b       => s!"sig({k}, {b.toString})"
  | .aead txt k a  => s!"aead(M:{txt}, SK:{k.toString}, AD:{a.toString})"

instance : ToString ByteSequence where
  toString := ByteSequence.toString

def match_bs (b1 b2 : ByteSequence) : Bool :=
  match b1, b2 with
  | .dh k1 k2, .dh k3 k4 =>
    match_key k1 k3 ∧ match_key k2 k4
  | .append b1 b2, .append b3 b4 =>
    match_bs b1 b3 ∧ match_bs b2 b4
  | .encode k1, .encode k2 => k1 = k2
  | _, _ => false


-- Define a simple abstract type for a Key Pair
structure KeyPair where
  privateKey : Key
  publicKey  : Key
  valid      : match_key privateKey publicKey
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
    publicKey  := Key.mk name label Kind.pub,
    valid      := by simp [match_key]; apply And.intro; repeat simp [Kind.rev]}

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
  OPKS   : List Key
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
   OPKS := agent.OPKs.map (·.publicKey)
 }


def toPrivateBundle (agent : Agent) : Bundle :=
 { IK := agent.IK.privateKey,
   SPK := agent.SPK.privateKey,
   SPK_Signature :=  ByteSequence.sig
      agent.IK.privateKey (ByteSequence.encode agent.SPK.privateKey),
   OPKS := agent.OPKs.map (·.privateKey)
 }


-- Alice computes shared secret from her ephemeral key and Bob's bundle
def deriveSharedSecret (ik : Key) (ek : Key) (bundle : Bundle)
 : ByteSequence :=
  let DH1 := ByteSequence.dh ik bundle.SPK
  let DH2 := ByteSequence.dh ek bundle.IK
  let DH3 := ByteSequence.dh ek bundle.SPK
  let res := (DH1.append DH2).append DH3
  match bundle.OPKS with
  | opk :: _ => res.append (ByteSequence.dh ek opk)
  | []     => res


structure Message where
  senderName : AgentName
  senderIK   : Key
  senderEK   : Key
  opkUsed    : Option Nat
  ciphertext : ByteSequence
 deriving Repr

instance : ToString Message where
  toString m :=
    s!"Message({m.senderName}, IK={m.senderIK}, EK={m.senderEK}, OPK={toString m.opkUsed}, T={m.ciphertext})"

def encrypt (plaintext : String) (key ad : ByteSequence)
  : ByteSequence :=
  ByteSequence.aead plaintext key ad


def decrypt (key ad : ByteSequence) (msg : Message)
  : Option String :=
  match msg.ciphertext with
  | .aead txt keyM adM =>
    if match_bs keyM key ∧ match_bs adM ad then
      some txt
    else
      none
  | _ => none


def makeMessage (alice : Agent) (EK_A : Key)
  (opkUsedIdx : Option Nat) (ciphertext : ByteSequence)
  : Message :=
  {
    senderName := alice.name
    senderIK   := alice.IK.publicKey
    senderEK   := EK_A
    opkUsed    := opkUsedIdx
    ciphertext := ciphertext
  }


def sendInitMessage (sender : Agent) (bundle : Bundle)
  (txt : String) : Except String Message :=

  -- the sender codename is Alice
  let alice := sender

  -- Alice verifies the prekey signature and aborts the protocol if
  -- verification fail
  if verify bundle then
    let EK_A := generateKeyPair alice.name "EK"

    let sk := deriveSharedSecret alice.IK.privateKey EK_A.privateKey bundle
    let ad := ByteSequence.append
      (ByteSequence.encode alice.IK.publicKey)
      (ByteSequence.encode bundle.IK)

    let opkUsedIdx := if bundle.OPKS.length > 0 then some 0 else none
    let plaintext := txt
    let ciphertext := encrypt plaintext sk ad

    -- Alice sent the message
    let msg := makeMessage alice EK_A.publicKey opkUsedIdx ciphertext
    Except.ok msg
  else
    Except.error "Invalid SPK signature"


def receiveInitMessage  (receiver : Agent) (msg : Message)
  : Except String String :=

  let bob := receiver

  -- get message from alice
  let ikpub := msg.senderIK
  let ekpub := msg.senderEK

  let sk := deriveSharedSecret ikpub ekpub (toPrivateBundle bob)

  let ad := ByteSequence.append
    (ByteSequence.encode ikpub)
    (ByteSequence.encode bob.IK.publicKey)

  match decrypt sk ad msg with
  | some s => Except.ok s
  | none => Except.error s!"not decrypted"


/-
#eval
  let r := Registry.mk [createAgent "Alice", createAgent "Bob"]
  let alice := r.agents[0]
  let bob := r.agents[1]
  let msg := sendInitMessage alice (toPublicBundle bob) "Hello Bob"
  match msg with
  | Except.ok m => receiveInitMessage bob m
  | Except.error s => Except.error s
-/

-- Basic Theorems about the protocol

theorem all_agentIK :
  ∀ (a : Agent), match_key a.IK.privateKey a.IK.publicKey := by
  intro a
  let h₁ := a.IK
  let k1 := a.IK.publicKey
  let k2 := a.IK.privateKey
  let h₂ := h₁.valid
  exact h₂


theorem commonSharedSecret {a b : Agent} {txt : String}
  (msg : Message) (h : b.OPKs = []) :
  sendInitMessage a (toPublicBundle b) txt = Except.ok msg →
  receiveInitMessage b msg = Except.ok txt := by
  intro h₁
  simp [sendInitMessage, receiveInitMessage,
    toPublicBundle, toPrivateBundle, deriveSharedSecret,
    decrypt, encrypt, generateKeyPair,
    ByteSequence.append, makeMessage, verify,
    match_bs] at *
  have h₂ := all_agentIK b
  have iav := a.IK.valid
  have ibv := b.IK.valid
  have spav := a.SPK.valid
  have spbv := b.SPK.valid
  simp [h₂, h] at h₁
  simp [h₂, h]
  rw [← h₁]
  have h₆ : match_bs
     ((ByteSequence.encode a.IK.publicKey).append (ByteSequence.encode b.IK.publicKey))
     ((ByteSequence.encode a.IK.publicKey).append (ByteSequence.encode b.IK.publicKey)) := by
    simp [match_bs]
  simp [h₆]
  have h₇ :
    match_bs
     (((ByteSequence.dh a.IK.privateKey b.SPK.publicKey).append
       (ByteSequence.dh { userName := a.name, label := "EK", kind := Kind.prv } b.IK.publicKey)).append
      (ByteSequence.dh { userName := a.name, label := "EK", kind := Kind.prv } b.SPK.publicKey))
     (((ByteSequence.dh a.IK.publicKey b.SPK.privateKey).append
       (ByteSequence.dh { userName := a.name, label := "EK", kind := Kind.pub } b.IK.privateKey)).append
      (ByteSequence.dh { userName := a.name, label := "EK", kind := Kind.pub } b.SPK.privateKey)) := by
    simp [match_bs, match_key] at *
    simp [iav, ibv, spav, spbv]
    repeat apply And.intro
    repeat simp [Kind.rev_rev]
    repeat apply And.intro
    simp [Kind.rev, Kind.rev_rev]
    simp [Kind.rev]
    simp [Kind.rev_rev]
    simp [Kind.rev]
  simp [h₇]

end X3DH
