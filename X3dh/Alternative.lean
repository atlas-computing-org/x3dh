
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
  SPK_Signature : Signature
  OPKs          : List KeyPair
  deriving Repr

abbrev AgentRegistry := List Agent

def generateKeyPair (label : String) : KeyPair :=
  { privateKey := label ++ "_priv", publicKey := label ++ "_pub" }

-- Register a new agent
def createAgent (reg : AgentRegistry) (name : AgentName) : AgentRegistry :=
  let IK := generateKeyPair (name ++ "_IK")
  let SPK := generateKeyPair (name ++ "_SPK")
  let sig := { message := SPK.publicKey, signer := name : Signature }
  let OPKs := (List.range 5).map (λ i => generateKeyPair (s!"{name}_OPK_{i}"))
  Agent.mk name IK SPK sig OPKs :: reg

-- Get an agent by name
def getAgent? (reg : AgentRegistry) (name : AgentName) : Option Agent :=
  reg.find? (·.name = name)


-- Signature verification
def verify (reg : AgentRegistry)
  (sig : Signature) (message : String) (expectedPub : String) : Bool :=
  match getAgent? reg sig.signer with
  | some agent => sig.message = message && agent.IK.publicKey = expectedPub
  | none => false

-- Public bundle (what Alice fetches)
structure PublicBundle where
  IK    : String
  SPK   : String
  SPK_Signature : Signature
  OPK   : Option String
  deriving Repr

def toPublicBundle (agent : Agent) : PublicBundle :=
 {
    IK := agent.IK.publicKey,
    SPK := agent.SPK.publicKey,
    SPK_Signature := agent.SPK_Signature,
    OPK := agent.OPKs.head?.map (·.publicKey)
  }

-- Simulate Diffie-Hellman: fake DH between priv and pub key
def dh (priv : String) (pub : String) : String :=
  s!"DH({priv},{pub})"

-- Fake key derivation function
def kdf (inputs : List String) : String :=
  s!"KDF({String.intercalate " || " inputs}"

-- Alice computes shared secret from her ephemeral key and Bob's bundle
def deriveSharedSecret (alice : Agent) (bobBundle : PublicBundle)
 : String :=
  let EK_A := generateKeyPair "Alice_EK"
  let DH1 := dh alice.IK.privateKey bobBundle.SPK
  let DH2 := dh EK_A.privateKey bobBundle.IK
  let DH3 := dh EK_A.privateKey bobBundle.SPK
  let DHs :=
    match bobBundle.OPK with
    | some opk => [DH1, DH2, DH3, dh EK_A.privateKey opk]
    | none     => [DH1, DH2, DH3]
  kdf DHs


-- Simulate Step 3
def simulateStep3 : String :=
  let reg0 := []
  let reg1 := createAgent reg0 "Alice"
  let reg2 := createAgent reg1 "Bob"
  let alice := getAgent? reg2 "Alice"
  let bob := getAgent? reg2 "Bob"
  match (alice, bob) with
  | (some a, some b) =>
      let bundle := toPublicBundle b
      if verify reg2 bundle.SPK_Signature bundle.SPK bundle.IK then
        deriveSharedSecret a bundle
      else "Invalid SPK signature"
  | _ => "Missing agent"

#eval simulateStep3


-- Full simulation
def simulate : Bool :=

  let reg0 := []
  let reg1 := createAgent reg0 "Alice"
  let reg2 := createAgent reg1 "Bob"

  -- Alice retrieves Bob bundle
  match getAgent? reg2 "Bob" with
  | some bob =>
      let bundle := toPublicBundle bob
      aliceVerifies reg2 bundle
  | none => false


#eval simulate
