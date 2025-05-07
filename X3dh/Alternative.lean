
-- Define a simple abstract type for keys
structure KeyPair where
  privateKey : String
  publicKey  : String
  deriving Repr

structure Signature where
  message : String
  signer  : String -- the private key used
  deriving Repr, BEq


-- Simulate key pair generation (in real crypto, this would be from random bytes)
def generateKeyPair (name : String) : KeyPair := {
    privateKey := name ++ "_priv",
    publicKey  := name ++ "_pub"
  }

-- Sign a message (public key) with a private key
def sign (message : String) (privateKey : String) : Signature :=
  { message := message, signer := privateKey }

-- Define Bob's keys
structure BobKeys where
  IK  : KeyPair
  SPK : KeyPair
  SPKSignature : Signature
  OPKs : List KeyPair
  deriving Repr

-- Generate Bob's full key bundle
def generateBobKeys : BobKeys :=
  let IK  := generateKeyPair "IK_B"
  let SPK := generateKeyPair "SPK_B"
  let sig := sign SPK.publicKey IK.privateKey
  let OPKs := (List.range 5).map (fun i => generateKeyPair s!"OPK_B_{i}")
  { IK := IK, SPK := SPK, SPKSignature := sig, OPKs := OPKs }

-- Example usage
#eval generateBobKeys

-- Verify a signature given the public key
-- (check it was signed by matching private)
def verify (sig : Signature) (message : String)
  (expectedPubKey : String) : Bool :=
  sig.message = message && sig.signer = "IK_B_priv" && expectedPubKey = "IK_B_pub"

-- Simulate Alice fetching Bob's key bundle from the server
structure BobPublicBundle where
  IK_B  : String
  SPK_B : String
  SPK_Signature : Signature
  OPK_B : Option String
  deriving Repr

-- Example: Alice receives this from the server
def bobBundleFromServer : BobPublicBundle :=
  let bobKeys := generateBobKeys
  {
    IK_B := bobKeys.IK.publicKey,
    SPK_B := bobKeys.SPK.publicKey,
    SPK_Signature := bobKeys.SPKSignature,
    OPK_B := bobKeys.OPKs.head?.map (·.publicKey)
  }

-- Alice verifies Bob's signed prekey
def aliceVerifiesSPK (bundle : BobPublicBundle) : Bool :=
  verify bundle.SPK_Signature bundle.SPK_B bundle.IK_B

-- Run Alice's verification
#eval aliceVerifiesSPK bobBundleFromServer
