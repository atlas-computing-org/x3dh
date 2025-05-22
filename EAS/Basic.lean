
import Batteries

namespace AES

-- Define constants and types

def Nb : Nat := 4  -- Number of columns in the state
def Nk : Nat := 4  -- Number of 32-bit words in the key (AES-128)
def Nr : Nat := 10 -- Number of rounds (AES-128)

abbrev Byte := UInt8
abbrev Word := Array Byte          -- A word is an array of 4 bytes
abbrev State := Array (Array Byte) -- A 4x4 array of bytes
abbrev KeySchedule := Array Word   -- Expanded key schedule


-- Helper functions
def xtime (b : Byte) : Byte :=
  if b.land 0x80 ≠ 0 then
    (b <<< 1) ^^^ 0x1b
  else
    b <<< 1

def gfMul (a b : Byte) : Byte := Id.run do
  let mut res := 0
  let mut x := a
  let mut y := b
  for _ in [0:8] do
   if y.land 1 ≠ 0 then
    res := res ^^^ x
   x := xtime x
   y := y >>> 1
  return res

-- SubBytes transformation
def subBytes (state : State) (sbox : Array Byte) : State :=
  state.map (fun row => row.map (fun b => sbox[b.toNat]!))

-- ShiftRows transformation
def shiftRows (state : State) : State :=
  state.mapIdx (fun i row => row.toList.rotateLeft i |>.toArray)

-- MixColumns transformation
def mixColumns (state : State) : State :=
  let a {α : Type} (as : Array (Array α)) : List (List α) :=
    as.toList.map (λ r => r.toList)
  let b {α : Type} (as: List (List α)) : Array (Array α) :=
    as.toArray.map (λ r => r.toArray)
  let mixColumn (col : Array Byte) : Array Byte :=
    let a := col
    let b := col.map xtime
    #[b[0]! ^^^ a[3]! ^^^ a[2]! ^^^ b[1]! ^^^ a[1]!,
      b[1]! ^^^ a[0]! ^^^ a[3]! ^^^ b[2]! ^^^ a[2]!,
      b[2]! ^^^ a[1]! ^^^ a[0]! ^^^ b[3]! ^^^ a[3]!,
      b[3]! ^^^ a[2]! ^^^ a[1]! ^^^ b[0]! ^^^ a[0]!]
  (b (a state).transpose).map mixColumn

-- AddRoundKey transformation
def addRoundKey (state : State) (roundKey : Array Word) : State :=
  state.zipWith (fun row key => row.zipWith (fun b k => b ^^^ k) key) roundKey

-- Key expansion
def keyExpansion (key : Array Word) : KeySchedule := Id.run do
  let rcon : Array Byte := #[0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36]
  let subWord (w : Word) (sbox : Array Byte) : Word :=
    w.map (fun b => sbox[b.toNat]!)
  let rotWord (w : Word) : Word :=
    w.toList.rotateLeft 1 |>.toArray
  let mut schedule := key
  for i in [Nk:(Nb * (Nr + 1))] do
    let mut temp := schedule[i - 1]
    if i % Nk == 0 then
      temp := subWord (rotWord temp) sbox ^^^ #[rcon[(i / Nk) - 1], 0, 0, 0]
    else if Nk > 6 && i % Nk == 4 then
      temp := subWord temp sbox
    schedule := schedule.push (schedule[i - Nk] ^^^ temp)
  return schedule

-- Cipher function
def cipher (input : State) (keySchedule : KeySchedule) (sbox : Array Byte)
  : State := Id.run do
  let mut state := addRoundKey input (keySchedule.take Nb)
  for round in [1:Nr] do
    state := mixColumns (shiftRows (subBytes state sbox))
    state := addRoundKey state (keySchedule.slice (round * Nb) ((round + 1) * Nb))
  state := shiftRows (subBytes state sbox)
  return addRoundKey state (keySchedule.slice (Nr * Nb) ((Nr + 1) * Nb))

-- Inverse transformations (for decryption)
def invShiftRows (state : State) : State :=
  state.mapIdx (fun i row => row.toList.rotateRight i |>.toArray)

def invMixColumns (state : State) : State :=
  let invMixColumn (col : Array Byte) : Array Byte :=
    let a := col
    #[gfMul a[0] 0x0e ^^^ gfMul a[1] 0x0b ^^^ gfMul a[2] 0x0d ^^^ gfMul a[3] 0x09,
      gfMul a[0] 0x09 ^^^ gfMul a[1] 0x0e ^^^ gfMul a[2] 0x0b ^^^ gfMul a[3] 0x0d,
      gfMul a[0] 0x0d ^^^ gfMul a[1] 0x09 ^^^ gfMul a[2] 0x0e ^^^ gfMul a[3] 0x0b,
      gfMul a[0] 0x0b ^^^ gfMul a[1] 0x0d ^^^ gfMul a[2] 0x09 ^^^ gfMul a[3] 0x0e]
  state.transpose.map invMixColumn.transpose

def invSubBytes (state : State) (invSbox : Array Byte) : State :=
  state.map (fun row => row.map (fun b => invSbox[b.toNat]!))

-- Inverse cipher function
def invCipher (input : State) (keySchedule : KeySchedule) (invSbox : Array Byte)
  : State := Id.run do
  let mut state := addRoundKey input (keySchedule.slice (Nr * Nb) ((Nr + 1) * Nb))
  for round in [1:Nr].reverse do
    state := invSubBytes (invShiftRows state) invSbox
    state := addRoundKey state (keySchedule.slice (round * Nb) ((round + 1) * Nb))
    state := invMixColumns state
  state := invSubBytes (invShiftRows state) invSbox
  return addRoundKey state (keySchedule.take Nb)

end AES
