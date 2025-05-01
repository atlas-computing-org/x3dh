-- SHA1.lean
import Init.Data.ByteArray
import Init.Data.Repr
import Init.Data.Vector.Basic
import Init.Data.Nat.Basic
import Mathlib.Data.UInt
import Util.HexString

namespace SHA1
open Mathlib

-- Type alias for 32-bit words
abbrev Word := UInt32

-- Initial hash values (H0) as per FIPS 180-4
def initialHash : Vector Word 5 :=
  ⟨#[0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0], rfl⟩

-- Constants K for each iteration
def K (t : Nat) : Word :=
  if t ≤ 19 then 0x5A827999
  else if t ≤ 39 then 0x6ED9EBA1
  else if t ≤ 59 then 0x8F1BBCDC
  else 0xCA62C1D6

-- Left rotate operation using mathlib's rotateLeft
def ROTL (n : Nat) (x : Word) : Word :=
  let nn : UInt32 := n.toUInt32
  ((x <<< nn) ||| (x >>> (32 - nn)))

-- Padding function
def padMessage (msg : ByteArray) : ByteArray :=
  -- Message length in bits
  let ml := UInt64.ofNat (msg.size * 8)
  -- Append '1' bit and seven '0' bits
  let padding : ByteArray := ByteArray.mk #[0x80]
  let zeroPaddingLength := (56 - ((msg.size + 1) % 64)) % 64
  let zeroPadding := ByteArray.mk (List.replicate zeroPaddingLength 0).toArray
  let lengthBytes := ByteArray.mk $ ((List.range 8).reverse.map
   fun (i: Nat) =>
    ((ml >>> (i * 8).toUInt64) &&& 0xFF).toUInt8).toArray
  msg ++ padding ++ zeroPadding ++ lengthBytes

-- Break message into 512-bit (64-byte) chunks
def chunkify (msg : ByteArray) : Array ByteArray :=
  let chunkSize := 64
  let numChunks := (msg.size + chunkSize - 1) / chunkSize
  let chunks := List.range numChunks |>.map
    fun i => msg.extract (i * chunkSize) ((i + 1) * chunkSize)
  chunks.toArray

-- Convert a 4-byte slice to a Word (UInt32)
def bytesToWord (bytes : ByteArray) : Word :=
  bytes.foldl (fun acc b => (acc <<< 8) ||| b.toUInt32) 0

-- Main hash function
def hash (message : ByteArray) : ByteArray :=
  let paddedMsg := padMessage message
  let chunks := chunkify paddedMsg
  let H := initialHash
  let finalHash := chunks.foldl (init := H) fun h0 chunk =>
    -- Prepare the message schedule W
    let words := List.range 16 |>.map fun i =>
      let bytes := chunk.extract (i * 4) ((i + 1) * 4)
      bytesToWord bytes
    let W := Id.run do
      let mut W := words
      for t in [16:80] do
        let wt := ROTL 1 (W[t - 3]! ^^^ W[t - 8]! ^^^ W[t - 14]! ^^^ W[t - 16]!)
        W := W.append [wt]
      W
    Id.run do
    -- Initialize working variables
    let mut a := h0[0]!
    let mut b := h0[1]!
    let mut c := h0[2]!
    let mut d := h0[3]!
    let mut e := h0[4]!
    -- Main loop
    for t in [0:80] do
      let f :=
        if t ≤ 19 then (b &&& c) ||| ((~~~b) &&& d)
        else if t ≤ 39 then b ^^^ c ^^^ d
        else if t ≤ 59 then (b &&& c) ||| (b &&& d) ||| (c &&& d)
        else b ^^^ c ^^^ d
      let temp := (ROTL 5 a) + f + e + K t + W[t]!
      e := d
      d := c
      c := ROTL 30 b
      b := a
      a := temp
    -- Compute the new hash values
    return ⟨h0.toArray.zipWith (· + ·) #[a, b, c, d, e], by simp⟩
  -- Concatenate the final hash values into a ByteArray
  let resultBytes := finalHash.toList.foldl (init := ByteArray.empty)
   fun acc (h: Word) =>
    let tmp := (List.range 4).toArray.reverse.map
      (fun (i: Nat) => ((h >>> (i.toUInt32 * 8)) &&& 0xFF).toUInt8)
      |> ByteArray.mk
    acc ++ tmp
  resultBytes

end SHA1

-- Example usage: SHA-1 hash
-- "Hello World" => 0a 4d 55 a8 d7 78 e5 02 2f ab 70 19 77 c5 d8 40 bb c4 86 d0
#eval (SHA1.hash ("Hello World".toUTF8)).toHexString
