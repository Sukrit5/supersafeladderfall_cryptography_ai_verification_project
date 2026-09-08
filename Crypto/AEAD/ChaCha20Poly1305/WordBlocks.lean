import Crypto.AEAD.ChaCha20Poly1305.Fast

namespace Crypto.ChaCha20Poly1305.WordBlocks

open Fast

/-- Four little-endian bytes, with all arithmetic in machine words. -/
@[inline] def pack4 (a b c d : UInt8) : UInt64 :=
  a.toUInt64 + 256 * (b.toUInt64 + 256 * (c.toUInt64 + 256 * d.toUInt64))

/-- Add a full 16-byte block and its implicit bit 128 directly to radix-2^26 limbs.
    Constant divisors and moduli are powers of two. -/
@[inline] def addWords (h : Limbs) (a b c d : UInt64) : Limbs :=
  ⟨h.h0 + a % 67108864,
   h.h1 + (a / 67108864 + (b % 1048576) * 64),
   h.h2 + (b / 1048576 + (c % 16384) * 4096),
   h.h3 + (c / 16384 + (d % 256) * 262144),
   h.h4 + (d / 256 + 16777216)⟩

/-- Full blocks avoid temporary chunk lists and arbitrary-precision decoding.
    The final short block retains the already verified reference path. -/
def blocks (r : RKey) : List UInt8 → Limbs → Limbs
  | a0 :: a1 :: a2 :: a3 :: b0 :: b1 :: b2 :: b3 ::
      c0 :: c1 :: c2 :: c3 :: d0 :: d1 :: d2 :: d3 :: rest, h =>
      blocks r rest (mulReduce (addWords h
        (pack4 a0 a1 a2 a3) (pack4 b0 b1 b2 b3)
        (pack4 c0 c1 c2 c3) (pack4 d0 d1 d2 d3)) r)
  | tail, h => blocksList r tail h

/-- Serialize the low 128 bits using two machine words and byte shifts. -/
def tagBytes (n : Nat) : List UInt8 :=
  let lo := n.toUInt64
  let hi := (n / 2^64).toUInt64
  (List.range 16).map fun i =>
    let word := if i < 8 then lo else hi
    (word >>> ((i % 8) * 8).toUInt64).toUInt8

def poly1305 (message keyBytes : List UInt8) : List UInt8 :=
  let rNat := bytesToNatLE (keyBytes.take 16) &&&
    0x0ffffffc0ffffffc0ffffffc0fffffff
  let h := blocks (RKey.ofNat rNat) message ⟨0, 0, 0, 0, 0⟩
  let s := bytesToNatLE (keyBytes.drop 16 |>.take 16)
  tagBytes ((h.value % prime + s) % (2 ^ 128))

end Crypto.ChaCha20Poly1305.WordBlocks
