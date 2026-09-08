/- Benchmark-only copy of the pre-convolution Poly1305 implementation. -/

import Crypto.AEAD.ChaCha20Poly1305.Spec

namespace Crypto.ChaCha20Poly1305.Archive.Original

def bytesToNatLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesToNatLE bs

def natToBytesLE (count n : Nat) : List UInt8 :=
  (List.range count).map fun i => ((n / 256 ^ i) % 256).toUInt8

def polyStep (r acc : Nat) (chunk : List UInt8) : Nat :=
  ((acc + bytesToNatLE chunk + 256 ^ chunk.length) * r) % (2 ^ 130 - 5)

def polyBlocks (r : Nat) : List UInt8 → Nat → Nat
  | [], acc => acc
  | b :: bs, acc =>
      let bytes := b :: bs
      let chunk := bytes.take 16
      polyBlocks r (bytes.drop 16) (polyStep r acc chunk)
termination_by bytes _ => bytes.length
decreasing_by simp_wf; omega

/-- The exact full-width-`Nat` implementation used before limb convolution. -/
def poly1305 (message oneTimeKey : List UInt8) : List UInt8 :=
  let r := bytesToNatLE (oneTimeKey.take 16) &&&
    0x0ffffffc0ffffffc0ffffffc0fffffff
  let s := bytesToNatLE (oneTimeKey.drop 16 |>.take 16)
  natToBytesLE 16 ((polyBlocks r message 0 + s) % (2 ^ 128))

end Crypto.ChaCha20Poly1305.Archive.Original
