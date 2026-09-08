import Crypto.AEAD.ChaCha20Poly1305.WordBlocks

namespace Crypto.ChaCha20Poly1305.Machine

open Fast

structure Words where
  w0 : UInt64
  w1 : UInt64
  w2 : UInt64
  w3 : UInt64

def Words.value (w : Words) : Nat :=
  w.w0.toNat + 2^32*w.w1.toNat + 2^64*w.w2.toNat + 2^96*w.w3.toNat

/-- The carry out of bit 130 after adding five selects reduction modulo 2^130-5. -/
@[inline] def quotient (h : Limbs) : UInt64 :=
  let g0 := h.h0 + 5
  let g1 := h.h1 + g0 / 67108864
  let g2 := h.h2 + g1 / 67108864
  let g3 := h.h3 + g2 / 67108864
  (h.h4 + g3 / 67108864) / 67108864

@[inline] def repack (h : Limbs) : Words :=
  ⟨h.h0 + (h.h1 % 64)*67108864,
   h.h1 / 64 + (h.h2 % 4096)*1048576,
   h.h2 / 4096 + (h.h3 % 262144)*16384,
   h.h3 / 262144 + h.h4*256⟩

/-- Add the pad and the reduction correction in radix 2^32. -/
@[inline] def addPad (w s : Words) (correction : UInt64) : Words :=
  let f0 := w.w0 + s.w0 + correction
  let f1 := w.w1 + s.w1 + f0 / 4294967296
  let f2 := w.w2 + s.w2 + f1 / 4294967296
  let f3 := w.w3 + s.w3 + f2 / 4294967296
  ⟨f0 % 4294967296, f1 % 4294967296, f2 % 4294967296, f3 % 4294967296⟩

@[inline] def finishCore (h : Limbs) (s : Words) : Words :=
  addPad (repack h) s (quotient h * 5)

def wordsBytes (w : Words) : List UInt8 :=
  (List.range 16).map fun i =>
    let x := if i < 4 then w.w0 else if i < 8 then w.w1 else if i < 12 then w.w2 else w.w3
    (x >>> ((i % 4)*8).toUInt64).toUInt8

def finish (h : Limbs) (s : Words) : List UInt8 :=
  wordsBytes (finishCore (carryWords h) s)

/-- Clamp the radix-2^26 digits directly, before any multiplication. -/
@[inline] def decodeWords (w : Words) : RKey :=
  ⟨(w.w0 % 67108864) &&& 0x3ffffff,
   (w.w0 / 67108864 + (w.w1 % 1048576)*64) &&& 0x3ffff03,
   (w.w1 / 1048576 + (w.w2 % 16384)*4096) &&& 0x3ffc0ff,
   (w.w2 / 16384 + (w.w3 % 256)*262144) &&& 0x3f03fff,
   (w.w3 / 256) &&& 0x00fffff⟩

/-- Missing key bytes are zero, preserving the existing total specification. -/
@[inline] def loadWords (a : Array UInt8) (offset : Nat) : Words :=
  let load := fun i => WordBlocks.pack4 (a[i]?.getD 0) (a[i+1]?.getD 0)
    (a[i+2]?.getD 0) (a[i+3]?.getD 0)
  ⟨load offset, load (offset+4), load (offset+8), load (offset+12)⟩

def poly1305 (message key : List UInt8) : List UInt8 :=
  let key := key.toArray
  let r := decodeWords (loadWords key 0)
  let s := loadWords key 16
  finish (WordBlocks.blocks r message ⟨0,0,0,0,0⟩) s

/-- Load and multiply one full block in its original array storage. -/
@[inline] def arrayStep (r : RKey) (a : Array UInt8) (offset : Nat) (h : Limbs) : Limbs :=
  let w := loadWords a offset
  mulReduce (WordBlocks.addWords h w.w0 w.w1 w.w2 w.w3) r

/-- Process full blocks in place; copy only the final short block to the
    reference decoder when called with `n = (a.size-offset)/16`. -/
def blocksArray (r : RKey) (a : Array UInt8) : Nat → Nat → Limbs → Limbs
  | 0, offset, h => blocksList r (a.extract offset a.size).toList h
  | n+1, offset, h =>
      blocksArray r a n (offset+16) (arrayStep r a offset h)

def poly1305Array (message key : Array UInt8) : List UInt8 :=
  let r := decodeWords (loadWords key 0)
  let s := loadWords key 16
  finish (blocksArray r message (message.size / 16) 0 ⟨0,0,0,0,0⟩) s

end Crypto.ChaCha20Poly1305.Machine
