import Crypto.AEAD.ChaCha20Poly1305.Spec

namespace Crypto.ChaCha20Poly1305.Fast

structure Limbs where
  h0 : UInt64
  h1 : UInt64
  h2 : UInt64
  h3 : UInt64
  h4 : UInt64
  deriving Repr

structure RKey where
  r0 : UInt64
  r1 : UInt64
  r2 : UInt64
  r3 : UInt64
  r4 : UInt64

def bytesToNatLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesToNatLE bs

def natToBytesLE (count n : Nat) : List UInt8 :=
  (List.range count).map fun i => ((n / 256 ^ i) % 256).toUInt8

def limbBase : Nat := 2 ^ 26
def prime : Nat := 2 ^ 130 - 5

def Limbs.value (h : Limbs) : Nat :=
  h.h0.toNat + limbBase * (h.h1.toNat + limbBase *
    (h.h2.toNat + limbBase * (h.h3.toNat + limbBase * h.h4.toNat)))

def RKey.ofNat (n : Nat) : RKey :=
  ⟨(n % limbBase).toUInt64,
   (n / limbBase % limbBase).toUInt64,
   (n / limbBase ^ 2 % limbBase).toUInt64,
   (n / limbBase ^ 3 % limbBase).toUInt64,
   (n / limbBase ^ 4 % limbBase).toUInt64⟩

@[inline] def byteAt (a : Array UInt8) (i : Nat) : UInt64 := a[i]!.toUInt64

@[inline] def load32 (a : Array UInt8) (i : Nat) : UInt64 :=
  byteAt a i ||| (byteAt a (i + 1) <<< 8) |||
    (byteAt a (i + 2) <<< 16) ||| (byteAt a (i + 3) <<< 24)

def decodeR (key : Array UInt8) : RKey :=
  let t0 := load32 key 0
  let t1 := load32 key 4
  let t2 := load32 key 8
  let t3 := load32 key 12
  ⟨t0 &&& 0x3ffffff,
   ((t0 >>> 26) ||| (t1 <<< 6)) &&& 0x3ffff03,
   ((t1 >>> 20) ||| (t2 <<< 12)) &&& 0x3ffc0ff,
   ((t2 >>> 14) ||| (t3 <<< 18)) &&& 0x3f03fff,
   (t3 >>> 8) &&& 0x00fffff⟩

@[inline] def convolve (h : Limbs) (r : RKey) : Limbs :=
  let s1 := r.r1 * 5
  let s2 := r.r2 * 5
  let s3 := r.r3 * 5
  let s4 := r.r4 * 5
  let d0 := h.h0*r.r0 + h.h1*s4 + h.h2*s3 + h.h3*s2 + h.h4*s1
  let d1 := h.h0*r.r1 + h.h1*r.r0 + h.h2*s4 + h.h3*s3 + h.h4*s2
  let d2 := h.h0*r.r2 + h.h1*r.r1 + h.h2*r.r0 + h.h3*s4 + h.h4*s3
  let d3 := h.h0*r.r3 + h.h1*r.r2 + h.h2*r.r1 + h.h3*r.r0 + h.h4*s4
  let d4 := h.h0*r.r4 + h.h1*r.r3 + h.h2*r.r2 + h.h3*r.r1 + h.h4*r.r0
  ⟨d0, d1, d2, d3, d4⟩

@[inline] def carryWords (d : Limbs) : Limbs :=
  let c0 := d.h0 >>> 26
  let h0 := d.h0 &&& 0x3ffffff
  let d1 := d.h1 + c0
  let c1 := d1 >>> 26
  let h1 := d1 &&& 0x3ffffff
  let d2 := d.h2 + c1
  let c2 := d2 >>> 26
  let h2 := d2 &&& 0x3ffffff
  let d3 := d.h3 + c2
  let c3 := d3 >>> 26
  let h3 := d3 &&& 0x3ffffff
  let d4 := d.h4 + c3
  let c4 := d4 >>> 26
  let h4 := d4 &&& 0x3ffffff
  let h0 := h0 + c4 * 5
  let c0 := h0 >>> 26
  ⟨h0 &&& 0x3ffffff, h1 + c0, h2, h3, h4⟩

@[inline] def mulReduce (h : Limbs) (r : RKey) : Limbs :=
  carryWords (convolve h r)

def Limbs.addNat (h : Limbs) (n : Nat) : Limbs :=
  ⟨h.h0 + (n % limbBase).toUInt64,
   h.h1 + (n / limbBase % limbBase).toUInt64,
   h.h2 + (n / limbBase ^ 2 % limbBase).toUInt64,
   h.h3 + (n / limbBase ^ 3 % limbBase).toUInt64,
   h.h4 + (n / limbBase ^ 4 % limbBase).toUInt64⟩

def blocksList (r : RKey) : List UInt8 → Limbs → Limbs
  | [], h => h
  | b :: bs, h =>
      let bytes := b :: bs
      let chunk := bytes.take 16
      let block := bytesToNatLE chunk + 256 ^ chunk.length
      blocksList r (bytes.drop 16) (mulReduce (h.addNat block) r)
termination_by bytes _ => bytes.length
decreasing_by simp_wf; omega

@[inline] def addBlock (h : Limbs) (a : Array UInt8) (offset count : Nat) : Limbs :=
  let t0 := load32 a offset
  let t1 := load32 a (offset + 4)
  let t2 := load32 a (offset + 8)
  let t3 := load32 a (offset + 12)
  let hibit : UInt64 := if count = 16 then (1 : UInt64) <<< 24 else 0
  ⟨h.h0 + (t0 &&& 0x3ffffff),
   h.h1 + (((t0 >>> 26) ||| (t1 <<< 6)) &&& 0x3ffffff),
   h.h2 + (((t1 >>> 20) ||| (t2 <<< 12)) &&& 0x3ffffff),
   h.h3 + (((t2 >>> 14) ||| (t3 <<< 18)) &&& 0x3ffffff),
   h.h4 + ((t3 >>> 8) ||| hibit)⟩

def paddedBlock (a : Array UInt8) (offset count : Nat) : Array UInt8 :=
  Array.ofFn (n := 16) fun i =>
    if i.val < count then a[offset + i.val]! else if i.val = count then 1 else 0

def blocks (r : RKey) (a : Array UInt8) : Nat → Nat → Limbs → Limbs
  | 0, _, h => h
  | n + 1, offset, h =>
      let count := min 16 (a.size - offset)
      let block := if count = 16 then a else paddedBlock a offset count
      let blockOffset := if count = 16 then offset else 0
      let h := addBlock h block blockOffset count
      blocks r a n (offset + 16) (mulReduce h r)

def finish (h : Limbs) (key : Array UInt8) : Array UInt8 :=
  let c1 := h.h1 >>> 26; let h1 := h.h1 &&& 0x3ffffff; let h2 := h.h2 + c1
  let c2 := h2 >>> 26; let h2 := h2 &&& 0x3ffffff; let h3 := h.h3 + c2
  let c3 := h3 >>> 26; let h3 := h3 &&& 0x3ffffff; let h4 := h.h4 + c3
  let c4 := h4 >>> 26; let h4 := h4 &&& 0x3ffffff; let h0 := h.h0 + c4*5
  let c0 := h0 >>> 26; let h0 := h0 &&& 0x3ffffff; let h1 := h1 + c0
  let g0 := h0 + 5
  let c0 := g0 >>> 26; let g0 := g0 &&& 0x3ffffff
  let g1 := h1 + c0; let c1 := g1 >>> 26; let g1 := g1 &&& 0x3ffffff
  let g2 := h2 + c1; let c2 := g2 >>> 26; let g2 := g2 &&& 0x3ffffff
  let g3 := h3 + c2; let c3 := g3 >>> 26; let g3 := g3 &&& 0x3ffffff
  let g4 := h4 + c3 - ((1 : UInt64) <<< 26)
  let mask : UInt64 := (g4 >>> 63) - 1
  let nmask := ~~~mask
  let h0 := (h0 &&& nmask) ||| (g0 &&& mask)
  let h1 := (h1 &&& nmask) ||| (g1 &&& mask)
  let h2 := (h2 &&& nmask) ||| (g2 &&& mask)
  let h3 := (h3 &&& nmask) ||| (g3 &&& mask)
  let h4 := (h4 &&& nmask) ||| (g4 &&& mask)
  let f0 := (h0 ||| (h1 <<< 26)) &&& 0xffffffff
  let f1 := ((h1 >>> 6) ||| (h2 <<< 20)) &&& 0xffffffff
  let f2 := ((h2 >>> 12) ||| (h3 <<< 14)) &&& 0xffffffff
  let f3 := ((h3 >>> 18) ||| (h4 <<< 8)) &&& 0xffffffff
  let f0 := f0 + load32 key 16
  let f1 := f1 + load32 key 20 + (f0 >>> 32)
  let f2 := f2 + load32 key 24 + (f1 >>> 32)
  let f3 := f3 + load32 key 28 + (f2 >>> 32)
  let words := #[f0, f1, f2, f3]
  Array.ofFn (n := 16) fun i => ((words[i.val / 4]! >>> ((i.val % 4) * 8).toUInt64).toUInt8)

def poly1305 (message keyBytes : List UInt8) : List UInt8 :=
  let rNat := bytesToNatLE (keyBytes.take 16) &&&
    0x0ffffffc0ffffffc0ffffffc0fffffff
  let r := RKey.ofNat rNat
  let h := blocksList r message ⟨0, 0, 0, 0, 0⟩
  let s := bytesToNatLE (keyBytes.drop 16 |>.take 16)
  natToBytesLE 16 ((h.value % prime + s) % (2 ^ 128))

end Crypto.ChaCha20Poly1305.Fast
