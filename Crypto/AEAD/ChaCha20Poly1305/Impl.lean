import Crypto.AEAD.ChaCha20Poly1305.Spec
import Crypto.AEAD.ChaCha20Poly1305.WordBlocks
import Crypto.AEAD.ChaCha20Poly1305.Machine
import Crypto.Stream.ChaCha20.Impl

namespace Crypto.ChaCha20Poly1305

open Crypto.ChaCha20
abbrev Sealed := Spec.Sealed

/-- Counter zero is used exclusively for Poly1305 key derivation. -/
def oneTimeKey (key : Key) (nonce : Nonce) : List UInt8 :=
  (keystreamBlock key nonce 0).toList.take 32

/-! ## Independent byte encoding -/

def bytesToNatLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesToNatLE bs

def natToBytesLE (count n : Nat) : List UInt8 :=
  (List.range count).map fun i => ((n / 256 ^ i) % 256).toUInt8

def padding16 (size : Nat) : List UInt8 :=
  List.replicate ((16 - size % 16) % 16) 0

def encodeLE64 (n : Nat) : List UInt8 := natToBytesLE 8 n

/-- Runtime construction of the RFC 8439 authenticated byte string.
    This definition deliberately does not call the specification encoder. -/
def encodeMacData (aad ciphertext : Array UInt8) : List UInt8 :=
  aad.toList ++ padding16 aad.size ++
  ciphertext.toList ++ padding16 ciphertext.size ++
  encodeLE64 aad.size ++ encodeLE64 ciphertext.size

/-- Construct authenticated bytes directly in array storage. -/
def encodeMacDataArray (aad ciphertext : Array UInt8) : Array UInt8 :=
  aad ++ Array.replicate ((16-aad.size%16)%16) 0 ++
  ciphertext ++ Array.replicate ((16-ciphertext.size%16)%16) 0 ++
  (encodeLE64 aad.size).toArray ++ (encodeLE64 ciphertext.size).toArray

/-! ## Five 26-bit limbs -/

def limbBase : Nat := 2 ^ 26
def poly1305Prime : Nat := 2 ^ 130 - 5
def clampMask : Nat := 0x0ffffffc0ffffffc0ffffffc0fffffff

/-- A machine-word representation whose live values are canonical 26-bit limbs. -/
structure Limbs26 where
  l0 : UInt64
  l1 : UInt64
  l2 : UInt64
  l3 : UInt64
  l4 : UInt64
  l0_lt : l0.toNat < limbBase
  l1_lt : l1.toNat < limbBase
  l2_lt : l2.toNat < limbBase
  l3_lt : l3.toNat < limbBase
  l4_lt : l4.toNat < limbBase

def mkLimb (n : Nat) : UInt64 :=
  UInt64.ofNatLT (n % limbBase) (by
    apply Nat.lt_trans (Nat.mod_lt _ (by simp [limbBase]))
    simp [limbBase, UInt64.size])

@[simp] theorem mkLimb_toNat (n : Nat) : (mkLimb n).toNat = n % limbBase := by
  simp [mkLimb]

def Limbs26.ofNat (n : Nat) : Limbs26 :=
  ⟨mkLimb n, mkLimb (n / limbBase), mkLimb (n / limbBase / limbBase),
   mkLimb (n / limbBase / limbBase / limbBase),
   mkLimb (n / limbBase / limbBase / limbBase / limbBase),
   by rw [mkLimb_toNat]; exact Nat.mod_lt _ (by simp [limbBase]),
   by rw [mkLimb_toNat]; exact Nat.mod_lt _ (by simp [limbBase]),
   by rw [mkLimb_toNat]; exact Nat.mod_lt _ (by simp [limbBase]),
   by rw [mkLimb_toNat]; exact Nat.mod_lt _ (by simp [limbBase]),
   by rw [mkLimb_toNat]; exact Nat.mod_lt _ (by simp [limbBase])⟩

def Limbs26.toNat (x : Limbs26) : Nat :=
  x.l0.toNat + limbBase * (x.l1.toNat + limbBase *
    (x.l2.toNat + limbBase * (x.l3.toNat + limbBase * x.l4.toNat)))

/-- Canonical reduction into five 26-bit machine-word limbs. -/
def Limbs26.reduce (n : Nat) : Limbs26 := Limbs26.ofNat (n % poly1305Prime)

/-! The convolution below is the usual radix-2^26 Poly1305 multiplication.
Products whose degree is at least five wrap around with a factor of five,
using `(2^26)^5 = 2^130 ≡ 5 (mod 2^130-5)`.  It never constructs the
full 260-bit product. -/

def limbConvolution (a r : Limbs26) : Nat :=
  let a0 := a.l0.toNat; let a1 := a.l1.toNat; let a2 := a.l2.toNat
  let a3 := a.l3.toNat; let a4 := a.l4.toNat
  let r0 := r.l0.toNat; let r1 := r.l1.toNat; let r2 := r.l2.toNat
  let r3 := r.l3.toNat; let r4 := r.l4.toNat
  let d0 := a0*r0 + 5*(a1*r4 + a2*r3 + a3*r2 + a4*r1)
  let d1 := a0*r1 + a1*r0 + 5*(a2*r4 + a3*r3 + a4*r2)
  let d2 := a0*r2 + a1*r1 + a2*r0 + 5*(a3*r4 + a4*r3)
  let d3 := a0*r3 + a1*r2 + a2*r1 + a3*r0 + 5*(a4*r4)
  let d4 := a0*r4 + a1*r3 + a2*r2 + a3*r1 + a4*r0
  d0 + limbBase * (d1 + limbBase * (d2 + limbBase * (d3 + limbBase * d4)))

def Limbs26.mulMod (a r : Limbs26) : Limbs26 :=
  Limbs26.reduce (limbConvolution a r)

def polyStep (r : Nat) (acc : Limbs26) (chunk : List UInt8) : Limbs26 :=
  let block := bytesToNatLE chunk + 256 ^ chunk.length
  let added := Limbs26.reduce (acc.toNat + block)
  added.mulMod (Limbs26.reduce r)

def polyBlocks (r : Nat) : List UInt8 → Limbs26 → Limbs26
  | [], acc => acc
  | b :: bs, acc =>
      let bytes := b :: bs
      let chunk := bytes.take 16
      polyBlocks r (bytes.drop 16) (polyStep r acc chunk)
termination_by bytes _ => bytes.length
decreasing_by simp_wf; omega

/-- Poly1305 with machine-word key setup, multiplication, carries, and finalization.
    The final short message block retains the reference decoder. -/
def poly1305 (message oneTimeKey : List UInt8) : List UInt8 :=
  Machine.poly1305 message oneTimeKey

/-- Array API avoids converting the message into a linked list. -/
def poly1305Array (message oneTimeKey : Array UInt8) : List UInt8 :=
  Machine.poly1305Array message oneTimeKey

def authenticate (aad ciphertext : Array UInt8) (oneTimeKey : List UInt8) : List UInt8 :=
  poly1305Array (encodeMacDataArray aad ciphertext) oneTimeKey.toArray

def sealPacket (key : Key) (nonce : Nonce) (aad plaintext : Array UInt8) : Sealed :=
  let ciphertext := Crypto.ChaCha20.encrypt key nonce plaintext
  ⟨ciphertext, authenticate aad ciphertext (oneTimeKey key nonce)⟩

/-- Functional full-tag comparison. Constant-time behavior is outside this Lean model. -/
def tagMatches (supplied expected : List UInt8) : Bool :=
  supplied.length == 16 && expected.length == 16 && supplied == expected

/-- Authenticate before decrypting. A failure contains no plaintext value. -/
def open? (key : Key) (nonce : Nonce) (aad : Array UInt8) (packet : Sealed) : Option (Array UInt8) :=
  let expected := authenticate aad packet.ciphertext (oneTimeKey key nonce)
  if tagMatches packet.tag expected then
    some (Crypto.ChaCha20.decrypt key nonce packet.ciphertext)
  else none

end Crypto.ChaCha20Poly1305
