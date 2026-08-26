/-
  Inspectable RFC 8439 ChaCha20-Poly1305 AEAD specification.

  This module deliberately spells out the composition boundary: counter zero
  derives the one-time MAC key, payload encryption starts at counter one, and
  the MAC covers padded AAD, padded ciphertext, and two little-endian lengths.
-/

import Crypto.Stream.ChaCha20.Spec

namespace Crypto.ChaCha20Poly1305.Spec

abbrev Key := Crypto.ChaCha20.Spec.Key
abbrev Nonce := Crypto.ChaCha20.Spec.Nonce
abbrev ByteString := Array UInt8

/-- Mathematical serialization of a ChaCha20 block at an explicit counter. -/
def blockBytes (key : Key) (nonce : Nonce) (counter : UInt32) : ByteString :=
  let state := Crypto.ChaCha20.Spec.block key counter nonce
  Array.ofFn (n := 64) fun i =>
    Crypto.ChaCha20.Spec.stateToBytes state ⟨i.val, i.isLt⟩

/-- RFC 8439's 256-bit one-time Poly1305 key, derived with counter zero. -/
def oneTimeKey (key : Key) (nonce : Nonce) : List UInt8 :=
  (blockBytes key nonce 0).toList.take 32

def bytesToNatLE : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * bytesToNatLE bs

def natToBytesLE (count n : Nat) : List UInt8 :=
  (List.range count).map fun i => ((n / 256 ^ i) % 256).toUInt8

def pad16 (xs : List UInt8) : List UInt8 :=
  List.replicate ((16 - xs.length % 16) % 16) 0

/-- Exactly eight bytes, least-significant byte first. -/
def le64 (n : Nat) : List UInt8 := natToBytesLE 8 n

/-- The exact byte layout authenticated by RFC 8439. -/
def macData (aad ciphertext : ByteString) : List UInt8 :=
  aad.toList ++ pad16 aad.toList ++
  ciphertext.toList ++ pad16 ciphertext.toList ++
  le64 aad.size ++ le64 ciphertext.size

def poly1305Prime : Nat := 2 ^ 130 - 5
def clampMask : Nat := 0x0ffffffc0ffffffc0ffffffc0fffffff

def polyStep (r acc : Nat) (chunk : List UInt8) : Nat :=
  ((acc + bytesToNatLE chunk + 256 ^ chunk.length) * r) % poly1305Prime

def polyBlocks (r : Nat) : List UInt8 → Nat → Nat
  | [], acc => acc
  | b :: bs, acc =>
      let bytes := b :: bs
      let chunk := bytes.take 16
      polyBlocks r (bytes.drop 16) (polyStep r acc chunk)
termination_by bytes _ => bytes.length
decreasing_by simp_wf; omega

/-- Straightforward mathematical Poly1305, using unbounded naturals. -/
def poly1305 (message oneTimeKey : List UInt8) : List UInt8 :=
  let r := bytesToNatLE (oneTimeKey.take 16) &&& clampMask
  let s := bytesToNatLE (oneTimeKey.drop 16 |>.take 16)
  natToBytesLE 16 ((polyBlocks r message 0 + s) % (2 ^ 128))

def payload (key : Key) (nonce : Nonce) (plaintext : ByteString) : ByteString :=
  Crypto.ChaCha20.Spec.encrypt key nonce plaintext

structure Sealed where
  ciphertext : ByteString
  tag : List UInt8
  deriving Repr

def sealPacket (key : Key) (nonce : Nonce) (aad plaintext : ByteString) : Sealed :=
  let ciphertext := payload key nonce plaintext
  ⟨ciphertext, poly1305 (macData aad ciphertext) (oneTimeKey key nonce)⟩

/-- Specification decryption releases plaintext only when the complete tag matches. -/
def open? (key : Key) (nonce : Nonce) (aad : ByteString) (packet : Sealed) : Option ByteString :=
  let expected := poly1305 (macData aad packet.ciphertext) (oneTimeKey key nonce)
  if packet.tag = expected then some (payload key nonce packet.ciphertext) else none

end Crypto.ChaCha20Poly1305.Spec
