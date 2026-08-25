/-
  Crypto.Stream.ChaCha20.Impl

  CHACHA20 CIPHER IMPLEMENTATION
  ==============================
  Array implementation with:
  1. Array-based state (O(1) random access, cache-friendly)
  2. Inlined quarter round operations
  3. Block-oriented encryption that computes each keystream block once
  4. A public encryption path whose control flow depends only on message length
-/

import Crypto.Stream.ChaCha20.Spec

namespace Crypto.ChaCha20

open Spec (Word rotl)

/-! ## Array-based state representation -/

/-- State as a fixed-size array of 16 words -/
abbrev StateArray := Array Word

/-- Ensure state array has exactly 16 elements -/
structure ValidState where
  arr : StateArray
  size_eq : arr.size = 16

/-! ## Key and Nonce types -/

structure Key where
  words : Array Word
  size_eq : words.size = 8

structure Nonce where
  words : Array Word
  size_eq : words.size = 3

/-! ## Constants (same as spec) -/

def const0 : Word := 0x61707865
def const1 : Word := 0x3320646e
def const2 : Word := 0x79622d32
def const3 : Word := 0x6b206574

/-! ## Optimized Quarter Round (inlined operations)

  Uses the same rotl from spec but with inline annotation
  for better code generation.
-/

/-- Quarter round returning 4 words - same logic as spec but explicit -/
@[inline]
def quarterRound (a b c d : Word) : Word × Word × Word × Word :=
  -- Step 1: a += b; d ^= a; d <<<= 16
  let a := a + b
  let d := rotl (d ^^^ a) 16
  -- Step 2: c += d; b ^= c; b <<<= 12
  let c := c + d
  let b := rotl (b ^^^ c) 12
  -- Step 3: a += b; d ^= a; d <<<= 8
  let a := a + b
  let d := rotl (d ^^^ a) 8
  -- Step 4: c += d; b ^= c; b <<<= 7
  let c := c + d
  let b := rotl (b ^^^ c) 7
  (a, b, c, d)

/-! ## State Operations with Proof-carrying Indices -/

/-- Get element from key with bounds proof -/
@[inline]
def Key.get (k : Key) (i : Fin 8) : Word :=
  k.words[i.val]'(by rw [k.size_eq]; exact i.isLt)

/-- Get element from nonce with bounds proof -/
@[inline]
def Nonce.get (n : Nonce) (i : Fin 3) : Word :=
  n.words[i.val]'(by rw [n.size_eq]; exact i.isLt)

/-- Initialize state array from key, counter, nonce -/
def initStateArray (key : Key) (counter : Word) (nonce : Nonce) : ValidState :=
  let arr : StateArray := #[
    const0, const1, const2, const3,
    key.get ⟨0, by omega⟩, key.get ⟨1, by omega⟩,
    key.get ⟨2, by omega⟩, key.get ⟨3, by omega⟩,
    key.get ⟨4, by omega⟩, key.get ⟨5, by omega⟩,
    key.get ⟨6, by omega⟩, key.get ⟨7, by omega⟩,
    counter,
    nonce.get ⟨0, by omega⟩, nonce.get ⟨1, by omega⟩, nonce.get ⟨2, by omega⟩
  ]
  ⟨arr, rfl⟩

/-! ## Size-preserving array operations -/

/-- set! preserves array size when index is valid -/
theorem Array.size_set!_of_lt {α : Type} (a : Array α) (i : Nat) (v : α) (h : i < a.size) :
    (a.set! i v).size = a.size := by
  simp [Array.set!, Array.setIfInBounds, h]

/-- Apply quarter round to array at indices a, b, c, d
    Uses unchecked array access for performance -/
@[inline]
def applyQRArrayUnchecked (s : StateArray) (ai bi ci di : Nat) : StateArray :=
  let a := s[ai]!
  let b := s[bi]!
  let c := s[ci]!
  let d := s[di]!
  let (a', b', c', d') := quarterRound a b c d
  let s := s.set! ai a'
  let s := s.set! bi b'
  let s := s.set! ci c'
  let s := s.set! di d'
  s

/-- applyQRArrayUnchecked preserves size -/
theorem applyQRArrayUnchecked_size (s : StateArray) (ai bi ci di : Nat)
    (hai : ai < s.size) (hbi : bi < s.size) (hci : ci < s.size) (hdi : di < s.size) :
    (applyQRArrayUnchecked s ai bi ci di).size = s.size := by
  unfold applyQRArrayUnchecked
  repeat rw [Array.size_set!_of_lt]
  all_goals simp_all

/-- A quarter round with the 16-word state invariant carried structurally. -/
def applyQRValid (s : ValidState) (ai bi ci di : Fin 16) : ValidState :=
  ⟨applyQRArrayUnchecked s.arr ai.val bi.val ci.val di.val,
   applyQRArrayUnchecked_size s.arr ai.val bi.val ci.val di.val
     (by rw [s.size_eq]; exact ai.isLt) (by rw [s.size_eq]; exact bi.isLt)
     (by rw [s.size_eq]; exact ci.isLt) (by rw [s.size_eq]; exact di.isLt) ▸ s.size_eq⟩

/-- Column round on array: QR on each column
    Indices: (0,4,8,12), (1,5,9,13), (2,6,10,14), (3,7,11,15) -/
@[inline]
def columnRoundArray (s : StateArray) : StateArray :=
  let s := applyQRArrayUnchecked s 0 4 8 12
  let s := applyQRArrayUnchecked s 1 5 9 13
  let s := applyQRArrayUnchecked s 2 6 10 14
  let s := applyQRArrayUnchecked s 3 7 11 15
  s

theorem columnRoundArray_size (s : StateArray) (hs : s.size = 16) :
    (columnRoundArray s).size = 16 := by
  unfold columnRoundArray
  have h0 : (applyQRArrayUnchecked s 0 4 8 12).size = 16 := by
    rw [applyQRArrayUnchecked_size] <;> omega
  have h1 : (applyQRArrayUnchecked (applyQRArrayUnchecked s 0 4 8 12) 1 5 9 13).size = 16 := by
    rw [applyQRArrayUnchecked_size] <;> omega
  have h2 : (applyQRArrayUnchecked (applyQRArrayUnchecked (applyQRArrayUnchecked s 0 4 8 12) 1 5 9 13) 2 6 10 14).size = 16 := by
    rw [applyQRArrayUnchecked_size] <;> omega
  rw [applyQRArrayUnchecked_size] <;> omega

/-- Diagonal round on array: QR on each diagonal
    Indices: (0,5,10,15), (1,6,11,12), (2,7,8,13), (3,4,9,14) -/
@[inline]
def diagonalRoundArray (s : StateArray) : StateArray :=
  let s := applyQRArrayUnchecked s 0 5 10 15
  let s := applyQRArrayUnchecked s 1 6 11 12
  let s := applyQRArrayUnchecked s 2 7 8 13
  let s := applyQRArrayUnchecked s 3 4 9 14
  s

theorem diagonalRoundArray_size (s : StateArray) (hs : s.size = 16) :
    (diagonalRoundArray s).size = 16 := by
  unfold diagonalRoundArray
  have h0 : (applyQRArrayUnchecked s 0 5 10 15).size = 16 := by
    rw [applyQRArrayUnchecked_size] <;> omega
  have h1 : (applyQRArrayUnchecked (applyQRArrayUnchecked s 0 5 10 15) 1 6 11 12).size = 16 := by
    rw [applyQRArrayUnchecked_size] <;> omega
  have h2 : (applyQRArrayUnchecked (applyQRArrayUnchecked (applyQRArrayUnchecked s 0 5 10 15) 1 6 11 12) 2 7 8 13).size = 16 := by
    rw [applyQRArrayUnchecked_size] <;> omega
  rw [applyQRArrayUnchecked_size] <;> omega

def columnRoundValid (s : ValidState) : ValidState :=
  applyQRValid (applyQRValid (applyQRValid (applyQRValid s 0 4 8 12) 1 5 9 13) 2 6 10 14) 3 7 11 15

def diagonalRoundValid (s : ValidState) : ValidState :=
  applyQRValid (applyQRValid (applyQRValid (applyQRValid s 0 5 10 15) 1 6 11 12) 2 7 8 13) 3 4 9 14

def doubleRoundValid (s : ValidState) : ValidState :=
  diagonalRoundValid (columnRoundValid s)

/-- Double round on array = diagonal ∘ column -/
@[inline]
def doubleRoundArray (s : StateArray) : StateArray :=
  diagonalRoundArray (columnRoundArray s)

theorem doubleRoundArray_size (s : StateArray) (hs : s.size = 16) :
    (doubleRoundArray s).size = 16 := by
  unfold doubleRoundArray
  exact diagonalRoundArray_size _ (columnRoundArray_size s hs)

/-! ## N Rounds with Tail Recursion -/

/-- Apply n double rounds to array (tail-recursive) -/
def nRoundsArrayTR (n : Nat) (s : StateArray) : StateArray :=
  match n with
  | 0 => s
  | n + 1 => nRoundsArrayTR n (doubleRoundArray s)

theorem nRoundsArrayTR_size (n : Nat) (s : StateArray) (hs : s.size = 16) :
    (nRoundsArrayTR n s).size = 16 := by
  induction n generalizing s with
  | zero => simp [nRoundsArrayTR, hs]
  | succ n ih =>
    simp only [nRoundsArrayTR]
    exact ih _ (doubleRoundArray_size s hs)

/-- Tail-recursive rounds with the 16-word invariant carried structurally. -/
def nRoundsState : Nat → ValidState → ValidState
  | 0, s => s
  | n + 1, s =>
      nRoundsState n (doubleRoundValid s)

/-- Add two state arrays element-wise -/
@[inline]
def addArrays (s1 s2 : StateArray) : StateArray :=
  Array.zipWith (· + ·) s1 s2

theorem addArrays_size (s1 s2 : StateArray) (h1 : s1.size = 16) (h2 : s2.size = 16) :
    (addArrays s1 s2).size = 16 := by
  simp only [addArrays, Array.size_zipWith, h1, h2, Nat.min_self]

/-! ## Block Function -/

/-- ChaCha20 block function on arrays
    Computes: initial + nRounds(10, initial) -/
def blockArray (key : Key) (counter : Word) (nonce : Nonce) : ValidState :=
  let initial := initStateArray key counter nonce
  let final := nRoundsState 10 initial
  let result := addArrays final.arr initial.arr
  ⟨result, addArrays_size final.arr initial.arr final.size_eq initial.size_eq⟩

/-! ## Serialization -/

/-- Extract byte from word at position (0-3, little-endian) -/
@[inline]
def wordToByte (w : Word) (pos : Nat) : UInt8 :=
  (w >>> (pos * 8).toUInt32).toUInt8

/-- State to 64 bytes (little-endian). -/
def stateToBytesArray (s : ValidState) : Array UInt8 :=
  Array.ofFn (n := 64) fun i =>
    wordToByte s.arr[i.val / 4]! (i.val % 4)

/-- Helper: pushing 4 elements increases size by 4 -/
theorem push4_size (arr : Array UInt8) (a b c d : UInt8) :
    (arr.push a |>.push b |>.push c |>.push d).size = arr.size + 4 := by
  simp [Array.size_push]

/-- Proof that stateToBytesArray produces exactly 64 bytes -/
theorem stateToBytesArray_size (s : ValidState) :
    (stateToBytesArray s).size = 64 := by
  simp [stateToBytesArray]

/-! ## Keystream Generation -/

/-- Generate keystream for a given block number -/
def keystreamBlock (key : Key) (nonce : Nonce) (blockNum : Word) : Array UInt8 :=
  stateToBytesArray (blockArray key blockNum nonce)

theorem keystreamBlock_size (key : Key) (nonce : Nonce) (blockNum : Word) :
    (keystreamBlock key nonce blockNum).size = 64 := by
  simp [keystreamBlock, stateToBytesArray_size]

/-! ## Length-oblivious block encryption -/

/-- Generate exactly `numBlocks` blocks, in counter order. -/
def generateKeystreamBlocks (key : Key) (nonce : Nonce) (numBlocks : Nat) :
    Array (Array UInt8) :=
  Array.ofFn (n := numBlocks) fun blockIndex =>
    keystreamBlock key nonce (blockIndex.val.toUInt32 + 1)

/-- XOR a message against precomputed blocks.  This loop performs one XOR per
    message byte and contains no cache hit/miss or byte-value branch. -/
def encryptCore (msg : Array UInt8) (blocks : Array (Array UInt8)) : Array UInt8 :=
  Array.ofFn (n := msg.size) fun i =>
    msg[i.val] ^^^ blocks[i.val / 64]![i.val % 64]!

/-- Block-oriented ChaCha20 encryption.  Its block schedule, loop counts, and
    array indices are functions of `msg.size`; byte values never affect control flow. -/
def encryptBlocks (key : Key) (nonce : Nonce) (msg : Array UInt8) : Array UInt8 :=
  let numBlocks := (msg.size + 63) / 64
  let blocks := generateKeystreamBlocks key nonce numBlocks
  encryptCore msg blocks

/-- Public encryption entry point. -/
def encrypt (key : Key) (nonce : Nonce) (msg : Array UInt8) : Array UInt8 :=
  encryptBlocks key nonce msg

/-- Decrypt is the same as encrypt (XOR is self-inverse) -/
def decrypt (key : Key) (nonce : Nonce) (msg : Array UInt8) : Array UInt8 :=
  encrypt key nonce msg

/-! ## List-based API (for compatibility with spec) -/

/-- Convert list-based key to array key -/
def keyFromList (words : List Word) (h : words.length = 8) : Key :=
  ⟨words.toArray, by simp [h]⟩

/-- Convert list-based nonce to array nonce -/
def nonceFromList (words : List Word) (h : words.length = 3) : Nonce :=
  ⟨words.toArray, by simp [h]⟩

/-- Encrypt with list input/output -/
def encryptList (key : Key) (nonce : Nonce) (msg : List UInt8) : List UInt8 :=
  (encrypt key nonce msg.toArray).toList

/-- Decrypt with list input/output -/
def decryptList (key : Key) (nonce : Nonce) (msg : List UInt8) : List UInt8 :=
  (decrypt key nonce msg.toArray).toList

/-! ## Size Preservation Theorems -/

theorem encrypt_size (key : Key) (nonce : Nonce) (msg : Array UInt8) :
    (encrypt key nonce msg).size = msg.size := by
  simp [encrypt, encryptBlocks, encryptCore]

theorem decrypt_size (key : Key) (nonce : Nonce) (msg : Array UInt8) :
    (decrypt key nonce msg).size = msg.size :=
  encrypt_size key nonce msg

end Crypto.ChaCha20
