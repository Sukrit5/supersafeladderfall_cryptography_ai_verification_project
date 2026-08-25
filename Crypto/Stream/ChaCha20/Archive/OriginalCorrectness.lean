/-
  Crypto.Stream.ChaCha20.Correctness

  CORRECTNESS PROOFS
  ==================
  This file proves the array implementation matches the minimal spec.

  REVIEW GUIDE:
  - INSPECTABLE THEOREMS: the end-to-end claims a reviewer should audit
  - SUPPORTING PROOF MACHINERY: representation and composition lemmas used by them
-/

import Crypto.Stream.ChaCha20.Spec
import Crypto.Stream.ChaCha20.Archive.OriginalImpl

namespace Crypto.ChaCha20

/-!
══════════════════════════════════════════════════════════════════════════════
 SUPPORTING PROOF MACHINERY
══════════════════════════════════════════════════════════════════════════════
-/

/-! ### Helper lemmas for array access -/

/-- Bounded array access equals unbounded access when index is in bounds -/
theorem Array.bounded_eq_unbounded {α : Type} [Inhabited α] (a : Array α) (i : Nat) (h : i < a.size) :
    a[i]'h = a[i]! := by
  simp [GetElem?.getElem!, Array.get!Internal, Array.getD, h]

/-! ### XOR properties -/

/-- XOR is self-inverse for UInt8 -/
theorem UInt8.xor_self_inverse (x k : UInt8) : (x ^^^ k) ^^^ k = x := by
  rw [UInt8.xor_assoc, UInt8.xor_self, UInt8.xor_zero]

/-- XOR with same keystream cancels -/
theorem xor_keystream_cancel (x ks : UInt8) : (x ^^^ ks) ^^^ ks = x :=
  UInt8.xor_self_inverse x ks

/-! ### Quarter round is identical -/

/-- The implementation quarter round equals the spec quarter round -/
theorem quarterRound_eq_spec (a b c d : Spec.Word) :
    quarterRound a b c d = Spec.quarterRound a b c d := rfl

/-! ### Constants are identical -/

theorem const0_eq : const0 = Spec.const0 := rfl
theorem const1_eq : const1 = Spec.const1 := rfl
theorem const2_eq : const2 = Spec.const2 := rfl
theorem const3_eq : const3 = Spec.const3 := rfl

/-! ### Conversion between array state and function state -/

/-- Convert ValidState (array) to Spec.State (function) -/
def toSpecState (s : ValidState) : Spec.State := fun i =>
  s.arr[i.val]!

/-- Convert Spec.State (function) to ValidState (array) -/
def fromSpecState (s : Spec.State) : ValidState :=
  ⟨Array.ofFn (n := 16) (fun i => s i), by simp⟩

theorem fromSpecState_toSpecState (s : Spec.State) :
    toSpecState (fromSpecState s) = s := by
  funext i
  simp [toSpecState, fromSpecState]

/-! ### Key and Nonce conversion -/

/-- Convert implementation Key to spec Key -/
def keyToSpec (k : Key) : Spec.Key := fun i =>
  k.words[i.val]!

/-- Convert implementation Nonce to spec Nonce -/
def nonceToSpec (n : Nonce) : Spec.Nonce := fun i =>
  n.words[i.val]!

/-! ### State initialization proof -/

/-- initStateArray produces an array where each position matches the spec's initState -/
theorem initStateArray_correct (key : Key) (counter : Spec.Word) (nonce : Nonce) (i : Fin 16) :
    (initStateArray key counter nonce).arr[i.val]! =
    Spec.initState (keyToSpec key) counter (nonceToSpec nonce) i := by
  simp only [initStateArray, Spec.initState, keyToSpec, nonceToSpec, Key.get, Nonce.get]
  -- Don't unfold constants to preserve equality
  rcases i with ⟨i, hi⟩
  match i, hi with
  | 0, _ => simp +arith; rfl
  | 1, _ => simp +arith; rfl
  | 2, _ => simp +arith; rfl
  | 3, _ => simp +arith; rfl
  | 4, _ =>
    simp +arith
    rw [← Array.bounded_eq_unbounded key.words 0 (by rw [key.size_eq]; omega)]
  | 5, _ =>
    simp +arith
    rw [← Array.bounded_eq_unbounded key.words 1 (by rw [key.size_eq]; omega)]
  | 6, _ =>
    simp +arith
    rw [← Array.bounded_eq_unbounded key.words 2 (by rw [key.size_eq]; omega)]
  | 7, _ =>
    simp +arith
    rw [← Array.bounded_eq_unbounded key.words 3 (by rw [key.size_eq]; omega)]
  | 8, _ =>
    simp +arith
    rw [← Array.bounded_eq_unbounded key.words 4 (by rw [key.size_eq]; omega)]
  | 9, _ =>
    simp +arith
    rw [← Array.bounded_eq_unbounded key.words 5 (by rw [key.size_eq]; omega)]
  | 10, _ =>
    simp +arith
    rw [← Array.bounded_eq_unbounded key.words 6 (by rw [key.size_eq]; omega)]
  | 11, _ =>
    simp +arith
    rw [← Array.bounded_eq_unbounded key.words 7 (by rw [key.size_eq]; omega)]
  | 12, _ => simp +arith
  | 13, _ =>
    simp +arith
    rw [← Array.bounded_eq_unbounded nonce.words 0 (by rw [nonce.size_eq]; omega)]
  | 14, _ =>
    simp +arith
    rw [← Array.bounded_eq_unbounded nonce.words 1 (by rw [nonce.size_eq]; omega)]
  | 15, _ =>
    simp +arith
    rw [← Array.bounded_eq_unbounded nonce.words 2 (by rw [nonce.size_eq]; omega)]
  | n + 16, h => exact absurd h (by omega)

theorem initStateArray_matches_spec (key : Key) (counter : Spec.Word) (nonce : Nonce) :
    toSpecState (initStateArray key counter nonce) =
    Spec.initState (keyToSpec key) counter (nonceToSpec nonce) := by
  funext i
  simp only [toSpecState]
  exact initStateArray_correct key counter nonce i

/-! ### Round-function correctness -/

set_option maxHeartbeats 200000
set_option maxRecDepth 10000

/-- Updating four distinct array positions implements the functional state update. -/
theorem applyQRValid_correct (s : ValidState) (ai bi ci di : Fin 16)
    (hab : ai ≠ bi) (hac : ai ≠ ci) (had : ai ≠ di)
    (hbc : bi ≠ ci) (hbd : bi ≠ di) (hcd : ci ≠ di) :
    toSpecState (applyQRValid s ai bi ci di) =
      Spec.applyQR (toSpecState s) ai bi ci di := by
  funext i
  rcases ai with ⟨ai, hai⟩
  rcases bi with ⟨bi, hbi⟩
  rcases ci with ⟨ci, hci⟩
  rcases di with ⟨di, hdi⟩
  rcases i with ⟨i, hi⟩
  have habv : ai ≠ bi := fun h => hab (Fin.ext h)
  have hacv : ai ≠ ci := fun h => hac (Fin.ext h)
  have hadv : ai ≠ di := fun h => had (Fin.ext h)
  have hbcv : bi ≠ ci := fun h => hbc (Fin.ext h)
  have hbdv : bi ≠ di := fun h => hbd (Fin.ext h)
  have hcdv : ci ≠ di := fun h => hcd (Fin.ext h)
  have hais : ai < s.arr.size := by rw [s.size_eq]; exact hai
  have hbis : bi < s.arr.size := by rw [s.size_eq]; exact hbi
  have hcis : ci < s.arr.size := by rw [s.size_eq]; exact hci
  have hdis : di < s.arr.size := by rw [s.size_eq]; exact hdi
  simp only [applyQRValid, toSpecState, applyQRArrayUnchecked, Spec.applyQR,
    quarterRound_eq_spec]
  by_cases hia : i = ai
  · subst i
    rw [Array.getElem!_set!_ne _ di ai _ (Ne.symm hadv)]
    rw [Array.getElem!_set!_ne _ ci ai _ (Ne.symm hacv)]
    rw [Array.getElem!_set!_ne _ bi ai _ (Ne.symm habv)]
    rw [Array.getElem!_set!_self _ ai _ hais]
    simp
  by_cases hib : i = bi
  · subst i
    rw [Array.getElem!_set!_ne _ di bi _ (Ne.symm hbdv)]
    rw [Array.getElem!_set!_ne _ ci bi _ (Ne.symm hbcv)]
    rw [Array.getElem!_set!_self _ bi _ (by simpa using hbis)]
    simp [hia]
  by_cases hic : i = ci
  · subst i
    rw [Array.getElem!_set!_ne _ di ci _ (Ne.symm hcdv)]
    rw [Array.getElem!_set!_self _ ci _ (by simpa using hcis)]
    simp [hia, hib]
  by_cases hid : i = di
  · subst i
    rw [Array.getElem!_set!_self _ di _ (by simpa using hdis)]
    simp [hia, hib, hic]
  rw [Array.getElem!_set!_ne _ di i _ (Ne.symm hid)]
  rw [Array.getElem!_set!_ne _ ci i _ (Ne.symm hic)]
  rw [Array.getElem!_set!_ne _ bi i _ (Ne.symm hib)]
  rw [Array.getElem!_set!_ne _ ai i _ (Ne.symm hia)]
  simp [hia, hib, hic, hid]

theorem columnRoundValid_correct (s : ValidState) :
    toSpecState (columnRoundValid s) = Spec.columnRound (toSpecState s) := by
  let q0 := applyQRValid s 0 4 8 12
  let q1 := applyQRValid q0 1 5 9 13
  let q2 := applyQRValid q1 2 6 10 14
  change toSpecState (applyQRValid q2 3 7 11 15) = _
  refine (applyQRValid_correct q2 3 7 11 15 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans ?_
  rw [applyQRValid_correct q1 2 6 10 14 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  rw [applyQRValid_correct q0 1 5 9 13 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  rw [applyQRValid_correct s 0 4 8 12 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  rfl

theorem diagonalRoundValid_correct (s : ValidState) :
    toSpecState (diagonalRoundValid s) = Spec.diagonalRound (toSpecState s) := by
  let q0 := applyQRValid s 0 5 10 15
  let q1 := applyQRValid q0 1 6 11 12
  let q2 := applyQRValid q1 2 7 8 13
  change toSpecState (applyQRValid q2 3 4 9 14) = _
  refine (applyQRValid_correct q2 3 4 9 14 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)).trans ?_
  rw [applyQRValid_correct q1 2 7 8 13 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  rw [applyQRValid_correct q0 1 6 11 12 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  rw [applyQRValid_correct s 0 5 10 15 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)]
  rfl

theorem doubleRoundValid_correct (s : ValidState) :
    toSpecState (doubleRoundValid s) = Spec.doubleRound (toSpecState s) := by
  unfold doubleRoundValid Spec.doubleRound
  rw [diagonalRoundValid_correct, columnRoundValid_correct]

/-- Interpret a raw implementation array as a specification state. -/
def arrayState (a : StateArray) : Spec.State := fun i => a[i.val]!

theorem applyQRArray_correct (a : StateArray) (hsize : a.size = 16)
    (ai bi ci di : Nat) (hai : ai < 16) (hbi : bi < 16) (hci : ci < 16) (hdi : di < 16)
    (hab : ai ≠ bi) (hac : ai ≠ ci) (had : ai ≠ di)
    (hbc : bi ≠ ci) (hbd : bi ≠ di) (hcd : ci ≠ di) :
    arrayState (applyQRArrayUnchecked a ai bi ci di) =
      Spec.applyQR (arrayState a) ⟨ai, hai⟩ ⟨bi, hbi⟩ ⟨ci, hci⟩ ⟨di, hdi⟩ := by
  funext i
  exact congrFun (applyQRValid_correct ⟨a, hsize⟩ ⟨ai, hai⟩ ⟨bi, hbi⟩ ⟨ci, hci⟩ ⟨di, hdi⟩
    (fun h => hab (congrArg Fin.val h)) (fun h => hac (congrArg Fin.val h))
    (fun h => had (congrArg Fin.val h)) (fun h => hbc (congrArg Fin.val h))
    (fun h => hbd (congrArg Fin.val h)) (fun h => hcd (congrArg Fin.val h))) i

theorem columnRoundArray_correct (a : StateArray) (hsize : a.size = 16) :
    arrayState (columnRoundArray a) = Spec.columnRound (arrayState a) := by
  let q0 := applyQRArrayUnchecked a 0 4 8 12
  let q1 := applyQRArrayUnchecked q0 1 5 9 13
  let q2 := applyQRArrayUnchecked q1 2 6 10 14
  have hs0 : q0.size = 16 := by dsimp [q0]; rw [applyQRArrayUnchecked_size] <;> omega
  have hs1 : q1.size = 16 := by dsimp [q1]; rw [applyQRArrayUnchecked_size] <;> omega
  have hs2 : q2.size = 16 := by dsimp [q2]; rw [applyQRArrayUnchecked_size] <;> omega
  change arrayState (applyQRArrayUnchecked q2 3 7 11 15) = _
  rw [applyQRArray_correct q2 hs2] <;> try omega
  rw [applyQRArray_correct q1 hs1] <;> try omega
  rw [applyQRArray_correct q0 hs0] <;> try omega
  rw [applyQRArray_correct a hsize] <;> try omega
  rfl

theorem diagonalRoundArray_correct (a : StateArray) (hsize : a.size = 16) :
    arrayState (diagonalRoundArray a) = Spec.diagonalRound (arrayState a) := by
  let q0 := applyQRArrayUnchecked a 0 5 10 15
  let q1 := applyQRArrayUnchecked q0 1 6 11 12
  let q2 := applyQRArrayUnchecked q1 2 7 8 13
  have hs0 : q0.size = 16 := by dsimp [q0]; rw [applyQRArrayUnchecked_size] <;> omega
  have hs1 : q1.size = 16 := by dsimp [q1]; rw [applyQRArrayUnchecked_size] <;> omega
  have hs2 : q2.size = 16 := by dsimp [q2]; rw [applyQRArrayUnchecked_size] <;> omega
  change arrayState (applyQRArrayUnchecked q2 3 4 9 14) = _
  rw [applyQRArray_correct q2 hs2] <;> try omega
  rw [applyQRArray_correct q1 hs1] <;> try omega
  rw [applyQRArray_correct q0 hs0] <;> try omega
  rw [applyQRArray_correct a hsize] <;> try omega
  rfl

theorem doubleRoundArray_correct (a : StateArray) (hsize : a.size = 16) :
    arrayState (doubleRoundArray a) = Spec.doubleRound (arrayState a) := by
  unfold doubleRoundArray Spec.doubleRound
  rw [diagonalRoundArray_correct _ (columnRoundArray_size a hsize),
    columnRoundArray_correct a hsize]

theorem nRoundsState_correct (n : Nat) (s : ValidState) :
    toSpecState (nRoundsState n s) = Spec.nRounds n (toSpecState s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      change toSpecState (nRoundsState n (doubleRoundValid s)) =
        Spec.nRounds n (Spec.doubleRound (toSpecState s))
      rw [ih, doubleRoundValid_correct]

/-- Element-wise array addition denotes specification state addition. -/
theorem addArrays_correct (s1 s2 : ValidState) :
    toSpecState ⟨addArrays s1.arr s2.arr,
      addArrays_size s1.arr s2.arr s1.size_eq s2.size_eq⟩ =
      Spec.addStates (toSpecState s1) (toSpecState s2) := by
  funext i
  simp only [toSpecState, Spec.addStates]
  rw [← Array.bounded_eq_unbounded _ i.val (by
    rw [addArrays_size s1.arr s2.arr s1.size_eq s2.size_eq]; exact i.isLt)]
  simp only [addArrays, Array.getElem_zipWith]
  rw [Array.bounded_eq_unbounded, Array.bounded_eq_unbounded]

/-!
══════════════════════════════════════════════════════════════════════════════
 INSPECTABLE THEOREMS — PRIMARY REVIEW SURFACE
══════════════════════════════════════════════════════════════════════════════

 These are the substantive end-to-end guarantees. A reviewer should inspect
 these statements together with the small definitions in `Spec.lean`.
-/

/-- **MAIN THEOREM 1 — BLOCK CORRECTNESS**
    The complete implementation block function—initialization, twenty rounds,
    and feed-forward addition—equals the specification for every key, counter,
    and nonce. -/
theorem block_correct (key : Key) (counter : Spec.Word) (nonce : Nonce) :
    toSpecState (blockArray key counter nonce) =
      Spec.block (keyToSpec key) counter (nonceToSpec nonce) := by
  let initial := initStateArray key counter nonce
  let final := nRoundsState 10 initial
  have hb : blockArray key counter nonce =
      ⟨addArrays final.arr initial.arr,
        addArrays_size final.arr initial.arr final.size_eq initial.size_eq⟩ := rfl
  rw [hb]
  rw [addArrays_correct final initial, nRoundsState_correct,
    initStateArray_matches_spec]
  rfl

/-! ### Serialization correctness -/

theorem wordToByte_eq_spec (w : Spec.Word) (pos : Nat) :
    wordToByte w pos = (w >>> (pos * 8).toUInt32).toUInt8 := rfl

/-- **MAIN THEOREM 2 — SERIALIZATION CORRECTNESS**
    Every one of the 64 serialized implementation bytes is the corresponding
    little-endian specification byte. -/
theorem stateToBytesArray_correct (s : ValidState) (i : Fin 64) :
    (stateToBytesArray s)[i.val]'(by rw [stateToBytesArray_size]; exact i.isLt) =
      Spec.stateToBytes (toSpecState s) i := by
  simp [stateToBytesArray, Spec.stateToBytes, wordToByte, toSpecState]

/-- Every generated implementation block byte agrees with the specification block. -/
theorem keystreamBlock_correct (key : Key) (nonce : Nonce) (counter : Spec.Word)
    (i : Fin 64) :
    (keystreamBlock key nonce counter)[i.val]'(by rw [keystreamBlock_size]; exact i.isLt) =
      Spec.stateToBytes (Spec.block (keyToSpec key) counter (nonceToSpec nonce)) i := by
  simp only [keystreamBlock]
  rw [stateToBytesArray_correct, block_correct]

/-! ### Cache and complete encryption correctness -/

/-- Semantic invariant for a populated keystream cache. -/
def CacheMatches (key : Key) (nonce : Nonce) (bytes : Array UInt8) (blockNum : Spec.Word) : Prop :=
  bytes = keystreamBlock key nonce blockNum

/-- **MAIN THEOREM 3 — CACHE CORRECTNESS**
    On both a cache hit and a cache miss, selection returns exactly the requested
    keystream block and records its counter. -/
theorem selectKeystream_correct (key : Key) (nonce : Nonce) (current cached : Spec.Word)
    (ks : Array UInt8) (hcache : ks.size = 0 ∨ CacheMatches key nonce ks cached) :
    (selectKeystream key nonce current ks cached).1 = keystreamBlock key nonce current ∧
    (selectKeystream key nonce current ks cached).2 = current := by
  unfold selectKeystream
  split
  · exact ⟨rfl, rfl⟩
  · rename_i hhit
    have hcounter : current = cached := by
      by_cases heq : current = cached
      · exact heq
      · exact False.elim (hhit (Or.inl (by simp [heq])))
    subst cached
    rcases hcache with hempty | hmatches
    · exact False.elim (hhit (Or.inr hempty))
    · exact ⟨by simpa [CacheMatches] using hmatches, rfl⟩

/-- **MAIN THEOREM 4 — ENCRYPTION CORRECTNESS**
    Complete array encryption is identical to the whole-message specification
    for every key, nonce, and message. -/
theorem encrypt_correct (key : Key) (nonce : Nonce) (msg : Array UInt8) :
    encrypt key nonce msg = Spec.encrypt (keyToSpec key) (nonceToSpec nonce) msg := by
  apply Array.ext
  · simp [encrypt, Spec.encrypt]
  · intro i h₁ h₂
    simp only [encrypt, Spec.encrypt, Array.getElem_ofFn]
    let j : Fin 64 := ⟨i % 64, by omega⟩
    have hk := keystreamBlock_correct key nonce ((i / 64).toUInt32 + 1) j
    simp only [j] at hk
    rw [hk]
    rfl

/-- **MAIN THEOREM 5 — FULL ROUNDTRIP**
    Decrypting a complete encrypted array recovers the original array as an
    equality of contents, not merely an equality of lengths. -/
theorem roundtrip (key : Key) (nonce : Nonce) (msg : Array UInt8) :
    decrypt key nonce (encrypt key nonce msg) = msg := by
  apply Array.ext
  · simp [decrypt, encrypt]
  · intro i h₁ h₂
    simp only [decrypt, encrypt, Array.getElem_ofFn]
    exact UInt8.xor_self_inverse _ _

/-! ### Single byte roundtrip -/

theorem byte_roundtrip (m ks : UInt8) : (m ^^^ ks) ^^^ ks = m :=
  xor_keystream_cancel m ks

/-!
══════════════════════════════════════════════════════════════════════════════
 SUPPORTING API COROLLARIES
══════════════════════════════════════════════════════════════════════════════

 These are useful local or structural facts, but they are not substitutes for
 the end-to-end theorems in the primary review surface above.
-/

/-- Quarter round is definitionally identical to the specification.
    The implementation quarter round is identical to the specification. -/
theorem quarterRound_correct (a b c d : Spec.Word) :
    quarterRound a b c d = Spec.quarterRound a b c d := rfl

/-- Initialization agrees with the specification.
    The array-based init produces the same state as the spec. -/
theorem init_correct (key : Key) (counter : Spec.Word) (nonce : Nonce) :
    toSpecState (initStateArray key counter nonce) =
    Spec.initState (keyToSpec key) counter (nonceToSpec nonce) :=
  initStateArray_matches_spec key counter nonce

/-- Encrypt and decrypt use the same XOR operation. -/
theorem encrypt_eq_decrypt (key : Key) (nonce : Nonce) (msg : Array UInt8) :
    encrypt key nonce msg = decrypt key nonce msg := rfl

/-- Encryption preserves message length.
    Encryption preserves message length. -/
theorem encrypt_preserves_length (key : Key) (nonce : Nonce) (msg : Array UInt8) :
    (encrypt key nonce msg).size = msg.size :=
  encrypt_size key nonce msg

/-- The full roundtrip theorem implies the weaker size-preservation fact.
    Retained as a convenience lemma, not as a correctness headline. -/
theorem roundtrip_size (key : Key) (nonce : Nonce) (msg : Array UInt8) :
    (decrypt key nonce (encrypt key nonce msg)).size = msg.size := by
  exact congrArg Array.size (roundtrip key nonce msg)

end Crypto.ChaCha20
