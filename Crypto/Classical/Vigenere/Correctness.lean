/-
  Crypto.Classical.Vigenere.Correctness

  CORRECTNESS PROOFS
  ==================
  This file proves the optimized implementation matches the minimal spec.

  STRUCTURE:
  - PART 1 (at bottom): INSPECTABLE THEOREMS - read these, they're simple
  - PART 2 (below): PROOF MACHINERY - Lean verifies, you don't need to read
-/

import Crypto.Classical.Vigenere.Spec
import Crypto.Classical.Vigenere.Impl

namespace Crypto.Vigenere

/-!
══════════════════════════════════════════════════════════════════════════════
 PROOF MACHINERY (Lean verifies these - you don't need to read)
══════════════════════════════════════════════════════════════════════════════
-/

/-! ### Spec helpers -/

theorem Spec.encrypt_lt_26 (p k : Nat) : Spec.encrypt p k < 26 := by
  simp [Spec.encrypt]; omega

theorem Spec.decrypt_lt_26 (c k : Nat) : Spec.decrypt c k < 26 := by
  simp [Spec.decrypt]; omega

/-! ### Table correctness: tables compute same as spec -/

theorem encTable_correct (k p : Fin 26) :
    (encTable k p).val = Spec.encrypt p.val k.val := by
  simp [encTable, Spec.encrypt, Nat.add_comm]

theorem decTable_correct (k c : Fin 26) :
    (decTable k c).val = Spec.decrypt c.val k.val := by
  simp [decTable, Spec.decrypt]

theorem encTable_eq (k p : Fin 26) :
    encTable k p = ⟨Spec.encrypt p.val k.val, Spec.encrypt_lt_26 p.val k.val⟩ := by
  ext; exact encTable_correct k p

theorem decTable_eq (k c : Fin 26) :
    decTable k c = ⟨Spec.decrypt c.val k.val, Spec.decrypt_lt_26 c.val k.val⟩ := by
  ext; exact decTable_correct k c

/-! ### Key expansion properties -/

theorem expandKey_length (key : Key) (n : Nat) :
    (expandKey key n).length = n := by
  simp [expandKey]

theorem expandKey_getElem (key : Key) (n : Nat) (i : Nat) (hi : i < n) :
    (expandKey key n)[i]'(by simp [expandKey_length]; exact hi) =
    key.chars[i % key.chars.length]'(Nat.mod_lt i key.nonempty) := by
  simp [expandKey]

/-! ### Core recursion properties -/

-- The key invariant: encryptCore msg ks acc = acc.reverse ++ zipWith msg ks
theorem encryptCore_acc_eq (msg ks acc : List Alphabet) (h : msg.length ≤ ks.length) :
    encryptCore msg ks acc = acc.reverse ++ List.zipWith (fun p k => encTable k p) msg ks := by
  induction msg generalizing ks acc with
  | nil => simp [encryptCore]
  | cons p ps ih =>
    cases ks with
    | nil => simp at h
    | cons k ks' =>
      simp only [encryptCore, List.zipWith_cons_cons]
      have hps : ps.length ≤ ks'.length := by simp at h; omega
      rw [ih ks' (encTable k p :: acc) hps]
      simp [List.reverse_cons]

theorem decryptCore_acc_eq (msg ks acc : List Alphabet) (h : msg.length ≤ ks.length) :
    decryptCore msg ks acc = acc.reverse ++ List.zipWith (fun c k => decTable k c) msg ks := by
  induction msg generalizing ks acc with
  | nil => simp [decryptCore]
  | cons c cs ih =>
    cases ks with
    | nil => simp at h
    | cons k ks' =>
      simp only [decryptCore, List.zipWith_cons_cons]
      have hcs : cs.length ≤ ks'.length := by simp at h; omega
      rw [ih ks' (decTable k c :: acc) hcs]
      simp [List.reverse_cons]

-- The core correctness: encryptCore produces zipWith when acc = []
theorem encryptCore_nil_eq_zipWith (msg ks : List Alphabet) (h : msg.length ≤ ks.length) :
    encryptCore msg ks [] = List.zipWith (fun p k => encTable k p) msg ks := by
  rw [encryptCore_acc_eq msg ks [] h]
  simp

theorem decryptCore_nil_eq_zipWith (msg ks : List Alphabet) (h : msg.length ≤ ks.length) :
    decryptCore msg ks [] = List.zipWith (fun c k => decTable k c) msg ks := by
  rw [decryptCore_acc_eq msg ks [] h]
  simp

/-! ### Main encrypt/decrypt as zipWith -/

theorem encrypt_eq_zipWith (key : Key) (msg : List Alphabet) :
    encrypt key msg = List.zipWith (fun p k => encTable k p) msg (expandKey key msg.length) := by
  simp only [encrypt]
  apply encryptCore_nil_eq_zipWith
  simp [expandKey_length]

theorem decrypt_eq_zipWith (key : Key) (msg : List Alphabet) :
    decrypt key msg = List.zipWith (fun c k => decTable k c) msg (expandKey key msg.length) := by
  simp only [decrypt]
  apply decryptCore_nil_eq_zipWith
  simp [expandKey_length]

/-! ### Length preservation -/

theorem encrypt_length (key : Key) (msg : List Alphabet) :
    (encrypt key msg).length = msg.length := by
  simp only [encrypt_eq_zipWith, List.length_zipWith, expandKey_length, Nat.min_self]

theorem decrypt_length (key : Key) (msg : List Alphabet) :
    (decrypt key msg).length = msg.length := by
  simp only [decrypt_eq_zipWith, List.length_zipWith, expandKey_length, Nat.min_self]

/-! ### Indexing into zipWith -/

theorem List.getElem_zipWith {α β γ : Type} (f : α → β → γ) (as : List α) (bs : List β)
    (i : Nat) (h : i < (List.zipWith f as bs).length) :
    (List.zipWith f as bs)[i] = f (as[i]'(by simp at h; omega)) (bs[i]'(by simp at h; omega)) := by
  induction as generalizing bs i with
  | nil => simp at h
  | cons a as' ih =>
    cases bs with
    | nil => simp at h
    | cons b bs' =>
      cases i with
      | zero => simp
      | succ j =>
        simp only [List.zipWith_cons_cons, List.getElem_cons_succ]
        exact ih bs' j (by simp at h ⊢; omega)

/-!
══════════════════════════════════════════════════════════════════════════════
 INSPECTABLE THEOREMS
══════════════════════════════════════════════════════════════════════════════

 These are the main correctness guarantees. Each states that the optimized
 implementation produces the same result as the simple mathematical spec.
-/

/-- **MAIN THEOREM 1**: Encryption is correct.
    The optimized encrypt (tables + expansion + tail recursion) produces
    the same result as the simple spec: (plaintext + key) mod 26 -/
theorem encrypt_correct (key : Key) (msg : List Alphabet) (i : Nat) (hi : i < msg.length) :
    (encrypt key msg)[i]'(by simp only [encrypt_length]; exact hi) =
    ⟨Spec.encrypt msg[i].val (key.chars[i % key.chars.length]'(Nat.mod_lt i key.nonempty)).val,
     Spec.encrypt_lt_26 msg[i].val (key.chars[i % key.chars.length]'(Nat.mod_lt i key.nonempty)).val⟩ := by
  simp only [encrypt_eq_zipWith]
  have hzip : i < (List.zipWith (fun p k => encTable k p) msg (expandKey key msg.length)).length := by
    simp [expandKey_length, hi]
  simp only [List.getElem_zipWith _ _ _ i hzip]
  simp only [expandKey_getElem key msg.length i hi]
  exact encTable_eq _ _

/-- **MAIN THEOREM 2**: Decryption is correct.
    The optimized decrypt produces the same result as spec: (ciphertext - key) mod 26 -/
theorem decrypt_correct (key : Key) (msg : List Alphabet) (i : Nat) (hi : i < msg.length) :
    (decrypt key msg)[i]'(by simp only [decrypt_length]; exact hi) =
    ⟨Spec.decrypt msg[i].val (key.chars[i % key.chars.length]'(Nat.mod_lt i key.nonempty)).val,
     Spec.decrypt_lt_26 msg[i].val (key.chars[i % key.chars.length]'(Nat.mod_lt i key.nonempty)).val⟩ := by
  simp only [decrypt_eq_zipWith]
  have hzip : i < (List.zipWith (fun c k => decTable k c) msg (expandKey key msg.length)).length := by
    simp [expandKey_length, hi]
  simp only [List.getElem_zipWith _ _ _ i hzip]
  simp only [expandKey_getElem key msg.length i hi]
  exact decTable_eq _ _

/-- **MAIN THEOREM 3**: Roundtrip property.
    Decrypting an encrypted message recovers the original. -/
theorem roundtrip (key : Key) (msg : List Alphabet) :
    decrypt key (encrypt key msg) = msg := by
  apply List.ext_getElem
  · simp only [decrypt_length, encrypt_length]
  · intro i h1 h2
    have h_enc_len : i < (encrypt key msg).length := by simp only [encrypt_length]; exact h2
    -- Get correctness of encrypt and decrypt
    have heq1 := encrypt_correct key msg i h2
    have heq2 := decrypt_correct key (encrypt key msg) i h_enc_len
    -- The encrypted message at position i
    have henc_val : (encrypt key msg)[i].val = Spec.encrypt msg[i].val (key.chars[i % key.chars.length]'(Nat.mod_lt i key.nonempty)).val := by
      rw [heq1]
    -- Substitute into heq2
    simp only [Fin.ext_iff] at heq1 heq2 ⊢
    rw [heq2, henc_val]
    simp only [Spec.decrypt, Spec.encrypt]
    have hk : (key.chars[i % key.chars.length]'(Nat.mod_lt i key.nonempty)).val < 26 :=
      (key.chars[i % key.chars.length]'(Nat.mod_lt i key.nonempty)).isLt
    omega

/-- **MAIN THEOREM 4**: Roundtrip (other direction). -/
theorem roundtrip' (key : Key) (msg : List Alphabet) :
    encrypt key (decrypt key msg) = msg := by
  apply List.ext_getElem
  · simp only [decrypt_length, encrypt_length]
  · intro i h1 h2
    have h_dec_len : i < (decrypt key msg).length := by simp only [decrypt_length]; exact h2
    -- Get correctness of encrypt and decrypt
    have heq1 := decrypt_correct key msg i h2
    have heq2 := encrypt_correct key (decrypt key msg) i h_dec_len
    -- The decrypted message at position i
    have hdec_val : (decrypt key msg)[i].val = Spec.decrypt msg[i].val (key.chars[i % key.chars.length]'(Nat.mod_lt i key.nonempty)).val := by
      rw [heq1]
    -- Substitute into heq2
    simp only [Fin.ext_iff] at heq1 heq2 ⊢
    rw [heq2, hdec_val]
    simp only [Spec.decrypt, Spec.encrypt]
    have hk : (key.chars[i % key.chars.length]'(Nat.mod_lt i key.nonempty)).val < 26 :=
      (key.chars[i % key.chars.length]'(Nat.mod_lt i key.nonempty)).isLt
    omega

end Crypto.Vigenere
