/-
  Crypto.ModArith
  Modular arithmetic lemmas for Fin 26 operations.
  These lemmas support proofs for cipher correctness.
-/

import Crypto.Basic

namespace Crypto

/-- For Alphabet (Fin 26): encrypt then decrypt returns original. -/
theorem Alphabet.encrypt_decrypt_cancel (p k : Alphabet) :
    (⟨((p.val + k.val) % 26 + 26 - k.val) % 26, Nat.mod_lt _ (by omega)⟩ : Alphabet) = p := by
  simp only [Fin.ext_iff]
  omega

/-- For Alphabet (Fin 26): decrypt then encrypt returns original. -/
theorem Alphabet.decrypt_encrypt_cancel (c k : Alphabet) :
    (⟨((c.val + 26 - k.val) % 26 + k.val) % 26, Nat.mod_lt _ (by omega)⟩ : Alphabet) = c := by
  simp only [Fin.ext_iff]
  omega

/-- Modular addition is commutative for Alphabet. -/
theorem Alphabet.add_comm (a b : Alphabet) :
    (⟨(a.val + b.val) % 26, Nat.mod_lt _ (by omega)⟩ : Alphabet) =
    (⟨(b.val + a.val) % 26, Nat.mod_lt _ (by omega)⟩ : Alphabet) := by
  simp only [Fin.ext_iff]
  omega

/-- Adding zero (identity key) leaves value unchanged. -/
theorem Alphabet.add_zero (a : Alphabet) :
    (⟨(a.val + 0) % 26, Nat.mod_lt _ (by omega)⟩ : Alphabet) = a := by
  simp only [Fin.ext_iff]
  omega

end Crypto

-- ============ VERIFICATION ============

#print axioms Crypto.Alphabet.encrypt_decrypt_cancel
#print axioms Crypto.Alphabet.decrypt_encrypt_cancel
#print axioms Crypto.Alphabet.add_comm
#print axioms Crypto.Alphabet.add_zero
