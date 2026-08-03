/-
  Crypto.Classical.Vigenere.Spec

  VIGENÈRE CIPHER SPECIFICATION
  =============================
  Ultra-minimal mathematical definition. THIS IS ALL YOU NEED TO INSPECT.

  The Vigenère cipher is defined by two functions on natural numbers:
    encrypt: (plaintext + key) mod 26
    decrypt: (ciphertext - key) mod 26  [using +26 to keep positive]

  That's it. The implementation may use optimizations (precomputed tables,
  key expansion, tail recursion, etc.) but must be PROVEN to match this spec.
-/

namespace Crypto.Vigenere.Spec

/-! ## THE ENTIRE SPECIFICATION: 2 lines of pure math -/

/-- Encrypt a single character: (p + k) mod 26 -/
def encrypt (p k : Nat) : Nat := (p + k) % 26

/-- Decrypt a single character: (c - k) mod 26 -/
def decrypt (c k : Nat) : Nat := (c + 26 - k) % 26

/-! ## Spec properties (trivially follow from definition) -/

theorem decrypt_encrypt (p k : Nat) (hp : p < 26) (hk : k < 26) :
    decrypt (encrypt p k) k = p := by
  simp only [encrypt, decrypt]
  omega

theorem encrypt_decrypt (c k : Nat) (hc : c < 26) (hk : k < 26) :
    encrypt (decrypt c k) k = c := by
  simp only [encrypt, decrypt]
  omega

end Crypto.Vigenere.Spec
