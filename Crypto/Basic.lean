/-
  Crypto.Basic
  Core types and abstractions for the cryptography library.
-/

/-- Letters A-Z mapped to 0-25. Uses Fin 26 for automatic modular arithmetic. -/
abbrev Alphabet := Fin 26

/-- Typeclass for symmetric ciphers with encrypt and decrypt operations. -/
class Cipher (C : Type) (K : Type) (P : Type) (CT : Type) where
  /-- Encrypt plaintext with a key -/
  encrypt : K → P → CT
  /-- Decrypt ciphertext with a key -/
  decrypt : K → CT → P

/-- Typeclass for invertible ciphers where decrypt inverts encrypt and vice versa. -/
class InvertibleCipher (C : Type) (K : Type) (M : Type) extends Cipher C K M M where
  /-- Decrypting an encrypted message recovers the original -/
  decrypt_encrypt : ∀ k m, decrypt k (encrypt k m) = m
  /-- Encrypting a decrypted message recovers the original -/
  encrypt_decrypt : ∀ k m, encrypt k (decrypt k m) = m

-- Verification: #check commands to confirm types
#check (Alphabet : Type)
#check Cipher
#check InvertibleCipher
