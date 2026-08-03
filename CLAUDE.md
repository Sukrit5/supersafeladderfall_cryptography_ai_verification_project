# Crypto - Verified Cryptography Library in Lean 4

## Project Overview

A formally verified cryptography library implemented in Lean 4. Cryptographic primitives are proven correct against inspectable specifications.

## Build & Run

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build
lake build Crypto.Classical.Vigenere.Tests  # Run tests
```

## Project Structure

```
Crypto/
├── Basic.lean                    -- Core types: Alphabet, Cipher, InvertibleCipher
├── Char.lean                     -- Character ↔ Alphabet conversions
├── ModArith.lean                 -- Modular arithmetic lemmas
└── Classical/
    └── Vigenere/
        ├── Spec.lean             -- SPECIFICATION (inspect this)
        ├── Impl.lean             -- Implementation
        ├── Correctness.lean      -- Proofs: impl matches spec
        └── Tests.lean            -- Test vectors
```

---

## Vigenère Cipher

### Verification Approach

```
┌─────────────────────────────────────────────────────┐
│  SPECIFICATION (User inspects this - ~20 lines)     │
│  encryptAtSpec: (msg[i] + key[i % |key|]) mod 26    │
│  decryptAtSpec: (msg[i] - key[i % |key|]) mod 26    │
└─────────────────────────────────────────────────────┘
                         │
                         │ proven equal (Correctness.lean)
                         ▼
┌─────────────────────────────────────────────────────┐
│  IMPLEMENTATION (Trust via proofs)                  │
│  encrypt, decrypt functions                         │
└─────────────────────────────────────────────────────┘
```

### What to Inspect (Spec.lean)

Only these definitions need review:

```lean
def encryptAtSpec (msg : List Alphabet) (key : List Alphabet) (i : Nat)
    (hi : i < msg.length) (hkey : key.length > 0) : Alphabet :=
  let p := msg[i]
  let k := key[i % key.length]'(Nat.mod_lt i hkey)
  ⟨(p.val + k.val) % 26, Nat.mod_lt _ (by omega)⟩

def decryptAtSpec (msg : List Alphabet) (key : List Alphabet) (i : Nat)
    (hi : i < msg.length) (hkey : key.length > 0) : Alphabet :=
  let c := msg[i]
  let k := key[i % key.length]'(Nat.mod_lt i hkey)
  ⟨(c.val + 26 - k.val) % 26, Nat.mod_lt _ (by omega)⟩
```

**Verify**: Does this match textbook Vigenère? (Yes: encrypt = p+k mod 26, decrypt = c-k mod 26, key cycles)

### Proven Theorems (Correctness.lean)

```lean
-- Implementation matches specification at every position
theorem encrypt_matches_spec (key : Key) (msg : List Alphabet) (i : Nat) (hi : i < msg.length) :
    (encrypt key msg)[i] = encryptAtSpec msg key.chars i hi key.nonempty

theorem decrypt_matches_spec (key : Key) (msg : List Alphabet) (i : Nat) (hi : i < msg.length) :
    (decrypt key msg)[i] = decryptAtSpec msg key.chars i hi key.nonempty

-- Roundtrip properties
theorem roundtrip (key : Key) (msg : List Alphabet) :
    decrypt key (encrypt key msg) = msg

theorem roundtrip' (key : Key) (msg : List Alphabet) :
    encrypt key (decrypt key msg) = msg
```

### Test Results (Tests.lean)

```
ATTACKATDAWN + LEMON = LXFOPVEFRNHR  ✓
decrypt(encrypt(msg)) == msg          ✓ (true)
HELLO + D (Caesar shift 3) = KHOOR   ✓
```

---

## Implementation Progress

| Component | Status |
|-----------|--------|
| Project Setup | ✅ Complete |
| Core Types (Basic.lean) | ✅ Complete |
| Character Utilities (Char.lean) | ✅ Complete |
| Modular Arithmetic (ModArith.lean) | ✅ Complete |
| **Vigenère Cipher** | ✅ Complete |

---

## Core Types (Crypto/Basic.lean)

```lean
abbrev Alphabet := Fin 26

class Cipher (C : Type) (K : Type) (P : Type) (CT : Type) where
  encrypt : K → P → CT
  decrypt : K → CT → P

class InvertibleCipher (C : Type) (K : Type) (M : Type) extends Cipher C K M M where
  decrypt_encrypt : ∀ k m, decrypt k (encrypt k m) = m
  encrypt_decrypt : ∀ k m, encrypt k (decrypt k m) = m
```

---

## Design Decisions

- **Specification-based verification**: User inspects spec, proofs verify impl matches
- **Alphabet as Fin 26**: Automatic bounds and modular arithmetic
- **Pointwise correctness**: `encrypt_matches_spec` proves each position matches spec
- **Numeric ASCII values**: Use `65`/`90` instead of `'A'`/`'Z'` for omega proofs

## Lessons Learned

1. **omega needs explicit bounds**: Char comparisons don't give omega numeric info
2. **Generic Fin proofs are harder**: Specialize to Fin 26 for Alphabet
3. **List.ext_getElem for equality**: Prove lists equal by proving each element equal
4. **Nat.mod_lt for index proofs**: `i % n < n` when `n > 0`
