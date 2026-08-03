# Phase 1: Cryptography Library Foundation

## Goal

Set up core infrastructure for a verified cryptography library in Lean 4.

---

## Step 1: Project Setup

**Tasks:**
- Initialize Lean 4 project with `lake init Crypto`
- Configure `lakefile.lean`
- Create base directory structure

**Evaluation:**
- [ ] `lake build` succeeds with no errors
- [ ] Project structure exists: `Crypto/Basic.lean`, `Crypto/Char.lean`, `Crypto/ModArith.lean`

---

## Step 2: Core Types (`Crypto/Basic.lean`)

**Tasks:**
- Define `Alphabet` as `Fin 26`
- Define `Cipher` typeclass with `encrypt`/`decrypt`
- Define `InvertibleCipher` with roundtrip proof requirements

**Evaluation:**
- [ ] `lake build` succeeds
- [ ] `#check Alphabet` outputs `Fin 26`
- [ ] `#check Cipher` shows typeclass with encrypt/decrypt
- [ ] `#check InvertibleCipher` shows extended typeclass with proof fields

---

## Step 3: Character Utilities (`Crypto/Char.lean`)

**Tasks:**
- Implement `Char.toAlphabet : Char → Option Alphabet`
- Implement `Alphabet.toChar : Alphabet → Char`
- Implement string conversion helpers

**Evaluation:**
- [ ] `#eval Char.toAlphabet 'A'` returns `some 0`
- [ ] `#eval Char.toAlphabet 'Z'` returns `some 25`
- [ ] `#eval Char.toAlphabet 'a'` returns `some 0` (lowercase support)
- [ ] `#eval Char.toAlphabet '5'` returns `none`
- [ ] `#eval Alphabet.toChar ⟨0, by omega⟩` returns `'A'`
- [ ] `#eval String.toAlphabets "Hello"` returns `[7, 4, 11, 11, 14]`
- [ ] Roundtrip: `Alphabet.toChar (Char.toAlphabet 'K').get! = 'K'`

---

## Step 4: Modular Arithmetic (`Crypto/ModArith.lean`)

**Tasks:**
- Prove `add_sub_cancel`: `(a + b - b) % 26 = a % 26` for valid inputs
- Prove `sub_add_cancel`: `(a - b + b) % 26 = a % 26` for valid inputs
- Any helper lemmas needed for Fin 26 operations

**Evaluation:**
- [ ] `lake build` succeeds with no `sorry`
- [ ] All theorems compile without axioms (check with `#print axioms theorem_name`)

---

## Final Checklist

| Criterion | How to Verify |
|-----------|---------------|
| Project builds | `lake build` exits 0 |
| No incomplete proofs | `grep -r "sorry" Crypto/` returns nothing |
| Types correct | `#check` commands in each file |
| Char conversion works | `#eval` tests pass expected values |
| Proofs are sound | `#print axioms` shows only `propext`, `quot.sound`, etc. |

---

## Next Phase

Implement Vigenère cipher using these foundations.
