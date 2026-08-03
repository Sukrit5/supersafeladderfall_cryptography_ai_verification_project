# Proof Failure Log

## 2026-08-03 (Vigenere)

### Crypto/Classical/Vigenere/Spec.lean:28 - key index proof
```
failed to prove index is valid
⊢ i % key.length < key.length
```
**Fix**: Use explicit proof with Nat.mod_lt

### Crypto/Classical/Vigenere/Spec.lean:50 - Unknown List.getElem_set_eq
```
Unknown constant `List.getElem_set_eq`
```
**Fix**: Use different lemma or native_decide

---

## 2026-08-03 (Phase 1)

### Crypto/Char.lean:13 - Char.toAlphabet uppercase bound [FIXED]
```
omega could not prove the goal:
  a - b ≥ 26
where
 a := ↑c.toNat
 b := ↑'A'.toNat
```
**Fix**: Use numeric literals (65, 90) instead of char comparisons so omega has direct access to bounds.

### Crypto/Char.lean:15 - Char.toAlphabet lowercase bound [FIXED]
```
omega could not prove the goal:
  a - b ≥ 26
where
 a := ↑c.toNat
 b := ↑'a'.toNat
```
**Fix**: Use numeric literals (97, 122) instead of char comparisons.

### Crypto/ModArith.lean:13 - Fin.add_sub_cancel generic [REMOVED]
```
omega could not prove the goal:
  c - d + e ≥ 1
where
 c := ↑((↑a + ↑b) % n + n - ↑b)
 d := ↑(↑a + ↑b) % ↑n
 e := ↑↑b
```
**Fix**: Removed generic theorem; kept Alphabet-specific version only.

### Crypto/ModArith.lean:19 - Fin.sub_add_cancel generic [REMOVED]
```
omega could not prove the goal:
  c - d - e ≤ 0
where
 c := ↑n
 d := ↑(↑a + n - ↑b) % ↑n
 e := ↑↑b
```
**Fix**: Removed generic theorem; kept Alphabet-specific version only.
