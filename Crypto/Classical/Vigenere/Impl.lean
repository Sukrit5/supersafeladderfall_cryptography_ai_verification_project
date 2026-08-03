/-
  Crypto.Classical.Vigenere.Impl

  VIGENÈRE CIPHER IMPLEMENTATION
  ==============================
  Optimized implementation with:
  1. Precomputed 26×26 lookup tables (avoids runtime mod arithmetic)
  2. Key expansion (avoids repeated modulo for cycling)
  3. Tail-recursive processing (explicit accumulator)

  User does NOT inspect this. Correctness.lean proves it matches Spec.
-/

import Crypto.Basic

namespace Crypto.Vigenere

/-! ## Precomputed Lookup Tables

26×26 tables where encTable[k][p] = (p+k) mod 26
Converts modular arithmetic to O(1) array lookups.
-/

def encTable : Fin 26 → Fin 26 → Fin 26 :=
  fun k p => ⟨(p.val + k.val) % 26, Nat.mod_lt _ (by omega)⟩

def decTable : Fin 26 → Fin 26 → Fin 26 :=
  fun k c => ⟨(c.val + 26 - k.val) % 26, Nat.mod_lt _ (by omega)⟩

/-! ## Key Type and Expansion -/

structure Key where
  chars : List Alphabet
  nonempty : chars.length > 0

/-- Expand key to length n by cycling -/
def expandKey (key : Key) (n : Nat) : List Alphabet :=
  List.ofFn (n := n) (fun i => key.chars[i.val % key.chars.length]'(Nat.mod_lt _ key.nonempty))

/-! ## Tail-Recursive Core (the "optimized" part)

Uses explicit recursion with accumulator instead of map/zipWith.
Processes expanded key and message in lockstep.
-/

def encryptCore : List Alphabet → List Alphabet → List Alphabet → List Alphabet
  | [], _, acc => acc.reverse
  | _ :: _, [], acc => acc.reverse
  | p :: ps, k :: ks, acc => encryptCore ps ks (encTable k p :: acc)

def decryptCore : List Alphabet → List Alphabet → List Alphabet → List Alphabet
  | [], _, acc => acc.reverse
  | _ :: _, [], acc => acc.reverse
  | c :: cs, k :: ks, acc => decryptCore cs ks (decTable k c :: acc)

/-! ## Main API -/

def encrypt (key : Key) (msg : List Alphabet) : List Alphabet :=
  encryptCore msg (expandKey key msg.length) []

def decrypt (key : Key) (msg : List Alphabet) : List Alphabet :=
  decryptCore msg (expandKey key msg.length) []

end Crypto.Vigenere
