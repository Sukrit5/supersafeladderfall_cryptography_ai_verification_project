/-
  Crypto.Classical.Vigenere.Tests

  TEST VECTORS
  ============
  Runtime verification with known test cases.
-/

import Crypto.Classical.Vigenere.Impl
import Crypto.Classical.Vigenere.Correctness
import Crypto.Char

namespace Crypto.Vigenere.Tests

open Crypto

/-- Classic test: ATTACKATDAWN + LEMON = LXFOPVEFRNHR -/
def attackatdawn : List Alphabet := String.toAlphabets "ATTACKATDAWN"
def lemon : List Alphabet := String.toAlphabets "LEMON"
def lxfopvefrnhr : List Alphabet := String.toAlphabets "LXFOPVEFRNHR"

def lemonKey : Key := ⟨lemon, by decide⟩

-- Test encryption
#eval encrypt lemonKey attackatdawn
-- Output: [11, 23, 5, 14, 15, 21, 4, 5, 17, 13, 7, 17]

#eval lxfopvefrnhr
-- Output: [11, 23, 5, 14, 15, 21, 4, 5, 17, 13, 7, 17] (matches!)

-- Test decryption
#eval decrypt lemonKey lxfopvefrnhr
-- Output: [0, 19, 19, 0, 2, 10, 0, 19, 3, 0, 22, 13]

#eval attackatdawn
-- Output: [0, 19, 19, 0, 2, 10, 0, 19, 3, 0, 22, 13] (matches!)

-- Test roundtrip
#eval decrypt lemonKey (encrypt lemonKey attackatdawn) == attackatdawn
-- Output: true

-- Convert back to string for readability
#eval List.toAlphabetString (encrypt lemonKey attackatdawn)
-- Output: "LXFOPVEFRNHR"

#eval List.toAlphabetString (decrypt lemonKey lxfopvefrnhr)
-- Output: "ATTACKATDAWN"

/-- Test with single character key (degenerates to Caesar) -/
def caesarKey : Key := ⟨String.toAlphabets "D", by decide⟩  -- shift of 3
def hello : List Alphabet := String.toAlphabets "HELLO"

#eval List.toAlphabetString (encrypt caesarKey hello)
-- Output: "KHOOR" (H+3=K, E+3=H, L+3=O, L+3=O, O+3=R)

#eval List.toAlphabetString (decrypt caesarKey (encrypt caesarKey hello))
-- Output: "HELLO"

/-- Test with key longer than message -/
def longKey : Key := ⟨String.toAlphabets "VERYLONGKEY", by decide⟩
def hi : List Alphabet := String.toAlphabets "HI"

#eval List.toAlphabetString (encrypt longKey hi)
#eval List.toAlphabetString (decrypt longKey (encrypt longKey hi))
-- Output: "HI"

end Crypto.Vigenere.Tests
