/-
  Crypto.Char
  Character and string conversion utilities.
-/

import Crypto.Basic

namespace Crypto

/-- Convert a character to Alphabet (0-25). Returns none for non-letters. -/
def Char.toAlphabet (c : Char) : Option Alphabet :=
  let cn := c.toNat
  if h : 65 ≤ cn ∧ cn ≤ 90 then
    some ⟨cn - 65, by omega⟩
  else if h : 97 ≤ cn ∧ cn ≤ 122 then
    some ⟨cn - 97, by omega⟩
  else
    none

/-- Convert Alphabet (0-25) to uppercase character. -/
def Alphabet.toChar (a : Alphabet) : Char :=
  Char.ofNat ('A'.toNat + a.val)

/-- Convert a string to a list of Alphabet values, filtering non-letters. -/
def String.toAlphabets (s : String) : List Alphabet :=
  s.toList.filterMap Char.toAlphabet

/-- Convert a list of Alphabet values to a string. -/
def List.toAlphabetString (as : List Alphabet) : String :=
  String.ofList (as.map Alphabet.toChar)

end Crypto

-- ============ EVALUATION TESTS ============

open Crypto in #eval Char.toAlphabet 'A'  -- Expected: some 0
open Crypto in #eval Char.toAlphabet 'Z'  -- Expected: some 25
open Crypto in #eval Char.toAlphabet 'a'  -- Expected: some 0
open Crypto in #eval Char.toAlphabet 'z'  -- Expected: some 25
open Crypto in #eval Char.toAlphabet '5'  -- Expected: none

open Crypto in #eval Alphabet.toChar ⟨0, by omega⟩   -- Expected: 'A'
open Crypto in #eval Alphabet.toChar ⟨25, by omega⟩  -- Expected: 'Z'

open Crypto in #eval String.toAlphabets "Hello"  -- Expected: [7, 4, 11, 11, 14]
open Crypto in #eval List.toAlphabetString [⟨7, by omega⟩, ⟨4, by omega⟩, ⟨11, by omega⟩, ⟨11, by omega⟩, ⟨14, by omega⟩]  -- Expected: "HELLO"

open Crypto in #eval (Char.toAlphabet 'K').map Alphabet.toChar  -- Expected: some 'K'
