import Crypto.Stream.ChaCha20.Spec

namespace Crypto.ChaCha20

open Spec (Word)

/-- Runtime representation of a 256-bit ChaCha20 key. -/
structure Key where
  words : Array Word
  size_eq : words.size = 8

/-- Runtime representation of a 96-bit IETF ChaCha20 nonce. -/
structure Nonce where
  words : Array Word
  size_eq : words.size = 3

/-- Representation map from runtime keys to the mathematical specification. -/
def Key.toSpec (key : Key) : Spec.Key := fun i => key.words[i.val]!

/-- Representation map from runtime nonces to the mathematical specification. -/
def Nonce.toSpec (nonce : Nonce) : Spec.Nonce := fun i => nonce.words[i.val]!

end Crypto.ChaCha20
