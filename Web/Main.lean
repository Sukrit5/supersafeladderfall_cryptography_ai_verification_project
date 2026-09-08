import Lean
import Crypto.Char
import Crypto.Classical.Vigenere.Impl
import Crypto.Stream.ChaCha20.Impl
import Crypto.AEAD.ChaCha20Poly1305.Impl

/-! JSON adapter for the local web app. Cryptographic operations delegate to
the existing implementations; this adapter is not part of their proof boundary. -/
namespace Crypto.Web

def hexDigit (c : Char) : Except String Nat :=
  if '0' ≤ c && c ≤ '9' then .ok (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then .ok (c.toNat - 55)
  else .error "Expected hexadecimal digits."

def parseHex (s : String) : Except String (Array UInt8) := do
  let rec go : List Char → List UInt8 → Except String (Array UInt8)
    | [], acc => .ok acc.reverse.toArray
    | [_], _ => .error "Hexadecimal input must have an even length."
    | a :: b :: rest, acc => do
      let hi ← hexDigit a
      let lo ← hexDigit b
      go rest ((hi * 16 + lo).toUInt8 :: acc)
  go s.toList []

def toHex (bytes : Array UInt8) : String :=
  let digit := fun n => Char.ofNat (if n < 10 then 48 + n else 87 + n)
  String.ofList (bytes.toList.flatMap fun b => [digit (b.toNat / 16), digit (b.toNat % 16)])

def wordAt (bs : Array UInt8) (i : Nat) : UInt32 :=
  bs[i]!.toUInt32 ||| (bs[i+1]!.toUInt32 <<< 8) |||
    (bs[i+2]!.toUInt32 <<< 16) ||| (bs[i+3]!.toUInt32 <<< 24)

def process (j : Lean.Json) : Except String Lean.Json := do
  let cipher ← j.getObjValAs? String "cipher"
  let operation ← j.getObjValAs? String "operation"
  if operation != "encrypt" && operation != "decrypt" then
    throw "Choose encrypt or decrypt."
  let key ← j.getObjValAs? String "key"
  let message ← j.getObjValAs? String "message"
  if message.utf8ByteSize > 131072 then throw "Message is too large."
  if cipher == "vigenere" then
    if key.length > 4096 || !(key.toList.all fun c => (Crypto.Char.toAlphabet c).isSome) then
      throw "The Vigenère key must contain only A–Z letters (maximum 4096)."
    let chars := Crypto.String.toAlphabets key
    if h : chars.length > 0 then
      let k : Crypto.Vigenere.Key := ⟨chars, h⟩
      let msg := Crypto.String.toAlphabets message
      let out := if operation == "encrypt" then Crypto.Vigenere.encrypt k msg
                 else Crypto.Vigenere.decrypt k msg
      pure (Lean.Json.mkObj [("result", Lean.toJson (Crypto.List.toAlphabetString out))])
    else throw "Enter a nonempty Vigenère key."
  else if cipher == "chacha20" || cipher == "chacha20-poly1305" then
    let nonce ← j.getObjValAs? String "nonce"
    if key.length != 64 then throw "ChaCha20 needs a 32-byte key (64 hex digits)."
    if nonce.length != 24 then throw "ChaCha20 needs a 12-byte nonce (24 hex digits)."
    let kb ← parseHex key
    let nb ← parseHex nonce
    let msg ← parseHex message
    let k : Crypto.ChaCha20.Key :=
      ⟨#[wordAt kb 0, wordAt kb 4, wordAt kb 8, wordAt kb 12,
         wordAt kb 16, wordAt kb 20, wordAt kb 24, wordAt kb 28], rfl⟩
    let n : Crypto.ChaCha20.Nonce := ⟨#[wordAt nb 0, wordAt nb 4, wordAt nb 8], rfl⟩
    if cipher == "chacha20-poly1305" then
      let aadHex ← j.getObjValAs? String "aad"
      if aadHex.length > 131072 then throw "Associated data is too large."
      let aad ← parseHex aadHex
      if operation == "encrypt" then
        let packet := Crypto.ChaCha20Poly1305.sealPacket k n aad msg
        pure (Lean.Json.mkObj [("result", Lean.toJson (toHex packet.ciphertext)),
          ("tag", Lean.toJson (toHex packet.tag.toArray))])
      else
        let tagHex ← j.getObjValAs? String "tag"
        if tagHex.length != 32 then throw "The authentication tag must be 16 bytes (32 hex digits)."
        let tag ← parseHex tagHex
        match Crypto.ChaCha20Poly1305.open? k n aad ⟨msg, tag.toList⟩ with
        | some plaintext => pure (Lean.Json.mkObj [("result", Lean.toJson (toHex plaintext)),
            ("authenticated", Lean.toJson true)])
        | none => throw "Authentication failed. Check the key, nonce, associated data, ciphertext, and tag."
    else
      pure (Lean.Json.mkObj [("result", Lean.toJson (toHex (Crypto.ChaCha20.encrypt k n msg)))])
  else throw "Unknown cipher."

end Crypto.Web

def main : IO Unit := do
  let input ← (← IO.getStdin).getLine
  let response := match Lean.Json.parse input >>= Crypto.Web.process with
    | .ok value => value
    | .error error => Lean.Json.mkObj [("error", Lean.toJson error)]
  (← IO.getStdout).putStrLn response.compress
