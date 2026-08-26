import Crypto.AEAD.ChaCha20Poly1305.Correctness

namespace Crypto.ChaCha20Poly1305.Tests

open Crypto.ChaCha20 Crypto.ChaCha20Poly1305

def hexDigit (c : Char) : UInt8 :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat.toUInt8 - 48
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat.toUInt8 - 87
  else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat.toUInt8 - 55
  else 0

def hexToBytes (s : String) : List UInt8 :=
  let rec go : List Char → List UInt8
    | a :: b :: rest => (hexDigit a * 16 + hexDigit b) :: go rest
    | _ => []
  go (s.toList.filter (· ≠ ' '))

def bytesToWord (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

def keyFromBytes (bs : List UInt8) : Key :=
  ⟨#[bytesToWord bs[0]! bs[1]! bs[2]! bs[3]!,
     bytesToWord bs[4]! bs[5]! bs[6]! bs[7]!,
     bytesToWord bs[8]! bs[9]! bs[10]! bs[11]!,
     bytesToWord bs[12]! bs[13]! bs[14]! bs[15]!,
     bytesToWord bs[16]! bs[17]! bs[18]! bs[19]!,
     bytesToWord bs[20]! bs[21]! bs[22]! bs[23]!,
     bytesToWord bs[24]! bs[25]! bs[26]! bs[27]!,
     bytesToWord bs[28]! bs[29]! bs[30]! bs[31]!], rfl⟩

def nonceFromBytes (bs : List UInt8) : Nonce :=
  ⟨#[bytesToWord bs[0]! bs[1]! bs[2]! bs[3]!,
     bytesToWord bs[4]! bs[5]! bs[6]! bs[7]!,
     bytesToWord bs[8]! bs[9]! bs[10]! bs[11]!], rfl⟩

-- RFC 8439 section 2.8.2.
def key := keyFromBytes (hexToBytes
  "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f")
def nonce := nonceFromBytes (hexToBytes "070000004041424344454647")
def aad := (hexToBytes "50515253c0c1c2c3c4c5c6c7").toArray
def plaintext :=
  "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."
    |>.toList.map (·.toNat.toUInt8) |>.toArray
def expectedCiphertext := (hexToBytes
  "d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d6\
   3dbea45e8ca9671282fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b36\
   92ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585808b4831d7bc\
   3ff4def08e4b7a9de576d26586cec64b6116").toArray
def expectedTag := hexToBytes "1ae10b594f09e26a7e902ecbd0600691"

#eval! do
  let packet := sealPacket key nonce aad plaintext
  let vectorPass := packet.ciphertext == expectedCiphertext && packet.tag == expectedTag
  let roundtripPass := open? key nonce aad packet == some plaintext
  let badPacket : Sealed := ⟨packet.ciphertext, 0 :: packet.tag.drop 1⟩
  let rejectionPass := open? key nonce aad badPacket == none
  IO.println s!"RFC 8439 AEAD vector: {if vectorPass then "PASS" else "FAIL"}"
  IO.println s!"Authenticated roundtrip: {if roundtripPass then "PASS" else "FAIL"}"
  IO.println s!"Modified tag rejected: {if rejectionPass then "PASS" else "FAIL"}"

end Crypto.ChaCha20Poly1305.Tests
