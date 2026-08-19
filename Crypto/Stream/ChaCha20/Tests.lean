/-
  Crypto.Stream.ChaCha20.Tests

  TEST VECTORS
  ============
  Runtime verification with test cases from RFC 8439.
  https://datatracker.ietf.org/doc/html/rfc8439
-/

import Crypto.Stream.ChaCha20.Impl
import Crypto.Stream.ChaCha20.Correctness

namespace Crypto.ChaCha20.Tests

open Crypto.ChaCha20

/-! ## Helper functions -/

/-- Convert hex string to list of UInt8 -/
def hexToBytes (s : String) : List UInt8 :=
  let chars := s.toList.filter (· ≠ ' ')
  let rec go : List Char → List UInt8
    | [] => []
    | [_] => []  -- Odd length, ignore last
    | c1 :: c2 :: rest =>
      let hexDigit (c : Char) : UInt8 :=
        if '0' ≤ c ∧ c ≤ '9' then c.toNat.toUInt8 - 48
        else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat.toUInt8 - 87
        else if 'A' ≤ c ∧ c ≤ 'F' then c.toNat.toUInt8 - 55
        else 0
      (hexDigit c1 * 16 + hexDigit c2) :: go rest
  go chars

/-- Convert list of bytes to hex string -/
def bytesToHex (bs : List UInt8) : String :=
  let hexDigit (n : UInt8) : Char :=
    if n < 10 then Char.ofNat (48 + n.toNat)
    else Char.ofNat (87 + n.toNat)
  String.ofList (bs.flatMap fun b => [hexDigit (b / 16), hexDigit (b % 16)])

/-- Convert 4 bytes to UInt32 (little-endian) -/
def bytesToWord (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

/-- Create key from 32 bytes -/
def keyFromBytes (bs : List UInt8) : Key :=
  let words := #[
    bytesToWord bs[0]! bs[1]! bs[2]! bs[3]!,
    bytesToWord bs[4]! bs[5]! bs[6]! bs[7]!,
    bytesToWord bs[8]! bs[9]! bs[10]! bs[11]!,
    bytesToWord bs[12]! bs[13]! bs[14]! bs[15]!,
    bytesToWord bs[16]! bs[17]! bs[18]! bs[19]!,
    bytesToWord bs[20]! bs[21]! bs[22]! bs[23]!,
    bytesToWord bs[24]! bs[25]! bs[26]! bs[27]!,
    bytesToWord bs[28]! bs[29]! bs[30]! bs[31]!
  ]
  ⟨words, rfl⟩

/-- Create nonce from 12 bytes -/
def nonceFromBytes (bs : List UInt8) : Nonce :=
  let words := #[
    bytesToWord bs[0]! bs[1]! bs[2]! bs[3]!,
    bytesToWord bs[4]! bs[5]! bs[6]! bs[7]!,
    bytesToWord bs[8]! bs[9]! bs[10]! bs[11]!
  ]
  ⟨words, rfl⟩

/-! ## RFC 8439 Section 2.1.1 - Quarter Round Test Vector -/

-- Test vector from RFC 8439 Section 2.1.1
-- Input:  a=0x11111111, b=0x01020304, c=0x9b8d6f43, d=0x01234567
-- Output: a=0xea2a92f4, b=0xcb1cf8ce, c=0x4581472e, d=0x5881c4bb
#eval
  let (a, b, c, d) := quarterRound 0x11111111 0x01020304 0x9b8d6f43 0x01234567
  (a == 0xea2a92f4, b == 0xcb1cf8ce, c == 0x4581472e, d == 0x5881c4bb)

/-! ## RFC 8439 Section 2.3.2 - ChaCha20 Block Function Test Vector -/

/-- RFC 8439 Section 2.3.2 key. -/
def testKey1 : Key :=
  keyFromBytes (hexToBytes "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")

/-- RFC 8439 Section 2.3.2 nonce. -/
def testNonce1 : Nonce :=
  nonceFromBytes (hexToBytes "000000090000004a00000000")

/-- Counter = 1 -/
def testCounter1 : UInt32 := 1

-- Test the block function output.
#eval!
  let state := blockArray testKey1 testCounter1 testNonce1
  -- First serialized word is 10 f1 e7 e4 (little-endian word 0xe4e7f110).
  state.arr[0]! == 0xe4e7f110
-- Expected: true

/-! ## RFC 8439 Section 2.4.2 - Encryption Test Vector -/

/-- Test key from RFC 8439 Section 2.4.2 -/
def testKey2 : Key :=
  keyFromBytes (hexToBytes "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")

/-- Test nonce from RFC 8439 Section 2.4.2 -/
def testNonce2 : Nonce :=
  nonceFromBytes (hexToBytes "000000000000004a00000000")

/-- Plaintext: "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it." -/
def testPlaintext : List UInt8 :=
  "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.".toList.map (·.toNat.toUInt8)

/-- Expected ciphertext from RFC 8439 -/
def expectedCiphertext : List UInt8 :=
  hexToBytes "6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0bf91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d807ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab77937365af90bbf74a35be6b40b8eedf2785e42874d"

-- Test encryption.
#eval!
  let ciphertext := encryptList testKey2 testNonce2 testPlaintext
  let expected := expectedCiphertext
  (ciphertext.length, expected.length, ciphertext == expected)
-- Expected: (114, 114, true)

-- Test decryption (roundtrip)
#eval!
  let ciphertext := encryptList testKey2 testNonce2 testPlaintext
  let decrypted := decryptList testKey2 testNonce2 ciphertext
  decrypted == testPlaintext
-- Expected: true

/-! ## Additional Tests -/

/-- Test with zero key and zero nonce -/
def zeroKey : Key :=
  keyFromBytes (hexToBytes "0000000000000000000000000000000000000000000000000000000000000000")

def zeroNonce : Nonce :=
  nonceFromBytes (hexToBytes "000000000000000000000000")

-- Test roundtrip with zeros
#eval!
  let msg := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
  let encrypted := encryptList zeroKey zeroNonce msg
  let decrypted := decryptList zeroKey zeroNonce encrypted
  decrypted == msg
-- Expected: true

-- Test that encrypt and decrypt are the same operation
#eval!
  let msg := testPlaintext
  let encrypted := encryptList testKey2 testNonce2 msg
  let doubleEncrypted := encryptList testKey2 testNonce2 encrypted
  doubleEncrypted == msg

-- Test multi-block message (> 64 bytes)
#eval!
  let msg := List.replicate 200 (42 : UInt8)
  let encrypted := encryptList testKey2 testNonce2 msg
  let decrypted := decryptList testKey2 testNonce2 encrypted
  (msg.length, encrypted.length, decrypted == msg)

/-! ## Verbose Test Output -/

#eval IO.println "=== ChaCha20 Test Results ==="

#eval do
  -- Quarter round test
  let (a, b, c, d) := quarterRound 0x11111111 0x01020304 0x9b8d6f43 0x01234567
  let qrPass := a == 0xea2a92f4 && b == 0xcb1cf8ce && c == 0x4581472e && d == 0x5881c4bb
  IO.println s!"Quarter Round Test: {if qrPass then "PASS" else "FAIL"}"

#eval! do
  -- Encryption test
  let ciphertext := encryptList testKey2 testNonce2 testPlaintext
  let encPass := ciphertext == expectedCiphertext
  IO.println s!"Encryption Test (RFC 8439 2.4.2): {if encPass then "PASS" else "FAIL"}"

#eval! do
  -- Roundtrip test
  let ciphertext := encryptList testKey2 testNonce2 testPlaintext
  let decrypted := decryptList testKey2 testNonce2 ciphertext
  let rtPass := decrypted == testPlaintext
  IO.println s!"Roundtrip Test: {if rtPass then "PASS" else "FAIL"}"

#eval! do
  -- XOR self-inverse test
  let encrypted := encryptList testKey2 testNonce2 testPlaintext
  let doubleEncrypted := encryptList testKey2 testNonce2 encrypted
  let xorPass := doubleEncrypted == testPlaintext
  IO.println s!"XOR Self-Inverse Test: {if xorPass then "PASS" else "FAIL"}"

#eval IO.println "=== All Tests Complete ==="

end Crypto.ChaCha20.Tests
