import Crypto.AEAD.ChaCha20Poly1305.Correctness
import Crypto.AEAD.ChaCha20Poly1305.Fast

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

-- RFC 8439 section 2.5.2: standalone Poly1305 vector.
def poly1305Key := hexToBytes
  "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b"
def poly1305Message :=
  "Cryptographic Forum Research Group".toList.map (·.toNat.toUInt8)
def expectedPoly1305Tag := hexToBytes "a8061dc1305136c6c22b8baf0c0127a9"

-- All-one limbs and many full blocks exercise the convolution's high-degree
-- terms, factor-five fold, and repeated canonical reductions.
def carryHeavyMessage : List UInt8 := List.replicate 257 0xff
def carryHeavyKey : List UInt8 := List.replicate 32 0xff

#eval! do
  let packet := sealPacket key nonce aad plaintext
  let vectorPass := packet.ciphertext == expectedCiphertext && packet.tag == expectedTag
  let roundtripPass := open? key nonce aad packet == some plaintext
  let badPacket : Sealed := ⟨packet.ciphertext, 0 :: packet.tag.drop 1⟩
  let rejectionPass := open? key nonce aad badPacket == none
  let polyVectorPass := poly1305 poly1305Message poly1305Key == expectedPoly1305Tag
  let carryAgreement := poly1305 carryHeavyMessage carryHeavyKey ==
    Spec.poly1305 carryHeavyMessage carryHeavyKey
  let fastPolyVectorPass := Fast.poly1305 poly1305Message poly1305Key == expectedPoly1305Tag
  let fastBoundaryAgreement := (List.range 258).all fun size =>
    let msg := (List.range size).map fun i => ((i * 73 + size * 19 + 11) % 256).toUInt8
    let key := (List.range 32).map fun i => ((i * 47 + size * 13 + 29) % 256).toUInt8
    Fast.poly1305 msg key == Spec.poly1305 msg key
  let wordBoundaryAgreement := (List.range 258).all fun size =>
    [0, 1, 2].all fun pattern =>
      let msg := (List.range size).map fun i =>
        if pattern = 0 then (0 : UInt8) else if pattern = 1 then 255
        else ((i * 73 + size * 19 + 11) % 256).toUInt8
      let key := (List.range 32).map fun i =>
        if pattern = 0 then (0 : UInt8) else if pattern = 1 then 255
        else ((i * 47 + size * 13 + 29) % 256).toUInt8
      poly1305 msg key == Spec.poly1305 msg key
  -- The existing public theorem covers arbitrary key-list lengths, not only 32.
  let keyLengthAgreement := [0, 1, 15, 16, 17, 31, 32, 33, 64].all fun keySize =>
    [0, 1, 15, 16, 17, 31, 32, 33, 65, 257, 1024].all fun size =>
      let msg := List.replicate size (255 : UInt8)
      let key := List.replicate keySize (255 : UInt8)
      poly1305 msg key == Spec.poly1305 msg key
  let serializationAgreement :=
    [0, 2^64-1, 2^64, 2^128-1, 2^128, 2^130-1].all fun n =>
      WordBlocks.tagBytes n == Spec.natToBytesLE 16 n
  let machineAgreement := (List.range 258).all fun size =>
    [0, 1, 2].all fun pattern =>
      let msg := (List.range size).map fun i =>
        if pattern = 0 then (0 : UInt8) else if pattern = 1 then 255
        else ((i*73+size*19+11)%256).toUInt8
      let key := (List.range 32).map fun i => ((i*47+size*13+29)%256).toUInt8
      let expected := Spec.poly1305 msg key
      Machine.poly1305 msg key == expected && Machine.poly1305Array msg.toArray key.toArray == expected
  let machineKeys := [0,1,15,16,17,31,32,33,64].all fun n =>
    [0,1,15,16,17,31,32,33,65,257,1024].all fun size =>
      let msg := List.replicate size (255 : UInt8)
      let key := List.replicate n (255 : UInt8)
      let expected := Spec.poly1305 msg key
      Machine.poly1305 msg key == expected && Machine.poly1305Array msg.toArray key.toArray == expected
  let finishAgreement :=
    let values := [0, 1, 2^130-6, 2^130-5, 2^130-4, 2^130-1]
    let states := values.map (Fast.Limbs.addNat ⟨0,0,0,0,0⟩) ++
      [(⟨134217727,134217727,134217727,134217727,134217727⟩ : Fast.Limbs),
       (⟨67108863,67108864,67108863,67108863,67108863⟩ : Fast.Limbs)]
    states.all fun h => [0,1,4294967295].all fun pad =>
      let s : Machine.Words := ⟨pad,pad,pad,pad⟩
      Machine.finish h s == Spec.natToBytesLE 16 ((h.value % Fast.prime + s.value) % 2^128)
  let macArrayAgreement := [0,1,15,16,17,31,32,33,65].all fun aadSize =>
    [0,1,15,16,17,31,32,33,65].all fun ctSize =>
      let a := Array.replicate aadSize (37 : UInt8)
      let c := Array.replicate ctSize (219 : UInt8)
      (encodeMacDataArray a c).toList == Spec.macData a c
  let aeadBoundaryAgreement := [0,1,15,16,17,31,32,33,65].all fun aadSize =>
    [0,1,15,16,17,31,32,33,65].all fun msgSize =>
      let a := Array.replicate aadSize (37 : UInt8)
      let msg := Array.replicate msgSize (219 : UInt8)
      let packet := sealPacket key nonce a msg
      packet.tag == Spec.poly1305 (Spec.macData a packet.ciphertext) (oneTimeKey key nonce) &&
        open? key nonce a packet == some msg
  IO.println s!"RFC 8439 AEAD vector: {if vectorPass then "PASS" else "FAIL"}"
  IO.println s!"RFC 8439 Poly1305 vector: {if polyVectorPass then "PASS" else "FAIL"}"
  IO.println s!"Carry-heavy optimized/spec agreement: {if carryAgreement then "PASS" else "FAIL"}"
  IO.println s!"UInt64 RFC Poly1305 vector: {if fastPolyVectorPass then "PASS" else "FAIL"}"
  IO.println s!"UInt64 boundary differential (0..257): {if fastBoundaryAgreement then "PASS" else "FAIL"}"
  IO.println s!"Authenticated roundtrip: {if roundtripPass then "PASS" else "FAIL"}"
  IO.println s!"Modified tag rejected: {if rejectionPass then "PASS" else "FAIL"}"
  IO.println s!"Word-block boundaries, key lengths, serialization: {if wordBoundaryAgreement && keyLengthAgreement && serializationAgreement then "PASS" else "FAIL"}"
  IO.println s!"Machine list/array, key lengths, final carries, MAC layout: {if machineAgreement && machineKeys && finishAgreement && macArrayAgreement then "PASS" else "FAIL"}"
  IO.println s!"AEAD array boundaries: {if aeadBoundaryAgreement then "PASS" else "FAIL"}"
  unless vectorPass && roundtripPass && rejectionPass && polyVectorPass &&
      carryAgreement && fastPolyVectorPass && fastBoundaryAgreement &&
      wordBoundaryAgreement && keyLengthAgreement && serializationAgreement &&
      machineAgreement && machineKeys && finishAgreement && macArrayAgreement && aeadBoundaryAgreement do
    throw (IO.userError "Poly1305/AEAD regression")

end Crypto.ChaCha20Poly1305.Tests
