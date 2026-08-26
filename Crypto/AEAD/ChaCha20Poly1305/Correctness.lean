import Crypto.AEAD.ChaCha20Poly1305.Impl
import Crypto.Stream.ChaCha20.Correctness

namespace Crypto.ChaCha20Poly1305

open Crypto.ChaCha20

set_option maxRecDepth 10000
set_option maxHeartbeats 200000

theorem oneTimeKey_correct (key : Key) (nonce : Nonce) :
    oneTimeKey key nonce = Spec.oneTimeKey key.toSpec nonce.toSpec := by
  have hblock : keystreamBlock key nonce 0 =
      Spec.blockBytes key.toSpec nonce.toSpec 0 := by
    apply Array.ext
    · rw [keystreamBlock_size]
      simp [Spec.blockBytes]
    · intro i hi₁ hi₂
      have hi : i < 64 := by rw [keystreamBlock_size] at hi₁; exact hi₁
      simpa [Spec.blockBytes, keyToSpec, nonceToSpec] using
        (keystreamBlock_correct key nonce 0 ⟨i, hi⟩)
  simp [oneTimeKey, Spec.oneTimeKey, hblock]

/-- The payload path uses counters 1, 2, ... exactly as the ChaCha specification. -/
theorem payload_correct (key : Key) (nonce : Nonce) (msg : Array UInt8) :
    Crypto.ChaCha20.encrypt key nonce msg = Spec.payload key.toSpec nonce.toSpec msg := by
  unfold Spec.payload
  exact encrypt_correct key nonce msg

theorem bytesToNatLE_correct (xs : List UInt8) :
    bytesToNatLE xs = Spec.bytesToNatLE xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [bytesToNatLE, Spec.bytesToNatLE, ih]

theorem natToBytesLE_correct (count n : Nat) :
    natToBytesLE count n = Spec.natToBytesLE count n := rfl

theorem encodeMacData_correct (aad ciphertext : Array UInt8) :
    encodeMacData aad ciphertext = Spec.macData aad ciphertext := by
  simp [encodeMacData, Spec.macData, padding16, Spec.pad16, encodeLE64,
    Spec.le64, natToBytesLE_correct]

theorem clampMask_correct : clampMask = Spec.clampMask := rfl

/-- The implementation derives exactly RFC 8439's clamped Poly1305 multiplier. -/
theorem clamp_correct (otk : List UInt8) :
    bytesToNatLE (otk.take 16) &&& clampMask =
      Spec.bytesToNatLE (otk.take 16) &&& Spec.clampMask := by
  rw [bytesToNatLE_correct, clampMask_correct]

theorem poly1305Prime_correct : poly1305Prime = Spec.poly1305Prime := rfl

theorem Limbs26.toNat_ofNat (n : Nat) (h : n < limbBase ^ 5) :
    (Limbs26.ofNat n).toNat = n := by
  simp only [Limbs26.ofNat, Limbs26.toNat, mkLimb_toNat]
  have hb : 0 < limbBase := by simp [limbBase]
  have h4 : n / limbBase / limbBase / limbBase / limbBase < limbBase := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
      Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul]
    · simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    · exact Nat.mul_pos hb (Nat.mul_pos hb (Nat.mul_pos hb hb))
  have htop :
      (n / limbBase / limbBase / limbBase / limbBase) % limbBase =
        n / limbBase / limbBase / limbBase / limbBase := Nat.mod_eq_of_lt h4
  rw [htop, Nat.mod_add_div, Nat.mod_add_div, Nat.mod_add_div, Nat.mod_add_div]

theorem Limbs26.reduce_correct (n : Nat) :
    (Limbs26.reduce n).toNat = n % Spec.poly1305Prime := by
  rw [← poly1305Prime_correct]
  apply Limbs26.toNat_ofNat
  apply Nat.lt_trans (Nat.mod_lt _ (by simp [poly1305Prime]))
  simp [poly1305Prime, limbBase]

theorem polyStep_correct (r : Nat) (acc : Limbs26) (chunk : List UInt8) :
    (polyStep r acc chunk).toNat = Spec.polyStep r acc.toNat chunk := by
  simp [polyStep, Spec.polyStep, Limbs26.reduce_correct, bytesToNatLE_correct]

theorem polyBlocks_correct (r : Nat) (message : List UInt8) (acc : Limbs26) :
    (polyBlocks r message acc).toNat = Spec.polyBlocks r message acc.toNat := by
  induction hlen : message.length using Nat.strongRecOn generalizing message acc with
  | ind n ih =>
      cases message with
      | nil => simp [polyBlocks, Spec.polyBlocks]
      | cons b bs =>
          simp only [polyBlocks, Spec.polyBlocks]
          rw [ih (List.length ((b :: bs).drop 16)) (by
              have hn : 0 < n := by rw [← hlen]; simp
              simp only [List.length_drop]
              rw [hlen]
              omega)
            ((b :: bs).drop 16) (polyStep r acc ((b :: bs).take 16)) rfl]
          rw [polyStep_correct]

theorem zero_limbs : (Limbs26.ofNat 0).toNat = 0 := by
  apply Limbs26.toNat_ofNat
  simp [limbBase]

theorem poly1305_correct (message otk : List UInt8) :
    poly1305 message otk = Spec.poly1305 message otk := by
  simp only [poly1305, Spec.poly1305]
  rw [bytesToNatLE_correct, bytesToNatLE_correct, clampMask_correct,
    natToBytesLE_correct, polyBlocks_correct, zero_limbs]

/-- The implementation constructs precisely the inspectable specification packet. -/
theorem seal_correct (key : Key) (nonce : Nonce) (aad plaintext : Array UInt8) :
    sealPacket key nonce aad plaintext =
      Spec.sealPacket key.toSpec nonce.toSpec aad plaintext := by
  simp only [sealPacket, Spec.sealPacket]
  rw [payload_correct, encodeMacData_correct, oneTimeKey_correct, poly1305_correct]

theorem poly1305_tag_length (message otk : List UInt8) :
    (Spec.poly1305 message otk).length = 16 := by
  simp [Spec.poly1305, Spec.natToBytesLE]

theorem poly1305_tag_length_impl (message otk : List UInt8) :
    (poly1305 message otk).length = 16 := by
  rw [poly1305_correct]
  exact poly1305_tag_length message otk

theorem tagMatches_correct_of_expected_tag (supplied expected : List UInt8)
    (he : expected.length = 16) :
    tagMatches supplied expected = true ↔ supplied = expected := by
  constructor
  · simp [tagMatches]
  · intro h
    subst supplied
    simp [tagMatches, he]

/-- Failed authentication has exactly one result: `none`; no plaintext is present. -/
theorem open_failure_releases_nothing (key : Key) (nonce : Nonce) (aad : Array UInt8)
    (packet : Sealed)
    (hbad : packet.tag ≠ Spec.poly1305 (Spec.macData aad packet.ciphertext)
      (Spec.oneTimeKey key.toSpec nonce.toSpec)) :
    open? key nonce aad packet = none := by
  unfold open?
  rw [encodeMacData_correct, oneTimeKey_correct, poly1305_correct]
  have hlen := poly1305_tag_length (Spec.macData aad packet.ciphertext)
    (Spec.oneTimeKey key.toSpec nonce.toSpec)
  have htag : tagMatches packet.tag
      (Spec.poly1305 (Spec.macData aad packet.ciphertext)
        (Spec.oneTimeKey key.toSpec nonce.toSpec)) = false := by
    cases h : tagMatches packet.tag
        (Spec.poly1305 (Spec.macData aad packet.ciphertext)
          (Spec.oneTimeKey key.toSpec nonce.toSpec)) with
    | false => rfl
    | true =>
        exfalso
        apply hbad
        exact (tagMatches_correct_of_expected_tag _ _ hlen).1 h
  dsimp
  rw [htag]
  rfl

/-- The complete authenticated-decryption API agrees with the specification,
    including both acceptance and rejection behavior. -/
theorem open_correct (key : Key) (nonce : Nonce) (aad : Array UInt8) (packet : Sealed) :
    open? key nonce aad packet = Spec.open? key.toSpec nonce.toSpec aad packet := by
  unfold open? Spec.open?
  rw [encodeMacData_correct, oneTimeKey_correct, poly1305_correct]
  let expected := Spec.poly1305 (Spec.macData aad packet.ciphertext)
    (Spec.oneTimeKey key.toSpec nonce.toSpec)
  have hlen : expected.length = 16 := poly1305_tag_length _ _
  change (if tagMatches packet.tag expected then
      some (Crypto.ChaCha20.decrypt key nonce packet.ciphertext) else none) =
    (if packet.tag = expected then
      some (Spec.payload key.toSpec nonce.toSpec packet.ciphertext) else none)
  by_cases h : packet.tag = expected
  · have ht : tagMatches packet.tag expected = true :=
      (tagMatches_correct_of_expected_tag _ _ hlen).2 h
    rw [if_pos ht, if_pos h]
    exact congrArg some ((Crypto.ChaCha20.encrypt_eq_decrypt key nonce _).symm.trans
      (payload_correct key nonce packet.ciphertext))
  · have ht : tagMatches packet.tag expected = false := by
      cases hv : tagMatches packet.tag expected with
      | false => rfl
      | true => exact False.elim (h ((tagMatches_correct_of_expected_tag _ _ hlen).1 hv))
    simp [ht, h]

/-- Successful authenticated decryption of a freshly sealed packet recovers the plaintext. -/
theorem open_seal (key : Key) (nonce : Nonce) (aad plaintext : Array UInt8) :
    open? key nonce aad (sealPacket key nonce aad plaintext) = some plaintext := by
  unfold open? sealPacket
  simp only
  have hlen := poly1305_tag_length_impl
    (encodeMacData aad (Crypto.ChaCha20.encrypt key nonce plaintext)) (oneTimeKey key nonce)
  rw [if_pos]
  · rw [Crypto.ChaCha20.roundtrip]
  · exact (tagMatches_correct_of_expected_tag _ _ hlen).2 rfl

end Crypto.ChaCha20Poly1305
