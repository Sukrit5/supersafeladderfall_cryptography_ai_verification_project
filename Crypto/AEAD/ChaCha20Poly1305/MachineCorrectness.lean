import Crypto.AEAD.ChaCha20Poly1305.Machine
import Crypto.AEAD.ChaCha20Poly1305.WordBlocksCorrectness

namespace Crypto.ChaCha20Poly1305.Machine

open Fast
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

def WordsBound (w : Words) : Prop :=
  w.w0.toNat < 2^32 ∧ w.w1.toNat < 2^32 ∧ w.w2.toNat < 2^32 ∧ w.w3.toNat < 2^32

theorem quotient_eq (h : Limbs) (hh : StateBound h) :
    (quotient h).toNat = (h.value + 5) / 2^130 := by
  rcases hh with ⟨h0,h1,h2,h3,h4⟩
  simp only [quotient, UInt64.toNat_div, UInt64.toNat_add]
  simp only [show (5 : UInt64).toNat = 5 from rfl,
    show (67108864 : UInt64).toNat = 67108864 from rfl]
  have e0 : (h.h0.toNat + 5) % 2^64 = h.h0.toNat + 5 := Nat.mod_eq_of_lt (by omega)
  rw [e0]
  have e1 : (h.h1.toNat + (h.h0.toNat + 5) / 67108864) % 2^64 =
      h.h1.toNat + (h.h0.toNat + 5) / 67108864 := Nat.mod_eq_of_lt (by omega)
  rw [e1]
  have e2 : (h.h2.toNat + (h.h1.toNat + (h.h0.toNat + 5) / 67108864) / 67108864) % 2^64 =
      h.h2.toNat + (h.h1.toNat + (h.h0.toNat + 5) / 67108864) / 67108864 := Nat.mod_eq_of_lt (by omega)
  rw [e2]
  have e3 : (h.h3.toNat + (h.h2.toNat + (h.h1.toNat + (h.h0.toNat + 5) / 67108864) / 67108864) / 67108864) % 2^64 =
      h.h3.toNat + (h.h2.toNat + (h.h1.toNat + (h.h0.toNat + 5) / 67108864) / 67108864) / 67108864 := Nat.mod_eq_of_lt (by omega)
  rw [e3]
  rw [Nat.mod_eq_of_lt (by omega)]
  simp only [Limbs.value, limbBase]
  omega

theorem carry_small (h : Limbs) (hh : StateBound h) :
    (carryWords h).value < prime + 2^27 := by
  have hw : WideBound h := by rcases hh with ⟨a,b,c,d,e⟩; exact ⟨by omega,by omega,by omega,by omega,by omega⟩
  have he := carryWords_correct h hw
  change (carryWords h).toNatLimbs.value < _
  rw [he]
  simp only [carryNat, NatLimbs.value, Limbs.toNatLimbs, limbBase, prime]
  rcases hh with ⟨a,b,c,d,e⟩
  omega

def WideWords (w : Words) : Prop :=
  w.w0.toNat < 2^40 ∧ w.w1.toNat < 2^40 ∧ w.w2.toNat < 2^40 ∧ w.w3.toNat < 2^40

theorem repack_eq (h : Limbs) (hh : StateBound h) :
    (repack h).value = h.value ∧ WideWords (repack h) := by
  rcases hh with ⟨h0,h1,h2,h3,h4⟩
  have e0 : (h.h0 + (h.h1 % 64)*67108864).toNat =
      h.h0.toNat + h.h1.toNat % 64 * 67108864 := by
    simp [UInt64.toNat_add, UInt64.toNat_mul]
    omega
  have e1 : (h.h1 / 64 + (h.h2 % 4096)*1048576).toNat =
      h.h1.toNat / 64 + h.h2.toNat % 4096 * 1048576 := by
    simp [UInt64.toNat_add, UInt64.toNat_mul]
    omega
  have e2 : (h.h2 / 4096 + (h.h3 % 262144)*16384).toNat =
      h.h2.toNat / 4096 + h.h3.toNat % 262144 * 16384 := by
    simp [UInt64.toNat_add, UInt64.toNat_mul]
    omega
  have e3 : (h.h3 / 262144 + h.h4*256).toNat =
      h.h3.toNat / 262144 + h.h4.toNat * 256 := by
    simp [UInt64.toNat_add, UInt64.toNat_mul]
    omega
  simp only [repack, Words.value, WideWords, e0,e1,e2,e3, Limbs.value, limbBase]
  constructor <;> omega

theorem sum3 (a b c : UInt64) (ha : a.toNat < 2^40)
    (hb : b.toNat < 2^40) (hc : c.toNat < 2^40) :
    (a+b+c).toNat = a.toNat+b.toNat+c.toNat := by
  rw [UInt64.toNat_add, UInt64.toNat_add]
  rw [Nat.mod_eq_of_lt (show a.toNat+b.toNat < 2^64 by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem addPad_eq (w s : Words) (c : UInt64) (hw : WideWords w)
    (hs : WordsBound s) (hc : c.toNat < 16) :
    WordsBound (addPad w s c) ∧
      (addPad w s c).value = (w.value+s.value+c.toNat) % 2^128 := by
  rcases hw with ⟨w0,w1,w2,w3⟩
  rcases hs with ⟨s0,s1,s2,s3⟩
  have e0 := sum3 w.w0 s.w0 c w0 (by omega) (by omega)
  have e1 := sum3 w.w1 s.w1 ((w.w0+s.w0+c)/4294967296) w1 (by omega)
    (by rw [UInt64.toNat_div, e0]; change _ / 4294967296 < _; omega)
  have e2 := sum3 w.w2 s.w2 ((w.w1+s.w1+(w.w0+s.w0+c)/4294967296)/4294967296)
    w2 (by omega) (by simp only [UInt64.toNat_div,e1,e0]; simp; omega)
  have e3 := sum3 w.w3 s.w3 ((w.w2+s.w2+(w.w1+s.w1+(w.w0+s.w0+c)/4294967296)/4294967296)/4294967296)
    w3 (by omega) (by simp only [UInt64.toNat_div,e2,e1,e0]; simp; omega)
  simp only [addPad, WordsBound, Words.value, UInt64.toNat_mod, e3,e2,e1,e0, UInt64.toNat_div]
  simp only [show (4294967296 : UInt64).toNat = 4294967296 from rfl]
  constructor <;> omega

theorem wordsBytes_eq (w : Words) (hw : WordsBound w) :
    wordsBytes w = natToBytesLE 16 w.value := by
  rcases hw with ⟨w0,w1,w2,w3⟩
  unfold wordsBytes natToBytesLE
  apply List.map_congr_left
  intro i hi
  have hi : i < 16 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply UInt8.toNat.inj <;>
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.toUInt64,
      Nat.toUInt8, UInt64.toNat_toUInt8, Words.value] <;> omega

theorem finishCore_eq (h : Limbs) (s : Words) (hh : StateBound h)
    (hs : WordsBound s) (hsmall : h.value < prime + 2^27) :
    WordsBound (finishCore h s) ∧
      (finishCore h s).value = (h.value % prime + s.value) % 2^128 := by
  have hq := quotient_eq h hh
  have hqsmall : (quotient h).toNat < 2 := by rw [hq]; simp [prime] at *; omega
  have hc : (quotient h * 5).toNat = (h.value + 5) / 2^130 * 5 := by
    rw [UInt64.toNat_mul]
    change ((quotient h).toNat * 5) % 2^64 = _
    rw [Nat.mod_eq_of_lt (by omega), hq]
  have hr := repack_eq h hh
  have ha := addPad_eq (repack h) s (quotient h * 5) hr.2 hs
    (by rw [hc]; simp [prime] at hsmall; omega)
  refine ⟨ha.1, ?_⟩
  change (addPad (repack h) s (quotient h * 5)).value = _
  rw [ha.2, hr.1, hc]
  by_cases hv : h.value < prime
  · have hq0 : (h.value+5)/2^130 = 0 := by simp [prime] at hv; omega
    rw [hq0, Nat.mod_eq_of_lt hv]
    simp
  · have hq1 : (h.value+5)/2^130 = 1 := by simp [prime] at hv hsmall; omega
    rw [hq1]
    have heq : h.value+s.value+1*5 = h.value%prime+s.value+4*2^128 := by
      simp [prime] at hv hsmall ⊢
      omega
    rw [heq]
    simp [Nat.add_mod]

theorem finish_eq (h : Limbs) (s : Words) (hh : StateBound h) (hs : WordsBound s) :
    finish h s = natToBytesLE 16 ((h.value % prime + s.value) % 2^128) := by
  have hw : WideBound h := by rcases hh with ⟨a,b,c,d,e⟩; exact ⟨by omega,by omega,by omega,by omega,by omega⟩
  have he := finishCore_eq (carryWords h) s (carryWords_stateBound h hw) hs (carry_small h hh)
  have hm : (carryWords h).value % prime = h.value % prime := by
    change (carryWords h).toNatLimbs.value % prime = _
    rw [carryWords_correct h hw, carryNat_mod]
    rfl
  simp only [finish, wordsBytes_eq _ he.1, he.2, hm]

theorem decodeWords_eq (w : Words) (hw : WordsBound w) :
    decodeWords w = RKey.ofNat (w.value &&& 0x0ffffffc0ffffffc0ffffffc0fffffff) := by
  rcases hw with ⟨w0,w1,w2,w3⟩
  have d0 : w.w0 % 67108864 = (w.value / 2^0 % 2^26).toUInt64 := by
    apply UInt64.toNat.inj
    simp [Nat.toUInt64, Words.value]
    omega
  have d1 : w.w0 / 67108864 + (w.w1 % 1048576)*64 = (w.value / 2^26 % 2^26).toUInt64 := by
    apply UInt64.toNat.inj
    simp [UInt64.toNat_add, UInt64.toNat_mul, Nat.toUInt64, Words.value]
    omega
  have d2 : w.w1 / 1048576 + (w.w2 % 16384)*4096 = (w.value / 2^52 % 2^26).toUInt64 := by
    apply UInt64.toNat.inj
    simp [UInt64.toNat_add, UInt64.toNat_mul, Nat.toUInt64, Words.value]
    omega
  have d3 : w.w2 / 16384 + (w.w3 % 256)*262144 = (w.value / 2^78 % 2^26).toUInt64 := by
    apply UInt64.toNat.inj
    simp [UInt64.toNat_add, UInt64.toNat_mul, Nat.toUInt64, Words.value]
    omega
  have d4 : w.w3 / 256 = (w.value / 2^104 % 2^26).toUInt64 := by
    apply UInt64.toNat.inj
    simp [Nat.toUInt64, Words.value]
    omega
  simp only [Nat.pow_zero, Nat.div_one] at d0
  change decodeWords w = ⟨((w.value &&& 0x0ffffffc0ffffffc0ffffffc0fffffff) % 2^26).toUInt64,
    ((w.value &&& 0x0ffffffc0ffffffc0ffffffc0fffffff) / 2^26 % 2^26).toUInt64,
    ((w.value &&& 0x0ffffffc0ffffffc0ffffffc0fffffff) / 2^52 % 2^26).toUInt64,
    ((w.value &&& 0x0ffffffc0ffffffc0ffffffc0fffffff) / 2^78 % 2^26).toUInt64,
    ((w.value &&& 0x0ffffffc0ffffffc0ffffffc0fffffff) / 2^104 % 2^26).toUInt64⟩
  simp only [Nat.and_div_two_pow, Nat.and_mod_two_pow, Nat.toUInt64, UInt64.ofNat_and]
  change decodeWords w = ⟨(w.value % 2^26).toUInt64 &&& 0x3ffffff,
    (w.value / 2^26 % 2^26).toUInt64 &&& 0x3ffff03,
    (w.value / 2^52 % 2^26).toUInt64 &&& 0x3ffc0ff,
    (w.value / 2^78 % 2^26).toUInt64 &&& 0x3f03fff,
    (w.value / 2^104 % 2^26).toUInt64 &&& 0x00fffff⟩
  rw [← d0, ← d1, ← d2, ← d3, ← d4]
  rfl

theorem take4_value (xs : List UInt8) :
    bytesToNatLE (xs.take 4) =
      (WordBlocks.pack4 (xs[0]?.getD 0) (xs[1]?.getD 0)
        (xs[2]?.getD 0) (xs[3]?.getD 0)).toNat := by
  rw [WordBlocks.pack4_toNat]
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;> simp [bytesToNatLE]

theorem take_add4 (xs : List UInt8) (n : Nat) :
    bytesToNatLE (xs.take (4+n)) = bytesToNatLE (xs.take 4) +
      2^32 * bytesToNatLE ((xs.drop 4).take n) := by
  rcases xs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, rest⟩⟩⟩⟩ <;>
    simp [show 4+n = n+1+1+1+1 by omega, bytesToNatLE, Nat.mul_add, Nat.add_assoc] <;> omega

theorem loadWords_bound (a : Array UInt8) (offset : Nat) : WordsBound (loadWords a offset) := by
  exact ⟨WordBlocks.pack4_bound .., WordBlocks.pack4_bound ..,
    WordBlocks.pack4_bound .., WordBlocks.pack4_bound ..⟩

theorem loadWords_value (a : Array UInt8) (offset : Nat) :
    (loadWords a offset).value = bytesToNatLE ((a.toList.drop offset).take 16) := by
  rw [show 16 = 4+12 from rfl, take_add4, show 12 = 4+8 from rfl, take_add4,
    show 8 = 4+4 from rfl, take_add4]
  simp only [take4_value, List.drop_drop, List.getElem?_drop, Array.getElem?_toList,
    loadWords, Words.value]
  simp only [Nat.add_assoc, Nat.add_zero, Nat.reduceAdd]
  omega

theorem poly1305_correct (message key : List UInt8) :
    poly1305 message key = Spec.poly1305 message key := by
  have hr := decodeWords_eq (loadWords key.toArray 0) (loadWords_bound ..)
  have hs := loadWords_value key.toArray 16
  have hv := loadWords_value key.toArray 0
  simp only [List.drop_zero] at hv
  rw [hv] at hr
  let rNat := bytesToNatLE (key.take 16) &&& 0x0ffffffc0ffffffc0ffffffc0fffffff
  have hb := blocksList_correct rNat message ⟨0,0,0,0,0⟩ zero_stateBound (clamped_lt_limbRange key)
  unfold poly1305
  dsimp only
  rw [hr, WordBlocks.blocks_eq, finish_eq _ _ hb.1 (loadWords_bound ..), hs, hb.2]
  simp only [Spec.poly1305, ← bytesToNatLE_correct, ← natToBytesLE_correct]
  rfl

end Crypto.ChaCha20Poly1305.Machine
