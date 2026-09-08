import Crypto.AEAD.ChaCha20Poly1305.WordBlocks
import Crypto.AEAD.ChaCha20Poly1305.FastCorrectness

namespace Crypto.ChaCha20Poly1305.WordBlocks

open Fast

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

theorem pack4_toNat (a b c d : UInt8) :
    (pack4 a b c d).toNat = a.toNat + 256 * (b.toNat + 256 * (c.toNat + 256 * d.toNat)) := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  have mul256 (x : UInt64) (hx : x.toNat < 2^32) :
      (256 * x).toNat = 256 * x.toNat := by
    rw [UInt64.toNat_mul]
    change (256 * x.toNat) % 2^64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have addByte (x : UInt64) (b : UInt8) (hx : x.toNat < 2^40) :
      (b.toUInt64 + x).toNat = b.toNat + x.toNat := by
    rw [UInt64.toNat_add, UInt8.toNat_toUInt64]
    have hb := b.toNat_lt
    exact Nat.mod_eq_of_lt (by omega)
  have h1 : (256 * d.toUInt64).toNat = 256 * d.toNat :=
    mul256 _ (by simpa using (show d.toNat < 2^32 by omega))
  have h2 : (c.toUInt64 + 256 * d.toUInt64).toNat = c.toNat + 256 * d.toNat := by
    rw [addByte _ _ (by rw [h1]; omega), h1]
  have h3 : (256 * (c.toUInt64 + 256 * d.toUInt64)).toNat =
      256 * (c.toNat + 256 * d.toNat) := by
    rw [mul256 _ (by rw [h2]; omega), h2]
  have h4 : (b.toUInt64 + 256 * (c.toUInt64 + 256 * d.toUInt64)).toNat =
      b.toNat + 256 * (c.toNat + 256 * d.toNat) := by
    rw [addByte _ _ (by rw [h3]; omega), h3]
  have h5 : (256 * (b.toUInt64 + 256 * (c.toUInt64 + 256 * d.toUInt64))).toNat =
      256 * (b.toNat + 256 * (c.toNat + 256 * d.toNat)) := by
    rw [mul256 _ (by rw [h4]; omega), h4]
  unfold pack4
  rw [addByte _ _ (by rw [h5]; omega), h5]

theorem addWords_eq (h : Limbs) (a b c d : UInt64)
    (ha : a.toNat < 2^32) (hb : b.toNat < 2^32)
    (hc : c.toNat < 2^32) (hd : d.toNat < 2^32) :
    addWords h a b c d = h.addNat
      (a.toNat + 2^32*b.toNat + 2^64*c.toNat + 2^96*d.toNat + 2^128) := by
  have limb0 : a % 67108864 =
      ((a.toNat + 2^32*b.toNat + 2^64*c.toNat + 2^96*d.toNat + 2^128) % limbBase).toUInt64 := by
    apply UInt64.toNat.inj
    simp [limbBase, UInt64.toNat_mod, Nat.toUInt64]
    omega
  have limb1 : a / 67108864 + (b % 1048576) * 64 =
      ((a.toNat + 2^32*b.toNat + 2^64*c.toNat + 2^96*d.toNat + 2^128) / limbBase % limbBase).toUInt64 := by
    apply UInt64.toNat.inj
    simp [limbBase, UInt64.toNat_add, UInt64.toNat_mul, Nat.toUInt64]
    omega
  have limb2 : b / 1048576 + (c % 16384) * 4096 =
      ((a.toNat + 2^32*b.toNat + 2^64*c.toNat + 2^96*d.toNat + 2^128) / limbBase^2 % limbBase).toUInt64 := by
    apply UInt64.toNat.inj
    simp [limbBase, UInt64.toNat_add, UInt64.toNat_mul, Nat.toUInt64]
    omega
  have limb3 : c / 16384 + (d % 256) * 262144 =
      ((a.toNat + 2^32*b.toNat + 2^64*c.toNat + 2^96*d.toNat + 2^128) / limbBase^3 % limbBase).toUInt64 := by
    apply UInt64.toNat.inj
    simp [limbBase, UInt64.toNat_add, UInt64.toNat_mul, Nat.toUInt64]
    omega
  have limb4 : d / 256 + 16777216 =
      ((a.toNat + 2^32*b.toNat + 2^64*c.toNat + 2^96*d.toNat + 2^128) / limbBase^4 % limbBase).toUInt64 := by
    apply UInt64.toNat.inj
    simp [limbBase, UInt64.toNat_add, Nat.toUInt64]
    omega
  simp only [addWords, Limbs.addNat, limb0, limb1, limb2, limb3, limb4]

theorem pack4_bound (a b c d : UInt8) : (pack4 a b c d).toNat < 2^32 := by
  rw [pack4_toNat]
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  omega

theorem add_full_eq (h : Limbs)
    (a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 : UInt8) :
    addWords h (pack4 a0 a1 a2 a3) (pack4 b0 b1 b2 b3)
      (pack4 c0 c1 c2 c3) (pack4 d0 d1 d2 d3) =
    h.addNat (bytesToNatLE [a0,a1,a2,a3,b0,b1,b2,b3,c0,c1,c2,c3,d0,d1,d2,d3] + 256^16) := by
  rw [addWords_eq h _ _ _ _ (pack4_bound ..) (pack4_bound ..)
    (pack4_bound ..) (pack4_bound ..)]
  simp only [pack4_toNat, bytesToNatLE]
  apply congrArg (fun n => h.addNat n)
  omega

theorem blocks_eq (r : RKey) (message : List UInt8) (h : Limbs) :
    blocks r message h = blocksList r message h := by
  fun_induction blocks r message h with
  | case1 a0 a1 a2 a3 b0 b1 b2 b3 c0 c1 c2 c3 d0 d1 d2 d3 rest h ih =>
      rw [blocksList]
      simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero,
        List.length_cons, List.length_nil]
      rw [add_full_eq]
      simpa only [add_full_eq] using ih
  | case2 tail h hn =>
      rfl

theorem tagBytes_eq (n : Nat) : tagBytes n = natToBytesLE 16 n := by
  unfold tagBytes natToBytesLE
  apply List.map_congr_left
  intro i hi
  have hi : i < 16 := List.mem_range.mp hi
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply UInt8.toNat.inj <;>
    simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow, Nat.toUInt64,
      Nat.toUInt8, UInt64.toNat_toUInt8] <;> omega

theorem poly1305_correct (message keyBytes : List UInt8) :
    poly1305 message keyBytes = Spec.poly1305 message keyBytes := by
  have heq : poly1305 message keyBytes = Fast.poly1305 message keyBytes := by
    simp only [poly1305, Fast.poly1305, blocks_eq, tagBytes_eq]
  exact heq.trans (Fast.poly1305_correct message keyBytes)

end Crypto.ChaCha20Poly1305.WordBlocks
