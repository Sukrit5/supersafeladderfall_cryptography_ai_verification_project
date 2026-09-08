import Crypto.AEAD.ChaCha20Poly1305.Fast

namespace Crypto.ChaCha20Poly1305.Fast

set_option maxHeartbeats 0
set_option maxRecDepth 10000

@[ext] structure NatLimbs where
  h0 : Nat
  h1 : Nat
  h2 : Nat
  h3 : Nat
  h4 : Nat

def NatLimbs.value (h : NatLimbs) : Nat :=
  h.h0 + limbBase * (h.h1 + limbBase *
    (h.h2 + limbBase * (h.h3 + limbBase * h.h4)))

def Limbs.toNatLimbs (h : Limbs) : NatLimbs :=
  ⟨h.h0.toNat, h.h1.toNat, h.h2.toNat, h.h3.toNat, h.h4.toNat⟩

def RKey.toNatLimbs (r : RKey) : NatLimbs :=
  ⟨r.r0.toNat, r.r1.toNat, r.r2.toNat, r.r3.toNat, r.r4.toNat⟩

@[simp] theorem toNatLimbs_value (h : Limbs) : h.toNatLimbs.value = h.value := rfl

def NatLimbs.ofNat (n : Nat) : NatLimbs :=
  ⟨n % limbBase, n / limbBase % limbBase,
   n / limbBase / limbBase % limbBase,
   n / limbBase / limbBase / limbBase % limbBase,
   n / limbBase / limbBase / limbBase / limbBase % limbBase⟩

theorem NatLimbs.value_ofNat (n : Nat) (hn : n < limbBase ^ 5) :
    (NatLimbs.ofNat n).value = n := by
  simp only [NatLimbs.ofNat, NatLimbs.value]
  have hb : 0 < limbBase := by simp [limbBase]
  have h4 : n / limbBase / limbBase / limbBase / limbBase < limbBase := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul,
      Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul]
    · simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hn
    · exact Nat.mul_pos hb (Nat.mul_pos hb (Nat.mul_pos hb hb))
  have htop :
      (n / limbBase / limbBase / limbBase / limbBase) % limbBase =
        n / limbBase / limbBase / limbBase / limbBase := Nat.mod_eq_of_lt h4
  rw [htop, Nat.mod_add_div, Nat.mod_add_div, Nat.mod_add_div, Nat.mod_add_div]

theorem RKey.ofNat_value (n : Nat) (hn : n < limbBase ^ 5) :
    (RKey.ofNat n).toNatLimbs.value = n := by
  have hdigit (x : Nat) (hx : x < limbBase) : x.toUInt64.toNat = x := by
    change x % 2 ^ 64 = x
    exact Nat.mod_eq_of_lt (Nat.lt_trans hx (by simp [limbBase]))
  have heq : (RKey.ofNat n).toNatLimbs = NatLimbs.ofNat n := by
    apply NatLimbs.ext <;>
      simp [RKey.ofNat, RKey.toNatLimbs, NatLimbs.ofNat, hdigit, Nat.mod_lt,
        Nat.div_div_eq_div_mul, limbBase, Nat.pow_two]
  rw [heq, NatLimbs.value_ofNat n hn]

def convolutionNat (h r : NatLimbs) : NatLimbs :=
  ⟨h.h0*r.h0 + 5*(h.h1*r.h4 + h.h2*r.h3 + h.h3*r.h2 + h.h4*r.h1),
   h.h0*r.h1 + h.h1*r.h0 + 5*(h.h2*r.h4 + h.h3*r.h3 + h.h4*r.h2),
   h.h0*r.h2 + h.h1*r.h1 + h.h2*r.h0 + 5*(h.h3*r.h4 + h.h4*r.h3),
   h.h0*r.h3 + h.h1*r.h2 + h.h2*r.h1 + h.h3*r.h0 + 5*(h.h4*r.h4),
   h.h0*r.h4 + h.h1*r.h3 + h.h2*r.h2 + h.h3*r.h1 + h.h4*r.h0⟩

def carryNat (d : NatLimbs) : NatLimbs :=
  let c0 := d.h0 / limbBase; let h0 := d.h0 % limbBase; let d1 := d.h1 + c0
  let c1 := d1 / limbBase; let h1 := d1 % limbBase; let d2 := d.h2 + c1
  let c2 := d2 / limbBase; let h2 := d2 % limbBase; let d3 := d.h3 + c2
  let c3 := d3 / limbBase; let h3 := d3 % limbBase; let d4 := d.h4 + c3
  let c4 := d4 / limbBase; let h4 := d4 % limbBase; let h0 := h0 + c4*5
  let c0 := h0 / limbBase
  ⟨h0 % limbBase, h1 + c0, h2, h3, h4⟩

private def convolutionOverflow (h r : NatLimbs) : Nat :=
  let c5 := h.h1*r.h4 + h.h2*r.h3 + h.h3*r.h2 + h.h4*r.h1
  let c6 := h.h2*r.h4 + h.h3*r.h3 + h.h4*r.h2
  let c7 := h.h3*r.h4 + h.h4*r.h3
  let c8 := h.h4*r.h4
  c5 + limbBase * (c6 + limbBase * (c7 + limbBase * c8))

theorem convolutionNat_decomposition (h r : NatLimbs) :
    h.value * r.value = (convolutionNat h r).value +
      prime * convolutionOverflow h r := by
  simp only [NatLimbs.value, convolutionNat, convolutionOverflow, limbBase, prime,
    Nat.add_mul, Nat.mul_add]
  simp only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  grind

theorem carryNat_mod (d : NatLimbs) :
    (carryNat d).value % prime = d.value % prime := by
  simp only [carryNat, NatLimbs.value, limbBase, prime]
  omega

theorem carryConvolution_mod (h r : NatLimbs) :
    (carryNat (convolutionNat h r)).value % prime =
      (h.value * r.value) % prime := by
  rw [carryNat_mod, convolutionNat_decomposition]
  simp [Nat.add_mod]

private theorem fiveProducts_noOverflow
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : UInt64)
    (ha0 : a0.toNat < 2^28) (ha1 : a1.toNat < 2^28)
    (ha2 : a2.toNat < 2^28) (ha3 : a3.toNat < 2^28) (ha4 : a4.toNat < 2^28)
    (hb0 : b0.toNat < 2^29) (hb1 : b1.toNat < 2^29)
    (hb2 : b2.toNat < 2^29) (hb3 : b3.toNat < 2^29) (hb4 : b4.toNat < 2^29) :
    (a0*b0 + a1*b1 + a2*b2 + a3*b3 + a4*b4).toNat =
      a0.toNat*b0.toNat + a1.toNat*b1.toNat + a2.toNat*b2.toNat +
        a3.toNat*b3.toNat + a4.toNat*b4.toNat := by
  simp only [UInt64.toNat_add, UInt64.toNat_mul]
  have hp0 : a0.toNat*b0.toNat < 2^28*2^29 :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha0) hb0 (by simp)
  have hp1 : a1.toNat*b1.toNat < 2^28*2^29 :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha1) hb1 (by simp)
  have hp2 : a2.toNat*b2.toNat < 2^28*2^29 :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha2) hb2 (by simp)
  have hp3 : a3.toNat*b3.toNat < 2^28*2^29 :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha3) hb3 (by simp)
  have hp4 : a4.toNat*b4.toNat < 2^28*2^29 :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha4) hb4 (by simp)
  repeat rw [Nat.mod_eq_of_lt (by omega)]

def RBound (r : RKey) : Prop :=
  r.r0.toNat < 2^26 ∧ r.r1.toNat < 2^26 ∧ r.r2.toNat < 2^26 ∧
    r.r3.toNat < 2^26 ∧ r.r4.toNat < 2^26

def AccBound (h : Limbs) : Prop :=
  h.h0.toNat < 2^28 ∧ h.h1.toNat < 2^28 ∧ h.h2.toNat < 2^28 ∧
    h.h3.toNat < 2^28 ∧ h.h4.toNat < 2^28

def StateBound (h : Limbs) : Prop :=
  h.h0.toNat < 2^27 ∧ h.h1.toNat < 2^27 ∧ h.h2.toNat < 2^27 ∧
    h.h3.toNat < 2^27 ∧ h.h4.toNat < 2^27

theorem RKey.ofNat_bound (n : Nat) : RBound (RKey.ofNat n) := by
  simp only [RBound, RKey.ofNat, Nat.toUInt64, limbBase]
  have digit (x : Nat) : x % 67108864 % 18446744073709551616 < 67108864 :=
    Nat.lt_of_le_of_lt (Nat.mod_le _ _) (Nat.mod_lt _ (by omega))
  exact ⟨digit _, digit _, digit _, digit _, digit _⟩

private theorem timesFive_noOverflow (x : UInt64) (hx : x.toNat < 2^26) :
    (x * 5).toNat = x.toNat * 5 ∧ (x * 5).toNat < 2^29 := by
  rw [UInt64.toNat_mul, show (5 : UInt64).toNat = 5 by rfl,
    Nat.mod_eq_of_lt (by omega)]
  omega

theorem convolve_correct (h : Limbs) (r : RKey) (hh : AccBound h) (hr : RBound r) :
    (convolve h r).toNatLimbs = convolutionNat h.toNatLimbs r.toNatLimbs := by
  rcases hh with ⟨hh0, hh1, hh2, hh3, hh4⟩
  rcases hr with ⟨hr0, hr1, hr2, hr3, hr4⟩
  have hs1 := timesFive_noOverflow r.r1 hr1
  have hs2 := timesFive_noOverflow r.r2 hr2
  have hs3 := timesFive_noOverflow r.r3 hr3
  have hs4 := timesFive_noOverflow r.r4 hr4
  apply NatLimbs.ext
  simp only [convolve, Limbs.toNatLimbs, convolutionNat]
  · exact fiveProducts_noOverflow _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
      (by omega) (by omega) (by omega)
      (by omega) (by simpa [hs4.1] using hs4.2) (by simpa [hs3.1] using hs3.2)
      (by simpa [hs2.1] using hs2.2) (by simpa [hs1.1] using hs1.2) |>.trans (by
        rw [hs1.1, hs2.1, hs3.1, hs4.1]
        simp [convolutionNat, Limbs.toNatLimbs, RKey.toNatLimbs]
        grind)
  · exact fiveProducts_noOverflow _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
        (by omega) (by omega) (by omega)
        (by omega) (by omega) (by simpa [hs4.1] using hs4.2)
        (by simpa [hs3.1] using hs3.2) (by simpa [hs2.1] using hs2.2) |>.trans (by
          rw [hs2.1, hs3.1, hs4.1]
          simp [convolutionNat, Limbs.toNatLimbs, RKey.toNatLimbs]
          grind)
  · exact fiveProducts_noOverflow _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
          (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by simpa [hs4.1] using hs4.2)
          (by simpa [hs3.1] using hs3.2) |>.trans (by
            simp [hs3.1, hs4.1, convolutionNat, Limbs.toNatLimbs, RKey.toNatLimbs]
            grind)
  · exact fiveProducts_noOverflow _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
            (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega)
            (by simpa [hs4.1] using hs4.2) |>.trans (by
              simp [hs4.1, convolutionNat, Limbs.toNatLimbs, RKey.toNatLimbs]
              grind)
  · exact fiveProducts_noOverflow _ _ _ _ _ _ _ _ _ _ (by omega) (by omega)
            (by omega) (by omega) (by omega)
            (by omega) (by omega) (by omega) (by omega) (by omega)

def WideBound (d : Limbs) : Prop :=
  d.h0.toNat < 2^60 ∧ d.h1.toNat < 2^60 ∧ d.h2.toNat < 2^60 ∧
    d.h3.toNat < 2^60 ∧ d.h4.toNat < 2^60

private theorem fiveProducts_bound
    (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : UInt64)
    (ha0 : a0.toNat < 2^28) (ha1 : a1.toNat < 2^28)
    (ha2 : a2.toNat < 2^28) (ha3 : a3.toNat < 2^28) (ha4 : a4.toNat < 2^28)
    (hb0 : b0.toNat < 2^29) (hb1 : b1.toNat < 2^29)
    (hb2 : b2.toNat < 2^29) (hb3 : b3.toNat < 2^29) (hb4 : b4.toNat < 2^29) :
    (a0*b0 + a1*b1 + a2*b2 + a3*b3 + a4*b4).toNat < 2^60 := by
  rw [fiveProducts_noOverflow _ _ _ _ _ _ _ _ _ _ ha0 ha1 ha2 ha3 ha4
    hb0 hb1 hb2 hb3 hb4]
  have hp0 : a0.toNat*b0.toNat < 2^28*2^29 :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha0) hb0 (by simp)
  have hp1 : a1.toNat*b1.toNat < 2^28*2^29 :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha1) hb1 (by simp)
  have hp2 : a2.toNat*b2.toNat < 2^28*2^29 :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha2) hb2 (by simp)
  have hp3 : a3.toNat*b3.toNat < 2^28*2^29 :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha3) hb3 (by simp)
  have hp4 : a4.toNat*b4.toNat < 2^28*2^29 :=
    Nat.mul_lt_mul_of_le_of_lt (Nat.le_of_lt ha4) hb4 (by simp)
  omega

theorem convolve_bound (h : Limbs) (r : RKey) (hh : AccBound h) (hr : RBound r) :
    WideBound (convolve h r) := by
  rcases hh with ⟨hh0, hh1, hh2, hh3, hh4⟩
  rcases hr with ⟨hr0, hr1, hr2, hr3, hr4⟩
  have hs1 := timesFive_noOverflow r.r1 hr1
  have hs2 := timesFive_noOverflow r.r2 hr2
  have hs3 := timesFive_noOverflow r.r3 hr3
  have hs4 := timesFive_noOverflow r.r4 hr4
  simp only [WideBound, convolve]
  exact ⟨fiveProducts_bound _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by simpa [hs4.1] using hs4.2)
      (by simpa [hs3.1] using hs3.2) (by simpa [hs2.1] using hs2.2)
      (by simpa [hs1.1] using hs1.2),
    fiveProducts_bound _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by simpa [hs4.1] using hs4.2)
      (by simpa [hs3.1] using hs3.2) (by simpa [hs2.1] using hs2.2),
    fiveProducts_bound _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simpa [hs4.1] using hs4.2) (by simpa [hs3.1] using hs3.2),
    fiveProducts_bound _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by simpa [hs4.1] using hs4.2),
    fiveProducts_bound _ _ _ _ _ _ _ _ _ _ (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

@[simp] theorem mask26_toNat (x : UInt64) :
    (x &&& 0x3ffffff).toNat = x.toNat % limbBase := by
  rw [UInt64.toNat_and]
  change x.toNat &&& 67108863 = x.toNat % limbBase
  rw [show (67108863 : Nat) = 2^26 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  rfl

@[simp] theorem shift26_toNat (x : UInt64) :
    (x >>> 26).toNat = x.toNat / limbBase := by
  rw [UInt64.toNat_shiftRight]
  change x.toNat >>> 26 = x.toNat / limbBase
  simp [Nat.shiftRight_eq_div_pow, limbBase]

theorem carryWords_correct (d : Limbs) (hd : WideBound d) :
    (carryWords d).toNatLimbs = carryNat d.toNatLimbs := by
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4⟩
  have hd1' : d.h1.toNat + d.h0.toNat / limbBase < 2^64 := by
    simp [limbBase] at *; omega
  have hd2' : d.h2.toNat + (d.h1.toNat + d.h0.toNat / limbBase) / limbBase < 2^64 := by
    simp [limbBase] at *; omega
  have hd3' : d.h3.toNat +
      (d.h2.toNat + (d.h1.toNat + d.h0.toNat / limbBase) / limbBase) / limbBase < 2^64 := by
    simp [limbBase] at *; omega
  have hd4' : d.h4.toNat + (d.h3.toNat +
      (d.h2.toNat + (d.h1.toNat + d.h0.toNat / limbBase) / limbBase) / limbBase) /
        limbBase < 2^64 := by
    simp [limbBase] at *; omega
  have hc4 : (d.h4.toNat + (d.h3.toNat +
      (d.h2.toNat + (d.h1.toNat + d.h0.toNat / limbBase) / limbBase) / limbBase) /
        limbBase) / limbBase * 5 < 2^64 := by
    simp [limbBase] at *; omega
  have hh0' : d.h0.toNat % limbBase +
      (d.h4.toNat + (d.h3.toNat +
        (d.h2.toNat + (d.h1.toNat + d.h0.toNat / limbBase) / limbBase) / limbBase) /
          limbBase) / limbBase * 5 < 2^64 := by
    have hm : d.h0.toNat % limbBase < limbBase :=
      Nat.mod_lt _ (by simp [limbBase])
    simp [limbBase] at *; omega
  have hh1' : (d.h1.toNat + d.h0.toNat / limbBase) % limbBase +
      (d.h0.toNat % limbBase +
        (d.h4.toNat + (d.h3.toNat +
          (d.h2.toNat + (d.h1.toNat + d.h0.toNat / limbBase) / limbBase) /
            limbBase) / limbBase) / limbBase * 5) / limbBase < 2^64 := by
    have hm1 : (d.h1.toNat + d.h0.toNat / limbBase) % limbBase < limbBase :=
      Nat.mod_lt _ (by simp [limbBase])
    simp [limbBase] at *; omega
  simp [limbBase] at hd1' hd2' hd3' hd4' hc4 hh0' hh1'
  apply NatLimbs.ext <;>
    simp only [carryWords, Limbs.toNatLimbs, carryNat, shift26_toNat,
      mask26_toNat, UInt64.toNat_add, UInt64.toNat_mul]
  all_goals
    simp [limbBase]
    simp only [Nat.mod_eq_of_lt hd1', Nat.mod_eq_of_lt hd2', Nat.mod_eq_of_lt hd3',
      Nat.mod_eq_of_lt hd4', Nat.mod_eq_of_lt hc4, Nat.mod_eq_of_lt hh0',
      Nat.mod_eq_of_lt hh1']

theorem carryNat_bound (d : NatLimbs)
    (hd : d.h0 < 2^60 ∧ d.h1 < 2^60 ∧ d.h2 < 2^60 ∧
      d.h3 < 2^60 ∧ d.h4 < 2^60) :
    (carryNat d).h0 < 2^27 ∧ (carryNat d).h1 < 2^27 ∧
      (carryNat d).h2 < 2^27 ∧ (carryNat d).h3 < 2^27 ∧
      (carryNat d).h4 < 2^27 := by
  rcases hd with ⟨hd0, hd1, hd2, hd3, hd4⟩
  simp only [carryNat]
  have hm : (d.h0 % limbBase +
      (d.h4 + (d.h3 + (d.h2 + (d.h1 + d.h0 / limbBase) / limbBase) / limbBase) /
        limbBase) / limbBase * 5) % limbBase < limbBase :=
    Nat.mod_lt _ (by simp [limbBase])
  simp [limbBase] at hm ⊢
  omega

theorem carryWords_stateBound (d : Limbs) (hd : WideBound d) : StateBound (carryWords d) := by
  have hc := carryWords_correct d hd
  have hn : d.toNatLimbs.h0 < 2^60 ∧ d.toNatLimbs.h1 < 2^60 ∧
      d.toNatLimbs.h2 < 2^60 ∧ d.toNatLimbs.h3 < 2^60 ∧
      d.toNatLimbs.h4 < 2^60 := hd
  have hb := carryNat_bound d.toNatLimbs hn
  rw [← hc] at hb
  simpa [StateBound, Limbs.toNatLimbs] using hb

theorem mulReduce_mod (h : Limbs) (r : RKey) (hh : AccBound h) (hr : RBound r) :
    (mulReduce h r).value % prime =
      (h.value * r.toNatLimbs.value) % prime := by
  have hconv := convolve_correct h r hh hr
  have hwide := convolve_bound h r hh hr
  have hcarry := carryWords_correct (convolve h r) hwide
  have hmodel := carryConvolution_mod h.toNatLimbs r.toNatLimbs
  simp only [mulReduce, ← toNatLimbs_value]
  rw [hcarry, hconv]
  simpa [toNatLimbs_value] using hmodel

theorem mulReduce_stateBound (h : Limbs) (r : RKey)
    (hh : AccBound h) (hr : RBound r) : StateBound (mulReduce h r) := by
  exact carryWords_stateBound (convolve h r) (convolve_bound h r hh hr)

theorem bytesToNatLE_correct (xs : List UInt8) :
    bytesToNatLE xs = Spec.bytesToNatLE xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [bytesToNatLE, Spec.bytesToNatLE, ih]

theorem natToBytesLE_correct (count n : Nat) :
    natToBytesLE count n = Spec.natToBytesLE count n := rfl

theorem bytesToNatLE_lt (xs : List UInt8) : bytesToNatLE xs < 256 ^ xs.length := by
  induction xs with
  | nil => simp [bytesToNatLE]
  | cons b bs ih =>
      have hb : b.toNat < 256 := by simpa using b.toNat_lt
      simp only [bytesToNatLE, List.length_cons, Nat.pow_succ]
      omega

private theorem digit_lt (n i : Nat) : n / limbBase ^ i % limbBase < limbBase :=
  Nat.mod_lt _ (by simp [limbBase])

theorem addNat_correct (h : Limbs) (n : Nat) (hh : StateBound h)
    (hn : n < limbBase ^ 5) :
    AccBound (h.addNat n) ∧ (h.addNat n).value = h.value + n := by
  rcases hh with ⟨hh0, hh1, hh2, hh3, hh4⟩
  have hd0 := digit_lt n 0
  have hd1 := digit_lt n 1
  have hd2 := digit_lt n 2
  have hd3 := digit_lt n 3
  have hd4 := digit_lt n 4
  have hd0' : n % limbBase < limbBase := Nat.mod_lt _ (by simp [limbBase])
  have hd1' : n / limbBase % limbBase < limbBase := Nat.mod_lt _ (by simp [limbBase])
  have hu0 : h.h0.toNat + n % limbBase < 2^64 := by
    simp [limbBase] at *; omega
  have hu1 : h.h1.toNat + n / limbBase % limbBase < 2^64 := by
    simp [limbBase] at *; omega
  have hu2 : h.h2.toNat + n / limbBase^2 % limbBase < 2^64 := by
    simp [limbBase] at *; omega
  have hu3 : h.h3.toNat + n / limbBase^3 % limbBase < 2^64 := by
    simp [limbBase] at *; omega
  have hu4 : h.h4.toNat + n / limbBase^4 % limbBase < 2^64 := by
    simp [limbBase] at *; omega
  have hdigit (x : Nat) (hx : x < limbBase) : x.toUInt64.toNat = x := by
    change x % 2^64 = x
    exact Nat.mod_eq_of_lt (Nat.lt_trans hx (by simp [limbBase]))
  constructor
  · simp only [AccBound, Limbs.addNat, UInt64.toNat_add]
    simp [hdigit, digit_lt, hu0, hu1, hu2, hu3, hu4, limbBase] at *
    omega
  · have hv := NatLimbs.value_ofNat n hn
    simp only [Limbs.addNat, Limbs.value, UInt64.toNat_add]
    simp only [hdigit _ hd0', hdigit _ hd1', hdigit _ hd2, hdigit _ hd3,
      hdigit _ hd4]
    rw [Nat.mod_eq_of_lt hu0, Nat.mod_eq_of_lt hu1, Nat.mod_eq_of_lt hu2,
      Nat.mod_eq_of_lt hu3, Nat.mod_eq_of_lt hu4]
    simp only [NatLimbs.ofNat, NatLimbs.value] at hv
    simp [limbBase] at hv ⊢
    omega

theorem blockValue_lt (chunk : List UInt8) (hlen : chunk.length ≤ 16) :
    bytesToNatLE chunk + 256 ^ chunk.length < limbBase ^ 5 := by
  have hb := bytesToNatLE_lt chunk
  have hp : 256 ^ chunk.length ≤ 256 ^ 16 :=
    Nat.pow_le_pow_right (by omega) hlen
  have hn : 2 * 256 ^ 16 < limbBase ^ 5 := by decide
  have hs : bytesToNatLE chunk + 256 ^ chunk.length <
      2 * 256 ^ chunk.length := by omega
  calc
    bytesToNatLE chunk + 256 ^ chunk.length < 2 * 256 ^ chunk.length := hs
    _ ≤ 2 * 256 ^ 16 := Nat.mul_le_mul_left 2 hp
    _ < limbBase ^ 5 := hn

theorem blocksList_correct (rNat : Nat) (message : List UInt8) (h : Limbs)
    (hh : StateBound h) (hrNat : rNat < limbBase ^ 5) :
    StateBound (blocksList (RKey.ofNat rNat) message h) ∧
      (blocksList (RKey.ofNat rNat) message h).value % prime =
        Spec.polyBlocks rNat message (h.value % prime) := by
  induction hlen : message.length using Nat.strongRecOn generalizing message h with
  | ind n ih =>
      cases message with
      | nil => simp [blocksList, Spec.polyBlocks, hh]
      | cons b bs =>
          let bytes := b :: bs
          let chunk := bytes.take 16
          let block := bytesToNatLE chunk + 256 ^ chunk.length
          let added := h.addNat block
          let next := mulReduce added (RKey.ofNat rNat)
          have hchunk : chunk.length ≤ 16 := List.length_take_le 16 bytes
          have hblock : block < limbBase ^ 5 := blockValue_lt chunk hchunk
          have hadd := addNat_correct h block hh hblock
          have hr : RBound (RKey.ofNat rNat) := RKey.ofNat_bound rNat
          have hnext : StateBound next := mulReduce_stateBound added (RKey.ofNat rNat) hadd.1 hr
          have hstep : next.value % prime = Spec.polyStep rNat (h.value % prime) chunk := by
            have hm := mulReduce_mod added (RKey.ofNat rNat) hadd.1 hr
            rw [RKey.ofNat_value rNat hrNat, hadd.2] at hm
            rw [hm]
            simp [Spec.polyStep, bytesToNatLE_correct, block, prime, Spec.poly1305Prime,
              Nat.add_assoc, Nat.add_mod, Nat.mul_mod]
          have hdrop : (bytes.drop 16).length < n := by
            have hn : 0 < n := by rw [← hlen]; simp
            simp only [List.length_drop]
            rw [hlen]
            omega
          have hrec := ih (bytes.drop 16).length hdrop (bytes.drop 16) next hnext rfl
          rw [hstep] at hrec
          constructor
          · simpa [blocksList, bytes, chunk, block, added, next] using hrec.1
          · simpa [blocksList, Spec.polyBlocks, bytes, chunk, block, added, next,
              hstep] using hrec.2

theorem clamped_lt_limbRange (xs : List UInt8) :
    bytesToNatLE (xs.take 16) &&& 0x0ffffffc0ffffffc0ffffffc0fffffff <
      limbBase ^ 5 := by
  have hm : (0x0ffffffc0ffffffc0ffffffc0fffffff : Nat) < 2 ^ 128 := by decide
  have hr := Nat.and_lt_two_pow (bytesToNatLE (xs.take 16)) hm
  simp [limbBase] at hr ⊢
  omega

theorem zero_stateBound : StateBound (⟨0, 0, 0, 0, 0⟩ : Limbs) := by
  simp [StateBound]

/-- The optimized fixed-width Poly1305 implementation refines the mathematical
    RFC 8439 specification for every message and one-time key. -/
theorem poly1305_correct (message keyBytes : List UInt8) :
    poly1305 message keyBytes = Spec.poly1305 message keyBytes := by
  let rNat := bytesToNatLE (keyBytes.take 16) &&&
    0x0ffffffc0ffffffc0ffffffc0fffffff
  let s := bytesToNatLE (keyBytes.drop 16 |>.take 16)
  have hr : rNat < limbBase ^ 5 := clamped_lt_limbRange keyBytes
  have hb := (blocksList_correct rNat message (⟨0, 0, 0, 0, 0⟩ : Limbs)
    zero_stateBound hr).2
  simp only [poly1305, Spec.poly1305]
  rw [← bytesToNatLE_correct, ← bytesToNatLE_correct, ← natToBytesLE_correct]
  change natToBytesLE 16
      (((blocksList (RKey.ofNat rNat) message ⟨0, 0, 0, 0, 0⟩).value % prime + s) %
        2 ^ 128) =
    natToBytesLE 16 ((Spec.polyBlocks rNat message 0 + s) % 2 ^ 128)
  rw [hb]
  rfl

end Crypto.ChaCha20Poly1305.Fast
