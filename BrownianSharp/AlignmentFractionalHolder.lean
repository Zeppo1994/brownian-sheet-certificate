import BrownianSharp.AlignmentFractionalTranslation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Quantitative translation regularity for the fractional RL feature kernels.

The scalar monotonicity inequalities used in the eventual integral split are
proved here first. The L² increment theorem will use them on the overlap of
the two causal supports; the singular origin and the truncation endpoint are
handled separately.
-/

noncomputable section
open MeasureTheory
open BrownianSharp.AlignmentFractionalKernel
open BrownianSharp.AlignmentFractionalTranslation

namespace BrownianSharp.AlignmentFractionalHolder

theorem sq_sub_le_sq_sub_of_nonneg_order {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) :
    (a - b)^2 ≤ a^2 - b^2 := by
  have hfactor : a^2 - b^2 = (a-b)*(a+b) := by ring
  rw [hfactor]
  have hdiff : 0 ≤ a-b := sub_nonneg.mpr hba
  nlinarith

theorem rpow_increment_sq_le_sq_increment_of_neg_exponent
    {q x h : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hq : q ≤ 0) :
    (x^q - (x+h)^q)^2 ≤ x^(2*q) - (x+h)^(2*q) := by
  have hx' : 0 ≤ x := hx.le
  have hxh : 0 < x+h := by linarith
  have hpow : 0 ≤ (x+h)^q := Real.rpow_nonneg hxh.le _
  have hxy : x ≤ x+h := by linarith
  have hmono : (x+h)^q ≤ x^q := Real.rpow_le_rpow_of_nonpos hx hxy hq
  have hsq := sq_sub_le_sq_sub_of_nonneg_order hpow hmono
  have hmulx : x^(2*q) = (x^q)^2 := by
    rw [show 2*q=q*2 by ring]
    calc
      x^(q*2) = (x^q)^(2:ℝ) := Real.rpow_mul hx' q 2
      _ = (x^q)^2 := Real.rpow_natCast (x^q) 2
  have hmulxh : (x+h)^(2*q) = ((x+h)^q)^2 := by
    rw [show 2*q=q*2 by ring]
    calc
      (x+h)^(q*2) = ((x+h)^q)^(2:ℝ) := Real.rpow_mul hxh.le q 2
      _ = ((x+h)^q)^2 := Real.rpow_natCast ((x+h)^q) 2
  simpa [hmulx, hmulxh] using hsq

theorem rpow_increment_sq_le_sq_increment_of_nonneg_exponent
    {q x h : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) (hq : 0 ≤ q) :
    ((x+h)^q - x^q)^2 ≤ (x+h)^(2*q) - x^(2*q) := by
  by_cases hxpos : x = 0
  · subst x
    by_cases hq0 : q = 0
    · subst q
      simp
    · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
      have hmul : h^(2*q) = (h^q)^2 := by
        rw [show 2*q=q*2 by ring]
        calc
          h^(q*2) = (h^q)^(2:ℝ) := Real.rpow_mul hh q 2
          _ = (h^q)^2 := Real.rpow_natCast (h^q) 2
      simp [Real.zero_rpow, hq0, hmul]
  have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm hxpos)
  have hxh : 0 < x+h := by linarith
  have hpow : 0 ≤ x^q := Real.rpow_nonneg hx _
  have hxy : x ≤ x+h := by linarith
  have hmono : x^q ≤ (x+h)^q := Real.rpow_le_rpow hx hxy hq
  have hsq := sq_sub_le_sq_sub_of_nonneg_order hpow hmono
  have hmulx : x^(2*q) = (x^q)^2 := by
    rw [show 2*q=q*2 by ring]
    calc
      x^(q*2) = (x^q)^(2:ℝ) := Real.rpow_mul hx q 2
      _ = (x^q)^2 := Real.rpow_natCast (x^q) 2
  have hmulxh : (x+h)^(2*q) = ((x+h)^q)^2 := by
    rw [show 2*q=q*2 by ring]
    calc
      (x+h)^(q*2) = ((x+h)^q)^(2:ℝ) := Real.rpow_mul hxh.le q 2
      _ = ((x+h)^q)^2 := Real.rpow_natCast ((x+h)^q) 2
  simpa [hmulx, hmulxh, sub_eq_add_neg, add_comm] using hsq

/-- The overlap contribution of a translated monotone power is controlled by
the singular boundary interval. This is the telescoping integral estimate
used for the negative-exponent RL kernels. -/
theorem rpow_overlap_integral_le_boundary {p h : ℝ}
    (hp : -1 < p) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ x in (0:ℝ)..(1-h), x^p - (x+h)^p) ≤
      ∫ x in (0:ℝ)..h, x^p := by
  let f : ℝ → ℝ := fun x => x^p
  have hbase : IntervalIntegrable f volume 0 1 := by
    exact intervalIntegral.intervalIntegrable_rpow' hp
  have h0 : IntervalIntegrable f volume 0 h := by
    apply hbase.mono_set
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      simp
    · rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      constructor <;> linarith
  have hshift : IntervalIntegrable (fun x => f (x+h)) volume 0 (1-h) := by
    have ht : IntervalIntegrable f volume h 1 := by
      apply hbase.mono_set
      apply Set.uIcc_subset_uIcc
      · rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
        constructor <;> linarith
      · rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
        simp
    simpa using ht.comp_add_right h
  have h01 : IntervalIntegrable f volume 0 (1-h) := by
    apply hbase.mono_set
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      simp
    · rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      constructor <;> linarith
  have hB : IntervalIntegrable f volume (1-h) 1 := by
    apply hbase.mono_set
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      constructor <;> linarith
    · rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      simp
  have hJ : IntervalIntegrable f volume h 1 := by
    apply hbase.mono_set
    apply Set.uIcc_subset_uIcc
    · rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      constructor <;> linarith
    · rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      simp
  have hsum1 := intervalIntegral.integral_add_adjacent_intervals h0 hJ
  have hsum2 := intervalIntegral.integral_add_adjacent_intervals h01 hB
  have hshiftEq : (∫ x in (0:ℝ)..(1-h), f (x+h)) = ∫ x in h..1, f x := by
    rw [intervalIntegral.integral_comp_add_right]
    simp [sub_add_cancel]
  have hidentity :
      (∫ x in (0:ℝ)..(1-h), f x) - ∫ x in h..1, f x =
        (∫ x in (0:ℝ)..h, f x) - ∫ x in (1-h)..1, f x := by
    linarith
  have hBnonneg : 0 ≤ ∫ x in (1-h)..1, f x := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro x hx
    have hx0 : 0 ≤ x := by
      linarith [hx.1]
    exact Real.rpow_nonneg hx0 _
  rw [intervalIntegral.integral_sub h01 hshift, hshiftEq]
  rw [hidentity]
  linarith

/-- The negative-power overlap estimate in the squared-kernel form. The two
interval-integrability hypotheses are the exact local inputs needed by the
integral comparison; for RL exponents they follow from `2q > -1`. -/
theorem rpow_overlap_squared_integral_le_boundary {q h : ℝ}
    (hq : -1/2 < q) (hq0 : q ≤ 0) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hL : IntervalIntegrable (fun x : ℝ => (x^q - (x+h)^q)^2)
      volume 0 (1-h))
    (hR : IntervalIntegrable (fun x : ℝ => x^(2*q) - (x+h)^(2*q))
      volume 0 (1-h)) :
    (∫ x in (0:ℝ)..(1-h), (x^q - (x+h)^q)^2) ≤
      ∫ x in (0:ℝ)..h, x^(2*q) := by
  have hp : -1 < 2*q := by linarith
  have hpt : ∀ x ∈ Set.Ioo (0:ℝ) (1-h),
      (x^q - (x+h)^q)^2 ≤ x^(2*q) - (x+h)^(2*q) := by
    intro x hx
    have hx0 : 0 < x := hx.1
    exact rpow_increment_sq_le_sq_increment_of_neg_exponent hx0 hh hq0
  have hcmp := intervalIntegral.integral_mono_on_of_le_Ioo
    (by linarith) hL hR hpt
  have htel := rpow_overlap_integral_le_boundary hp hh hh1
  exact hcmp.trans htel

private theorem intervalIntegrable_rpow_subinterval {p a b : ℝ}
    (hp : -1 < p) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (fun x : ℝ => x^p) volume a b := by
  have hbase : IntervalIntegrable (fun x : ℝ => x^p) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hp
  apply hbase.mono_set
  apply Set.uIcc_subset_uIcc
  · rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    constructor <;> linarith
  · rw [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
    constructor <;> linarith

private theorem rpow_shift_intervalIntegrable {p h : ℝ}
    (hp : -1 < p) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    IntervalIntegrable (fun x : ℝ => (x+h)^p) volume 0 (1-h) := by
  have hbase : IntervalIntegrable (fun x : ℝ => x^p) volume h 1 :=
    intervalIntegrable_rpow_subinterval hp hh (by linarith) le_rfl
  simpa using hbase.comp_add_right h

private theorem rpow_difference_square_intervalIntegrable {q h : ℝ}
    (hq : -1/2 < q) (hh : 0 < h) (hh1 : h ≤ 1) :
    IntervalIntegrable (fun x : ℝ => (x^q - (x+h)^q)^2)
      volume 0 (1-h) := by
  have hq' : -1 < q := by linarith
  have h2q : -1 < 2*q := by linarith
  have hqInterval : IntervalIntegrable (fun x : ℝ => x^q)
      volume 0 (1-h) := intervalIntegrable_rpow_subinterval hq' (by norm_num)
        (by linarith) (by linarith)
  have h2qInterval : IntervalIntegrable (fun x : ℝ => x^(2*q))
      volume 0 (1-h) := intervalIntegrable_rpow_subinterval h2q (by norm_num)
        (by linarith) (by linarith)
  have h2qShift : IntervalIntegrable (fun x : ℝ => (x+h)^(2*q))
      volume 0 (1-h) := rpow_shift_intervalIntegrable h2q (le_of_lt hh) hh1
  have hqShift : IntervalIntegrable (fun x : ℝ => (x+h)^q)
      volume 0 (1-h) := rpow_shift_intervalIntegrable hq' (le_of_lt hh) hh1
  have hcont : ContinuousOn (fun x : ℝ => (x+h)^q) (Set.uIcc 0 (1-h)) := by
    apply (continuousOn_id.add continuousOn_const).rpow_const
    intro x hx
    change x+h ≠ 0 ∨ 0 ≤ q
    left
    have hx' : x ∈ Set.Icc 0 (1-h) := by
      simpa [Set.uIcc_of_le (by linarith : (0:ℝ)≤1-h)] using hx
    linarith [hx'.1]
  have hprod : IntervalIntegrable (fun x : ℝ => x^q * (x+h)^q)
      volume 0 (1-h) := hqInterval.mul_continuousOn hcont
  have hexpand : ∀ x ∈ Set.uIoo (0:ℝ) (1-h),
      (x^q - (x+h)^q)^2 = x^(2*q) + (x+h)^(2*q) -
        2 * (x^q * (x+h)^q) := by
    intro x hx
    have hx0 : 0 ≤ x := by
      have hx' : x ∈ Set.Ioo 0 (1-h) := by
        simpa [Set.uIoo_of_le (by linarith : (0:ℝ)≤1-h)] using hx
      linarith [hx'.1]
    have hxh0 : 0 ≤ x+h := by linarith [hh.le]
    have hxpow : (x^q)^2 = x^(2*q) := by
      calc
        (x^q)^2 = x^(q*2) := (Real.rpow_mul_natCast hx0 q 2).symm
        _ = x^(2*q) := by rw [mul_comm q 2]
    have hxhpw : ((x+h)^q)^2 = (x+h)^(2*q) := by
      calc
        ((x+h)^q)^2 = (x+h)^(q*2) := (Real.rpow_mul_natCast hxh0 q 2).symm
        _ = (x+h)^(2*q) := by rw [mul_comm q 2]
    rw [sub_sq, hxpow, hxhpw]
    ring
  have hsum : IntervalIntegrable
      (fun x : ℝ => x^(2*q) + (x+h)^(2*q) - 2 * (x^q * (x+h)^q))
      volume 0 (1-h) := (h2qInterval.add h2qShift).sub (hprod.const_mul 2)
  exact (intervalIntegrable_congr_uIoo hexpand).mpr hsum

theorem rpow_overlap_squared_integral_le_boundary_of_order
    {q h : ℝ} (hq : -1/2 < q) (hq0 : q ≤ 0)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ x in (0:ℝ)..(1-h), (x^q - (x+h)^q)^2) ≤
      ∫ x in (0:ℝ)..h, x^(2*q) := by
  by_cases hh0 : h = 0
  · subst h
    simp
  have hpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
  have hq' : -1 < q := by linarith
  have h2q : -1 < 2*q := by linarith
  have hL := rpow_difference_square_intervalIntegrable hq hpos hh1
  have hRleft : IntervalIntegrable (fun x : ℝ => x^(2*q)) volume 0 (1-h) :=
    intervalIntegrable_rpow_subinterval h2q (by norm_num) (by linarith) (by linarith)
  have hRright : IntervalIntegrable (fun x : ℝ => (x+h)^(2*q))
      volume 0 (1-h) := rpow_shift_intervalIntegrable h2q hh hh1
  have hR := hRleft.sub hRright
  exact rpow_overlap_squared_integral_le_boundary hq hq0 hh hh1 hL hR

/-! ### The nonsingular support edge

The preceding overlap estimate deals with the only singular part of a
translated negative power.  At the right edge of the cutoff the power is
bounded, and its contribution is linear in the translation distance. -/

theorem rpow_right_edge_integral_le {p h : ℝ} (hp : 0 ≤ p)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ x in (1-h:ℝ)..1, x^p) ≤ h := by
  have hi : IntervalIntegrable (fun x : ℝ => x^p) volume (1-h) 1 := by
    apply (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < p)).mono_set
    have hs : Set.uIcc (1-h:ℝ) 1 ⊆ Set.uIcc 0 1 := by
      rw [Set.uIcc_of_le (by linarith : (1:ℝ)-h ≤ 1),
        Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩
    exact hs
  have hpoint : ∀ x ∈ Set.Ioo (1-h:ℝ) 1, x^p ≤ 1 := by
    intro x hx
    exact Real.rpow_le_one (by linarith [hx.1]) (by linarith [hx.2]) hp
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (by linarith)
    hi intervalIntegrable_const hpoint
  simpa [intervalIntegral.integral_const] using hmono

theorem rpow_overlap_integral_le_right_edge {p h : ℝ} (hp : 0 ≤ p)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ x in (0:ℝ)..(1-h), (x+h)^p - x^p) ≤
      ∫ x in (1-h)..1, x^p := by
  let f : ℝ → ℝ := fun x => x^p
  have hbase : IntervalIntegrable f volume 0 1 := by
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < p))
  have h0 : IntervalIntegrable f volume 0 h := by
    apply hbase.mono_set
    have hs : Set.uIcc (0:ℝ) h ⊆ Set.uIcc 0 1 := by
      rw [Set.uIcc_of_le hh, Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      intro x hx
      exact ⟨hx.1, by linarith [hx.2, hh1]⟩
    exact hs
  have hshift : IntervalIntegrable (fun x => f (x+h)) volume 0 (1-h) := by
    have ht : IntervalIntegrable f volume h 1 := by
      apply hbase.mono_set
      have hs : Set.uIcc (h:ℝ) 1 ⊆ Set.uIcc 0 1 := by
        rw [Set.uIcc_of_le (by linarith : h ≤ 1),
          Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
        intro x hx
        exact ⟨by linarith [hx.1, hh], hx.2⟩
      exact hs
    simpa using ht.comp_add_right h
  have h01 : IntervalIntegrable f volume 0 (1-h) := by
    apply hbase.mono_set
    have hs : Set.uIcc (0:ℝ) (1-h) ⊆ Set.uIcc 0 1 := by
      rw [Set.uIcc_of_le (by linarith : (0:ℝ)≤1-h),
        Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      intro x hx
      exact ⟨hx.1, by linarith [hx.2]⟩
    exact hs
  have hB : IntervalIntegrable f volume (1-h) 1 := by
    apply hbase.mono_set
    have hs : Set.uIcc (1-h:ℝ) 1 ⊆ Set.uIcc 0 1 := by
      rw [Set.uIcc_of_le (by linarith : (1:ℝ)-h ≤ 1),
        Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      intro x hx
      exact ⟨by linarith [hx.1, hh], hx.2⟩
    exact hs
  have hJ : IntervalIntegrable f volume h 1 := by
    apply hbase.mono_set
    have hs : Set.uIcc (h:ℝ) 1 ⊆ Set.uIcc 0 1 := by
      rw [Set.uIcc_of_le (by linarith : h ≤ 1),
        Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      intro x hx
      exact ⟨by linarith [hx.1, hh], hx.2⟩
    exact hs
  have hsum1 := intervalIntegral.integral_add_adjacent_intervals h0 hJ
  have hsum2 := intervalIntegral.integral_add_adjacent_intervals h01 hB
  have hshiftEq : (∫ x in (0:ℝ)..(1-h), f (x+h)) = ∫ x in h..1, f x := by
    rw [intervalIntegral.integral_comp_add_right]
    simp [sub_add_cancel]
  have hidentity :
      (∫ x in (0:ℝ)..(1-h), f (x+h)) - ∫ x in (0:ℝ)..(1-h), f x =
        (∫ x in (1-h:ℝ)..1, f x) - ∫ x in (0:ℝ)..h, f x := by
    linarith
  have hleft_nonneg : 0 ≤ ∫ x in (0:ℝ)..h, f x := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro x hx
    exact Real.rpow_nonneg (by linarith [hx.1]) _
  change (∫ x in (0:ℝ)..(1-h), f (x+h) - f x) ≤ _
  rw [intervalIntegral.integral_sub hshift h01, hidentity]
  linarith

theorem rpow_overlap_squared_integral_le_right_edge
    {q h : ℝ} (hq : 0 ≤ q) (hh : 0 ≤ h) (hh1 : h ≤ 1)
    (hL : IntervalIntegrable (fun x : ℝ => ((x+h)^q - x^q)^2)
      volume 0 (1-h))
    (hR : IntervalIntegrable (fun x : ℝ => (x+h)^(2*q) - x^(2*q))
      volume 0 (1-h)) :
    (∫ x in (0:ℝ)..(1-h), ((x+h)^q - x^q)^2) ≤
      ∫ x in (1-h)..1, x^(2*q) := by
  have hpt : ∀ x ∈ Set.Ioo (0:ℝ) (1-h),
      ((x+h)^q - x^q)^2 ≤ (x+h)^(2*q) - x^(2*q) := by
    intro x hx
    exact rpow_increment_sq_le_sq_increment_of_nonneg_exponent
      (le_of_lt hx.1) hh hq
  have hcmp := intervalIntegral.integral_mono_on_of_le_Ioo
    (by linarith) hL hR hpt
  have htel := rpow_overlap_integral_le_right_edge (p := 2*q) (by positivity) hh hh1
  exact hcmp.trans htel

theorem rpow_overlap_squared_integral_le_h_of_nonneg_order
    {q h : ℝ} (hq : 0 ≤ q) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ x in (0:ℝ)..(1-h), ((x+h)^q - x^q)^2) ≤ h := by
  by_cases hh0 : h = 0
  · subst h
    simp
  have hpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
  have hq' : -1/2 < q := by linarith
  have hL := rpow_difference_square_intervalIntegrable hq' hpos hh1
  have hL' : IntervalIntegrable (fun x : ℝ => ((x+h)^q - x^q)^2)
      volume 0 (1-h) := by
    apply hL.congr_uIoo
    intro x hx
    ring
  have h2q : -1 < 2*q := by linarith
  have hRleft : IntervalIntegrable (fun x : ℝ => x^(2*q)) volume 0 (1-h) :=
    intervalIntegrable_rpow_subinterval h2q (by norm_num) (by linarith) (by linarith)
  have hRright : IntervalIntegrable (fun x : ℝ => (x+h)^(2*q))
      volume 0 (1-h) := rpow_shift_intervalIntegrable h2q hh hh1
  have hR := hRright.sub hRleft
  have hcmp := rpow_overlap_squared_integral_le_right_edge hq hh hh1 hL' hR
  have htop := rpow_right_edge_integral_le (p := 2*q) (by positivity) hh hh1
  exact hcmp.trans htop

theorem rpow_left_edge_integral_le {p h : ℝ} (hp : 0 ≤ p)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ x in (0:ℝ)..h, x^p) ≤ h := by
  have hi : IntervalIntegrable (fun x : ℝ => x^p) volume 0 h := by
    apply (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < p)).mono_set
    have hs : Set.uIcc (0:ℝ) h ⊆ Set.uIcc 0 1 := by
      rw [Set.uIcc_of_le hh, Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      intro x hx
      exact ⟨hx.1, by linarith [hx.2, hh1]⟩
    exact hs
  have hpoint : ∀ x ∈ Set.Ioo (0:ℝ) h, x^p ≤ 1 := by
    intro x hx
    exact Real.rpow_le_one (by linarith [hx.1]) (by linarith [hx.2, hh1]) hp
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (by linarith)
    hi intervalIntegrable_const hpoint
  simpa [intervalIntegral.integral_const] using hmono

theorem rpow_boundary_integral_eq {p h : ℝ} (hp : -1 < p)
    (_hh : 0 ≤ h) :
    (∫ x in (0:ℝ)..h, x^p) = h^(p+1) / (p+1) := by
  have hp1 : p + 1 ≠ 0 := ne_of_gt (by linarith)
  rw [integral_rpow (Or.inl hp)]
  rw [Real.zero_rpow hp1]
  ring

theorem rpow_overlap_squared_integral_le_explicit_boundary
    {q h : ℝ} (hq : -1/2 < q) (hq0 : q ≤ 0)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ x in (0:ℝ)..(1-h), (x^q - (x+h)^q)^2) ≤
      h^(2*q+1) / (2*q+1) := by
  have hbase := rpow_overlap_squared_integral_le_boundary_of_order hq hq0 hh hh1
  have hp : -1 < 2*q := by linarith
  have hformula := rpow_boundary_integral_eq hp hh
  rw [hformula] at hbase
  exact hbase

theorem rpow_negative_right_edge_integral_le_holder {p h : ℝ}
    (hp : -1 < p) (hp0 : p ≤ 0) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ x in (1-h:ℝ)..1, x^p) ≤
      (2 / (p+1) + (1/2:ℝ)^p) * h^(p+1) := by
  have hbase : IntervalIntegrable (fun x : ℝ => x^p) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' hp
  have hexp0 : 0 < p+1 := by linarith
  have hexp1 : p+1 ≤ 1 := by linarith
  by_cases hsmall : h ≤ 1/2
  · by_cases hh0 : h = 0
    · subst h
      simp [Real.zero_rpow hexp0.ne']
    have hpos : 0 < h := lt_of_le_of_ne hh (Ne.symm hh0)
    have hi : IntervalIntegrable (fun x : ℝ => x^p) volume (1-h) 1 := by
      apply hbase.mono_set
      have hs : Set.uIcc (1-h:ℝ) 1 ⊆ Set.uIcc 0 1 := by
        rw [Set.uIcc_of_le (by linarith : (1:ℝ)-h ≤ 1),
          Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
        intro x hx
        exact ⟨by linarith [hx.1], hx.2⟩
      exact hs
    have hpoint : ∀ x ∈ Set.Ioo (1-h:ℝ) 1, x^p ≤ (1/2:ℝ)^p := by
      intro x hx
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith [hx.1, hsmall]) hp0
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (by linarith)
      hi intervalIntegrable_const hpoint
    have hpow : h ≤ h^(p+1) := by
      calc
        h = h^1 := (Real.rpow_one h).symm
        _ ≤ h^(p+1) := Real.rpow_le_rpow_of_exponent_ge hpos (by linarith [hh1]) hexp1
    have hC : (1/2:ℝ)^p ≤ 2 / (p+1) + (1/2:ℝ)^p := by
      have hd : 0 < 2 / (p+1) := by positivity
      linarith
    calc
      (∫ x in (1-h:ℝ)..1, x^p) ≤ h * (1/2:ℝ)^p := by
        simpa [intervalIntegral.integral_const] using hmono
      _ ≤ h^(p+1) * (2 / (p+1) + (1/2:ℝ)^p) := by
        have hc : 0 ≤ (1/2:ℝ)^p := Real.rpow_nonneg (by norm_num) _
        nlinarith [mul_le_mul_of_nonneg_right hpow hc,
          mul_le_mul_of_nonneg_left hC (by positivity : 0 ≤ h^(p+1))]
      _ = (2 / (p+1) + (1/2:ℝ)^p) * h^(p+1) := by ring
  · have hlarge : 1/2 < h := lt_of_not_ge hsmall
    have hlow : IntervalIntegrable (fun x : ℝ => x^p) volume 0 (1-h) := by
      apply hbase.mono_set
      have hs : Set.uIcc (0:ℝ) (1-h) ⊆ Set.uIcc 0 1 := by
        rw [Set.uIcc_of_le (by linarith : (0:ℝ)≤1-h),
          Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
        intro x hx
        exact ⟨hx.1, by linarith [hx.2, hh1]⟩
      exact hs
    have hsum := intervalIntegral.integral_add_adjacent_intervals hlow
      (hbase.mono_set (by
        have hs : Set.uIcc (1-h:ℝ) 1 ⊆ Set.uIcc 0 1 := by
          rw [Set.uIcc_of_le (by linarith : (1:ℝ)-h ≤ 1),
            Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
          intro x hx
          exact ⟨by linarith [hx.1, hh], hx.2⟩
        exact hs))
    have hlow_nonneg : 0 ≤ ∫ x in (0:ℝ)..(1-h), x^p := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro x hx
      exact Real.rpow_nonneg (by linarith [hx.1]) _
    have hwhole0 := rpow_boundary_integral_eq hp (by norm_num : 0 ≤ (1:ℝ))
    have hwhole : (∫ x in (0:ℝ)..1, x^p) = 1 / (p+1) := by simpa using hwhole0
    have hsmallBound : (∫ x in (1-h:ℝ)..1, x^p) ≤ 1 / (p+1) := by
      linarith [hsum, hlow_nonneg, hwhole]
    have hpower : (1/2:ℝ) ≤ h^(p+1) := by
      calc
        (1/2:ℝ) ≤ h := le_of_lt hlarge
        _ ≤ h^(p+1) := by
          calc
            h = h^1 := (Real.rpow_one h).symm
            _ ≤ h^(p+1) := Real.rpow_le_rpow_of_exponent_ge (by linarith)
              (by linarith [hh1]) hexp1
    have hC : 2 / (p+1) ≤ 2 / (p+1) + (1/2:ℝ)^p := by
      have hpownonneg : 0 ≤ (1/2:ℝ)^p := Real.rpow_nonneg (by norm_num) _
      linarith
    calc
      (∫ x in (1-h:ℝ)..1, x^p) ≤ 1 / (p+1) := hsmallBound
      _ ≤ (2 / (p+1) + (1/2:ℝ)^p) * h^(p+1) := by
        have hmul := mul_le_mul_of_nonneg_right hpower (by positivity : 0 ≤ 2/(p+1))
        have hmul2 := mul_le_mul_of_nonneg_left hC (by positivity : 0 ≤ h^(p+1))
        have heq : (1/2:ℝ) * (2/(p+1)) = 1/(p+1) := by field_simp
        nlinarith

def kernelCutIncrement (α h x : ℝ) : ℝ :=
  kernelCut α (x+h) - kernelCut α x

private theorem kernelCut_eq_kernel_of_pos_le_one {α x : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) : kernelCut α x = kernel α x := by
  simp [kernelCut, Set.mem_Ioc, hx0, hx1]

private theorem kernelCut_eq_zero_of_nonpos {α x : ℝ} (hx : x ≤ 0) :
    kernelCut α x = 0 := by
  simp [kernelCut, Set.mem_Ioc, not_lt.mpr hx]

private theorem kernelCut_eq_zero_of_one_lt {α x : ℝ} (hx : 1 < x) :
    kernelCut α x = 0 := by
  simp [kernelCut, Set.mem_Ioc, not_le.mpr hx]

private theorem kernel_sq_eq_gamma_rpow {α x : ℝ} (hx : 0 < x) :
    (kernel α x)^2 = ((Real.Gamma α)⁻¹)^2 * x^(2*(α-1)) := by
  unfold kernel
  have hp : (x^(α-1))^2 = x^(2*(α-1)) := by
    calc
      (x^(α-1))^2 = x^((α-1)*2) := (Real.rpow_mul_natCast hx.le (α-1) 2).symm
      _ = x^(2*(α-1)) := by congr 1; ring
  rw [mul_pow, hp]

theorem kernelCut_increment_sq_integrable {α h : ℝ} (hα : 1/2 < α) :
    Integrable (fun x : ℝ => (kernelCutIncrement α h x)^2) volume := by
  have hm : MeasurePreserving (fun x : ℝ => x+h) volume volume := by
    simpa [add_comm] using measurePreserving_add_left volume h
  have hk : MemLp (kernelCut α) 2 (volume : Measure ℝ) := kernelCut_memLp hα
  have hshift : MemLp (fun x : ℝ => kernelCut α (x+h)) 2 volume :=
    hk.comp_measurePreserving hm
  have hdiff : MemLp (kernelCutIncrement α h) 2 volume := by
    exact hshift.sub hk
  exact (memLp_two_iff_integrable_sq hdiff.aestronglyMeasurable).mp hdiff

theorem kernelCut_increment_sq_integral_eq_interval {α h : ℝ}
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ x, (kernelCutIncrement α h x)^2) =
      ∫ x in (-3:ℝ)..3, (kernelCutIncrement α h x)^2 := by
  have hs : Function.support (fun x : ℝ => (kernelCutIncrement α h x)^2) ⊆
      Set.Ioc (-3:ℝ) 3 := by
    apply Function.support_subset_iff'.2
    intro x hx
    by_cases hl : x ≤ -3
    · have hx0 : x ≤ 0 := by linarith
      have hx1 : x+h ≤ 0 := by linarith [hh1]
      simp [kernelCutIncrement, kernelCut_eq_zero_of_nonpos hx0,
        kernelCut_eq_zero_of_nonpos hx1]
    · have hx2 : 3 ≤ x := by
        by_contra hnot
        have hxlt : x < 3 := lt_of_not_ge hnot
        exact hx ⟨by linarith, hxlt.le⟩
      have hx0 : 1 < x := by linarith
      have hx1 : 1 < x+h := by linarith
      simp [kernelCutIncrement, kernelCut_eq_zero_of_one_lt hx0,
        kernelCut_eq_zero_of_one_lt hx1]
  exact (intervalIntegral.integral_eq_integral_of_support_subset hs).symm

theorem kernelCut_increment_sq_integral_le_of_order_le_one
    {α h : ℝ} (hα : 1/2 < α) (hα1 : α ≤ 1)
    (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ x, (kernelCutIncrement α h x)^2) ≤
      ((Real.Gamma α)⁻¹)^2 *
        (4 / (2*(α-1)+1) + (1/2:ℝ)^(2*(α-1))) * h^(2*α-1) := by
  let q : ℝ := α-1
  have hq : -1/2 < q := by dsimp [q]; linarith
  have hq0 : q ≤ 0 := by dsimp [q]; linarith
  have hq1 : 2*q+1 = 2*α-1 := by dsimp [q]; ring
  have hI := kernelCut_increment_sq_integrable (α := α) (h := h) hα
  have hIall : ∀ a b : ℝ, IntervalIntegrable
      (fun x : ℝ => (kernelCutIncrement α h x)^2) volume a b :=
    fun a b => hI.intervalIntegrable
  have hA := hIall (-3) (-h)
  have hB := hIall (-h) 0
  have hC := hIall 0 (1-h)
  have hD := hIall (1-h) 1
  have hE := hIall 1 3
  have hs1 := intervalIntegral.integral_add_adjacent_intervals hA hB
  have hs2 := intervalIntegral.integral_add_adjacent_intervals hC hD
  have hs3 := intervalIntegral.integral_add_adjacent_intervals hE
    (hIall 3 4)
  have hs4 := intervalIntegral.integral_add_adjacent_intervals
    (hIall 1 3) (hIall 3 4)
  have hleftTail : (∫ x in (-3:ℝ)..(-h),
      (kernelCutIncrement α h x)^2) = 0 := by
    calc
      (∫ x in (-3:ℝ)..(-h), (kernelCutIncrement α h x)^2) =
          ∫ x in (-3:ℝ)..(-h), (0:ℝ) := intervalIntegral.integral_congr_uIoo (by
            intro x hx
            have hx' : x ∈ Set.Ioo (-3:ℝ) (-h) := by
              simpa [Set.uIoo_of_le (by linarith : (-3:ℝ) ≤ -h)] using hx
            have hx0 : x ≤ 0 := by linarith [hx'.2]
            have hx1 : x+h ≤ 0 := by linarith [hx'.2]
            simp [kernelCutIncrement, kernelCut_eq_zero_of_nonpos hx0,
              kernelCut_eq_zero_of_nonpos hx1])
      _ = 0 := by simp
  have hrightTail : (∫ x in (1:ℝ)..3,
      (kernelCutIncrement α h x)^2) = 0 := by
    calc
      (∫ x in (1:ℝ)..3, (kernelCutIncrement α h x)^2) =
          ∫ x in (1:ℝ)..3, (0:ℝ) := intervalIntegral.integral_congr_uIoo (by
            intro x hx
            have hx' : x ∈ Set.Ioo (1:ℝ) 3 := by
              simpa [Set.uIoo_of_le (by norm_num : (1:ℝ) ≤ 3)] using hx
            have hx0 : 1 < x := hx'.1
            have hx1 : 1 < x+h := by linarith [hh]
            simp [kernelCutIncrement, kernelCut_eq_zero_of_one_lt hx0,
              kernelCut_eq_zero_of_one_lt hx1])
      _ = 0 := by simp
  have houterTail : (∫ x in (3:ℝ)..4,
      (kernelCutIncrement α h x)^2) = 0 := by
    calc
      (∫ x in (3:ℝ)..4, (kernelCutIncrement α h x)^2) =
          ∫ x in (3:ℝ)..4, (0:ℝ) := intervalIntegral.integral_congr_uIoo (by
            intro x hx
            have hx' : x ∈ Set.Ioo (3:ℝ) 4 := by
              simpa [Set.uIoo_of_le (by norm_num : (3:ℝ) ≤ 4)] using hx
            have hx0 : 1 < x := by linarith [hx'.1]
            have hx1 : 1 < x+h := by linarith [hx'.1, hh]
            simp [kernelCutIncrement, kernelCut_eq_zero_of_one_lt hx0,
              kernelCut_eq_zero_of_one_lt hx1])
      _ = 0 := by simp
  have hparts : (∫ x in (-3:ℝ)..3, (kernelCutIncrement α h x)^2) =
      (∫ x in (-h:ℝ)..0, (kernelCutIncrement α h x)^2) +
      (∫ x in (0:ℝ)..(1-h), (kernelCutIncrement α h x)^2) +
      (∫ x in (1-h:ℝ)..1, (kernelCutIncrement α h x)^2) := by
    have hsbase := intervalIntegral.integral_add_adjacent_intervals (hIall (-3) 0) hC
    have hsone := intervalIntegral.integral_add_adjacent_intervals (hIall (-3) (1-h)) hD
    have hstwo := intervalIntegral.integral_add_adjacent_intervals (hIall (-3) 1) hE
    linarith [hs1, hsbase, hsone, hstwo, hleftTail, hrightTail]
  have hlowEq : Set.EqOn (fun x : ℝ => (kernelCutIncrement α h x)^2)
      (fun x => (kernel α (x+h))^2) (Set.uIoo (-h) 0) := by
    intro x hx
    have hx' : x ∈ Set.Ioo (-h) 0 := by
      simpa [Set.uIoo_of_le (by linarith : (-h:ℝ) ≤ 0)] using hx
    have hxarg : 0 < x+h := by linarith [hx'.1]
    have hxarg1 : x+h ≤ 1 := by linarith [hh1, hx'.2]
    have hxnonpos : x ≤ 0 := le_of_lt hx'.2
    simp [kernelCutIncrement, kernelCut_eq_kernel_of_pos_le_one hxarg hxarg1,
      kernelCut_eq_zero_of_nonpos hxnonpos]
  have hlow : (∫ x in (-h:ℝ)..0, (kernelCutIncrement α h x)^2) =
      ((Real.Gamma α)⁻¹)^2 * (h^(2*q+1)/(2*q+1)) := by
    rw [intervalIntegral.integral_congr_uIoo hlowEq]
    have hcomp : (∫ x in (-h:ℝ)..0, (kernel α (x+h))^2) =
        ∫ x in (0:ℝ)..h, (kernel α x)^2 := by
      simpa [sub_add_cancel] using (intervalIntegral.integral_comp_add_right
        (a := -h) (b := (0:ℝ)) (f := fun y => (kernel α y)^2) h)
    have hform := rpow_boundary_integral_eq (p := 2*q) (by linarith) hh
    have hkernel : ∀ x ∈ Set.Ioo (0:ℝ) h,
        (kernel α x)^2 = ((Real.Gamma α)⁻¹)^2 * x^(2*q) := by
      intro x hx
      simpa [q] using kernel_sq_eq_gamma_rpow (α := α) hx.1
    rw [hcomp]
    calc
      (∫ x in (0:ℝ)..h, (kernel α x)^2) =
          ∫ x in (0:ℝ)..h, ((Real.Gamma α)⁻¹)^2 * x^(2*q) :=
        intervalIntegral.integral_congr_uIoo (by
          intro x hx
          have hx' : x ∈ Set.Ioo (0:ℝ) h := by
            simpa [Set.uIoo_of_le hh] using hx
          exact hkernel x hx')
      _ = ((Real.Gamma α)⁻¹)^2 * (∫ x in (0:ℝ)..h, x^(2*q)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = ((Real.Gamma α)⁻¹)^2 * (h^(2*q+1)/(2*q+1)) := by rw [hform]
  have hoverlapEq : Set.EqOn (fun x : ℝ => (kernelCutIncrement α h x)^2)
      (fun x => ((Real.Gamma α)⁻¹)^2 * ((x+h)^q-x^q)^2)
      (Set.uIoo 0 (1-h)) := by
    intro x hx
    have hx' : x ∈ Set.Ioo (0:ℝ) (1-h) := by
      simpa [Set.uIoo_of_le (by linarith : (0:ℝ)≤1-h)] using hx
    have hx0 : 0 < x := hx'.1
    have hx1 : x ≤ 1 := by linarith [hx'.2]
    have hxarg : 0 < x+h := by linarith [hh]
    have hxarg1 : x+h ≤ 1 := by linarith [hx'.2]
    have hk0 := kernelCut_eq_kernel_of_pos_le_one (α := α) hx0 hx1
    have hk1 := kernelCut_eq_kernel_of_pos_le_one (α := α) hxarg hxarg1
    simp [kernelCutIncrement, hk0, hk1, kernel, q]
    ring
  have hoverlap : (∫ x in (0:ℝ)..(1-h),
      (kernelCutIncrement α h x)^2) ≤
      ((Real.Gamma α)⁻¹)^2 * (h^(2*q+1)/(2*q+1)) := by
    have hrev : (∫ x in (0:ℝ)..(1-h), ((x+h)^q-x^q)^2) =
        ∫ x in (0:ℝ)..(1-h), (x^q-(x+h)^q)^2 := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      ring
    calc
      (∫ x in (0:ℝ)..(1-h), (kernelCutIncrement α h x)^2) =
          ((Real.Gamma α)⁻¹)^2 *
            (∫ x in (0:ℝ)..(1-h), ((x+h)^q-x^q)^2) := by
        rw [intervalIntegral.integral_congr_uIoo hoverlapEq,
          intervalIntegral.integral_const_mul]
      _ = ((Real.Gamma α)⁻¹)^2 *
          (∫ x in (0:ℝ)..(1-h), (x^q-(x+h)^q)^2) := by rw [hrev]
      _ ≤ ((Real.Gamma α)⁻¹)^2 * (h^(2*q+1)/(2*q+1)) :=
        mul_le_mul_of_nonneg_left
          (rpow_overlap_squared_integral_le_explicit_boundary hq hq0 hh hh1)
          (sq_nonneg _)
  have hrightEq : Set.EqOn (fun x : ℝ => (kernelCutIncrement α h x)^2)
      (fun x => (kernel α x)^2) (Set.uIoo (1-h) 1) := by
    intro x hx
    have hx' : x ∈ Set.Ioo (1-h) 1 := by
      simpa [Set.uIoo_of_le (by linarith : (1-h:ℝ)≤1)] using hx
    have hx0 : 0 < x := by linarith [hx'.1]
    have hx1 : x ≤ 1 := le_of_lt hx'.2
    have hxarg : 1 < x+h := by linarith [hx'.1, hh]
    change (kernelCut α (x+h) - kernelCut α x)^2 = (kernel α x)^2
    rw [kernelCut_eq_zero_of_one_lt hxarg,
      kernelCut_eq_kernel_of_pos_le_one hx0 hx1]
    ring
  have hright : (∫ x in (1-h:ℝ)..1, (kernelCutIncrement α h x)^2) ≤
      ((Real.Gamma α)⁻¹)^2 *
        (2/(2*q+1) + (1/2:ℝ)^(2*q)) * h^(2*q+1) := by
    have hkernel : ∀ x ∈ Set.Ioo (1-h:ℝ) 1,
        (kernel α x)^2 = ((Real.Gamma α)⁻¹)^2 * x^(2*q) := by
      intro x hx
      simpa [q] using kernel_sq_eq_gamma_rpow (α := α) (by linarith [hx.1, hh1])
    calc
      (∫ x in (1-h:ℝ)..1, (kernelCutIncrement α h x)^2) =
          ∫ x in (1-h:ℝ)..1, (kernel α x)^2 :=
        intervalIntegral.integral_congr_uIoo hrightEq
      _ = ((Real.Gamma α)⁻¹)^2 * (∫ x in (1-h:ℝ)..1, x^(2*q)) := by
        rw [intervalIntegral.integral_congr_uIoo]
        · rw [intervalIntegral.integral_const_mul]
        · intro x hx
          have hx' : x ∈ Set.Ioo (1-h:ℝ) 1 := by
            simpa [Set.uIoo_of_le (by linarith : (1-h:ℝ)≤1)] using hx
          exact hkernel x hx'
      _ ≤ ((Real.Gamma α)⁻¹)^2 *
          ((2/(2*q+1) + (1/2:ℝ)^(2*q)) * h^(2*q+1)) :=
        mul_le_mul_of_nonneg_left
          (rpow_negative_right_edge_integral_le_holder (p := 2*q)
            (by linarith) (by linarith) hh hh1) (sq_nonneg _)
      _ = ((Real.Gamma α)⁻¹)^2 *
          (2/(2*q+1) + (1/2:ℝ)^(2*q)) * h^(2*q+1) := by ring
  have hright' : (∫ x in (1-h:ℝ)..1, (kernelCutIncrement α h x)^2) ≤
      ((Real.Gamma α)⁻¹)^2 *
        ((2/(2*q+1) + (1/2:ℝ)^(2*q)) * h^(2*q+1)) := by
    simpa [mul_assoc] using hright
  rw [kernelCut_increment_sq_integral_eq_interval hh hh1]
  rw [hparts]
  rw [hlow]
  have hqden : 0 < 2*q+1 := by linarith
  calc
    ((Real.Gamma α)⁻¹)^2 * (h^(2*q+1)/(2*q+1)) +
        (∫ x in (0:ℝ)..(1-h), (kernelCutIncrement α h x)^2) +
        (∫ x in (1-h:ℝ)..1, (kernelCutIncrement α h x)^2) ≤
      ((Real.Gamma α)⁻¹)^2 *
        (h^(2*q+1)/(2*q+1) + h^(2*q+1)/(2*q+1) +
          (2/(2*q+1) + (1/2:ℝ)^(2*q))*h^(2*q+1)) := by
      calc
        (((Real.Gamma α)⁻¹)^2 * (h^(2*q+1)/(2*q+1)) +
            (∫ x in (0:ℝ)..(1-h), (kernelCutIncrement α h x)^2)) +
            (∫ x in (1-h:ℝ)..1, (kernelCutIncrement α h x)^2) =
            ((Real.Gamma α)⁻¹)^2 * (h^(2*q+1)/(2*q+1)) +
              ((∫ x in (0:ℝ)..(1-h), (kernelCutIncrement α h x)^2) +
                (∫ x in (1-h:ℝ)..1, (kernelCutIncrement α h x)^2)) := by ring
        _ ≤ ((Real.Gamma α)⁻¹)^2 * (h^(2*q+1)/(2*q+1)) +
            (((Real.Gamma α)⁻¹)^2 * (h^(2*q+1)/(2*q+1)) +
              ((Real.Gamma α)⁻¹)^2 *
                ((2/(2*q+1) + (1/2:ℝ)^(2*q))*h^(2*q+1))) :=
          add_le_add le_rfl (add_le_add hoverlap hright')
        _ = ((Real.Gamma α)⁻¹)^2 *
            (h^(2*q+1)/(2*q+1) + h^(2*q+1)/(2*q+1) +
              (2/(2*q+1) + (1/2:ℝ)^(2*q))*h^(2*q+1)) := by ring_nf
    _ = ((Real.Gamma α)⁻¹)^2 *
        (4/(2*q+1) + (1/2:ℝ)^(2*q)) * h^(2*q+1) := by
          calc
            _ = ((Real.Gamma α)⁻¹)^2 *
                (h^(2*q+1)/(2*q+1) + h^(2*q+1)/(2*q+1) +
                  (2/(2*q+1) + (1/2:ℝ)^(2*q))*h^(2*q+1)) := by ring
            _ = ((Real.Gamma α)⁻¹)^2 *
                ((4/(2*q+1) + (1/2:ℝ)^(2*q))*h^(2*q+1)) := by
                  have hcoeff : h^(2*q+1)/(2*q+1) + h^(2*q+1)/(2*q+1) +
                      (2/(2*q+1) + (1/2:ℝ)^(2*q))*h^(2*q+1) =
                      (4/(2*q+1) + (1/2:ℝ)^(2*q))*h^(2*q+1) := by
                    rw [div_eq_mul_inv]
                    ring
                  exact congrArg (fun z : ℝ => ((Real.Gamma α)⁻¹)^2 * z) hcoeff
            _ = _ := by ring
    _ = ((Real.Gamma α)⁻¹)^2 *
        (4/(2*(α-1)+1) + (1/2:ℝ)^(2*(α-1))) * h^(2*α-1) := by
          dsimp [q]
          rw [show 2*(α-1)+1 = 2*α-1 by ring]

private theorem fullL2_norm_sq (f : FullL2) :
    ‖f‖^2 = ∫ x, (f x)^2 ∂(volume : Measure ℝ) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  simp [pow_two]

theorem translatedFullKernelFamily_increment_sq_norm_le
    {α s t : ℝ} (hα : 1/2 < α) (hα1 : α ≤ 1)
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    ‖translatedFullKernelFamily α hα ⟨t, ⟨by linarith, ht1⟩⟩ -
      translatedFullKernelFamily α hα ⟨s, ⟨hs0, by linarith⟩⟩‖^2 ≤
      ((Real.Gamma α)⁻¹)^2 *
        (4 / (2*(α-1)+1) + (1/2:ℝ)^(2*(α-1))) * (t-s)^(2*α-1) := by
  let h : ℝ := t-s
  have hh : 0 ≤ h := by dsimp [h]; linarith
  have hh1 : h ≤ 1 := by dsimp [h]; linarith
  have hsum : s+h=t := by dsimp [h]; ring
  let hmR := reflectionTranslation_measurePreserving s
  have hmA : MeasurePreserving (fun x : ℝ => x+h) volume volume := by
    simpa [add_comm] using measurePreserving_add_left volume h
  have hcomp : MeasurePreserving (fun x : ℝ => (s-x)+h) volume volume :=
    hmA.comp hmR
  have hfun : (fun x : ℝ => t-x) = (fun x => (s-x)+h) := by
    funext x
    dsimp [h]
    ring
  let K := fullKernelVector α hα
  have hFt : translatedFullKernelFamily α hα ⟨t, ⟨by linarith, ht1⟩⟩ =
      Lp.compMeasurePreserving (fun x : ℝ => (s-x)+h) hcomp K := by
    apply Lp.ext
    have hleft := Lp.coeFn_compMeasurePreserving K
      (reflectionTranslation_measurePreserving t)
    have hright := Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA K) hmR
    have hadd := (Lp.coeFn_compMeasurePreserving K hmA)
    have hadd' := hmR.quasiMeasurePreserving.ae_eq_comp hadd
    filter_upwards [hleft, hright, hadd'] with x hleft hright hadd
    calc
      translatedFullKernelFamily α hα ⟨t, ⟨by linarith, ht1⟩⟩ x = K (t-x) := hleft
      _ = K ((s-x)+h) := congrArg K (congrFun hfun x)
      _ = Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA K (s-x) := hadd.symm
      _ = Lp.compMeasurePreserving (fun x : ℝ => (s-x)+h) hcomp K x := hright.symm
  have hFt' : translatedFullKernelFamily α hα ⟨t, ⟨by linarith, ht1⟩⟩ =
      Lp.compMeasurePreserving (reflectionTranslation s) hmR
        (Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA K) := by
    rw [hFt]
    simpa [Function.comp_def, reflectionTranslation, hcomp] using
      (Lp.compMeasurePreserving_comp_apply K hmA hmR)
  have hFs : translatedFullKernelFamily α hα ⟨s, ⟨hs0, by linarith⟩⟩ =
      Lp.compMeasurePreserving (reflectionTranslation s) hmR K := rfl
  have hk : MemLp (kernelCut α) 2 (volume : Measure ℝ) := kernelCut_memLp hα
  have hkShift : MemLp (fun x : ℝ => kernelCut α (x+h)) 2 volume :=
    hk.comp_measurePreserving hmA
  have hDelta : MemLp (kernelCutIncrement α h) 2 volume := hkShift.sub hk
  have hDcomp : Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA K - K =
      hDelta.toLp (kernelCutIncrement α h) := by
    change (Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA (hk.toLp (kernelCut α))) -
      hk.toLp (kernelCut α) = _
    rw [Lp.toLp_compMeasurePreserving]
    exact (MemLp.toLp_sub hkShift hk).symm
  calc
    ‖translatedFullKernelFamily α hα ⟨t, ⟨by linarith, ht1⟩⟩ -
        translatedFullKernelFamily α hα ⟨s, ⟨hs0, by linarith⟩⟩‖^2 =
      ‖Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA K - K‖^2 := by
        rw [hFt', hFs]
        have hmap := (Lp.compMeasurePreserving (reflectionTranslation s) hmR).map_sub
          (Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA K) K
        rw [← hmap, Lp.norm_compMeasurePreserving]
    _ = ‖hDelta.toLp (kernelCutIncrement α h)‖^2 := by rw [hDcomp]
    _ = ∫ x, (kernelCutIncrement α h x)^2 ∂(volume : Measure ℝ) := by
      rw [fullL2_norm_sq]
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hDelta] with x hx
      rw [hx]
    _ ≤ ((Real.Gamma α)⁻¹)^2 *
        (4 / (2*(α-1)+1) + (1/2:ℝ)^(2*(α-1))) * h^(2*α-1) :=
      kernelCut_increment_sq_integral_le_of_order_le_one hα hα1 hh hh1
    _ = ((Real.Gamma α)⁻¹)^2 *
        (4 / (2*(α-1)+1) + (1/2:ℝ)^(2*(α-1))) * (t-s)^(2*α-1) := by rfl

theorem translatedUnitKernelFamily_increment_sq_norm_le
    {α s t : ℝ} (hα : 1/2 < α) (hα1 : α ≤ 1)
    (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    ‖translatedUnitKernelFamily α hα ⟨t, ⟨by linarith, ht1⟩⟩ -
      translatedUnitKernelFamily α hα ⟨s, ⟨hs0, by linarith⟩⟩‖^2 ≤
      ((Real.Gamma α)⁻¹)^2 *
        (4 / (2*(α-1)+1) + (1/2:ℝ)^(2*(α-1))) * (t-s)^(2*α-1) := by
  have hfull := translatedFullKernelFamily_increment_sq_norm_le hα hα1 hs0 hst ht1
  let Ft := translatedFullKernelFamily α hα ⟨t, ⟨by linarith, ht1⟩⟩
  let Fs := translatedFullKernelFamily α hα ⟨s, ⟨hs0, by linarith⟩⟩
  have hnorm : ‖restrictUnitCLM (Ft-Fs)‖ ≤ ‖Ft-Fs‖ := by
    calc
      ‖restrictUnitCLM (Ft-Fs)‖ ≤ ‖restrictUnitCLM‖ * ‖Ft-Fs‖ :=
        restrictUnitCLM.le_opNorm _
      _ ≤ 1 * ‖Ft-Fs‖ := mul_le_mul_of_nonneg_right restrictUnitCLM_norm_le
        (norm_nonneg _)
      _ = ‖Ft-Fs‖ := by ring
  have hsub : restrictUnitCLM Ft - restrictUnitCLM Fs = restrictUnitCLM (Ft-Fs) := by
    exact (map_sub restrictUnitCLM Ft Fs).symm
  rw [show translatedUnitKernelFamily α hα ⟨t, ⟨by linarith, ht1⟩⟩ = restrictUnitCLM Ft by rfl,
    show translatedUnitKernelFamily α hα ⟨s, ⟨hs0, by linarith⟩⟩ = restrictUnitCLM Fs by rfl,
    hsub]
  nlinarith [hnorm, hfull, norm_nonneg (restrictUnitCLM (Ft-Fs)), norm_nonneg (Ft-Fs)]

theorem kernelCut_increment_sq_integral_le_of_order_ge_one
    {α h : ℝ} (hα : 1 ≤ α) (hh : 0 ≤ h) (hh1 : h ≤ 1) :
    (∫ x, (kernelCutIncrement α h x)^2) ≤
      3 * ((Real.Gamma α)⁻¹)^2 * h := by
  let q : ℝ := α-1
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hI := kernelCut_increment_sq_integrable (α := α) (h := h)
    (by linarith : 1/2 < α)
  have hIall : ∀ a b : ℝ, IntervalIntegrable
      (fun x : ℝ => (kernelCutIncrement α h x)^2) volume a b := fun a b => hI.intervalIntegrable
  have hA := hIall (-3) (-h)
  have hB := hIall (-h) 0
  have hC := hIall 0 (1-h)
  have hD := hIall (1-h) 1
  have hE := hIall 1 3
  have hs1 := intervalIntegral.integral_add_adjacent_intervals hA hB
  have hs2 := intervalIntegral.integral_add_adjacent_intervals hC hD
  have hleftTail : (∫ x in (-3:ℝ)..(-h), (kernelCutIncrement α h x)^2) = 0 := by
    calc
      (∫ x in (-3:ℝ)..(-h), (kernelCutIncrement α h x)^2) =
          ∫ x in (-3:ℝ)..(-h), (0:ℝ) := intervalIntegral.integral_congr_uIoo (by
            intro x hx
            have hx' : x ∈ Set.Ioo (-3:ℝ) (-h) := by
              simpa [Set.uIoo_of_le (by linarith : (-3:ℝ)≤-h)] using hx
            have hx0 : x≤0 := by linarith [hx'.2]
            have hx1 : x+h≤0 := by linarith [hx'.2]
            simp [kernelCutIncrement, kernelCut_eq_zero_of_nonpos hx0,
              kernelCut_eq_zero_of_nonpos hx1])
      _ = 0 := by simp
  have hrightTail : (∫ x in (1:ℝ)..3, (kernelCutIncrement α h x)^2) = 0 := by
    calc
      (∫ x in (1:ℝ)..3, (kernelCutIncrement α h x)^2) =
          ∫ x in (1:ℝ)..3, (0:ℝ) := intervalIntegral.integral_congr_uIoo (by
            intro x hx
            have hx' : x ∈ Set.Ioo (1:ℝ) 3 := by
              simpa [Set.uIoo_of_le (by norm_num : (1:ℝ)≤3)] using hx
            have hx0 : 1<x := hx'.1
            have hx1 : 1<x+h := by linarith [hx'.1, hh]
            simp [kernelCutIncrement, kernelCut_eq_zero_of_one_lt hx0,
              kernelCut_eq_zero_of_one_lt hx1])
      _ = 0 := by simp
  have hparts : (∫ x in (-3:ℝ)..3, (kernelCutIncrement α h x)^2) =
      (∫ x in (-h:ℝ)..0, (kernelCutIncrement α h x)^2) +
      (∫ x in (0:ℝ)..(1-h), (kernelCutIncrement α h x)^2) +
      (∫ x in (1-h:ℝ)..1, (kernelCutIncrement α h x)^2) := by
    have hsbase := intervalIntegral.integral_add_adjacent_intervals (hIall (-3) 0) hC
    have hsone := intervalIntegral.integral_add_adjacent_intervals (hIall (-3) (1-h)) hD
    have hstwo := intervalIntegral.integral_add_adjacent_intervals (hIall (-3) 1) hE
    linarith [hs1, hsbase, hsone, hstwo, hleftTail, hrightTail]
  have hlowEq : Set.EqOn (fun x : ℝ => (kernelCutIncrement α h x)^2)
      (fun x => (kernel α (x+h))^2) (Set.uIoo (-h) 0) := by
    intro x hx
    have hx' : x∈Set.Ioo (-h) 0 := by
      simpa [Set.uIoo_of_le (by linarith : (-h:ℝ)≤0)] using hx
    have hxarg : 0<x+h := by linarith [hx'.1]
    have hxarg1 : x+h≤1 := by linarith [hx'.2, hh1]
    simp [kernelCutIncrement, kernelCut_eq_kernel_of_pos_le_one hxarg hxarg1,
      kernelCut_eq_zero_of_nonpos (le_of_lt hx'.2)]
  have hlow : (∫ x in (-h:ℝ)..0, (kernelCutIncrement α h x)^2) ≤
      ((Real.Gamma α)⁻¹)^2 * h := by
    rw [intervalIntegral.integral_congr_uIoo hlowEq]
    have hcomp : (∫ x in (-h:ℝ)..0, (kernel α (x+h))^2) =
        ∫ x in (0:ℝ)..h, (kernel α x)^2 := by
      simpa [sub_add_cancel] using (intervalIntegral.integral_comp_add_right
        (a := -h) (b := (0:ℝ)) (f := fun y => (kernel α y)^2) h)
    rw [hcomp]
    calc
      (∫ x in (0:ℝ)..h, (kernel α x)^2) =
          ((Real.Gamma α)⁻¹)^2 * (∫ x in (0:ℝ)..h, x^(2*q)) := by
        have hEq : Set.EqOn (fun x : ℝ => (kernel α x)^2)
            (fun x => ((Real.Gamma α)⁻¹)^2*x^(2*q)) (Set.uIoo 0 h) := by
          intro x hx
          have hx' : x∈Set.Ioo (0:ℝ) h := by
            simpa [Set.uIoo_of_le hh] using hx
          simpa [q] using kernel_sq_eq_gamma_rpow (α:=α) hx'.1
        rw [intervalIntegral.integral_congr_uIoo hEq,
          intervalIntegral.integral_const_mul]
      _ ≤ ((Real.Gamma α)⁻¹)^2*h := by
        have htop := rpow_left_edge_integral_le (p:=2*q) (by positivity) hh hh1
        nlinarith [mul_le_mul_of_nonneg_left htop (sq_nonneg ((Real.Gamma α)⁻¹))]
  have hoverlapEq : Set.EqOn (fun x : ℝ => (kernelCutIncrement α h x)^2)
      (fun x => ((Real.Gamma α)⁻¹)^2*((x+h)^q-x^q)^2) (Set.uIoo 0 (1-h)) := by
    intro x hx
    have hx' : x∈Set.Ioo (0:ℝ) (1-h) := by
      simpa [Set.uIoo_of_le (by linarith : (0:ℝ)≤1-h)] using hx
    have hx0 : 0<x := hx'.1
    have hx1 : x≤1 := by linarith [hx'.2]
    have hxarg : 0<x+h := by linarith [hh]
    have hxarg1 : x+h≤1 := by linarith [hx'.2]
    have hk0 := kernelCut_eq_kernel_of_pos_le_one (α:=α) hx0 hx1
    have hk1 := kernelCut_eq_kernel_of_pos_le_one (α:=α) hxarg hxarg1
    simp [kernelCutIncrement, hk0, hk1, kernel, q]
    ring
  have hoverlap : (∫ x in (0:ℝ)..(1-h), (kernelCutIncrement α h x)^2) ≤
      ((Real.Gamma α)⁻¹)^2*h := by
    have h0 := rpow_overlap_squared_integral_le_h_of_nonneg_order hq0 hh hh1
    calc
      (∫ x in (0:ℝ)..(1-h), (kernelCutIncrement α h x)^2) =
          ((Real.Gamma α)⁻¹)^2 * (∫ x in (0:ℝ)..(1-h), ((x+h)^q-x^q)^2) := by
        rw [intervalIntegral.integral_congr_uIoo hoverlapEq,
          intervalIntegral.integral_const_mul]
      _ ≤ ((Real.Gamma α)⁻¹)^2*h := by
        nlinarith [mul_le_mul_of_nonneg_left h0 (sq_nonneg ((Real.Gamma α)⁻¹))]
  have hrightEq : Set.EqOn (fun x : ℝ => (kernelCutIncrement α h x)^2)
      (fun x => (kernel α x)^2) (Set.uIoo (1-h) 1) := by
    intro x hx
    have hx' : x∈Set.Ioo (1-h) 1 := by
      simpa [Set.uIoo_of_le (by linarith : (1-h:ℝ)≤1)] using hx
    have hx0 : 0<x := by linarith [hx'.1]
    have hxarg : 1<x+h := by linarith [hx'.1, hh]
    change (kernelCut α (x+h)-kernelCut α x)^2 = (kernel α x)^2
    rw [kernelCut_eq_zero_of_one_lt hxarg,
      kernelCut_eq_kernel_of_pos_le_one (α:=α) hx0 hx'.2.le]
    ring
  have hright : (∫ x in (1-h:ℝ)..1, (kernelCutIncrement α h x)^2) ≤
      ((Real.Gamma α)⁻¹)^2*h := by
    rw [intervalIntegral.integral_congr_uIoo hrightEq]
    have hEq : Set.EqOn (fun x : ℝ => (kernel α x)^2)
        (fun x => ((Real.Gamma α)⁻¹)^2*x^(2*q)) (Set.uIoo (1-h) 1) := by
      intro x hx
      have hx' : x∈Set.Ioo (1-h) 1 := by
        simpa [Set.uIoo_of_le (by linarith : (1-h:ℝ)≤1)] using hx
      simpa [q] using kernel_sq_eq_gamma_rpow (α:=α) (by linarith [hx'.1, hh1])
    rw [intervalIntegral.integral_congr_uIoo hEq,
      intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left
      (rpow_right_edge_integral_le (p:=2*q) (by positivity) hh hh1)
      (sq_nonneg ((Real.Gamma α)⁻¹))
  rw [kernelCut_increment_sq_integral_eq_interval hh hh1,
    hparts]
  have hsum := add_le_add (add_le_add hlow hoverlap) hright
  nlinarith

theorem translatedFullKernelFamily_increment_sq_norm_le_of_ge_one
    {α s t : ℝ} (hα : 1 ≤ α) (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    ‖translatedFullKernelFamily α (by linarith : 1/2 < α)
        ⟨t, ⟨by linarith, ht1⟩⟩ -
      translatedFullKernelFamily α (by linarith : 1/2 < α)
        ⟨s, ⟨hs0, by linarith⟩⟩‖^2 ≤ 3*((Real.Gamma α)⁻¹)^2*(t-s) := by
  let h := t-s
  have hh : 0≤h := by dsimp [h]; linarith
  have hh1 : h≤1 := by dsimp [h]; linarith
  have hsum : s+h=t := by dsimp [h]; ring
  let hα' : 1/2<α := by linarith
  let hmR := reflectionTranslation_measurePreserving s
  have hmA : MeasurePreserving (fun x : ℝ => x+h) volume volume := by
    simpa [add_comm] using measurePreserving_add_left volume h
  have hcomp : MeasurePreserving (fun x : ℝ => (s-x)+h) volume volume := hmA.comp hmR
  have hfun : (fun x : ℝ => t-x) = (fun x => (s-x)+h) := by
    funext x
    dsimp [h]
    ring
  let K := fullKernelVector α hα'
  have hFt : translatedFullKernelFamily α hα' ⟨t, ⟨by linarith, ht1⟩⟩ =
      Lp.compMeasurePreserving (fun x : ℝ => (s-x)+h) hcomp K := by
    apply Lp.ext
    have hleft := Lp.coeFn_compMeasurePreserving K
      (reflectionTranslation_measurePreserving t)
    have hright := Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA K) hmR
    have hadd := hmR.quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving K hmA)
    filter_upwards [hleft, hright, hadd] with x hleft hright hadd
    calc
      translatedFullKernelFamily α hα' ⟨t, ⟨by linarith, ht1⟩⟩ x = K (t-x) := hleft
      _ = K ((s-x)+h) := congrArg K (congrFun hfun x)
      _ = Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA K (s-x) := hadd.symm
      _ = Lp.compMeasurePreserving (fun x : ℝ => (s-x)+h) hcomp K x := hright.symm
  have hFt' : translatedFullKernelFamily α hα' ⟨t, ⟨by linarith, ht1⟩⟩ =
      Lp.compMeasurePreserving (reflectionTranslation s) hmR
        (Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA K) := by
    rw [hFt]
    simpa [Function.comp_def, reflectionTranslation, hcomp] using
      (Lp.compMeasurePreserving_comp_apply K hmA hmR)
  have hFs : translatedFullKernelFamily α hα' ⟨s, ⟨hs0, by linarith⟩⟩ =
      Lp.compMeasurePreserving (reflectionTranslation s) hmR K := rfl
  have hk : MemLp (kernelCut α) 2 (volume : Measure ℝ) := kernelCut_memLp hα'
  have hkShift : MemLp (fun x : ℝ => kernelCut α (x+h)) 2 volume := hk.comp_measurePreserving hmA
  have hDelta : MemLp (kernelCutIncrement α h) 2 volume := hkShift.sub hk
  have hDcomp : Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA K-K =
      hDelta.toLp (kernelCutIncrement α h) := by
    change Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA (hk.toLp (kernelCut α))-
      hk.toLp (kernelCut α) = _
    rw [Lp.toLp_compMeasurePreserving]
    exact (MemLp.toLp_sub hkShift hk).symm
  calc
    ‖translatedFullKernelFamily α hα' ⟨t, ⟨by linarith, ht1⟩⟩-
        translatedFullKernelFamily α hα' ⟨s, ⟨hs0, by linarith⟩⟩‖^2 =
      ‖Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA K-K‖^2 := by
        rw [hFt', hFs]
        have hmap := (Lp.compMeasurePreserving (reflectionTranslation s) hmR).map_sub
          (Lp.compMeasurePreserving (fun x : ℝ => x+h) hmA K) K
        rw [← hmap, Lp.norm_compMeasurePreserving]
    _ = ‖hDelta.toLp (kernelCutIncrement α h)‖^2 := by rw [hDcomp]
    _ = ∫ x, (kernelCutIncrement α h x)^2 ∂(volume : Measure ℝ) := by
      rw [fullL2_norm_sq]
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp hDelta] with x hx
      rw [hx]
    _ ≤ 3*((Real.Gamma α)⁻¹)^2*h :=
      kernelCut_increment_sq_integral_le_of_order_ge_one hα hh hh1
    _ = 3*((Real.Gamma α)⁻¹)^2*(t-s) := by rfl

theorem translatedUnitKernelFamily_increment_sq_norm_le_of_ge_one
    {α s t : ℝ} (hα : 1 ≤ α) (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    ‖translatedUnitKernelFamily α (by linarith : 1/2 < α)
        ⟨t, ⟨by linarith, ht1⟩⟩ -
      translatedUnitKernelFamily α (by linarith : 1/2 < α)
        ⟨s, ⟨hs0, by linarith⟩⟩‖^2 ≤ 3*((Real.Gamma α)⁻¹)^2*(t-s) := by
  have hfull := translatedFullKernelFamily_increment_sq_norm_le_of_ge_one hα hs0 hst ht1
  let Ft := translatedFullKernelFamily α (by linarith : 1/2 < α)
    ⟨t, ⟨by linarith, ht1⟩⟩
  let Fs := translatedFullKernelFamily α (by linarith : 1/2 < α)
    ⟨s, ⟨hs0, by linarith⟩⟩
  have hnorm : ‖restrictUnitCLM (Ft-Fs)‖≤‖Ft-Fs‖ := by
    calc
      ‖restrictUnitCLM (Ft-Fs)‖≤‖restrictUnitCLM‖*‖Ft-Fs‖ := restrictUnitCLM.le_opNorm _
      _≤1*‖Ft-Fs‖ := mul_le_mul_of_nonneg_right restrictUnitCLM_norm_le (norm_nonneg _)
      _=‖Ft-Fs‖ := by ring
  have hsub : restrictUnitCLM Ft-restrictUnitCLM Fs=restrictUnitCLM (Ft-Fs) :=
    (map_sub restrictUnitCLM Ft Fs).symm
  rw [show translatedUnitKernelFamily α (by linarith : 1/2 < α)
      ⟨t, ⟨by linarith, ht1⟩⟩=restrictUnitCLM Ft by rfl,
    show translatedUnitKernelFamily α (by linarith : 1/2 < α)
      ⟨s, ⟨hs0, by linarith⟩⟩=restrictUnitCLM Fs by rfl,hsub]
  nlinarith [hnorm,hfull,norm_nonneg (restrictUnitCLM (Ft-Fs)),norm_nonneg (Ft-Fs)]

/-- A quantitative local translation exponent for a causal RL feature kernel
in L². The squared norm has exponent `2 * holderExponent α`: the fractional
singularity exponent below order one and a boundary-based square-root norm
modulus at and above order one. The latter bound is not asserted optimal. -/
noncomputable def holderExponent (α : ℝ) : ℝ := min (α - 1/2) (1/2)

theorem holderExponent_pos {α : ℝ} (hα : 1/2 < α) : 0 < holderExponent α := by
  unfold holderExponent
  exact lt_min (by linarith) (by norm_num)

/-- A single quantitative modulus for all RL orders α>1/2. This is stated
directly for the actual restricted L² kernel vectors used in the RL operator. -/
theorem translatedUnitKernelFamily_increment_sq_norm_le_holder
    {α s t : ℝ} (hα : 1/2 < α) (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) :
    ‖translatedUnitKernelFamily α hα ⟨t, ⟨by linarith, ht1⟩⟩ -
      translatedUnitKernelFamily α hα ⟨s, ⟨hs0, by linarith⟩⟩‖^2 ≤
      max (((Real.Gamma α)⁻¹)^2 *
        (4 / (2*(α-1)+1) + (1/2:ℝ)^(2*(α-1))))
        (3*((Real.Gamma α)⁻¹)^2) * (t-s)^(2*holderExponent α) := by
  let h := t-s
  have hh : 0 ≤ h := by dsimp [h]; linarith
  have hh1 : h ≤ 1 := by dsimp [h]; linarith
  by_cases hα1 : α ≤ 1
  · have hbound := translatedUnitKernelFamily_increment_sq_norm_le
      hα hα1 hs0 hst ht1
    have hexp : 2 * holderExponent α = 2*α-1 := by
      rw [holderExponent, min_eq_left (by linarith : α-1/2 ≤ (1/2:ℝ))]
      ring
    have hpow : 0 ≤ h^(2*α-1) := Real.rpow_nonneg hh _
    rw [hexp]
    calc
      ‖translatedUnitKernelFamily α hα ⟨t, ⟨by linarith, ht1⟩⟩ -
        translatedUnitKernelFamily α hα ⟨s, ⟨hs0, by linarith⟩⟩‖^2 ≤
          ((Real.Gamma α)⁻¹)^2 *
            (4 / (2*(α-1)+1) + (1/2:ℝ)^(2*(α-1))) * (t-s)^(2*α-1) := hbound
      _ ≤ max (((Real.Gamma α)⁻¹)^2 *
            (4 / (2*(α-1)+1) + (1/2:ℝ)^(2*(α-1))))
            (3*((Real.Gamma α)⁻¹)^2) * (t-s)^(2*α-1) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpow
  · have hα1' : 1 ≤ α := le_of_not_ge hα1
    have hbound := translatedUnitKernelFamily_increment_sq_norm_le_of_ge_one
      hα1' hs0 hst ht1
    have hexp : 2 * holderExponent α = 1 := by
      rw [holderExponent, min_eq_right (by linarith : (1/2:ℝ) ≤ α-1/2)]
      norm_num
    have hpow : 0 ≤ t-s := by linarith
    rw [hexp]
    rw [Real.rpow_one]
    calc
      ‖translatedUnitKernelFamily α (by linarith : 1/2 < α)
        ⟨t, ⟨by linarith, ht1⟩⟩ -
        translatedUnitKernelFamily α (by linarith : 1/2 < α)
        ⟨s, ⟨hs0, by linarith⟩⟩‖^2 ≤ 3*((Real.Gamma α)⁻¹)^2*(t-s) := hbound
      _ ≤ max (((Real.Gamma α)⁻¹)^2 *
            (4 / (2*(α-1)+1) + (1/2:ℝ)^(2*(α-1))))
            (3*((Real.Gamma α)⁻¹)^2) * (t-s) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hpow

end BrownianSharp.AlignmentFractionalHolder
