import BrownianSharp.PeriodicAtomDerivatives
import BrownianSharp.SmoothResolution
import Mathlib.Tactic

/-! Deterministic synthesis estimates for smooth dyadic atoms. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp

/-- If a finite family of real summands has pairwise disjoint nonzero sets,
then its `p`th absolute moment is the sum of the individual moments. -/
theorem abs_sum_rpow_eq_sum_abs_rpow_of_pairwise_mul_eq_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) (p : ℝ) (hp : 0 < p)
    (hpair : ∀ i j, i ≠ j → f i * f j = 0) :
    |∑ i, f i| ^ p = ∑ i, |f i| ^ p := by
  classical
  by_cases hzero : ∀ i, f i = 0
  · simp [hzero, Real.zero_rpow hp.ne']
  · push_neg at hzero
    obtain ⟨i₀, hi₀⟩ := hzero
    have hvanish : ∀ j, j ≠ i₀ → f j = 0 := by
      intro j hji
      have hprod := hpair i₀ j hji.symm
      rcases mul_eq_zero.mp hprod with h | h
      · exact (hi₀ h).elim
      · exact h
    have hsum : (∑ i, f i) = f i₀ := by
      apply Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)
      intro j hj hji
      exact hvanish j hji
    have hsumPow : (∑ i, |f i| ^ p) = |f i₀| ^ p := by
      apply Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)
      intro j hj hji
      rw [hvanish j hji, abs_zero, Real.zero_rpow hp.ne']
    rw [hsum, hsumPow]

/-- The zero-order atom occupies one dyadic cell, so its normalized-circle
`L²` mass is bounded by the squared bump supremum times the cell length. -/
theorem periodizedDyadicAtomDerivative1_L2_sq_le_zero
    (s j : ℕ) (hj : j < 2 ^ s) {C : ℝ}
    (hC : ∀ x : ℝ, |smoothAtom x| ≤ C) :
    (∫ x : UnitAddCircle,
      ‖(periodizedDyadicAtomDerivative1 s j hj 0 x : ℂ)‖ ^ 2
        ∂AddCircle.haarAddCircle) ≤ C ^ 2 * ((2 : ℝ) ^ s)⁻¹ := by
  let H : UnitAddCircle → ℝ := fun x =>
    ‖(periodizedDyadicAtomDerivative1 s j hj 0 x : ℂ)‖ ^ 2
  have hpre := AddCircle.intervalIntegral_preimage (T := 1) (t := (0 : ℝ)) H
  have hunit : (∫ x : UnitAddCircle, H x ∂AddCircle.haarAddCircle) =
      ∫ x in (0 : ℝ)..1, |smoothDyadicAtomReal s j x| ^ 2 := by
    rw [AddCircle.integral_haarAddCircle]
    norm_num
    rw [← hpre]
    norm_num only [zero_add]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    change ‖(periodizedDyadicAtomDerivative1 s j hj 0 (x : UnitAddCircle) : ℂ)‖ ^ 2 = _
    rw [periodizedDyadicAtomDerivative1_unit_interval s j hj 0 x
      ⟨hx.1.le, hx.2⟩]
    simp [H, iteratedDeriv_zero]
  have hcont : Continuous smoothAtom := smoothAtom_contDiff.continuous
  have hbase := intervalIntegral_sq_le_of_support_Icc
    (g := smoothAtom) (A := -(j : ℝ))
    (B := (2 : ℝ) ^ s - j) (C := C)
    (by exact neg_nonpos.mpr (Nat.cast_nonneg j))
    (by
      have hjle : j + 1 ≤ 2 ^ s := Nat.succ_le_of_lt hj
      have hjcast : (j : ℝ) + 1 ≤ (2 : ℝ) ^ s := by exact_mod_cast hjle
      nlinarith)
    hcont
    (fun x hx => smoothAtom_support x (Or.inl hx))
    (fun x hx => smoothAtom_support x (Or.inr hx))
    hC
  let g : ℝ → ℝ := fun x => |smoothAtom x| ^ 2
  have hmeasure :
      (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j), g x) ≤ C ^ 2 := by
    simpa [g] using hbase
  have hscale :
      (∫ x in (0 : ℝ)..1, |smoothDyadicAtomReal s j x| ^ 2) =
        ((2 : ℝ) ^ s)⁻¹ *
          (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j), g x) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, g ((2 : ℝ) ^ s * x - j) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro x hx
        dsimp [g, smoothDyadicAtomReal]
      _ = ((2 : ℝ) ^ s)⁻¹ *
          (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j), g x) := by
        rw [intervalIntegral.integral_comp_mul_sub g
          (by positivity : (2 : ℝ) ^ s ≠ 0) (j : ℝ)]
        simp [smul_eq_mul]
  calc
    (∫ x : UnitAddCircle,
      ‖(periodizedDyadicAtomDerivative1 s j hj 0 x : ℂ)‖ ^ 2
        ∂AddCircle.haarAddCircle) =
      (∫ x in (0 : ℝ)..1, |smoothDyadicAtomReal s j x| ^ 2) := hunit
    _ = ((2 : ℝ) ^ s)⁻¹ *
        (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j), g x) := hscale
    _ ≤ ((2 : ℝ) ^ s)⁻¹ * C ^ 2 := by
      exact mul_le_mul_of_nonneg_left hmeasure (inv_nonneg.mpr (by positivity))
    _ = C ^ 2 * ((2 : ℝ) ^ s)⁻¹ := by ring

/-- A compactly supported integrand bounded by `C^p` on one unit interval
has at most that integral on any interval containing its support. -/
theorem intervalIntegral_rpow_le_of_support_Icc
    {g : ℝ → ℝ} {A B C p : ℝ}
    (hA : A ≤ 0) (hB : 1 ≤ B) (hC : 0 ≤ C) (hp : 0 < p)
    (hg : Continuous g)
    (hleft : ∀ x ≤ 0, g x = 0)
    (hright : ∀ x, 1 ≤ x → g x = 0)
    (hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ C) :
    (∫ x in A..B, |g x| ^ p) ≤ C ^ p := by
  let f : ℝ → ℝ := fun x => |g x| ^ p
  have hf : Continuous f := by
    dsimp [f]
    exact (Real.continuous_rpow_const hp.le).comp (hg.abs)
  have hInt : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    fun a b => hf.intervalIntegrable a b
  have hleftzero : (∫ x in A..0, f x) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with x hx
    have hx0 : x ≤ 0 := by simpa [max_eq_right hA] using hx.2
    simp [f, hleft x hx0, Real.zero_rpow hp.ne']
  have hrightzero : (∫ x in 1..B, f x) = 0 := by
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with x hx
    have hx1 : 1 ≤ x := by
      have hx1' : 1 < x := by simpa [min_eq_left hB] using hx.1
      exact le_of_lt hx1'
    simp [f, hright x hx1, Real.zero_rpow hp.ne']
  have hdecomp : (∫ x in A..B, f x) =
      (∫ x in A..0, f x) + (∫ x in 0..1, f x) +
        (∫ x in 1..B, f x) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hInt A 0) (hInt 0 B),
      ← intervalIntegral.integral_add_adjacent_intervals (hInt 0 1) (hInt 1 B)]
    ring
  have hmid : (∫ x in 0..1, f x) ≤ C ^ p := by
    calc
      (∫ x in 0..1, f x) ≤ ∫ x in 0..1, (fun _ : ℝ => C ^ p) x := by
        apply intervalIntegral.integral_mono_on (hab := by norm_num)
          (hf := hInt 0 1) (hg := by simp)
        intro x hx
        dsimp [f]
        exact Real.rpow_le_rpow (abs_nonneg _) (hbound x ⟨hx.1, hx.2⟩) hp.le
      _ = C ^ p := by simp
  rw [hdecomp, hleftzero, hrightzero, zero_add, add_zero]
  exact hmid

end BrownianSharp

