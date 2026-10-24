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

/-- A single coefficient times one dyadic atom has `p`th integral at most
the cell length times the coefficient's `p`th power. -/
theorem periodizedDyadicAtomDerivative1_rpow_integral_le
    (s j : ℕ) (hj : j < 2 ^ s) (p c : ℝ) (hp : 0 < p) :
    (∫ x : UnitAddCircle,
      |c * periodizedDyadicAtomDerivative1 s j hj 0 x| ^ p
        ∂AddCircle.haarAddCircle) ≤ |c| ^ p * ((2 : ℝ) ^ s)⁻¹ := by
  let H : UnitAddCircle → ℝ := fun x =>
    |c * periodizedDyadicAtomDerivative1 s j hj 0 x| ^ p
  have hpre := AddCircle.intervalIntegral_preimage (T := 1) (t := (0 : ℝ)) H
  have hunit : (∫ x : UnitAddCircle, H x ∂AddCircle.haarAddCircle) =
      ∫ x in (0 : ℝ)..1,
        |c * smoothDyadicAtomReal s j x| ^ p := by
    rw [AddCircle.integral_haarAddCircle]
    norm_num
    rw [← hpre]
    norm_num only [zero_add]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    change |c * periodizedDyadicAtomDerivative1 s j hj 0
      (x : UnitAddCircle)| ^ p = _
    rw [periodizedDyadicAtomDerivative1_unit_interval s j hj 0 x
      ⟨hx.1.le, hx.2⟩]
    simp [smoothDyadicAtomReal, iteratedDeriv_zero]
  let g : ℝ → ℝ := fun x => c * smoothAtom x
  have hg : Continuous g := by
    dsimp [g]
    exact continuous_const.mul smoothAtom_contDiff.continuous
  have hleft : ∀ x ≤ 0, c * smoothAtom x = 0 :=
    fun x hx => by rw [smoothAtom_support x (Or.inl hx)]; ring
  have hright : ∀ x, 1 ≤ x → c * smoothAtom x = 0 :=
    fun x hx => by rw [smoothAtom_support x (Or.inr hx)]; ring
  have hbound : ∀ x ∈ Set.Icc (0 : ℝ) 1, |c * smoothAtom x| ≤ |c| := by
    intro x hx
    rw [abs_mul]
    rw [abs_of_nonneg (smoothAtom_bounds x).1]
    calc
      |c| * smoothAtom x ≤ |c| * 1 :=
        mul_le_mul_of_nonneg_left (smoothAtom_bounds x).2 (abs_nonneg c)
      _ = |c| := by ring
  have hpow : 0 < (2 : ℝ) ^ s := by positivity
  have hjle : j + 1 ≤ 2 ^ s := Nat.succ_le_of_lt hj
  have hjcast : (j : ℝ) + 1 ≤ (2 : ℝ) ^ s := by exact_mod_cast hjle
  have hA : -(j : ℝ) ≤ 0 := by exact neg_nonpos.mpr (Nat.cast_nonneg j)
  have hB : 1 ≤ (2 : ℝ) ^ s - j := by nlinarith
  have hbase := intervalIntegral_rpow_le_of_support_Icc
    (A := -(j : ℝ)) (B := (2 : ℝ) ^ s - j) hA hB
    (abs_nonneg c) hp hg hleft hright hbound
  have hscale :
      (∫ x in (0 : ℝ)..1, |c * smoothDyadicAtomReal s j x| ^ p) =
        ((2 : ℝ) ^ s)⁻¹ *
          (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j), |g x| ^ p) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, |g ((2 : ℝ) ^ s * x - j)| ^ p := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
        intro x hx
        dsimp [g, smoothDyadicAtomReal]
      _ = ((2 : ℝ) ^ s)⁻¹ *
          (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j), |g x| ^ p) := by
        rw [intervalIntegral.integral_comp_mul_sub (fun y : ℝ => |g y| ^ p)
          (by positivity : (2 : ℝ) ^ s ≠ 0) (j : ℝ)]
        simp [g, smul_eq_mul]
  calc
    (∫ x : UnitAddCircle,
      |c * periodizedDyadicAtomDerivative1 s j hj 0 x| ^ p
        ∂AddCircle.haarAddCircle) =
      (∫ x in (0 : ℝ)..1,
        |c * smoothDyadicAtomReal s j x| ^ p) := by simpa [H] using hunit
    _ = ((2 : ℝ) ^ s)⁻¹ *
        (∫ x in (-(j : ℝ))..((2 : ℝ) ^ s - j), |g x| ^ p) := hscale
    _ ≤ ((2 : ℝ) ^ s)⁻¹ * |c| ^ p :=
      mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr hpow.le)
    _ = |c| ^ p * ((2 : ℝ) ^ s)⁻¹ := by ring

/-- Finite synthesis at one dyadic depth has the expected normalized `Lᵖ`
power bound: cell supports are disjoint and each cell has length `2^-s`. -/
theorem periodizedDyadicLevel_rpow_integral_le
    (s : ℕ) (c : Fin (2 ^ s) → ℝ) (p : ℝ) (hp : 0 < p) :
    (∫ x : UnitAddCircle,
      |∑ j : Fin (2 ^ s), c j *
          periodizedDyadicAtomDerivative1 s j.val j.isLt 0 x| ^ p
        ∂AddCircle.haarAddCircle) ≤
      ((2 : ℝ) ^ s)⁻¹ * ∑ j : Fin (2 ^ s), |c j| ^ p := by
  classical
  let atom : Fin (2 ^ s) → UnitAddCircle → ℝ := fun j x =>
    periodizedDyadicAtomDerivative1 s j.val j.isLt 0 x
  let term : Fin (2 ^ s) → UnitAddCircle → ℝ := fun j x => c j * atom j x
  have hpairsum (x : UnitAddCircle) :
      |∑ j : Fin (2 ^ s), term j x| ^ p =
        ∑ j : Fin (2 ^ s), |term j x| ^ p := by
    apply abs_sum_rpow_eq_sum_abs_rpow_of_pairwise_mul_eq_zero
      (fun j => term j x) p hp
    intro i j hij
    have hval : i.val ≠ j.val := by
      intro h
      exact hij (Fin.ext h)
    have hdisj := periodizedDyadicAtomDerivative1_pairwise_product_eq_zero
      s i.val j.val i.isLt j.isLt hval 0 x
    have hreal : atom i x * atom j x = 0 := by
      have hcast : ((atom i x * atom j x : ℝ) : ℂ) = 0 := by
        simpa [atom, Complex.star_def] using hdisj
      exact_mod_cast hcast
    dsimp [term]
    calc
      c i * atom i x * (c j * atom j x) =
          (c i * c j) * (atom i x * atom j x) := by ring
      _ = 0 := by rw [hreal]; ring
  have hterm_cont (j : Fin (2 ^ s)) :
      Continuous (fun x : UnitAddCircle => |term j x| ^ p) := by
    dsimp [term, atom]
    exact (Real.continuous_rpow_const hp.le).comp
      ((continuous_const.mul
        (periodizedDyadicAtomDerivative1 s j.val j.isLt 0).continuous).abs)
  have hterm_bound (j : Fin (2 ^ s)) :
      ∀ x : UnitAddCircle, |term j x| ^ p ≤ |c j| ^ p := by
    intro x
    dsimp [term, atom]
    apply Real.rpow_le_rpow (abs_nonneg _) _ hp.le
    rw [abs_mul]
    have hatom := periodizedDyadicAtomDerivative1_abs_le s j.val j.isLt 0
      smoothAtom_abs_le_one x
    calc
      |c j| * |periodizedDyadicAtomDerivative1 s j.val j.isLt 0 x| ≤
          |c j| * 1 := mul_le_mul_of_nonneg_left (by simpa using hatom)
            (abs_nonneg _)
      _ = |c j| := by simp
  have hterm_int (j : Fin (2 ^ s)) :
      Integrable (fun x : UnitAddCircle => |term j x| ^ p)
        AddCircle.haarAddCircle := by
    apply MeasureTheory.Integrable.of_bound
      (hterm_cont j).aestronglyMeasurable (|c j| ^ p)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hterm_bound j x
  have hsum_int :
      Integrable (fun x : UnitAddCircle =>
        ∑ j : Fin (2 ^ s), |term j x| ^ p) AddCircle.haarAddCircle :=
    MeasureTheory.integrable_finset_sum Finset.univ (fun j hj => hterm_int j)
  have hsum_integral := MeasureTheory.integral_finset_sum Finset.univ
    (fun j hj => hterm_int j)
  have hpoint : (fun x : UnitAddCircle =>
      |∑ j : Fin (2 ^ s), term j x| ^ p) =
      fun x => ∑ j : Fin (2 ^ s), |term j x| ^ p := by
    funext x
    exact hpairsum x
  calc
    (∫ x : UnitAddCircle,
      |∑ j : Fin (2 ^ s), c j *
          periodizedDyadicAtomDerivative1 s j.val j.isLt 0 x| ^ p
        ∂AddCircle.haarAddCircle) =
      ∑ j : Fin (2 ^ s),
        ∫ x : UnitAddCircle, |term j x| ^ p ∂AddCircle.haarAddCircle := by
          rw [show (fun x : UnitAddCircle =>
            |∑ j : Fin (2 ^ s), c j *
                periodizedDyadicAtomDerivative1 s j.val j.isLt 0 x| ^ p) =
              (fun x => ∑ j : Fin (2 ^ s), |term j x| ^ p) from by
                funext x
                simpa [term, atom] using hpairsum x]
          exact hsum_integral
    _ ≤
      ∑ j : Fin (2 ^ s), |c j| ^ p * ((2 : ℝ) ^ s)⁻¹ := by
        apply Finset.sum_le_sum
        intro j hj
        simpa [term, atom] using
          periodizedDyadicAtomDerivative1_rpow_integral_le
            s j.val j.isLt p (c j) hp
    _ = ((2 : ℝ) ^ s)⁻¹ * ∑ j : Fin (2 ^ s), |c j| ^ p := by
      rw [← Finset.sum_mul]
      ring

end BrownianSharp

