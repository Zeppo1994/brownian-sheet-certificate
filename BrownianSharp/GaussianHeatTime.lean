import BrownianSharp.GaussianHeat
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Time differentiation of the one-dimensional Gaussian heat kernel
-/

open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology

namespace BrownianSharp

/-- The Euclidean supremum norm of a finite product standard Gaussian has a
finite first moment. -/
theorem integrable_norm_id_productStandardGaussian {κ : Type*} [Fintype κ] :
    Integrable (fun z : κ → ℝ => ‖z‖) (productStandardGaussian κ) := by
  let μ := productStandardGaussian κ
  have hcoord (i : κ) : Integrable (fun z : κ → ℝ => |z i|) μ := by
    simpa [μ, productStandardGaussian] using
      (MeasureTheory.integrable_comp_eval
        (μ := fun _ : κ => ProbabilityTheory.gaussianReal 0 1)
        (i := i) integrable_abs_id_standardGaussian)
  have hsum : Integrable (fun z : κ → ℝ => ∑ i, |z i|) μ := by
    classical
    exact integrable_finset_sum Finset.univ (fun i hi => hcoord i)
  refine hsum.mono' ?_ ?_
  · exact (continuous_norm.comp continuous_id).measurable.aestronglyMeasurable
  · filter_upwards [] with z
    have hnorm : ‖z‖ ≤ ∑ i, |z i| := by
      by_cases hne : Nonempty κ
      · apply (pi_norm_le_iff_of_nonneg (by positivity)).2
        intro i
        calc
          ‖z i‖ ≤ ∑ j ∈ Finset.univ, ‖z j‖ := by
            exact Finset.single_le_sum (fun j hj => norm_nonneg (z j))
              (Finset.mem_univ i)
          _ = ∑ j, |z j| := by simp [Real.norm_eq_abs]
      · letI : IsEmpty κ := not_nonempty_iff.mp hne
        have hz : z = 0 := by
          funext i
          exact isEmptyElim i
        simp [hz]
    simpa using hnorm

/-- Time differentiation of finite-product Gaussian heat averaging. -/
theorem hasDerivAt_gaussianHeat_time_of_contDiff_compactSupport
    {κ : Type*} [Fintype κ] (q : (κ → ℝ) → ℝ)
    (hq : ContDiff ℝ 2 q) (hqc : HasCompactSupport q)
    (x : κ → ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => gaussianHeat q s x)
      (∫ z, fderiv ℝ q (x + Real.sqrt t • z)
        ((2 * Real.sqrt t)⁻¹ • z) ∂productStandardGaussian κ) t := by
  let μ := productStandardGaussian κ
  let F : ℝ → (κ → ℝ) → ℝ := fun s z => q (x + Real.sqrt s • z)
  let F' : ℝ → (κ → ℝ) → ℝ := fun s z =>
    fderiv ℝ q (x + Real.sqrt s • z) ((2 * Real.sqrt s)⁻¹ • z)
  have hq_cont : Continuous q := hq.continuous
  have hq'cont : Continuous (fderiv ℝ q) := hq.continuous_fderiv (by norm_num)
  have hq'compact : HasCompactSupport (fderiv ℝ q) := hqc.fderiv (𝕜 := ℝ)
  obtain ⟨Cq0, hCq0⟩ := hq_cont.bounded_above_of_compact_support hqc
  obtain ⟨Cq'0, hCq'0⟩ := hq'cont.bounded_above_of_compact_support hq'compact
  let Cq := max Cq0 0
  let Cq' := max Cq'0 0
  have hCq (y : κ → ℝ) : ‖q y‖ ≤ Cq := (hCq0 y).trans (le_max_left _ _)
  have hCq' (y : κ → ℝ) : ‖fderiv ℝ q y‖ ≤ Cq' :=
    (hCq'0 y).trans (le_max_left _ _)
  have hs : Set.Ioo (t / 2) (3 * t / 2) ∈ 𝓝 t := by
    apply Ioo_mem_nhds <;> linarith
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) μ := by
    filter_upwards [] with s
    change AEStronglyMeasurable (fun z => q (x + Real.sqrt s • z)) μ
    have hm : Continuous (fun z : κ → ℝ => x + Real.sqrt s • z) := by fun_prop
    exact ((hq_cont.comp hm).measurable).aestronglyMeasurable
  have hF_int : Integrable (F t) μ := by
    apply (integrable_const Cq).mono'
    · change AEStronglyMeasurable (fun z => q (x + Real.sqrt t • z)) μ
      have hm : Continuous (fun z : κ → ℝ => x + Real.sqrt t • z) := by fun_prop
      exact ((hq_cont.comp hm).measurable).aestronglyMeasurable
    · filter_upwards [] with z
      simpa [F] using hCq (x + Real.sqrt t • z)
  have hF'_meas : AEStronglyMeasurable (F' t) μ := by
    change AEStronglyMeasurable (fun z =>
      fderiv ℝ q (x + Real.sqrt t • z) ((2 * Real.sqrt t)⁻¹ • z)) μ
    fun_prop
  have hdenom : 0 < 2 * Real.sqrt (t / 2) := by positivity
  let B : (κ → ℝ) → ℝ := fun z =>
    Cq' * (‖z‖ / (2 * Real.sqrt (t / 2)))
  have hbound : ∀ᵐ z ∂μ, ∀ s ∈ Set.Ioo (t / 2) (3 * t / 2),
      ‖F' s z‖ ≤ B z := by
    filter_upwards [] with z
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hsqrt : Real.sqrt (t / 2) ≤ Real.sqrt s := Real.sqrt_le_sqrt hs.1.le
    have hratio : ‖z‖ / (2 * Real.sqrt s) ≤
        ‖z‖ / (2 * Real.sqrt (t / 2)) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt s)
        hdenom).2
      nlinarith [norm_nonneg z, hsqrt]
    calc
      ‖F' s z‖ ≤ ‖fderiv ℝ q (x + Real.sqrt s • z)‖ *
          ‖(2 * Real.sqrt s)⁻¹ • z‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ q (x + Real.sqrt s • z)‖ *
          (‖z‖ / (2 * Real.sqrt s)) := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
            simp [div_eq_mul_inv, mul_comm]
      _ ≤ Cq' * (‖z‖ / (2 * Real.sqrt s)) :=
        mul_le_mul_of_nonneg_right (hCq' _) (by positivity)
      _ ≤ Cq' * (‖z‖ / (2 * Real.sqrt (t / 2))) := by
        exact mul_le_mul_of_nonneg_left hratio (le_max_right _ _)
      _ = B z := by rfl
  have hB_int : Integrable B μ := by
    have hnorm : Integrable (fun z : κ → ℝ => ‖z‖) μ :=
      integrable_norm_id_productStandardGaussian (κ := κ)
    have hscaled := (hnorm.const_mul Cq').const_mul
      ((2 * Real.sqrt (t / 2))⁻¹)
    simpa [B, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hscaled
  have hdiff : ∀ᵐ z ∂μ, ∀ s ∈ Set.Ioo (t / 2) (3 * t / 2),
      HasDerivAt (F · z) (F' s z) s := by
    filter_upwards [] with z
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hsqrt := Real.hasDerivAt_sqrt hs0.ne'
    have hinner : HasDerivAt (fun a : ℝ => x + Real.sqrt a • z)
        ((2 * Real.sqrt s)⁻¹ • z) s := by
      convert (hasDerivAt_const (c := x) s).add (hsqrt.smul_const z) using 1
      ext i
      simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    have houter := (hq.differentiable (by norm_num) (x + Real.sqrt s • z)).hasFDerivAt
    have hcomp := houter.comp_hasDerivAt s hinner
    convert hcomp using 1
    ext a
    rfl
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.Ioo (t / 2) (3 * t / 2)) (x₀ := t) (F := F) (F' := F') (bound := B)
    hs hF_meas hF_int hF'_meas hbound hB_int hdiff
  simpa [gaussianHeat, μ, F, F'] using h.2

set_option maxHeartbeats 2000000 in
/-- Joint continuity in time and space of heat averaging a continuous compactly
supported function. -/
theorem tendsto_gaussianHeat_pair_of_continuous_compactSupport
    {κ : Type*} [Fintype κ] (q : (κ → ℝ) → ℝ)
    (hq : Continuous q) (hqc : HasCompactSupport q)
    (t : ℝ) (x : κ → ℝ) :
    Tendsto (fun p : ℝ × (κ → ℝ) => gaussianHeat q p.1 p.2)
      (𝓝 (t, x)) (𝓝 (gaussianHeat q t x)) := by
  let μ := productStandardGaussian κ
  obtain ⟨C0, hC0⟩ := hq.bounded_above_of_compact_support hqc
  let C := max C0 0
  have hC (y : κ → ℝ) : ‖q y‖ ≤ C := (hC0 y).trans (le_max_left _ _)
  have hF_meas : ∀ᶠ p in 𝓝 (t, x),
      AEStronglyMeasurable (fun z : κ → ℝ => q (p.2 + Real.sqrt p.1 • z)) μ := by
    filter_upwards [] with p
    have hm : Continuous (fun z : κ → ℝ => p.2 + Real.sqrt p.1 • z) := by fun_prop
    exact ((hq.comp hm).measurable).aestronglyMeasurable
  have hbound : ∀ᶠ p in 𝓝 (t, x), ∀ᵐ z ∂μ,
      ‖q (p.2 + Real.sqrt p.1 • z)‖ ≤ C := by
    filter_upwards [] with p
    filter_upwards [] with z
    exact hC _
  have hCint : Integrable (fun _ : κ → ℝ => C) μ := integrable_const C
  have hlim : ∀ᵐ z ∂μ, Tendsto
      (fun p : ℝ × (κ → ℝ) => q (p.2 + Real.sqrt p.1 • z))
      (𝓝 (t, x)) (𝓝 (q (x + Real.sqrt t • z))) := by
    filter_upwards [] with z
    have hm : Continuous (fun p : ℝ × (κ → ℝ) => p.2 + Real.sqrt p.1 • z) := by
      fun_prop
    have hm0 : Tendsto (fun p : ℝ × (κ → ℝ) => p.2 + Real.sqrt p.1 • z)
        (𝓝 (t, x)) (𝓝 (x + Real.sqrt t • z)) := hm.tendsto (t, x)
    exact hq.continuousAt.tendsto.comp hm0
  have h : Tendsto (fun p : ℝ × (κ → ℝ) =>
      ∫ z, q (p.2 + Real.sqrt p.1 • z) ∂μ)
      (𝓝 (t, x)) (𝓝 (∫ z, q (x + Real.sqrt t • z) ∂μ)) :=
    tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := fun (p : ℝ × (κ → ℝ)) (z : κ → ℝ) =>
      q (p.2 + Real.sqrt p.1 • z))
    (f := fun z : κ → ℝ => q (x + Real.sqrt t • z)) (bound := fun _ => C)
    hF_meas hbound hCint hlim
  simpa only [gaussianHeat, μ] using h

/-- Joint continuity on the full time-space parameter space. -/
theorem continuous_gaussianHeat_of_continuous_compactSupport
    {κ : Type*} [Fintype κ] (q : (κ → ℝ) → ℝ)
    (hq : Continuous q) (hqc : HasCompactSupport q) :
    Continuous (fun p : ℝ × (κ → ℝ) => gaussianHeat q p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  change Tendsto (fun p : ℝ × (κ → ℝ) => gaussianHeat q p.1 p.2)
    (𝓝 p) (𝓝 (gaussianHeat q p.1 p.2))
  exact tendsto_gaussianHeat_pair_of_continuous_compactSupport q hq hqc p.1 p.2

end BrownianSharp
