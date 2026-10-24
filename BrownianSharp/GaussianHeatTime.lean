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

/-- Scalar Gaussian heat transform, used to isolate the time derivative from
finite-product bookkeeping. -/
noncomputable def scalarGaussianHeat (q : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ z, q (x + Real.sqrt t * z) ∂ProbabilityTheory.gaussianReal 0 1

/-- Differentiate scalar Gaussian heat averaging under the integral. The
compact support assumptions make the function and its first derivative
bounded, and the only nonconstant dominating function is the integrable first
absolute Gaussian moment. -/
theorem hasDerivAt_scalarGaussianHeat_of_contDiff_compactSupport
    {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q) (hqc : HasCompactSupport q)
    (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => scalarGaussianHeat q s x)
      (∫ z, deriv q (x + Real.sqrt t * z) * (z / (2 * Real.sqrt t))
        ∂ProbabilityTheory.gaussianReal 0 1) t := by
  let μ := ProbabilityTheory.gaussianReal 0 1
  let F : ℝ → ℝ → ℝ := fun s z => q (x + Real.sqrt s * z)
  let F' : ℝ → ℝ → ℝ := fun s z => deriv q (x + Real.sqrt s * z) * (z / (2 * Real.sqrt s))
  have hq_cont : Continuous q := hq.continuous
  have hq'_cont : Continuous (deriv q) := hq.continuous_deriv (by norm_num)
  have hq'_compact : HasCompactSupport (deriv q) := hqc.deriv
  obtain ⟨Cq0, hCq0⟩ := hq_cont.bounded_above_of_compact_support hqc
  obtain ⟨Cq'0, hCq'0⟩ := hq'_cont.bounded_above_of_compact_support hq'_compact
  let Cq := max Cq0 0
  let Cq' := max Cq'0 0
  have hCq_nonneg : 0 ≤ Cq := le_max_right _ _
  have hCq'nonneg : 0 ≤ Cq' := le_max_right _ _
  have hCq (y : ℝ) : ‖q y‖ ≤ Cq := (hCq0 y).trans (le_max_left _ _)
  have hCq' (y : ℝ) : ‖deriv q y‖ ≤ Cq' := (hCq'0 y).trans (le_max_left _ _)
  have hs : Set.Ioo (t / 2) (3 * t / 2) ∈ 𝓝 t := by
    apply Ioo_mem_nhds
    · linarith
    · linarith
  have hF_meas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) μ := by
    filter_upwards [] with s
    change AEStronglyMeasurable (fun z => q (x + Real.sqrt s * z)) μ
    have hm : Continuous (fun z : ℝ => x + Real.sqrt s * z) := by fun_prop
    exact ((hq_cont.comp hm).measurable).aestronglyMeasurable
  have hF_int : Integrable (F t) μ := by
    apply (integrable_const Cq).mono'
    · change AEStronglyMeasurable (fun z => q (x + Real.sqrt t * z)) μ
      have hm : Continuous (fun z : ℝ => x + Real.sqrt t * z) := by fun_prop
      exact ((hq_cont.comp hm).measurable).aestronglyMeasurable
    · filter_upwards [] with z
      simpa [F] using hCq (x + Real.sqrt t * z)
  have hF'_meas : AEStronglyMeasurable (F' t) μ := by
    change AEStronglyMeasurable
      (fun z => deriv q (x + Real.sqrt t * z) * (z / (2 * Real.sqrt t))) μ
    fun_prop
  have hdenom : 0 < 2 * Real.sqrt (t / 2) := by
    have hpos : 0 < Real.sqrt (t / 2) := Real.sqrt_pos.2 (by linarith)
    positivity
  let B : ℝ → ℝ := fun z => (Cq' / (2 * Real.sqrt (t / 2))) * |z|
  have hbound : ∀ᵐ z ∂μ, ∀ s ∈ Set.Ioo (t / 2) (3 * t / 2), ‖F' s z‖ ≤ B z := by
    filter_upwards [] with z
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hsqrt : Real.sqrt (t / 2) ≤ Real.sqrt s := Real.sqrt_le_sqrt hs.1.le
    have hsqrt0 : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
    have hratio : |z| / (2 * Real.sqrt s) ≤
        |z| / (2 * Real.sqrt (t / 2)) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.sqrt s)
        hdenom).2
      nlinarith [abs_nonneg z, hsqrt]
    rw [Real.norm_eq_abs]
    simp only [F', abs_mul, abs_div, abs_of_nonneg (le_of_lt hsqrt0), abs_of_pos (by positivity : 0 < 2 * Real.sqrt s)]
    calc
      |deriv q (x + Real.sqrt s * z)| * (|z| / (2 * Real.sqrt s)) ≤
          Cq' * (|z| / (2 * Real.sqrt s)) :=
        mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hCq' (x + Real.sqrt s * z)) (by positivity)
      _ ≤ Cq' * (|z| / (2 * Real.sqrt (t / 2))) := mul_le_mul_of_nonneg_left hratio hCq'nonneg
      _ = B z := by
        simp only [B]
        field_simp
  have hB_int : Integrable B μ := by
    simpa [B] using integrable_abs_id_standardGaussian.const_mul (Cq' / (2 * Real.sqrt (t / 2)))
  have hdiff : ∀ᵐ z ∂μ, ∀ s ∈ Set.Ioo (t / 2) (3 * t / 2), HasDerivAt (F · z) (F' s z) s := by
    filter_upwards [] with z
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    have hsqrt := Real.hasDerivAt_sqrt hs0.ne'
    have hinner : HasDerivAt (fun a : ℝ => x + Real.sqrt a * z)
        (z / (2 * Real.sqrt s)) s := by
      convert (hasDerivAt_const (c := x) s).add (hsqrt.mul_const z) using 1 <;> ring
    have hq' := (hq.differentiable (by norm_num) (x + Real.sqrt s * z)).hasDerivAt
    have hcomp := hq'.comp s hinner
    simpa [F, F', Function.comp_def] using hcomp
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.Ioo (t / 2) (3 * t / 2)) (x₀ := t) (F := F) (F' := F') (bound := B)
    hs hF_meas hF_int hF'_meas hbound hB_int hdiff
  simpa [scalarGaussianHeat, μ, F, F'] using h.2

/-- Gaussian integration by parts converts the time derivative into one half
of the Gaussian average of the second spatial derivative. -/
theorem scalarGaussianHeat_time_deriv_eq_half_second
    {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q) (hqc : HasCompactSupport q)
    (x t : ℝ) (ht : 0 < t) :
    (∫ z, deriv q (x + Real.sqrt t * z) * (z / (2 * Real.sqrt t))
      ∂ProbabilityTheory.gaussianReal 0 1) =
    (1 / 2) * ∫ z, deriv (deriv q) (x + Real.sqrt t * z)
      ∂ProbabilityTheory.gaussianReal 0 1 := by
  let f : ℝ → ℝ := fun z => deriv q (x + Real.sqrt t * z)
  have hq' : ContDiff ℝ 1 (deriv q) := hq.deriv'
  have hq'c : HasCompactSupport (deriv q) := hqc.deriv
  have ha : Real.sqrt t ≠ 0 := (Real.sqrt_pos.2 ht).ne'
  let H : Homeomorph ℝ ℝ :=
    (Homeomorph.smulOfNeZero (Real.sqrt t) ha).trans (Homeomorph.addLeft x)
  have hfc : HasCompactSupport f := by
    change HasCompactSupport (fun z => deriv q (x + Real.sqrt t * z))
    exact hq'c.comp_homeomorph H
  have hf : ContDiff ℝ 1 f := by
    change ContDiff ℝ 1 (fun z => deriv q (x + Real.sqrt t * z))
    exact hq'.comp (by fun_prop)
  have hibp := integral_id_mul_gaussian_eq_integral_deriv_gaussian hf hfc
  have hderiv (z : ℝ) : deriv f z =
      Real.sqrt t * deriv (deriv q) (x + Real.sqrt t * z) := by
    have hinner : HasDerivAt (fun w : ℝ => x + Real.sqrt t * w) (Real.sqrt t) z := by
      convert (hasDerivAt_const (c := x) z).add
        ((hasDerivAt_id z).const_mul (Real.sqrt t)) using 1
      ext w
      simp
      ring
    have houter : HasDerivAt (deriv q) (deriv (deriv q) (x + Real.sqrt t * z))
        (x + Real.sqrt t * z) :=
      (hq'.differentiable (by norm_num) _).hasDerivAt
    have hc := houter.comp z hinner
    have := hc.deriv
    simpa [f, Function.comp_def, mul_comm] using this
  calc
    (∫ z, deriv q (x + Real.sqrt t * z) * (z / (2 * Real.sqrt t))
        ∂ProbabilityTheory.gaussianReal 0 1)
        = (1 / (2 * Real.sqrt t)) *
          ∫ z, z * f z ∂ProbabilityTheory.gaussianReal 0 1 := by
          simp only [f]
          rw [show (fun z : ℝ => deriv q (x + Real.sqrt t * z) *
              (z / (2 * Real.sqrt t))) =
              fun z => (1 / (2 * Real.sqrt t)) *
                (z * deriv q (x + Real.sqrt t * z)) by
                funext z
                field_simp]
          rw [integral_const_mul]
    _ = (1 / (2 * Real.sqrt t)) *
          ∫ z, deriv f z ∂ProbabilityTheory.gaussianReal 0 1 := by rw [hibp]
    _ = (1 / 2) * ∫ z, deriv (deriv q) (x + Real.sqrt t * z)
          ∂ProbabilityTheory.gaussianReal 0 1 := by
          have hrewrite : (fun z : ℝ => deriv f z) =
              fun z => Real.sqrt t * deriv (deriv q) (x + Real.sqrt t * z) := by
            funext z
            exact hderiv z
          rw [hrewrite, integral_const_mul]
          field_simp [ha]

/-- Spatial differentiation of scalar Gaussian heat averaging. -/
theorem hasDerivAt_scalarGaussianHeat_spatial_of_contDiff_compactSupport
    {q : ℝ → ℝ} (hq : ContDiff ℝ 1 q) (hqc : HasCompactSupport q)
    (t x : ℝ) :
    HasDerivAt (fun y => scalarGaussianHeat q t y)
      (∫ z, deriv q (x + Real.sqrt t * z)
        ∂ProbabilityTheory.gaussianReal 0 1) x := by
  let μ := ProbabilityTheory.gaussianReal 0 1
  let F : ℝ → ℝ → ℝ := fun y z => q (y + Real.sqrt t * z)
  let F' : ℝ → ℝ → ℝ := fun y z => deriv q (y + Real.sqrt t * z)
  have hq_cont : Continuous q := hq.continuous
  have hq'_cont : Continuous (deriv q) := hq.continuous_deriv (by norm_num)
  have hq'_compact : HasCompactSupport (deriv q) := hqc.deriv
  obtain ⟨Cq0, hCq0⟩ := hq_cont.bounded_above_of_compact_support hqc
  obtain ⟨Cq'0, hCq'0⟩ := hq'_cont.bounded_above_of_compact_support hq'_compact
  let Cq := max Cq0 0
  let Cq' := max Cq'0 0
  have hCq_nonneg : 0 ≤ Cq := le_max_right _ _
  have hCq'nonneg : 0 ≤ Cq' := le_max_right _ _
  have hCq (y : ℝ) : ‖q y‖ ≤ Cq := (hCq0 y).trans (le_max_left _ _)
  have hCq' (y : ℝ) : ‖deriv q y‖ ≤ Cq' := (hCq'0 y).trans (le_max_left _ _)
  have hs : Set.univ ∈ 𝓝 x := Filter.univ_mem
  have hF_meas : ∀ᶠ y in 𝓝 x, AEStronglyMeasurable (F y) μ := by
    filter_upwards [] with y
    change AEStronglyMeasurable (fun z => q (y + Real.sqrt t * z)) μ
    have hm : Continuous (fun z : ℝ => y + Real.sqrt t * z) := by fun_prop
    exact ((hq_cont.comp hm).measurable).aestronglyMeasurable
  have hF_int : Integrable (F x) μ := by
    apply (integrable_const Cq).mono'
    · change AEStronglyMeasurable (fun z => q (x + Real.sqrt t * z)) μ
      have hm : Continuous (fun z : ℝ => x + Real.sqrt t * z) := by fun_prop
      exact ((hq_cont.comp hm).measurable).aestronglyMeasurable
    · filter_upwards [] with z
      simpa [F] using hCq (x + Real.sqrt t * z)
  have hF'_meas : AEStronglyMeasurable (F' x) μ := by
    change AEStronglyMeasurable (fun z => deriv q (x + Real.sqrt t * z)) μ
    fun_prop
  let B : ℝ → ℝ := fun _ => Cq'
  have hbound : ∀ᵐ z ∂μ, ∀ y ∈ Set.univ, ‖F' y z‖ ≤ B z := by
    filter_upwards [] with z
    intro y hy
    simpa [F', B] using hCq' (y + Real.sqrt t * z)
  have hB_int : Integrable B μ := by
    simpa [B] using (integrable_const Cq' : Integrable (fun _ : ℝ => Cq') μ)
  have hdiff : ∀ᵐ z ∂μ, ∀ y ∈ Set.univ,
      HasDerivAt (F · z) (F' y z) y := by
    filter_upwards [] with z
    intro y hy
    have hinner : HasDerivAt (fun a : ℝ => a + Real.sqrt t * z) 1 y := by
      convert (hasDerivAt_id y).add (hasDerivAt_const y (Real.sqrt t * z)) using 1
      ext a
      simp
      ring
    have houter := (hq.differentiable (by norm_num) (y + Real.sqrt t * z)).hasDerivAt
    have hcomp := houter.comp y hinner
    change HasDerivAt (fun a => q (a + Real.sqrt t * z))
      (deriv q (y + Real.sqrt t * z)) y
    simpa [Function.comp_def] using hcomp
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (x₀ := x) (F := F) (F' := F') (bound := B)
    hs hF_meas hF_int hF'_meas hbound hB_int hdiff
  simpa [scalarGaussianHeat, μ, F, F'] using h.2

/-- The second spatial derivative is the Gaussian average of the second
derivative of the test function. -/
theorem hasDerivAt_deriv_scalarGaussianHeat_of_contDiff_compactSupport
    {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q) (hqc : HasCompactSupport q)
    (t x : ℝ) :
    HasDerivAt (deriv (fun y => scalarGaussianHeat q t y))
      (∫ z, deriv (deriv q) (x + Real.sqrt t * z)
        ∂ProbabilityTheory.gaussianReal 0 1) x := by
  have hfirst (y : ℝ) :=
    hasDerivAt_scalarGaussianHeat_spatial_of_contDiff_compactSupport
      (hq.of_le (by norm_num)) hqc t y
  have hsecond := hasDerivAt_scalarGaussianHeat_spatial_of_contDiff_compactSupport
    (show ContDiff ℝ 1 (deriv q) from hq.deriv') hqc.deriv t x
  have hderiv_eq (y : ℝ) : deriv (fun w => scalarGaussianHeat q t w) y =
      ∫ z, deriv q (y + Real.sqrt t * z)
        ∂ProbabilityTheory.gaussianReal 0 1 := (hfirst y).deriv
  have hfun : (fun y => deriv (fun w => scalarGaussianHeat q t w) y) =
      fun y => scalarGaussianHeat (deriv q) t y := by
    funext y
    rw [hderiv_eq]
    rfl
  change HasDerivAt (fun y => deriv (fun w => scalarGaussianHeat q t w) y)
    (∫ z, deriv (deriv q) (x + Real.sqrt t * z)
      ∂ProbabilityTheory.gaussianReal 0 1) x
  rw [hfun]
  exact hsecond

/-- Scalar Gaussian heat flow solves the one-dimensional heat equation. -/
theorem hasDerivAt_scalarGaussianHeat_time_eq_half_second_spatial
    {q : ℝ → ℝ} (hq : ContDiff ℝ 2 q) (hqc : HasCompactSupport q)
    (x t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => scalarGaussianHeat q s x)
      ((1 / 2) * deriv (deriv (fun y => scalarGaussianHeat q t y)) x) t := by
  have htime := hasDerivAt_scalarGaussianHeat_of_contDiff_compactSupport hq hqc x t ht
  have hparts := scalarGaussianHeat_time_deriv_eq_half_second hq hqc x t ht
  have hspace := hasDerivAt_deriv_scalarGaussianHeat_of_contDiff_compactSupport hq hqc t x
  have hspaceval : deriv (deriv (fun y => scalarGaussianHeat q t y)) x =
      ∫ z, deriv (deriv q) (x + Real.sqrt t * z)
        ∂ProbabilityTheory.gaussianReal 0 1 := hspace.deriv
  convert htime using 1
  rw [hparts, hspaceval]

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

/-- Heat averaging converges pointwise to the original compactly supported
continuous function as time decreases to zero. -/
theorem tendsto_gaussianHeat_zero_of_continuous_compactSupport
    {κ : Type*} [Fintype κ] (q : (κ → ℝ) → ℝ)
    (hq : Continuous q) (hqc : HasCompactSupport q) (x : κ → ℝ) :
    Tendsto (fun t : ℝ => gaussianHeat q t x) (𝓝[>] (0 : ℝ)) (𝓝 (q x)) := by
  let μ := productStandardGaussian κ
  obtain ⟨C0, hC0⟩ := hq.bounded_above_of_compact_support hqc
  let C := max C0 0
  have hC (y : κ → ℝ) : ‖q y‖ ≤ C := (hC0 y).trans (le_max_left _ _)
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto).mono_left
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hF_meas : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      AEStronglyMeasurable (fun z : κ → ℝ => q (x + Real.sqrt t • z)) μ := by
    filter_upwards [] with t
    have hm : Continuous (fun z : κ → ℝ => x + Real.sqrt t • z) := by fun_prop
    exact ((hq.comp hm).measurable).aestronglyMeasurable
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ᵐ z ∂μ,
      ‖q (x + Real.sqrt t • z)‖ ≤ C := by
    filter_upwards [] with t
    filter_upwards [] with z
    exact hC _
  have hCint : Integrable (fun _ : κ → ℝ => C) μ := integrable_const C
  have hlim : ∀ᵐ z ∂μ, Tendsto
      (fun t : ℝ => q (x + Real.sqrt t • z)) (𝓝[>] (0 : ℝ)) (𝓝 (q x)) := by
    filter_upwards [] with z
    apply hq.continuousAt.tendsto.comp
    simpa using tendsto_const_nhds.add (hsqrt.smul_const z)
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := fun t z => q (x + Real.sqrt t • z))
    (f := fun _ : κ → ℝ => q x) (bound := fun _ => C)
    hF_meas hbound hCint hlim
  simpa [gaussianHeat, μ] using h

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
