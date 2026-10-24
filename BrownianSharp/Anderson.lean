import Isoperimetric.PrekopaLeindler
import BrownianSharp.GaussianDensity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic

/-!
# Midpoint-log-concave integral comparison

This file formalizes the analytic core of Anderson's inequality directly by
Prékopa--Leindler.  It is independent of any covariance inverse, so the
comparison itself is valid in the presence of singular linear maps.  The
conversion from Gaussian probabilities of convex sets to these integrals is
kept as an explicit interface below; this file does not claim the Brownian
sharp small-ball estimate.
-/

open MeasureTheory
open scoped ENNReal

namespace BrownianSharp

/-- The unnormalized standard-Gaussian density kernel on a finite coordinate
space. The missing normalizing constant cancels in all comparisons below. -/
def gaussianQuadratic {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2

noncomputable def gaussianKernel {N : ℕ} (x : Fin N → ℝ) : ℝ :=
  Real.exp (-gaussianQuadratic x / 2)

/-- Density of a shifted linear image event against the unnormalized standard
Gaussian kernel. -/
noncomputable def shiftedGaussianDensity {N M : ℕ} (C : Set (Fin M → ℝ))
    (A : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ)) (shift : Fin M → ℝ)
    (x : Fin N → ℝ) : ENNReal := by
  classical
  exact if A x + shift ∈ C then ENNReal.ofReal (gaussianKernel x) else 0

/-- Unshifted density of the same linear image event. -/
noncomputable def gaussianImageDensity {N M : ℕ} (C : Set (Fin M → ℝ))
    (A : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ)) (x : Fin N → ℝ) : ENNReal := by
  classical
  exact if A x ∈ C then ENNReal.ofReal (gaussianKernel x) else 0

/-- Change of variables for nonnegative integrals under scalar dilation on
finite-dimensional Euclidean space. -/
private theorem lintegral_comp_real_smul
    (N : ℕ) (f : (Fin N → ℝ) → ENNReal) (hf : Measurable f)
    (c : ℝ) (hc : c ≠ 0) :
    ∫⁻ x, f (c • x) =
      ENNReal.ofReal (abs ((c ^ N : ℝ)⁻¹)) * ∫⁻ x, f x := by
  rw [← lintegral_map hf (by fun_prop : Measurable (fun x : Fin N → ℝ => c • x))]
  rw [MeasureTheory.Measure.map_addHaar_smul (volume : Measure (Fin N → ℝ)) hc]
  simp [lintegral_smul_measure]

/-- The midpoint form of Prékopa--Leindler implies that translating the
argument of a measurable nonnegative profile with the reflected midpoint
property cannot increase its integral.

The functions take values in `ENNReal`, and all required measurability and
midpoint log-concavity hypotheses are explicit.  No finiteness or strict
positivity assumptions on the integrals are needed. -/
theorem midpoint_lintegral_translate_le
    (d : ℕ) (f h : (Fin (d + 1) → ℝ) → ENNReal)
    (hf : Measurable f) (hh : Measurable h)
    (hmid : ∀ x y, (f x) ^ (1 / 2 : ℝ) * (f y) ^ (1 / 2 : ℝ) ≤
      h ((1 / 2 : ℝ) • (x - y))) :
    ∫⁻ x, f x ≤ ∫⁻ x, h x := by
  let F : (Fin (d + 1) → ℝ) → ENNReal := fun x => f ((2 : ℝ) • x)
  let G : (Fin (d + 1) → ℝ) → ENNReal := fun y => f ((-2 : ℝ) • y)
  have hF : Measurable F := hf.comp (by fun_prop)
  have hG : Measurable G := hf.comp (by fun_prop)
  have hconditions : PLConditions (d + 1) (1 / 2 : ℝ) F G h := by
    refine ⟨by norm_num, by norm_num, hF, hG, hh, ?_⟩
    intro x y
    have hs := hmid ((2 : ℝ) • x) ((-2 : ℝ) • y)
    have hx : (1 / 2 : ℝ) • ((2 : ℝ) • x - (-2 : ℝ) • y) = x + y := by module
    rw [hx] at hs
    simpa only [F, G, show 1 - (1 / 2 : ℝ) = (1 / 2 : ℝ) by norm_num] using hs
  have hPL := prekopa_leindler hconditions
  let q : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ (d + 1 : ℕ))
  have hscale : ∫⁻ x : Fin (d + 1) → ℝ, F x =
      q⁻¹ * ∫⁻ x : Fin (d + 1) → ℝ, f x := by
    change (∫⁻ x : Fin (d + 1) → ℝ, f ((2 : ℝ) • x)) = _
    calc
      _ = ENNReal.ofReal (abs ((2 ^ (d + 1) : ℝ)⁻¹)) *
          ∫⁻ x : Fin (d + 1) → ℝ, f x :=
        lintegral_comp_real_smul (d + 1) f hf 2 (by norm_num)
      _ = q⁻¹ * ∫⁻ x : Fin (d + 1) → ℝ, f x := by
        have hpow : abs ((2 ^ (d + 1) : ℝ)⁻¹) =
            ((2 : ℝ) ^ (d + 1 : ℕ))⁻¹ := by
          rw [abs_of_nonneg (by positivity : 0 ≤ ((2 : ℝ) ^ (d + 1 : ℕ))⁻¹)]
        rw [hpow, ENNReal.ofReal_inv_of_pos (by positivity : 0 < (2 ^ (d + 1) : ℝ))]
  have hscaleG : ∫⁻ x : Fin (d + 1) → ℝ, G x =
      q⁻¹ * ∫⁻ x : Fin (d + 1) → ℝ, f x := by
    change (∫⁻ x : Fin (d + 1) → ℝ, f ((-2 : ℝ) • x)) = _
    calc
      _ = ENNReal.ofReal (abs (((-2 : ℝ) ^ (d + 1 : ℕ))⁻¹)) *
          ∫⁻ x : Fin (d + 1) → ℝ, f x :=
        lintegral_comp_real_smul (d + 1) f hf (-2) (by norm_num)
      _ = q⁻¹ * ∫⁻ x : Fin (d + 1) → ℝ, f x := by
        have hAbs : abs (((-2 : ℝ) ^ (d + 1 : ℕ))⁻¹) =
            ((2 : ℝ) ^ (d + 1 : ℕ))⁻¹ := by
          rw [abs_inv, abs_pow, abs_neg, abs_of_pos (by norm_num : 0 < (2 : ℝ))]
        rw [hAbs, ENNReal.ofReal_inv_of_pos (by positivity : 0 < (2 ^ (d + 1) : ℝ))]
  have hfactor : ENNReal.ofReal
      ((1 - (1 / 2 : ℝ)) ^ ((↑(d + 1) : ℝ) * (1 - (1 / 2 : ℝ))) *
        (1 / 2 : ℝ) ^ ((↑(d + 1) : ℝ) * (1 / 2 : ℝ)))⁻¹ = q := by
    have hbase : (1 - (1 / 2 : ℝ)) ^ ((↑(d + 1) : ℝ) * (1 - (1 / 2 : ℝ))) *
        (1 / 2 : ℝ) ^ ((↑(d + 1) : ℝ) * (1 / 2 : ℝ)) =
        (2 : ℝ) ^ (-((↑(d + 1) : ℝ))) := by
      rw [show 1 - (1 / 2 : ℝ) = (1 / 2 : ℝ) by norm_num]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
      have hexp : (↑(d + 1) : ℝ) * (1 / 2) + (↑(d + 1) : ℝ) * (1 / 2) =
          (↑(d + 1) : ℝ) := by ring
      rw [hexp]
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      rw [← Real.rpow_neg_eq_inv_rpow]
    have hp : 0 < (2 : ℝ) ^ (-((↑(d + 1) : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    calc
      ENNReal.ofReal ((1 - (1 / 2 : ℝ)) ^ ((↑(d + 1) : ℝ) * (1 - (1 / 2 : ℝ))) *
          (1 / 2 : ℝ) ^ ((↑(d + 1) : ℝ) * (1 / 2 : ℝ)))⁻¹ =
          (ENNReal.ofReal ((2 : ℝ) ^ (-((↑(d + 1) : ℝ)))))⁻¹ := by
            rw [hbase, ← ENNReal.ofReal_inv_of_pos hp]
      _ = ENNReal.ofReal ((2 : ℝ) ^ (↑(d + 1) : ℝ)) := by
        rw [← ENNReal.ofReal_inv_of_pos hp]
        congr 1
        rw [Real.rpow_neg (by norm_num : 0 ≤ (2 : ℝ)), inv_inv]
      _ = q := by
        dsimp [q]
        rw [Real.rpow_natCast]
  rw [hscale, hscaleG] at hPL
  have hfactor' := hfactor
  simp only [Nat.cast_add, Nat.cast_one] at hfactor'
  rw [hfactor'] at hPL
  rw [show (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) by norm_num] at hPL
  have hhalf : ((q⁻¹ *
      (∫⁻ x : Fin (d + 1) → ℝ, f x)) ^ (1 / 2 : ℝ)) *
      ((q⁻¹ *
      (∫⁻ x : Fin (d + 1) → ℝ, f x)) ^ (1 / 2 : ℝ)) =
      q⁻¹ * (∫⁻ x : Fin (d + 1) → ℝ, f x) := by
    let a : ENNReal := q⁻¹ * (∫⁻ x : Fin (d + 1) → ℝ, f x)
    by_cases ha0 : a = 0
    · simp [a, ha0]
    by_cases hatop : a = ⊤
    · simp [a, hatop]
    · rw [← ENNReal.rpow_add _ _ ha0 hatop]
      norm_num [a]
  have hq0 : q ≠ 0 := by dsimp [q]; positivity
  have hqtop : q ≠ ⊤ := by dsimp [q]; finiteness
  rw [mul_assoc, hhalf] at hPL
  rw [ENNReal.mul_inv_cancel_left hq0 hqtop] at hPL
  exact hPL

/-- The quadratic exponent of the Gaussian kernel is midpoint-log-concave
with respect to the reflected midpoint used by the PL comparison. -/
theorem gaussianKernel_midpoint_le {N : ℕ} (x y : Fin N → ℝ) :
    gaussianKernel x ^ (1 / 2 : ℝ) * gaussianKernel y ^ (1 / 2 : ℝ) ≤
      gaussianKernel ((1 / 2 : ℝ) • (x - y)) := by
  have hquad : gaussianQuadratic ((1 / 2 : ℝ) • (x - y)) ≤
      (gaussianQuadratic x + gaussianQuadratic y) / 2 := by
    unfold gaussianQuadratic
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
    nlinarith [sq_nonneg (x i + y i)]
  have harg : -gaussianQuadratic x / 4 - gaussianQuadratic y / 4 ≤
      -gaussianQuadratic ((1 / 2 : ℝ) • (x - y)) / 2 := by
    nlinarith
  change Real.exp (-gaussianQuadratic x / 2) ^ (1 / 2 : ℝ) *
      Real.exp (-gaussianQuadratic y / 2) ^ (1 / 2 : ℝ) ≤
      Real.exp (-gaussianQuadratic ((1 / 2 : ℝ) • (x - y)) / 2)
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [harg]

/-- For a convex symmetric target set, the shifted linear-image indicator
times the standard Gaussian kernel satisfies the midpoint premise of the
singular-safe Prékopa--Leindler comparison. The linear map is not assumed
injective or nonsingular. -/
theorem shiftedGaussianDensity_midpoint_le
    {N M : ℕ} (C : Set (Fin M → ℝ))
    (A : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ)) (shift : Fin M → ℝ)
    (hconv : Convex ℝ C) (hsymm : ∀ z, z ∈ C → -z ∈ C) :
    ∀ x y, (shiftedGaussianDensity C A shift x) ^ (1 / 2 : ℝ) *
      (shiftedGaussianDensity C A shift y) ^ (1 / 2 : ℝ) ≤
        gaussianImageDensity C A ((1 / 2 : ℝ) • (x - y)) := by
  intro x y
  by_cases hx : A x + shift ∈ C
  · by_cases hy : A y + shift ∈ C
    · have hneg : -(A y + shift) ∈ C := hsymm _ hy
      have hmid : midpoint ℝ (A x + shift) (-(A y + shift)) ∈ C :=
        hconv.midpoint_mem hx hneg
      have hmember : A ((1 / 2 : ℝ) • (x - y)) ∈ C := by
        rw [midpoint_eq_smul_add] at hmid
        have hscalar : (⅟(2 : ℝ)) = (1 / 2 : ℝ) := by norm_num
        rw [hscalar] at hmid
        have heq : A ((1 / 2 : ℝ) • (x - y)) =
            (1 / 2 : ℝ) • (A x + shift + -(A y + shift)) := by
          simp only [map_smul, map_sub]
          module
        rw [heq]
        exact hmid
      have hkernel := gaussianKernel_midpoint_le x y
      have hkernelx : 0 < gaussianKernel x := Real.exp_pos _
      have hkernely : 0 < gaussianKernel y := Real.exp_pos _
      have hkernelm : 0 < gaussianKernel ((1 / 2 : ℝ) • (x - y)) := Real.exp_pos _
      simp only [shiftedGaussianDensity, gaussianImageDensity, hx, hy, hmember,
        ↓reduceIte]
      rw [ENNReal.ofReal_rpow_of_nonneg hkernelx.le (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        ENNReal.ofReal_rpow_of_nonneg hkernely.le (by norm_num : 0 ≤ (1 / 2 : ℝ)),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt hkernelx) _)]
      exact ENNReal.ofReal_le_ofReal hkernel
    · simp [shiftedGaussianDensity, gaussianImageDensity, hx, hy]
  · simp [shiftedGaussianDensity, gaussianImageDensity, hx]

private theorem measurable_shiftedGaussianDensity
    {N M : ℕ} (C : Set (Fin M → ℝ))
    (A : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ)) (shift : Fin M → ℝ)
    (hC : MeasurableSet C) :
    Measurable (shiftedGaussianDensity C A shift) := by
  classical
  have hmap : Measurable (fun x : Fin N → ℝ => A x + shift) := by
    fun_prop
  have hevent : MeasurableSet {x : Fin N → ℝ | A x + shift ∈ C} :=
    hC.preimage hmap
  have hkernel : Measurable (fun x : Fin N → ℝ =>
      ENNReal.ofReal (gaussianKernel x)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold gaussianKernel gaussianQuadratic
    fun_prop
  change Measurable (fun x : Fin N → ℝ =>
    if A x + shift ∈ C then ENNReal.ofReal (gaussianKernel x) else 0)
  exact Measurable.ite hevent hkernel measurable_const

private theorem measurable_gaussianImageDensity
    {N M : ℕ} (C : Set (Fin M → ℝ))
    (A : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ))
    (hC : MeasurableSet C) :
    Measurable (gaussianImageDensity C A) := by
  classical
  have hmap : Measurable (fun x : Fin N → ℝ => A x) := by
    fun_prop
  have hevent : MeasurableSet {x : Fin N → ℝ | A x ∈ C} :=
    hC.preimage hmap
  have hkernel : Measurable (fun x : Fin N → ℝ =>
      ENNReal.ofReal (gaussianKernel x)) := by
    apply ENNReal.measurable_ofReal.comp
    unfold gaussianKernel gaussianQuadratic
    fun_prop
  change Measurable (fun x : Fin N → ℝ =>
    if A x ∈ C then ENNReal.ofReal (gaussianKernel x) else 0)
  exact Measurable.ite hevent hkernel measurable_const

/-- Anderson's Gaussian-shift integral inequality for every measurable
convex symmetric target set. The linear map is arbitrary, including singular
maps; measurability follows from the target-set hypothesis. -/
theorem gaussianImageDensity_translate_integral_le
    {d M : ℕ} (C : Set (Fin M → ℝ))
    (A : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin M → ℝ)) (shift : Fin M → ℝ)
    (hconv : Convex ℝ C) (hsymm : ∀ z, z ∈ C → -z ∈ C)
    (hC : MeasurableSet C) :
    ∫⁻ x, shiftedGaussianDensity C A shift x ≤
      ∫⁻ x, gaussianImageDensity C A x := by
  exact midpoint_lintegral_translate_le d (shiftedGaussianDensity C A shift)
    (gaussianImageDensity C A)
    (measurable_shiftedGaussianDensity C A shift hC)
    (measurable_gaussianImageDensity C A hC)
    (shiftedGaussianDensity_midpoint_le C A shift hconv hsymm)

/-- The normalized finite product standard-Gaussian density is a positive
constant multiple of the unnormalized kernel used by the PL argument. -/
theorem standardGaussian_density_eq_const_mul_kernel {N : ℕ}
    (x : Fin N → ℝ) :
    GaussianDensity.density x =
      (Real.sqrt (2 * Real.pi))⁻¹ ^ N * gaussianKernel x := by
  classical
  rw [GaussianDensity.density, ProbabilityTheory.gaussianPDFReal_def]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 1
  · simp
  · unfold gaussianKernel gaussianQuadratic
    simp only [sub_zero, NNReal.coe_one, mul_one]
    congr 1
    calc
      (∑ i, -(x i) ^ 2 / 2) = ∑ i, -((x i) ^ 2 / 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = -(∑ i, (x i) ^ 2 / 2) := by rw [Finset.sum_neg_distrib]
      _ = (-(∑ i, (x i) ^ 2)) / 2 := by
        rw [← Finset.sum_div]
        ring

/-- Anderson's inequality for an arbitrary finite linear image of an
independent standard Gaussian vector. The conclusion is an inequality of
actual product-Gaussian probabilities, and permits singular maps. -/
theorem standardGaussian_linear_shift_le
    {d M : ℕ} (C : Set (Fin M → ℝ))
    (A : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin M → ℝ)) (shift : Fin M → ℝ)
    (hconv : Convex ℝ C) (hsymm : ∀ z, z ∈ C → -z ∈ C)
    (hC : MeasurableSet C) :
    (Measure.pi (fun _ : Fin (d + 1) => ProbabilityTheory.gaussianReal 0 1))
        {x | A x + shift ∈ C} ≤
    (Measure.pi (fun _ : Fin (d + 1) => ProbabilityTheory.gaussianReal 0 1))
        {x | A x ∈ C} := by
  classical
  let μ := Measure.pi (fun _ : Fin (d + 1) => ProbabilityTheory.gaussianReal 0 1)
  let c : ℝ := (Real.sqrt (2 * Real.pi))⁻¹ ^ (d + 1)
  let ce : ENNReal := ENNReal.ofReal c
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hshiftSet : MeasurableSet {x : Fin (d + 1) → ℝ | A x + shift ∈ C} := by
    exact hC.preimage (by fun_prop)
  have hzeroSet : MeasurableSet {x : Fin (d + 1) → ℝ | A x ∈ C} := by
    exact hC.preimage (by fun_prop)
  have hshiftDensity : Measurable (shiftedGaussianDensity C A shift) :=
    measurable_shiftedGaussianDensity C A shift hC
  have hzeroDensity : Measurable (gaussianImageDensity C A) :=
    measurable_gaussianImageDensity C A hC
  have hshiftIntegrand (x : Fin (d + 1) → ℝ) :
      Set.indicator {x : Fin (d + 1) → ℝ | A x + shift ∈ C}
          (fun x => ENNReal.ofReal (GaussianDensity.density x)) x =
        ce * shiftedGaussianDensity C A shift x := by
    by_cases hx : A x + shift ∈ C
    · simp only [Set.indicator, Set.mem_ofPred_eq, hx,
        shiftedGaussianDensity, ↓reduceIte]
      change ENNReal.ofReal (GaussianDensity.density x) =
        ENNReal.ofReal c * ENNReal.ofReal (gaussianKernel x)
      rw [standardGaussian_density_eq_const_mul_kernel]
      change ENNReal.ofReal (c * gaussianKernel x) =
        ENNReal.ofReal c * ENNReal.ofReal (gaussianKernel x)
      exact ENNReal.ofReal_mul (by positivity : 0 ≤ c)
    · simp [Set.indicator, hx, shiftedGaussianDensity]
  have hzeroIntegrand (x : Fin (d + 1) → ℝ) :
      Set.indicator {x : Fin (d + 1) → ℝ | A x ∈ C}
          (fun x => ENNReal.ofReal (GaussianDensity.density x)) x =
        ce * gaussianImageDensity C A x := by
    by_cases hx : A x ∈ C
    · simp only [Set.indicator, Set.mem_ofPred_eq, hx,
        gaussianImageDensity, ↓reduceIte]
      change ENNReal.ofReal (GaussianDensity.density x) =
        ENNReal.ofReal c * ENNReal.ofReal (gaussianKernel x)
      rw [standardGaussian_density_eq_const_mul_kernel]
      change ENNReal.ofReal (c * gaussianKernel x) =
        ENNReal.ofReal c * ENNReal.ofReal (gaussianKernel x)
      exact ENNReal.ofReal_mul (by positivity : 0 ≤ c)
    · simp [Set.indicator, hx, gaussianImageDensity]
  have hshiftProb : μ {x | A x + shift ∈ C} =
      ce * ∫⁻ x, shiftedGaussianDensity C A shift x := by
    rw [show μ = Measure.pi (fun _ : Fin (d + 1) => ProbabilityTheory.gaussianReal 0 1) by rfl,
      GaussianDensity.standardGaussian_eq_withDensity]
    rw [withDensity_apply _ hshiftSet, ← lintegral_indicator hshiftSet]
    calc
      _ = ∫⁻ x, ce * shiftedGaussianDensity C A shift x := by
        apply lintegral_congr_ae
        exact ae_of_all _ hshiftIntegrand
      _ = ce * ∫⁻ x, shiftedGaussianDensity C A shift x :=
        lintegral_const_mul ce hshiftDensity
  have hzeroProb : μ {x | A x ∈ C} =
      ce * ∫⁻ x, gaussianImageDensity C A x := by
    rw [show μ = Measure.pi (fun _ : Fin (d + 1) => ProbabilityTheory.gaussianReal 0 1) by rfl,
      GaussianDensity.standardGaussian_eq_withDensity]
    rw [withDensity_apply _ hzeroSet, ← lintegral_indicator hzeroSet]
    calc
      _ = ∫⁻ x, ce * gaussianImageDensity C A x := by
        apply lintegral_congr_ae
        exact ae_of_all _ hzeroIntegrand
      _ = ce * ∫⁻ x, gaussianImageDensity C A x :=
        lintegral_const_mul ce hzeroDensity
  rw [hshiftProb, hzeroProb]
  exact mul_le_mul_of_nonneg_left (gaussianImageDensity_translate_integral_le
    C A shift hconv hsymm hC) (by positivity)

/-- The Anderson bound persists after averaging over an independent residual
shift. This is the finite-dimensional product-law step used to keep all
unselected Gaussian modes in the conditioning argument. -/
theorem standardGaussian_residual_mixture_le
    {d M : ℕ} (C : Set (Fin M → ℝ))
    (A : (Fin (d + 1) → ℝ) →ₗ[ℝ] (Fin M → ℝ))
    (ν : Measure (Fin M → ℝ)) [IsProbabilityMeasure ν]
    (hconv : Convex ℝ C) (hsymm : ∀ z, z ∈ C → -z ∈ C)
    (hC : MeasurableSet C) :
    ∫⁻ z, (Measure.pi (fun _ : Fin (d + 1) =>
      ProbabilityTheory.gaussianReal 0 1)) {x | A x + z ∈ C} ∂ν ≤
      (Measure.pi (fun _ : Fin (d + 1) =>
        ProbabilityTheory.gaussianReal 0 1)) {x | A x ∈ C} := by
  calc
    _ ≤ ∫⁻ z, (Measure.pi (fun _ : Fin (d + 1) =>
        ProbabilityTheory.gaussianReal 0 1)) {x | A x ∈ C} ∂ν :=
      lintegral_mono fun z => standardGaussian_linear_shift_le
        C A z hconv hsymm hC
    _ = (Measure.pi (fun _ : Fin (d + 1) =>
        ProbabilityTheory.gaussianReal 0 1)) {x | A x ∈ C} := by
      simp

end BrownianSharp
