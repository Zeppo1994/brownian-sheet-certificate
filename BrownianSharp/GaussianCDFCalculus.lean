import BrownianSharp.Concentration
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-!
# Calculus of the one-dimensional Gaussian distribution profile

This file develops the smooth one-dimensional profile used in Ehrhard-style
interpolation.  It makes no finite-dimensional Gaussian isoperimetric claim.
-/

open MeasureTheory Filter
open scoped ENNReal Topology ProbabilityTheory

namespace BrownianSharp

private noncomputable def stdPdf : ℝ → ℝ := ProbabilityTheory.gaussianPDFReal 0 1

/-- The standard Gaussian CDF is an integral of its density on each lower ray. -/
theorem standardGaussianCDF_eq_density_integral (x : ℝ) :
    Concentration.standardGaussianCDF x = ∫ y in Set.Iic x, stdPdf y := by
  rw [Concentration.standardGaussianCDF_eq_cdf, ProbabilityTheory.cdf_eq_real]
  rw [MeasureTheory.measureReal_def]
  have hgauss := ProbabilityTheory.gaussianReal_apply_eq_integral
    (0 : ℝ) (v := 1) (by norm_num) (Set.Iic x)
  rw [hgauss]
  exact ENNReal.toReal_ofReal (MeasureTheory.integral_nonneg (fun y =>
    ProbabilityTheory.gaussianPDFReal_nonneg 0 1 y))

/-- The derivative of the strict standard Gaussian CDF is its density. -/
theorem hasDerivAt_standardGaussianCDF (x : ℝ) :
    HasDerivAt Concentration.standardGaussianCDF (stdPdf x) x := by
  have hpdfcont : Continuous stdPdf := by
    rw [stdPdf, ProbabilityTheory.gaussianPDFReal_def]
    fun_prop
  have hIic (y : ℝ) : IntegrableOn stdPdf (Set.Iic y) :=
    (ProbabilityTheory.integrable_gaussianPDFReal 0 1).integrableOn
  have hdiff : ∀ y : ℝ,
      (∫ z in Set.Iic y, stdPdf z) - (∫ z in Set.Iic (0 : ℝ), stdPdf z) =
        ∫ z in (0 : ℝ)..y, stdPdf z := by
    intro y
    exact intervalIntegral.integral_Iic_sub_Iic (hIic 0) (hIic y)
  have hzero : ∫ z in Set.Iic (0 : ℝ), stdPdf z = 1 / 2 := by
    rw [← Concentration.standardGaussianCDF_zero]
    symm
    exact standardGaussianCDF_eq_density_integral 0
  have hrepr : Concentration.standardGaussianCDF =
      fun y => 1 / 2 + ∫ z in (0 : ℝ)..y, stdPdf z := by
    funext y
    have h := hdiff y
    rw [← standardGaussianCDF_eq_density_integral y,
      ← standardGaussianCDF_eq_density_integral 0,
      Concentration.standardGaussianCDF_zero] at h
    linarith
  rw [hrepr]
  have hsm : StronglyMeasurableAtFilter stdPdf (𝓝 x) volume :=
    hpdfcont.stronglyMeasurableAtFilter volume (𝓝 x)
  have hFTC : HasDerivAt (fun y => ∫ z in (0 : ℝ)..y, stdPdf z)
      (stdPdf x) x :=
    intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ))
      (ProbabilityTheory.integrable_gaussianPDFReal 0 1).intervalIntegrable hsm
      hpdfcont.continuousAt
  convert hFTC.const_add (1 / 2 : ℝ) using 1

/-- The inverse-CDF quantile is continuous at every interior probability. -/
theorem standardGaussianQuantile_continuousAt {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ContinuousAt Concentration.standardGaussianQuantile u := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  let a := Concentration.standardGaussianQuantile u
  let lo := Concentration.standardGaussianCDF (a - ε)
  let hi := Concentration.standardGaussianCDF (a + ε)
  have ha : Concentration.standardGaussianCDF a = u :=
    Concentration.standardGaussianCDF_standardGaussianQuantile hu0 hu1
  have hlo : lo < u := by
    dsimp [lo]
    rw [← ha]
    exact Concentration.standardGaussianCDF_strictMono (by linarith)
  have hhi : u < hi := by
    dsimp [hi]
    rw [← ha]
    exact Concentration.standardGaussianCDF_strictMono (by linarith)
  let δ := min (u - lo) (hi - u)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro v hv
  have hvabs : |v - u| < δ := by simpa [Real.dist_eq] using hv
  have hvlo : u - δ < v := by
    have h := (abs_lt.mp hvabs).1
    linarith
  have hvhi : v < u + δ := by
    have h := (abs_lt.mp hvabs).2
    linarith
  have hδlo : δ ≤ u - lo := min_le_left _ _
  have hδhi : δ ≤ hi - u := min_le_right _ _
  have hlo0 : 0 ≤ lo := by
    dsimp [lo, Concentration.standardGaussianCDF]
    exact ENNReal.toReal_nonneg
  have hhi1 : hi ≤ 1 := by
    dsimp [hi, Concentration.standardGaussianCDF]
    calc
      (ProbabilityTheory.gaussianReal 0 1).real {z | z < a + ε} ≤
          (ProbabilityTheory.gaussianReal 0 1).real Set.univ :=
        MeasureTheory.measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  have hv0 : 0 < v := by linarith
  have hv1 : v < 1 := by linarith
  have hvq : Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile v) = v :=
    Concentration.standardGaussianCDF_standardGaussianQuantile hv0 hv1
  have hlow : a - ε < Concentration.standardGaussianQuantile v := by
    by_contra h
    have hle : Concentration.standardGaussianQuantile v ≤ a - ε := le_of_not_gt h
    have hmono := Concentration.standardGaussianCDF_strictMono.monotone hle
    change Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile v) ≤ lo at hmono
    rw [hvq] at hmono
    linarith
  have hhigh : Concentration.standardGaussianQuantile v < a + ε := by
    by_contra h
    have hle : a + ε ≤ Concentration.standardGaussianQuantile v := le_of_not_gt h
    have hmono := Concentration.standardGaussianCDF_strictMono.monotone hle
    change hi ≤ Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile v) at hmono
    rw [hvq] at hmono
    linarith
  have hdist : |Concentration.standardGaussianQuantile v -
      Concentration.standardGaussianQuantile u| < ε := by
    rw [show Concentration.standardGaussianQuantile u = a by rfl]
    apply abs_lt.mpr
    constructor <;> dsimp [a] at * <;> linarith
  simpa [Real.dist_eq] using hdist

/-- The inverse Gaussian CDF has the reciprocal-density derivative. -/
theorem hasDerivAt_standardGaussianQuantile {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt Concentration.standardGaussianQuantile
      (stdPdf (Concentration.standardGaussianQuantile u))⁻¹ u := by
  let q := Concentration.standardGaussianQuantile
  let f := Concentration.standardGaussianCDF
  have hqcont : ContinuousAt q u := standardGaussianQuantile_continuousAt hu0 hu1
  have hf : HasDerivAt f (stdPdf (q u)) (q u) := hasDerivAt_standardGaussianCDF (q u)
  have hfne : stdPdf (q u) ≠ 0 :=
    (ProbabilityTheory.gaussianPDFReal_pos 0 1 (q u) (by norm_num)).ne'
  have hleft : ∀ᶠ v in 𝓝 u, f (q v) = v := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with v hv
    exact Concentration.standardGaussianCDF_standardGaussianQuantile hv.1 hv.2
  have h := hf.of_local_left_inverse hqcont hfne hleft
  simpa [q, f] using h

/-- Isoperimetric profile of the standard Gaussian, defined on all reals by a
 harmless totalization; calculus claims below are restricted to `(0,1)`. -/
noncomputable def standardGaussianIsoperimetricProfile (u : ℝ) : ℝ :=
  stdPdf (Concentration.standardGaussianQuantile u)

/-- The one-dimensional Gaussian profile is positive in the open unit interval. -/
theorem standardGaussianIsoperimetricProfile_pos {u : ℝ} (_hu0 : 0 < u) (_hu1 : u < 1) :
    0 < standardGaussianIsoperimetricProfile u := by
  exact ProbabilityTheory.gaussianPDFReal_pos 0 1
    (Concentration.standardGaussianQuantile u) (by norm_num)

/-- A compact derivative identity for the Gaussian density. -/
theorem hasDerivAt_stdPdf (x : ℝ) : HasDerivAt stdPdf (-x * stdPdf x) x := by
  rw [stdPdf, ProbabilityTheory.gaussianPDFReal_def]
  have hquad : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    convert ((hasDerivAt_id x).pow 2).const_mul (-1 / 2 : ℝ) using 1
    · ext y
      simp
      ring
    · simp
      ring
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
      (Real.exp (-(x ^ 2) / 2) * -x) x := by
    convert (Real.hasDerivAt_exp (-(x ^ 2) / 2)).comp x hquad using 1
    · ext y
      simp
  convert hexp.const_mul ((Real.sqrt (2 * Real.pi))⁻¹) using 1
  · ext y
    simp [ProbabilityTheory.gaussianPDFReal_def]
  · simp [stdPdf, ProbabilityTheory.gaussianPDFReal_def]
    ring

/-- First derivative of the Gaussian isoperimetric profile. -/
theorem hasDerivAt_standardGaussianIsoperimetricProfile {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt standardGaussianIsoperimetricProfile
      (-Concentration.standardGaussianQuantile u) u := by
  let q := Concentration.standardGaussianQuantile
  have hq := hasDerivAt_standardGaussianQuantile hu0 hu1
  have hpdf := hasDerivAt_stdPdf (q u)
  have hcomp := hpdf.comp u hq
  have hne : stdPdf (q u) ≠ 0 :=
    (ProbabilityTheory.gaussianPDFReal_pos 0 1 (q u) (by norm_num)).ne'
  change HasDerivAt (stdPdf ∘ q) (-q u) u
  convert hcomp using 1 <;> simp [q, hne, mul_assoc, neg_mul]

/-- On the open unit interval, the profile derivative is minus the Gaussian
quantile. -/
theorem deriv_standardGaussianIsoperimetricProfile {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) :
    deriv standardGaussianIsoperimetricProfile u =
      -Concentration.standardGaussianQuantile u := by
  exact (hasDerivAt_standardGaussianIsoperimetricProfile hu0 hu1).deriv

/-- The second derivative of the Gaussian isoperimetric profile is `-1/I`. -/
theorem hasDerivAt_deriv_standardGaussianIsoperimetricProfile {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (deriv standardGaussianIsoperimetricProfile)
      (-(standardGaussianIsoperimetricProfile u)⁻¹) u := by
  have hq := (hasDerivAt_standardGaussianQuantile hu0 hu1).neg
  have heq : (fun v => deriv standardGaussianIsoperimetricProfile v) =ᶠ[𝓝 u]
      (fun v => -Concentration.standardGaussianQuantile v) := by
    filter_upwards [Ioo_mem_nhds hu0 hu1] with v hv
    exact deriv_standardGaussianIsoperimetricProfile hv.1 hv.2
  have h := hq.congr_of_eventuallyEq heq
  convert h using 1
  simp [standardGaussianIsoperimetricProfile]

/-- The one-dimensional standard Gaussian isoperimetric profile is strictly
concave on `(0,1)`. Its derivative formula is `I'=-Φ⁻¹`; the preceding theorem
also records the exact curvature `I''=-1/I`. -/
theorem standardGaussianIsoperimetricProfile_strictConcave :
    StrictConcaveOn ℝ (Set.Ioo (0 : ℝ) 1) standardGaussianIsoperimetricProfile := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioo 0 1)
  · intro u hu
    exact (hasDerivAt_standardGaussianIsoperimetricProfile hu.1 hu.2).continuousAt.continuousWithinAt
  · intro u hu v hv huv
    have hu' : u ∈ Set.Ioo (0 : ℝ) 1 := interior_subset hu
    have hv' : v ∈ Set.Ioo (0 : ℝ) 1 := interior_subset hv
    rw [deriv_standardGaussianIsoperimetricProfile (Set.mem_Ioo.mp hu').1
        (Set.mem_Ioo.mp hu').2,
      deriv_standardGaussianIsoperimetricProfile (Set.mem_Ioo.mp hv').1
        (Set.mem_Ioo.mp hv').2]
    have hqu := Concentration.standardGaussianCDF_standardGaussianQuantile
      (Set.mem_Ioo.mp hu').1 (Set.mem_Ioo.mp hu').2
    have hqv := Concentration.standardGaussianCDF_standardGaussianQuantile
      (Set.mem_Ioo.mp hv').1 (Set.mem_Ioo.mp hv').2
    have hqmono : Concentration.standardGaussianQuantile u <
        Concentration.standardGaussianQuantile v := by
      by_contra h
      have hle : Concentration.standardGaussianQuantile v ≤
          Concentration.standardGaussianQuantile u := le_of_not_gt h
      have hm := Concentration.standardGaussianCDF_strictMono.monotone hle
      rw [hqv, hqu] at hm
      linarith
    exact neg_lt_neg hqmono

end BrownianSharp
