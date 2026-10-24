import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

namespace BrownianSharp.GaussianRIP

open MeasureTheory ProbabilityTheory

private theorem gaussianSquare_density_mul (t x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-((1 / 2 : ℝ) - t) * x ^ 2) := by
  rw [gaussianPDFReal_def]
  simp only [sub_zero]
  have hc : (Real.sqrt (2 * Real.pi * (1 : NNReal)))⁻¹ =
      (Real.sqrt (2 * Real.pi))⁻¹ := by norm_num
  rw [hc]
  norm_num
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring

/-- Exponential-square functions are integrable whenever the resulting
Gaussian density still has a strictly negative quadratic exponent. -/
theorem integrable_exp_mul_sq_gaussianReal (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (t * x ^ 2)) (gaussianReal 0 1) := by
  have hb : 0 < (1 / 2 : ℝ) - t := by linarith
  have hv : (1 : NNReal) ≠ 0 := by norm_num
  rw [gaussianReal_of_var_ne_zero 0 hv, gaussianPDF_def]
  apply (integrable_withDensity_iff_integrable_smul' (by fun_prop)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)).2
  have hfun : (fun x : ℝ => (ENNReal.ofReal (gaussianPDFReal 0 1 x)).toReal •
      Real.exp (t * x ^ 2)) = fun x =>
      (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-((1 / 2 : ℝ) - t) * x ^ 2) := by
    funext x
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 x), ← gaussianSquare_density_mul]
    rfl
  rw [hfun]
  exact (integrable_exp_neg_mul_sq hb).const_mul _

theorem integral_exp_mul_sq_gaussianReal (t : ℝ) (ht : t < 1 / 2) :
    (∫ x : ℝ, Real.exp (t * x ^ 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
  have hb : 0 < (1 / 2 : ℝ) - t := by linarith
  have hv : (1 : NNReal) ≠ 0 := by norm_num
  rw [integral_gaussianReal_eq_integral_smul hv]
  have hpoint : (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2)) =
      fun x => (Real.sqrt (2 * Real.pi))⁻¹ *
        Real.exp (-((1 / 2 : ℝ) - t) * x ^ 2) := by
    funext x
    exact gaussianSquare_density_mul t x
  rw [show (fun x : ℝ => gaussianPDFReal 0 1 x • Real.exp (t * x ^ 2)) =
      fun x => gaussianPDFReal 0 1 x * Real.exp (t * x ^ 2) by rfl, hpoint,
    integral_const_mul, integral_gaussian]
  have hden : 0 < 1 - 2 * t := by linarith
  apply (sq_eq_sq₀ (by positivity) (by positivity)).1
  rw [mul_pow, inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ Real.pi / ((1 / 2 : ℝ) - t)),
    inv_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 - 2 * t)]
  field_simp

end BrownianSharp.GaussianRIP
