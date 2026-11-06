import BrownianSharp.AlignmentPaperSpatialConvexity
import BrownianSharp.AlignmentPaperSpatialVariance

/-! Literal spatial soft-maximum to Gaussian-convexity transfer. The
remaining geometric input is the continuum row correlation bound. -/
noncomputable section
open MeasureTheory
open BrownianSharp.Concentration
namespace BrownianSharp.AlignmentPaperSpatialConfinement
open AlignmentPaperSpatialExponential AlignmentPaperSpatialConvexity

variable {α κ : Type*} [MeasurableSpace α] [Fintype κ]

/-- Uniform smallness of the normalized field forces the spatial soft
maximum below exp(-tau/4), as in the manuscript proof. -/
theorem spatialCoshAverage_le_of_row_bound
    (μ : Measure α) [IsProbabilityMeasure μ] (τ : ℝ) (hτ : 0 ≤ τ)
    (a : α → κ → ℝ) (ha : ∀ x, ∑ i, a x i^2=1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) (z : κ → ℝ)
    (hsmall : ∀ x, |∑ i, a x i*z i| ≤ Real.sqrt τ/4) :
    spatialCoshAverage μ τ a z ≤ Real.exp (-τ/4) := by
  have hi := spatialCosh_integrand_integrable μ τ a ha haMeas z
  have hc (x : α) : Real.cosh (Real.sqrt τ * ∑ i, a x i*z i) ≤ Real.exp (τ/4) := by
    have hcosh : Real.cosh (Real.sqrt τ * ∑ i, a x i*z i) ≤
        Real.exp |Real.sqrt τ * ∑ i, a x i*z i| := by
      rw [Real.cosh_eq]
      have hp := Real.exp_le_exp.mpr (le_abs_self (Real.sqrt τ * ∑ i, a x i*z i))
      have hn := Real.exp_le_exp.mpr (neg_le_abs (Real.sqrt τ * ∑ i, a x i*z i))
      linarith
    apply hcosh.trans
    apply Real.exp_le_exp.mpr
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg τ)]
    have h := mul_le_mul_of_nonneg_left (hsmall x) (Real.sqrt_nonneg τ)
    nlinarith [Real.sq_sqrt hτ]
  have hint : (∫ x, Real.cosh (Real.sqrt τ * ∑ i, a x i*z i) ∂μ) ≤ Real.exp (τ/4) := by
    calc
      _ ≤ ∫ _ : α, Real.exp (τ/4) ∂μ := integral_mono hi (integrable_const _) hc
      _ = _ := by simp
  calc
    spatialCoshAverage μ τ a z ≤ Real.exp (-τ/2)*Real.exp (τ/4) :=
      mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le
    _ = Real.exp (-τ/4) := by rw [← Real.exp_add]; congr 1; ring

/-- The small-field event is mapped into the convex log-soft-maximum tail.
All mean/convexity/integrability premises are internally discharged. -/
theorem spatial_row_smallBall_mass_le
    (μ : Measure α) [IsProbabilityMeasure μ] (τ : ℝ) (hτ : 4 ≤ τ)
    (a : α → κ → ℝ) (ha : ∀ x, ∑ i, a x i^2=1)
    (haMeas : ∀ i, Measurable (fun x => a x i))
    {σ : ℝ} (hσ : 0 < σ) (hσ₄ : σ ≤ 1/4)
    (hvar : ProbabilityTheory.variance (spatialCoshAverage μ τ a)
      (productStandardGaussian κ) ≤ σ^2) :
    (productStandardGaussian κ).real
      {z | ∀ x, |∑ i, a x i*z i| ≤ Real.sqrt τ/4} ≤
      Real.exp (-(standardGaussianQuantile (3/4)*(τ/4-1))^2/(18*σ^2)) := by
  have hτ0 : 0 ≤ τ := by linarith
  have hsub : {z : κ → ℝ | ∀ x, |∑ i, a x i*z i| ≤ Real.sqrt τ/4} ⊆
      {z : κ → ℝ | Real.log (spatialCoshAverage μ τ a z) ≤ -(τ/4)} := by
    intro z hz
    have hU := spatialCoshAverage_le_of_row_bound μ τ hτ0 a ha haMeas z hz
    have hpos : 0 < spatialCoshAverage μ τ a z :=
      (Real.exp_pos (-τ/2)).trans_le (spatialCoshAverage_bounds μ τ a ha haMeas z).1
    simpa [neg_div] using Real.log_le_log hpos hU
  exact (MeasureTheory.measureReal_mono hsub).trans
    (spatialCoshAverage_lower_tail μ τ hτ0 a ha haMeas (by linarith) hσ hσ₄ hvar)

/-- Elementary cancellation of the variance scale in the last step of the
paper's confinement proof. The exponent is proportional to the number of
coefficients, with a constant independent of tau and that number. -/
theorem confinement_exponent_le {q C τ D : ℝ}
    (hC : 0 < C) (hD : 0 < D) (hτ : 8 ≤ τ) :
    -(q*(τ/4-1))^2/(18*(C*τ^2/D)) ≤ -(q^2/(1152*C))*D := by
  have hτ0 : 0 < τ := by linarith
  have ht : τ/8 ≤ τ/4-1 := by linarith
  have hsq : τ^2/64 ≤ (τ/4-1)^2 := by nlinarith
  have hnum : q^2*(τ^2/64) ≤ q^2*(τ/4-1)^2 :=
    mul_le_mul_of_nonneg_left hsq (sq_nonneg q)
  have hden : 0 < 18*(C*τ^2/D) := by positivity
  have hratio : q^2/(1152*C)*D ≤ (q*(τ/4-1))^2/(18*(C*τ^2/D)) := by
    apply (le_div_iff₀ hden).2
    have hτne : τ ≠ 0 := hτ0.ne'
    field_simp [hC.ne', hD.ne']
    nlinarith [hnum]
  simpa only [neg_div, neg_mul] using (neg_le_neg hratio)

/-- Final variance cancellation for the actual spatial field. The coefficient
count D appears with a fixed exponential rate once C tau²/D is small. -/
theorem spatial_row_confinement_of_variance
    (μ : Measure α) [IsProbabilityMeasure μ] (τ : ℝ) (hτ : 8 ≤ τ)
    (a : α → κ → ℝ) (ha : ∀ x, ∑ i, a x i^2=1)
    (haMeas : ∀ i, Measurable (fun x => a x i))
    {C D : ℝ} (hC : 0 < C) (hD : 0 < D)
    (hsmall : C*τ^2/D ≤ 1/16)
    (hvar : ProbabilityTheory.variance (spatialCoshAverage μ τ a)
      (productStandardGaussian κ) ≤ C*τ^2/D) :
    (productStandardGaussian κ).real
      {z | ∀ x, |∑ i, a x i*z i| ≤ Real.sqrt τ/4} ≤
      Real.exp (-(standardGaussianQuantile (3/4)^2/(1152*C))*D) := by
  have hτ0 : 0 < τ := by linarith
  let σ := Real.sqrt (C*τ^2/D)
  have hσ : 0 < σ := by dsimp [σ]; positivity
  have hσsq : σ^2 = C*τ^2/D := Real.sq_sqrt (by positivity)
  have hσ₄ : σ ≤ 1/4 := by nlinarith
  have hvar' : ProbabilityTheory.variance (spatialCoshAverage μ τ a)
      (productStandardGaussian κ) ≤ σ^2 := by rwa [hσsq]
  have hbound := spatial_row_smallBall_mass_le μ τ (by linarith) a ha haMeas hσ hσ₄ hvar'
  rw [hσsq] at hbound
  exact hbound.trans (Real.exp_le_exp.mpr (confinement_exponent_le hC hD hτ))

end BrownianSharp.AlignmentPaperSpatialConfinement
