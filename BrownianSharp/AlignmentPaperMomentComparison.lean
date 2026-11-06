import BrownianSharp.AlignmentPaperQuantization

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperMomentComparison

/-- Mathlib's Holder inequality specializes to the moment comparison needed
for real empirical Wasserstein continuity. -/
theorem second_moment_le_sqrt_fourth
    {X:Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ:Measure X) [IsProbabilityMeasure μ] (o:X) :
    (∫⁻ x,edist x o^2∂μ)≤ennrealSqrt (∫⁻ x,edist x o^4∂μ) := by
  have hf:Measurable (fun x:X=>edist x o^2):=
    (continuous_id.edist continuous_const).measurable.pow_const 2
  have h:=ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
    (μ:=μ) Real.HolderConjugate.two_two hf.aemeasurable
    (measurable_const:Measurable (fun _:X=>(1:ℝ≥0∞))).aemeasurable
  have he (x:X):(edist x o^2)^2=edist x o^4 := by rw [←pow_mul]
  simpa [ennrealSqrt,he] using h

theorem second_moment_ne_top_of_fourth
    {X:Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ:Measure X) [IsProbabilityMeasure μ] (o:X)
    (h:(∫⁻ x,edist x o^4∂μ)≠⊤) :
    (∫⁻ x,edist x o^2∂μ)≠⊤ := by
  exact ne_of_lt ((second_moment_le_sqrt_fourth μ o).trans_lt
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h))

end BrownianSharp.AlignmentPaperMomentComparison
