import Mathlib.Probability.Moments.Covariance

noncomputable section
open MeasureTheory ProbabilityTheory
namespace BrownianSharp.AlignmentPaperCovarianceCombination

theorem covariance_linear_combination {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {X Y U V : Ω → ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ)
    (hU : MemLp U 2 μ) (hV : MemLp V 2 μ) (a b c d : ℝ) :
    covariance (fun ω => a * X ω + b * Y ω)
      (fun ω => c * U ω + d * V ω) μ =
      a*c*covariance X U μ + a*d*covariance X V μ +
      b*c*covariance Y U μ + b*d*covariance Y V μ := by
  change covariance (a • X + b • Y) (c • U + d • V) μ = _
  rw [covariance_add_left (hX.const_smul a) (hY.const_smul b)
    ((hU.const_smul c).add (hV.const_smul d))]
  rw [covariance_add_right (hX.const_smul a) (hU.const_smul c) (hV.const_smul d),
    covariance_add_right (hY.const_smul b) (hU.const_smul c) (hV.const_smul d)]
  simp only [covariance_smul_left, covariance_smul_right]
  ring

end BrownianSharp.AlignmentPaperCovarianceCombination
