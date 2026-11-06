import BrownianSharp.AlignmentPaperJointGradeScaleEnvelope

/-! The full-rank scalar stage-scale estimate with the sampling dimension
factor restored. -/

noncomputable section
open scoped ENNReal NNReal

namespace BrownianSharp.AlignmentPaperJointGradeScaleUnscaled

open BrownianSharp.AlignmentPaperJointGradeScaleEnvelope
open BrownianSharp.AlignmentPaperJointLowGradeCover
open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperJointDyadicStages
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperLpJointDvp

/-- The sharp full-rank scale estimate, unscaled by the reciprocal sampling
dimension. Its constant is uniform in the grade. -/
theorem exists_stageScale_unscaled_envelope {d : ℕ} {p A : ℝ}
    (hd : 2 ≤ d) (hp : 1 < p) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      stageScale d n (gradeSeriesSourceRadius d p A n) ≤
        K * (2:ℝ)^(-(n:ℝ)) * Real.sqrt (n+1:ℝ) *
          (JointSampleDimension d n:ℝ)^(1/p) := by
  obtain ⟨K, hK, hscale⟩ := exists_stageScale_fullRank_envelope hd hp hA
  refine ⟨K, hK, ?_⟩
  intro n
  let D : ℝ := JointSampleDimension d n
  have hD : 0 < D := by
    dsimp [D]
    exact_mod_cast jointSampleDimension_pos_of_dimension_pos (n := n) (by omega : 0 < d)
  have hprod : D^(-1/p) * D^(1/p) = 1 := by
    rw [← Real.rpow_add hD]
    have he : -1/p + 1/p = 0 := by ring
    rw [he, Real.rpow_zero]
  have hrew : stageScale d n (gradeSeriesSourceRadius d p A n) =
      (stageScale d n (gradeSeriesSourceRadius d p A n) * D^(-1/p)) * D^(1/p) := by
    rw [mul_assoc, hprod, mul_one]
  rw [hrew]
  have hmul := mul_le_mul_of_nonneg_right (hscale n)
    (by positivity : 0 ≤ D^(1/p))
  simpa [D, mul_assoc] using hmul

end BrownianSharp.AlignmentPaperJointGradeScaleUnscaled
