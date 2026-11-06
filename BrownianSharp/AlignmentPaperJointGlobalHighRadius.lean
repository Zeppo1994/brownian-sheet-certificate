import BrownianSharp.AlignmentPaperJointGlobalHighScalar
import BrownianSharp.AlignmentPaperJointHighGradeCovers
import BrownianSharp.AlignmentPaperJointGradeScaleUnscaled
import BrownianSharp.AlignmentPaperJointHighGradeCostSum

/-! Summed high-grade radii for the actual rank profile. -/

noncomputable section
open scoped BigOperators NNReal

namespace BrownianSharp.AlignmentPaperJointGlobalHighRadius

open BrownianSharp.AlignmentPaperJointGlobalRankProfile
open BrownianSharp.AlignmentPaperJointGradeScaleEnvelope
open BrownianSharp.AlignmentPaperJointGradeScaleUnscaled
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperJointDyadicStages
open BrownianSharp.AlignmentPaperJointGlobalHighScalar
open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.AlignmentPaperJointHighGradeCostSum

theorem decodedRadius_coe_le {d n : ℕ} {p B : ℝ} {J : ℕ}
    (hB : 0 < B) :
    (decodedGradeDyadicRadius d n p B J : ℝ) ≤
      24 * (5:ℝ)^d * stageScale d n B * ((2:ℝ)^J)^(-1/p) := by
  have hscale : 0 < stageScale d n B := stageScale_pos hB
  have hpow : 0 < ((2:ℝ)^J)^(-1/p) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have harg : 0 < 2 * (3 * stageScale d n B * ((2:ℝ)^J)^(-1/p)) := by positivity
  unfold decodedGradeDyadicRadius
  change (2 * (5:ℝ)^d) *
    (2 * Real.toNNReal (2 * (3 * stageScale d n B * ((2:ℝ)^J)^(-1/p)))) ≤ _
  rw [Real.coe_toNNReal _ harg.le]
  ring_nf
  rfl

end BrownianSharp.AlignmentPaperJointGlobalHighRadius
