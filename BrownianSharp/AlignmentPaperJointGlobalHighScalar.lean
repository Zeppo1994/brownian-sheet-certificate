import BrownianSharp.AlignmentPaperJointGlobalRankProfile
import BrownianSharp.AlignmentPaperJointGradeScaleEnvelope
import BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
import BrownianSharp.AlignmentPaperJointHighGradeRankUpper

/-! Scalar high-window estimates for the actual dyadic rank profile. -/

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 500000

namespace BrownianSharp.AlignmentPaperJointGlobalHighScalar

open BrownianSharp.AlignmentPaperJointGlobalRankProfile
open BrownianSharp.AlignmentPaperJointGradeScaleEnvelope
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.AlignmentPaperJointHighGradeRankUpper

theorem highProfileRank_pow_upper {d N j : ℕ} {p : ℝ}
    (hd : 2 ≤ d) (hp1 : 1 < p) (hp2 : p < 2)
    (hj : j ≤ highProfileWindow p N) :
    (2 : ℝ) ^ highProfileRank d p N j ≤
      2 * (JointSampleDimension d N : ℝ) *
        Real.exp (-highProfileEta p * (j : ℝ)) := by
  exact high_profile_rank_upper hd hp1 hp2 hj

end BrownianSharp.AlignmentPaperJointGlobalHighScalar
