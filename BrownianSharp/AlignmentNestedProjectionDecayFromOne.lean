import BrownianSharp.AlignmentNestedProjectionDecay

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentNestedProjectionDecayFromOne
open AlignmentNestedProjectionBasis AlignmentNestedProjectionGrades
open AlignmentNestedProjectionDecay
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem projection_residual_norm_le (U : Submodule ℝ E)
    [U.HasOrthogonalProjection] (x : E) : ‖x-U.starProjection x‖ ≤ ‖x‖ := by
  have h := Uᗮ.norm_starProjection_apply_le x
  simpa only [Submodule.starProjection_orthogonal, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply] using h

end BrownianSharp.AlignmentNestedProjectionDecayFromOne
