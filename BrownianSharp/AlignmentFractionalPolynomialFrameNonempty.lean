import BrownianSharp.AlignmentFractionalPolynomialConvergence
import BrownianSharp.AlignmentFractionalGradedPolynomialFeature

noncomputable section
namespace BrownianSharp.AlignmentFractionalPolynomialFrameNonempty
open AlignmentFractionalPolynomialSpaces AlignmentFractionalPolynomialConvergence
open AlignmentFractionalDyadicProjection AlignmentFractionalHaarProjection
open AlignmentNestedProjectionGrades

theorem piecewisePolynomials_finrank_pos {q : ℕ} (hq : 0 < q) (n : ℕ) :
    0 < Module.finrank ℝ (piecewisePolynomials q n) := by
  have hm := Submodule.finrank_mono (piecewiseConstants_le_polynomials hq n)
  rw [sourceDyadicPiecewiseConstants_finrank] at hm
  exact lt_of_lt_of_le (by positivity : 0 < 2^n) hm

end BrownianSharp.AlignmentFractionalPolynomialFrameNonempty
