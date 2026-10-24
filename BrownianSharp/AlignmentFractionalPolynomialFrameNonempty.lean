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

theorem polynomialTensorFrameIndex_nonempty {d : ℕ} (q : Fin d → ℕ)
    (hq : ∀ i, 0 < q i) (N : ℕ) :
    Nonempty (∀ i : Fin d, GradedFrameIndex (piecewisePolynomials (q i)) N) := by
  refine ⟨fun i => ⟨⟨0,by omega⟩,?_⟩⟩
  change Fin (Module.finrank ℝ (piecewisePolynomials (q i) 0))
  exact ⟨0,piecewisePolynomials_finrank_pos (hq i) 0⟩

end BrownianSharp.AlignmentFractionalPolynomialFrameNonempty
