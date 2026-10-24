import BrownianSharp.AlignmentGaussianDiagonalCoordinates
import BrownianSharp.AlignmentFractionalSheetTensorFeature
import Mathlib.Tactic

/-! Small exact bridge used when instantiating the abstract graded reverse:
finite orthonormal coefficients remain Holder-controlled after the diagonal
grading contraction. -/
noncomputable section
open InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianAuditFrameProfile

open BrownianSharp.AlignmentGaussianDiagonalCoordinates
open HaarQuarter

/-- Diagonal contraction of a finite orthonormal coordinate family is
contractive, so the contracted coefficient field inherits the feature's
Holder increment bound. -/
theorem contracted_frame_increment_le_of_holder
    {d : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (K : C(BrownianCubeAnchor d, H))
    {ι : Type} [Fintype ι]
    (e : ι → H) (he : Orthonormal ℝ e) (grade : ι → ℕ)
    (η : ℝ) (hη : 0 ≤ η) (hη1 : η ≤ 1) (N : ℕ)
    (h R : ℝ) (hh : 0 < h) (hR : 0 ≤ R)
    (hholder : ∀ z w, ‖K z-K w‖^2 ≤ R*(dist z w)^(2*h)) :
    ∀ z w, ∑ i : ι,
      (contractionScale η N (grade i) *
        (⟪K z,e i⟫-⟪K w,e i⟫))^2 ≤ R*(dist z w)^(2*h) := by
  intro z w
  let scale : ι → ℝ := fun i => contractionScale η N (grade i)
  have hscale : ∀ i, |scale i| ≤ 1 := by
    intro i
    exact contractionScale_abs_le_one hη hη1 N (grade i)
  have hdiag := diagonalCoordinates_norm_le (H := H) e he scale hscale (K z-K w)
  have hdiagSq : ‖diagonalCoordinates (H := H) e scale (K z-K w)‖^2 ≤ ‖K z-K w‖^2 := by
    nlinarith [norm_nonneg (diagonalCoordinates (H := H) e scale (K z-K w)), norm_nonneg (K z-K w)]
  have hsum : (∑ i : ι, (scale i * ⟪K z-K w,e i⟫)^2) ≤ ‖K z-K w‖^2 := by
    rw [← diagonalCoordinates_norm_sq (H := H)]
    exact hdiagSq
  have hcoeff (i : ι) :
      scale i*(⟪K z,e i⟫-⟪K w,e i⟫) = scale i*⟪K z-K w,e i⟫ := by
    rw [inner_sub_left]
  calc
    _ = ∑ i : ι, (scale i*⟪K z-K w,e i⟫)^2 := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoeff]
    _ ≤ ‖K z-K w‖^2 := hsum
    _ ≤ R*(dist z w)^(2*h) := hholder z w

end BrownianSharp.AlignmentGaussianAuditFrameProfile
