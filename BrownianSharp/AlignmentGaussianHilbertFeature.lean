import BrownianSharp.AlignmentGaussianDiagonalCoordinates
import BrownianSharp.AlignmentGaussianFiniteFeature

/-! Finite Gaussian fields obtained from diagonally scaled Hilbert features. -/
noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentGaussianHilbertFeature
open AlignmentGaussianDiagonalCoordinates AlignmentGaussianFiniteFeature
open HaarQuarter
variable {H ι : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [Fintype ι]

def diagonalFeature {d : ℕ} (K : C(BrownianCubeAnchor d,H))
    (e : ι → H) (w : ι → ℝ) (i : ι) : C(BrownianCubeAnchor d,ℝ) :=
  ⟨fun t => w i * ⟪K t,e i⟫, continuous_const.mul
    (K.continuous.inner continuous_const)⟩

theorem diagonalFeature_square_sum {d : ℕ} (K : C(BrownianCubeAnchor d,H))
    (e : ι → H) (w : ι → ℝ) (t : BrownianCubeAnchor d) :
    (∑ i, (diagonalFeature K e w i t)^2) =
      ‖diagonalCoordinates e w (K t)‖^2 := by
  rw [diagonalCoordinates_norm_sq]
  rfl

theorem diagonalFeature_increment_square_sum {d : ℕ}
    (K : C(BrownianCubeAnchor d,H)) (e : ι → H) (w : ι → ℝ)
    (t s : BrownianCubeAnchor d) :
    (∑ i, (diagonalFeature K e w i t-diagonalFeature K e w i s)^2) =
      ‖diagonalCoordinates e w (K t-K s)‖^2 := by
  rw [diagonalCoordinates_norm_sq]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [diagonalFeature,ContinuousMap.coe_mk,inner_sub_left]
  ring

theorem diagonalFeature_increment_square_sum_le {d : ℕ}
    (K : C(BrownianCubeAnchor d,H)) (e : ι → H) (he : Orthonormal ℝ e)
    (w : ι → ℝ) (hw : ∀ i, |w i| ≤ 1)
    (R : ℝ) (hmetric : ∀ t s, ‖K t-K s‖^2 ≤ R*dist t s)
    (t s : BrownianCubeAnchor d) :
    (∑ i, (diagonalFeature K e w i t-diagonalFeature K e w i s)^2) ≤ R*dist t s := by
  rw [diagonalFeature_increment_square_sum]
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (diagonalCoordinates_norm_le e he w hw _) 2).trans (hmetric t s)

end BrownianSharp.AlignmentGaussianHilbertFeature
