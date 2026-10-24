import BrownianSharp.FiniteOrthogonalCoordinates
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Contractive diagonal coordinate maps for finite Gaussian source fields. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentGaussianDiagonalCoordinates
variable {H ι : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [Fintype ι]

def diagonalCoordinates (e : ι → H) (w : ι → ℝ) :
    H →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i => w i * ⟪x,e i⟫)
  map_add' x y := by ext i; simp [inner_add_left]; ring
  map_smul' a x := by ext i; simp [real_inner_smul_left]; ring

theorem diagonalCoordinates_norm_sq (e : ι → H) (w : ι → ℝ) (x : H) :
    ‖diagonalCoordinates e w x‖^2 = ∑ i, (w i*⟪x,e i⟫)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [diagonalCoordinates,Real.norm_eq_abs,mul_pow,sq_abs]

theorem diagonalCoordinates_norm_le (e : ι → H) (he : Orthonormal ℝ e)
    (w : ι → ℝ) (hw : ∀ i, |w i| ≤ 1) (x : H) :
    ‖diagonalCoordinates e w x‖ ≤ ‖x‖ := by
  have hsum : (∑ i, (w i*⟪x,e i⟫)^2) ≤ ∑ i, ⟪x,e i⟫^2 := by
    apply Finset.sum_le_sum
    intro i hi
    have hwsq : (w i)^2 ≤ 1 := by nlinarith [hw i, sq_abs (w i), abs_nonneg (w i)]
    nlinarith [mul_le_mul_of_nonneg_right hwsq (sq_nonneg ⟪x,e i⟫)]
  have hbase := finiteOrthonormalCoordinates_norm_le e he x
  rw [← finiteOrthonormalCoordinates_norm_sq] at hsum
  rw [← diagonalCoordinates_norm_sq] at hsum
  nlinarith [norm_nonneg (diagonalCoordinates e w x),
    norm_nonneg (finiteOrthonormalCoordinates e x),norm_nonneg x]

def diagonalCoordinateCLM (e : ι → H) (he : Orthonormal ℝ e)
    (w : ι → ℝ) (hw : ∀ i, |w i| ≤ 1) :
    H →L[ℝ] EuclideanSpace ℝ ι :=
  (diagonalCoordinates e w).mkContinuous 1
    (by intro x; simpa using diagonalCoordinates_norm_le e he w hw x)

def contractionScale (η : ℝ) (N g : ℕ) : ℝ :=
  if g ≤ N then η^(N-g) else 1

theorem contractionScale_pos {η : ℝ} (hη : 0 < η) (N g : ℕ) :
    0 < contractionScale η N g := by
  unfold contractionScale
  split_ifs <;> positivity

theorem contractionScale_le_one {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (N g : ℕ) : contractionScale η N g ≤ 1 := by
  unfold contractionScale
  split_ifs
  · exact pow_le_one₀ hη0 hη1
  · exact le_rfl

theorem contractionScale_abs_le_one {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (N g : ℕ) : |contractionScale η N g| ≤ 1 := by
  have hnonneg : 0 ≤ contractionScale η N g := by
    unfold contractionScale
    split_ifs <;> positivity
  rw [abs_of_nonneg hnonneg]
  exact contractionScale_le_one hη0 hη1 N g

end BrownianSharp.AlignmentGaussianDiagonalCoordinates
