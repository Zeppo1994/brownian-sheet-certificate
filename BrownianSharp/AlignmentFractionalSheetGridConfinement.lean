import BrownianSharp.AlignmentFractionalSheetTensorFeature
import BrownianSharp.AlignmentGaussianFiniteGridConfinement

/-! Actual fractional-sheet finite-grid confinement through the checked MvN covariance. -/
noncomputable section
open MeasureTheory ProbabilityTheory HaarQuarter
open scoped BigOperators RealInnerProductSpace ENNReal
namespace BrownianSharp.AlignmentFractionalSheetGridConfinement
open AlignmentGaussianRates AlignmentFractionalSheetTensorFeature
open AlignmentGaussianFiniteGridConfinement GaussianProjection

private def finiteUnivEquiv {J : Type*} [Fintype J] :
    (↥(Finset.univ : Finset J)) ≃ J :=
  { toFun := fun i => i.1
    invFun := fun j => ⟨j, Finset.mem_univ j⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro j; rfl }

theorem fractionalSheet_grid_hasGaussianLaw
    {d : ℕ} {Ω J : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype J]
    (B : FractionalBrownianSheetOnCube d Ω P) (x : J → BrownianCubeAnchor d) :
    HasGaussianLaw (fun ω j => B.path ω (x j)) P := by
  let hp := B.gaussian.comp_right x
  have hr := hp.hasGaussianLaw Finset.univ
  let R : ((↥(Finset.univ : Finset J)) → ℝ) ≃L[ℝ] (J → ℝ) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : J => ℝ) finiteUnivEquiv
  have heq : (fun ω j => B.path ω (x j)) =
      (fun ω => R (fun i => B.path ω (x i.1))) := by
    funext ω j
    rfl
  rw [heq]
  exact hr.map_equiv R

end BrownianSharp.AlignmentFractionalSheetGridConfinement
