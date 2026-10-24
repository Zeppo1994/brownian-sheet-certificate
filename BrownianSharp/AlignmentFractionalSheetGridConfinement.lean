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

theorem fractionalSheet_grid_confinement
    {d : ℕ} {Ω I J : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [Nonempty I] [Fintype J] [Nonempty J] {P : Measure Ω} [IsProbabilityMeasure P]
    (H : Fin d → ℝ) (hH : ∀ i, 0<H i ∧ H i<1)
    (B : FractionalBrownianSheetOnCube d Ω P) (hBH : B.H=H)
    (x : J → BrownianCubeAnchor d) (e : I → FullProductL2 d)
    (he : ∀ i j, ⟪e i,e j⟫=if i=j then 1 else 0)
    (a : I → ℝ) (ρ τ : ℝ) (hρ : 0<ρ) (hτ : 0≤τ)
    (ha : ∀ i, 0<a i) (ha1 : ∀ i, a i≤1)
    (hscaled : (1/2:ENNReal) ≤ productStandardGaussian I
      {z | ∀ j, |∑ i, ⟪fractionalSheetFeature H hH (x j),e i⟫*(a i*z i)|≤ρ})
    (hres : ∀ j, ‖fractionalSheetFeature H hH (x j)-
      projection e (fractionalSheetFeature H hH (x j))‖≤τ)
    (hbudget : 2*τ*Real.sqrt (Real.log (2*(Fintype.card J:ℝ)+2))≤ρ/2) :
    ENNReal.ofReal (∏ i,a i)*((1/2:ENNReal)*(1/2:ENNReal)) ≤
      P {ω | ∀ j, |B.path ω (x j)|≤2*ρ} := by
  apply finiteGrid_confinement_of_main_half_mass
    (fun ω j => B.path ω (x j)) e (fun j => fractionalSheetFeature H hH (x j))
    (fractionalSheet_grid_hasGaussianLaw B x) (fun j => B.mean_zero (x j))
    ?_ he a ρ τ hρ hτ ha ha1 hscaled hres hbudget
  intro i j
  rw [B.covariance,hBH,fractionalSheetFeature_gram]

end BrownianSharp.AlignmentFractionalSheetGridConfinement
