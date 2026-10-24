import BrownianSharp.AlignmentGaussianShift
import BrownianSharp.SheetProjection

/-! Finite orthogonal source-coordinate decomposition of actual integrated
Brownian-sheet evaluations.  The projected kernel is stated both in the exact
Brownian feature span and, through its isometric embedding, as the actual
Gamma-normalized tensor RL kernel. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianIntegratedFiniteProjection

open HaarQuarter
open BrownianSharp.AlignmentGaussianBochner
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentGaussianShift
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.CameronMartin
open BrownianSharp.GaussianProjection
open BrownianSharp.SheetProjection

/-- On any finite grid, the actual integrated sheet is the sum of its
orthogonal finite-source projection and an independent Gaussian residual.
The deterministic feature is the exact integrated Brownian feature; its
ambient image is the corresponding Gamma-normalized tensor RL kernel. -/
theorem integratedSheet_finiteGrid_orthogonal_decomposition
    {d : ℕ} {Ω I J : Type*} [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ)
    (e : I → brownianCubeBoxSpan d)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0)
    (x : J → BrownianCubeAnchor d) :
    ∃ W : IsonormalGaussianFamily (brownianCubeBoxSpan d) Ω (Sum I J) P,
      iIndepFun (fun i ω => W.eval (e i) ω) P ∧
      (∀ i, P.map (W.eval (e i)) = gaussianReal 0 1) ∧
      IndepFun (fun ω i => W.eval (e i) ω)
        (fun ω j => W.eval (integratedFeatureField m (x j) -
          projection e (integratedFeatureField m (x j))) ω) P ∧
      (∀ j, (fun ω => integrateSheetPath m (B.path ω) (x j)) =ᵐ[P]
        fun ω =>
          (∑ i, ⟪e i, integratedFeatureField m (x j)⟫ * W.eval (e i) ω) +
            W.eval (integratedFeatureField m (x j) -
              projection e (integratedFeatureField m (x j))) ω) ∧
      (∀ j, brownianCubeSpanEmbedding d (integratedFeatureField m (x j)) =
        unitCubeZeroExtendCLM d
          (tensorKernelFamily (fun i => (m i : ℝ) + 1)
            (by
              intro i
              have hm : 0 ≤ (m i : ℝ) := Nat.cast_nonneg _
              linarith)
            (x j))) := by
  classical
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Sum I J) B
  have hT_eval (z : BrownianCubeAnchor d) :
      brownianEvalToLp B z = T (featureVector z) := by
    rw [brownianEvalToLp_eq, ← hT z]
    apply congrArg T
    apply Subtype.ext
    rfl
  let X₀ : ContinuousIsonormalField P T := {
    path := B.path
    feature := ⟨featureVector, featureVector_continuous d⟩
    measurable_path := B.measurable_path
    eval_ae := by
      intro z
      have hmem : MemLp (B.eval z) 2 P := (B.eval_gaussian z).memLp_two
      have hrep : (fun ω => brownianEvalToLp B z ω) =ᵐ[P] B.eval z := by
        simpa [brownianEvalToLp] using hmem.coeFn_toLp
      have hclass : (fun ω => brownianEvalToLp B z ω) =ᵐ[P]
          fun ω => T (featureVector z) ω := by
        filter_upwards with ω
        exact congrArg (fun q : Lp ℝ 2 P => q ω) (hT_eval z)
      exact hrep.symm.trans hclass
    feature_norm_le_one := featureVector_norm_le_one
  }
  let X := integrateSheetIsonormalField m X₀
  have hpathAE (z : BrownianCubeAnchor d) :
      (fun ω => integrateSheetPath m (B.path ω) z) =ᵐ[P]
        fun ω => T (integratedFeatureField m z) ω := by
    have h := X.eval_ae z
    rw [integrateSheetIsonormalField_path] at h
    rw [integrateSheetIsonormalField_feature] at h
    simpa [X, X₀, integratedFeatureField, integrateSheetFeatureField] using h
  let K : J → brownianCubeBoxSpan d := fun j => integratedFeatureField m (x j)
  have hprocess (j : J) :
      (fun ω => integrateSheetPath m (B.path ω) (x j)) =ᵐ[P]
        fun ω => W.eval (K j) ω := by
    exact (hpathAE (x j)).trans (hW (K j)).symm
  refine ⟨W, coefficients_independent W e K he,
    (fun i => coefficient_standard_normal W e K he i),
    ?_, ?_, ?_⟩
  · simpa [K] using coefficients_residual_independent W e K he
  · intro j
    have hdecomp := eval_decomposition_ae W e (K j)
    filter_upwards [hprocess j, hdecomp] with ω hω hd
    calc
      integrateSheetPath m (B.path ω) (x j) = W.eval (K j) ω := hω
      _ = _ := hd
  · intro j
    rw [integrateSheetFeatureField_naturalTensor,
      naturalTensorFeature_eq_fractionalKernel]

end BrownianSharp.AlignmentGaussianIntegratedFiniteProjection
