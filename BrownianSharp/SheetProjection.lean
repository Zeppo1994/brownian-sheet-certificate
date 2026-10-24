import BrownianSharp.GaussianProjection
import BrownianSharp.BrownianSheetCubeIsonormal
import BrownianSharp.BrownianCriticalResidual

/-!
Finite orthogonal projection of the original continuous Brownian sheet.
The source sheet and all nonselected modes are retained. No claim about
confinement probability is made by this linear/Gaussian construction.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.SheetProjection
open HaarQuarter
open GaussianProjection

/-- Finite linearity is inherited from the existing stochastic-integral
linearity theorem, with all equalities interpreted almost surely. -/
theorem eval_sum_ae {H Ω K A : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype K] [Nonempty K] [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    (W : IsonormalGaussianFamily H Ω K P) (f : A → H) (s : Finset A) :
    (fun ω => W.eval (∑ i ∈ s, f i) ω) =ᵐ[P]
      (fun ω => ∑ i ∈ s, W.eval (f i) ω) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := isonormal_eval_smul_ae W (0 : H) 0
    simpa using h
  | @insert a s ha ih =>
    have hadd := isonormal_eval_add_ae W (f a) (∑ i ∈ s, f i)
    filter_upwards [hadd, ih] with ω hω hi
    simpa [Finset.sum_insert ha, hi] using hω

/-- The finite projection is exactly the linear combination of its actual
Gaussian coordinates, rather than merely a covariance surrogate. -/
theorem eval_projection_ae {H Ω K I : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype K] [Nonempty K] [Fintype I] [DecidableEq I]
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (W : IsonormalGaussianFamily H Ω K P) (e : I → H) (v : H) :
    (fun ω => W.eval (projection e v) ω) =ᵐ[P]
      (fun ω => ∑ i, ⟪e i, v⟫ * W.eval (e i) ω) := by
  have hsum := eval_sum_ae W (fun i => ⟪e i, v⟫ • e i) Finset.univ
  have hsmul : ∀ᵐ ω ∂P, ∀ i : I,
      W.eval (⟪e i, v⟫ • e i) ω = ⟪e i, v⟫ * W.eval (e i) ω := by
    exact ae_all_iff.mpr (fun i => isonormal_eval_smul_ae W (e i) ⟪e i, v⟫)
  filter_upwards [hsum, hsmul] with ω hs hm
  rw [projection, hs]
  apply Finset.sum_congr rfl
  intro i hi
  exact hm i

/-- Exact original-coordinate decomposition into the selected Gaussian
layer and its independent isonormal residual. -/
theorem eval_decomposition_ae {H Ω K I : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype K] [Nonempty K] [Fintype I] [DecidableEq I]
    [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (W : IsonormalGaussianFamily H Ω K P) (e : I → H) (v : H) :
    (fun ω => W.eval v ω) =ᵐ[P]
      (fun ω => (∑ i, ⟪e i, v⟫ * W.eval (e i) ω) +
        W.eval (v - projection e v) ω) := by
  have hadd := isonormal_eval_add_ae W (v - projection e v) (projection e v)
  have hproj := eval_projection_ae W e v
  filter_upwards [hadd, hproj] with ω ha hp
  have hid : (v - projection e v) + projection e v = v := sub_add_cancel _ _
  rw [hid, hp] at ha
  linarith

/-- The original full continuous sheet admits the finite orthogonal layer
and an independent residual, on its original probability space. The only
geometric input is the displayed orthonormality of the selected vectors in
the existing anchored-box span. -/
theorem original_sheet_projection
    {d : ℕ} {Ω I J : Type*} [MeasurableSpace Ω]
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype J]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P)
    (e : I → brownianCubeBoxSpan d) (x : J → BrownianCubeAnchor d)
    (he : ∀ i k, ⟪e i, e k⟫ = if i = k then 1 else 0) :
    ∃ W : IsonormalGaussianFamily (brownianCubeBoxSpan d) Ω (Sum I J) P,
      iIndepFun (fun i ω => W.eval (e i) ω) P ∧
      (∀ i, P.map (W.eval (e i)) = gaussianReal 0 1) ∧
      IndepFun (fun ω i => W.eval (e i) ω)
        (fun ω j => B.eval (x j) ω -
          ∑ i, ⟪e i, (⟨brownianSheetBoxIndicatorLp (x j).val,
            brownianCubeBoxIndicator_mem (x j)⟩ : brownianCubeBoxSpan d)⟫ *
              W.eval (e i) ω) P := by
  classical
  let box : J → brownianCubeBoxSpan d := fun j =>
    ⟨brownianSheetBoxIndicatorLp (x j).val, brownianCubeBoxIndicator_mem (x j)⟩
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Sum I J) B
  have hbox (j : J) : W.eval (box j) =ᵐ[P] B.eval (x j) := by
    apply (hW (box j)).trans
    change (fun ω => T ⟨brownianSheetBoxIndicatorLp (x j).val, brownianCubeBoxIndicator_mem (x j)⟩ ω) =ᵐ[P] B.eval (x j)
    rw [hT (x j)]
    exact ((B.gaussian.hasGaussianLaw_eval (x j)).memLp_two).coeFn_toLp
  have hres (j : J) :
      (fun ω => W.eval (box j - projection e (box j)) ω) =ᵐ[P]
        (fun ω => B.eval (x j) ω - ∑ i, ⟪e i, box j⟫ * W.eval (e i) ω) := by
    filter_upwards [hbox j, eval_decomposition_ae W e (box j)] with ω hb hd
    linarith
  have hresAll :
      (fun ω j => W.eval (box j - projection e (box j)) ω) =ᵐ[P]
        (fun ω j => B.eval (x j) ω - ∑ i, ⟪e i, box j⟫ * W.eval (e i) ω) := by
    have h := ae_all_iff.mpr hres
    filter_upwards [h] with ω hω
    funext j
    exact hω j
  refine ⟨W, coefficients_independent W e box he, ?_, ?_⟩
  · intro i
    exact coefficient_standard_normal W e box he i
  · exact (coefficients_residual_independent W e box he).congr
      (Filter.Eventually.of_forall (fun _ => rfl)) hresAll

end BrownianSharp.SheetProjection
