import BrownianSharp.HaarGridCoordinates
import BrownianSharp.NativeProjection
import BrownianSharp.SheetProjection
import BrownianSharp.GaussianGridStatistics

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentEndpointGaussianHaarLaw

open BrownianSharp BrownianSharp.CameronMartin BrownianSharp.GaussianProjection
open BrownianSharp.SheetProjection
open HaarQuarter

/-- The unscaled finite-Haar coefficient row at an endpoint-grid point. -/
def unscaledHaarGridRow {d M : ℕ}
    (z : FiniteHaarIndex d M → ℝ) (j : CubeDyadicGrid d M) : ℝ :=
  ∑ a, z a * ⟪finiteHaarVector a, featureVector (cubeDyadicAnchor j)⟫

/-- The actual Brownian-sheet values on a finite dyadic endpoint grid have
exactly the joint law of the independent finite-Haar Gaussian row vector.
The proof uses the exact finite Haar expansion of each grid feature, so the
orthogonal residual vanishes at every grid point. -/
theorem brownian_grid_event_eq_product_gaussian
    {d M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (ε : ℝ) :
    P {ω | ∀ j : CubeDyadicGrid d M,
        |B.eval (cubeDyadicAnchor j) ω| ≤ ε} =
      productStandardGaussian (FiniteHaarIndex d M)
        {z | ∀ j : CubeDyadicGrid d M, |unscaledHaarGridRow z j| ≤ ε} := by
  classical
  let I := FiniteHaarIndex d M
  let J := CubeDyadicGrid d M
  let e : I → brownianCubeBoxSpan d := finiteHaarVector
  let box : J → brownianCubeBoxSpan d := fun j => featureVector (cubeDyadicAnchor j)
  have hcard : Fintype.card I = (2^M)^d := finiteHaarIndex_card_grid d M
  letI : Nonempty I := Fintype.card_pos_iff.mp (by rw [hcard]; positivity)
  have he : ∀ a b : I, ⟪e a, e b⟫ = if a=b then 1 else 0 := by
    intro a b
    exact finiteHaarVector_orthonormal a b
  obtain ⟨T,W,hT,hW⟩ := brownianSheetCube_exists_isonormal (ι := Sum I J) B
  let G : I → Ω → ℝ := fun a ω => W.eval (e a) ω
  have hG : ∀ a, Measurable (G a) := by
    intro a
    exact W.measurable_eval (e a)
  have hIndep : iIndepFun G P :=
    coefficients_independent W e box he
  have hLaw : ∀ a, P.map (G a) = gaussianReal 0 1 := by
    intro a
    exact coefficient_standard_normal W e box he a
  have hvecLaw : P.map (fun ω a => G a ω) = productStandardGaussian I := by
    rw [hIndep.map_fun_eq_pi_map (fun a => (hG a).aemeasurable)]
    congr 1
    funext a
    exact hLaw a
  have hbox (j : J) :
      (fun ω => W.eval (box j) ω) =ᵐ[P] (fun ω => B.eval (cubeDyadicAnchor j) ω) := by
    apply (hW (box j)).trans
    change (fun ω => T ⟨brownianSheetBoxIndicatorLp (cubeDyadicAnchor j).val,
      brownianCubeBoxIndicator_mem (cubeDyadicAnchor j)⟩ ω) =ᵐ[P]
        (fun ω => B.eval (cubeDyadicAnchor j) ω)
    rw [hT (cubeDyadicAnchor j)]
    exact ((B.gaussian.hasGaussianLaw_eval (cubeDyadicAnchor j)).memLp_two).coeFn_toLp
  have hprojection (j : J) : projection e (box j) = box j := by
    have hexp := grid_feature_eq_finite_haar_sum hcard j
    have hexp' : box j = ∑ a : I, ⟪e a, box j⟫ • e a := by
      calc
        box j = ∑ a : I, ⟪featureVector (cubeDyadicAnchor j), finiteHaarVector a⟫ •
            finiteHaarVector a := hexp
        _ = ∑ a : I, ⟪finiteHaarVector a, featureVector (cubeDyadicAnchor j)⟫ •
            finiteHaarVector a := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [real_inner_comm]
        _ = ∑ a : I, ⟪e a, box j⟫ • e a := by rfl
    unfold projection
    exact hexp'.symm
  have hrow (j : J) :
      (fun ω => B.eval (cubeDyadicAnchor j) ω) =ᵐ[P]
        (fun ω => unscaledHaarGridRow (fun a => G a ω) j) := by
    have heval := SheetProjection.eval_projection_ae W e (box j)
    have heval' : (fun ω => W.eval (box j) ω) =ᵐ[P]
        (fun ω => ∑ a, ⟪e a, box j⟫ * W.eval (e a) ω) := by
      filter_upwards [heval] with ω hω
      simpa [hprojection j] using hω
    filter_upwards [hbox j, heval'] with ω hb hr
    have h := hb.symm.trans hr
    convert h using 1 <;> simp only [unscaledHaarGridRow, G, e, box, featureVector]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  have hrowAll :
      (fun ω => fun j : J => B.eval (cubeDyadicAnchor j) ω) =ᵐ[P]
        (fun ω => fun j : J => unscaledHaarGridRow (fun a => G a ω) j) := by
    have hall := ae_all_iff.mpr hrow
    filter_upwards [hall] with ω hω
    funext j
    exact hω j
  let E : Set (I → ℝ) :=
    {z | ∀ j : J, |unscaledHaarGridRow z j| ≤ ε}
  have hE : MeasurableSet E := by
    dsimp [E]
    simpa only [Set.setOf_forall] using
      MeasurableSet.iInter (fun j : J => measurableSet_le
        (by unfold unscaledHaarGridRow; fun_prop : Measurable
          (fun z : I → ℝ => |unscaledHaarGridRow z j|))
        measurable_const)
  have hvec : Measurable (fun ω a => G a ω) := measurable_pi_lambda hG
  have hevent :
      {ω | ∀ j : J, |B.eval (cubeDyadicAnchor j) ω| ≤ ε} =ᵐ[P]
        (fun ω a => G a ω) ⁻¹' E := by
    filter_upwards [hrowAll] with ω hω
    change ((∀ j : J, |B.eval (cubeDyadicAnchor j) ω| ≤ ε) =
      (∀ j : J, |unscaledHaarGridRow (fun a => G a ω) j| ≤ ε))
    apply propext
    constructor
    · intro hh j
      rw [← congrFun hω j]
      exact hh j
    · intro hh j
      rw [congrFun hω j]
      exact hh j
  calc
    P {ω | ∀ j : J, |B.eval (cubeDyadicAnchor j) ω| ≤ ε} =
        P ((fun ω a => G a ω) ⁻¹' E) := measure_congr hevent
    _ = productStandardGaussian I E := by
      calc
        P ((fun ω a => G a ω) ⁻¹' E) = (P.map (fun ω a => G a ω)) E :=
          (Measure.map_apply hvec hE).symm
        _ = productStandardGaussian I E := by rw [hvecLaw]

end BrownianSharp.AlignmentEndpointGaussianHaarLaw
