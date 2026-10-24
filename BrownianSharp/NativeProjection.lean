import BrownianSharp.Projection
import BrownianSharp.SheetProjection
import Mathlib.Probability.Independence.Basic

/-!
The actual grade-n Brownian layer on the original probability space. Native
indices, dyadic orthonormality, and the continuous-sheet isonormal constructor
are connected here, retaining every nonselected mode in the residual.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp
open HaarQuarter

/-- The exact anchored-box vector, in the already formalized sheet domain. -/
noncomputable def nativeBoxVector {d : ℕ} (t : BrownianCubeAnchor d) :
    brownianCubeBoxSpan d :=
  ⟨brownianSheetBoxIndicatorLp t.val, brownianCubeBoxIndicator_mem t⟩

/-- Evaluate a finite native layer from its actual standard normal coordinates. -/
noncomputable def nativeLayerEvaluation {d n : ℕ} {Ω : Type*}
    (G : LayerIndex d n → Ω → ℝ) (t : BrownianCubeAnchor d) (ω : Ω) : ℝ :=
  ∑ a, ⟪nativeLayerVector a, nativeBoxVector t⟫ * G a ω

theorem nativeLayerIndex_nonempty (d n : ℕ) (hd : 0 < d) :
    Nonempty (LayerIndex d n) := by
  apply Fintype.card_pos_iff.mp
  rw [layerIndex_card d n hd]
  exact Nat.mul_pos (by positivity) (Nat.choose_pos (by omega))

/-- The full original sheet supplies exactly D_n mutually independent
standard Gaussian native coefficients; its finite residual is independent of
the whole coefficient vector. No covariance replacement or accepted gain
result enters this construction. -/
theorem original_sheet_native_layer
    {d n : ℕ} {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 0 < d) (B : BrownianSheetOnCube d Ω P)
    (t : J → BrownianCubeAnchor d) :
    ∃ G : LayerIndex d n → Ω → ℝ,
      (∀ a, Measurable (G a)) ∧ iIndepFun G P ∧
      (∀ a, P.map (G a) = gaussianReal 0 1) ∧
      IndepFun (fun ω a => G a ω)
        (fun ω j => B.eval (t j) ω - nativeLayerEvaluation G (t j) ω) P := by
  classical
  letI : Nonempty (LayerIndex d n) := nativeLayerIndex_nonempty d n hd
  obtain ⟨W, hIndep, hLaw, hResidual⟩ :=
    SheetProjection.original_sheet_projection B
      (nativeLayerVector (d := d) (n := n)) t nativeLayerVector_orthonormal
  refine ⟨fun a ω => W.eval (nativeLayerVector a) ω, ?_, hIndep, hLaw, ?_⟩
  · intro a
    exact W.measurable_eval _
  · exact hResidual

/-- The independent native coordinate vector has the literal product standard
Gaussian measure used in finite-dimensional concentration, with no law left
as an analytic hypothesis. -/
theorem native_coordinate_joint_law
    {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : LayerIndex d n → Ω → ℝ)
    (hG : ∀ a, Measurable (G a)) (hindep : iIndepFun G P)
    (hlaw : ∀ a, P.map (G a) = gaussianReal 0 1) :
    P.map (fun ω a => G a ω) =
      Measure.pi (fun _ : LayerIndex d n => gaussianReal 0 1) := by
  rw [hindep.map_fun_eq_pi_map (fun a => (hG a).aemeasurable)]
  congr 1
  funext a
  exact hlaw a

end BrownianSharp
