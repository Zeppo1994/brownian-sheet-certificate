import BrownianSharp.SheetComparison
import BrownianSharp.NativeMatrix

/-! Compare the actual continuous Brownian sheet directly to product-Gaussian
native coefficients on an arbitrary deterministic finite midpoint subset. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp
open HaarQuarter

/-- The comparison retains the original full sheet and every residual mode. -/
theorem original_sheet_product_native_comparison
    {d n : ℕ} {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hd : 0 < d)
    (B : BrownianSheetOnCube d Ω P) (q : ι → MidpointGridIndex d n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P {ω | ‖B.path ω‖ ≤ ε} ≤
      productStandardGaussian (LayerIndex d n)
        {x | ∀ i, |∑ a, nativeLayerRowCoefficient (q i) a * x a| ≤ ε} := by
  classical
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let t := fun j => nativeMidpointBrownianAnchor (q (e j))
  obtain ⟨G, hG, hIndep, hLaw, hcomp⟩ :=
    original_sheet_native_grid_comparison (n := n) hd B t
  have hmap := native_coordinate_joint_law G hG hIndep hLaw
  let E : Set (LayerIndex d n → ℝ) :=
    {x | ∀ i, |∑ a, nativeLayerRowCoefficient (q i) a * x a| ≤ ε}
  have hE : MeasurableSet E := by
    dsimp [E]
    simpa only [Set.setOf_forall] using
      MeasurableSet.iInter (fun i : ι => measurableSet_le
        (by fun_prop : Measurable (fun x : LayerIndex d n → ℝ =>
          |∑ a, nativeLayerRowCoefficient (q i) a * x a|)) measurable_const)
  have hvec : Measurable (fun ω a => G a ω) := measurable_pi_lambda hG
  have hevent : {ω | ‖fun j : Fin (Fintype.card ι) => nativeLayerEvaluation G (t j) ω‖ ≤ ε} =
      (fun ω a => G a ω) ⁻¹' E := by
    ext ω
    rw [Set.mem_setOf_eq, pi_norm_le_iff_of_nonneg hε]
    change (∀ j, |nativeLayerEvaluation G (t j) ω| ≤ ε) ↔ _
    constructor
    · intro h i
      simpa [E, t, nativeLayerEvaluation, nativeBoxVector, nativeLayerRowCoefficient,
        nativeMidpointBrownianAnchor] using h (e.symm i)
    · intro h j
      simpa [E, t, nativeLayerEvaluation, nativeBoxVector, nativeLayerRowCoefficient,
        nativeMidpointBrownianAnchor] using h (e j)
  calc
    _ ≤ P {ω | ‖fun j : Fin (Fintype.card ι) => nativeLayerEvaluation G (t j) ω‖ ≤ ε} :=
      hcomp ε hε
    _ = P ((fun ω a => G a ω) ⁻¹' E) := congrArg P hevent
    _ = productStandardGaussian (LayerIndex d n) E := by
      change P ((fun ω a => G a ω) ⁻¹' E) =
        (Measure.pi (fun _ : LayerIndex d n => gaussianReal 0 1)) E
      rw [← hmap, Measure.map_apply hvec hE]

end BrownianSharp
