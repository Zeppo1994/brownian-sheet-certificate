import BrownianSharp.SmoothGridConfinement
import BrownianSharp.CameronMartinNativeConfinement

/-! Actual finite periodic synthesis and its translated-ball cover obstruction. -/
set_option maxHeartbeats 1800000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp
open Torus HaarQuarter

/-- Continuous periodic native synthesis with the original layer indexing. -/
def periodicNativeSynthesisLinear {d n : ℕ} :
    (LayerIndex d n → ℝ) →ₗ[ℝ] RealPeriodic d where
  toFun x := ∑ a, x a • periodicNativeAtom a
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul, mul_comm]

theorem periodicNativeSynthesisLinear_apply {d n : ℕ}
    (x : LayerIndex d n → ℝ) (z : UnitAddTorus (Fin d)) :
    periodicNativeSynthesisLinear x z = smoothPeriodicSynthesis x z := by
  simp [periodicNativeSynthesisLinear, smoothPeriodicSynthesis]

theorem periodicNativeSynthesis_reindex_scaled {d n : ℕ}
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (A : ℝ) (x : Fin (Fintype.card (LayerIndex d n)) → ℝ) :
    PeriodicCover.gaussianSynthesis (fun i => A • periodicNativeAtom (e i)) x =
      A • periodicNativeSynthesisLinear (CameronMartinCover.reindexNative e x) := by
  change (∑ i, x i • (A • periodicNativeAtom (e i))) = _
  rw [show A • periodicNativeSynthesisLinear (CameronMartinCover.reindexNative e x) =
      ∑ a, A • (CameronMartinCover.reindexNative e x a • periodicNativeAtom a) by
        simp [periodicNativeSynthesisLinear, Finset.smul_sum]]
  apply Fintype.sum_equiv e
  intro i
  simp [CameronMartinCover.reindexNative, smul_smul, mul_comm]

end BrownianSharp
