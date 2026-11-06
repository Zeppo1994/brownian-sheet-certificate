import BrownianSharp.GaussianUniformEvent
import BrownianSharp.CameronMartinRate
import BrownianSharp.ExtendedStatements

/-! Exact coefficient reindexing and scale identification for applying the
native confinement estimate to the Cameron--Martin entropy cover. -/
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp
open HaarQuarter

/-- Reindexing the actual coefficient Gaussian preserves its full law. -/
theorem reindexNative_measurePreserving {d n : ℕ}
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n) :
    MeasurePreserving (CameronMartinCover.reindexNative e)
      (productStandardGaussian (Fin (Fintype.card (LayerIndex d n))))
      (productStandardGaussian (LayerIndex d n)) := by
  have hf : CameronMartinCover.reindexNative e =
      (MeasurableEquiv.piCongrLeft (fun _ : LayerIndex d n => ℝ) e) := by
    funext x a
    simp [CameronMartinCover.reindexNative, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft, Equiv.piCongrLeft']
  rw [hf]
  exact measurePreserving_piCongrLeft (α := fun _ : LayerIndex d n => ℝ)
    (fun _ => gaussianReal 0 1) e

end BrownianSharp
