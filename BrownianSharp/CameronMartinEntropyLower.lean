import BrownianSharp.CameronMartinCover
import BrownianSharp.PeriodicEntropy

/-!
# Native Cameron--Martin cover obstruction to dyadic entropy

This module composes the proved finite-grid Gaussian-cover argument with the
abstract dyadic entropy-number definition.  Its only analytic input is the
centered finite-grid confinement estimate stated in the theorem below.
-/

open MeasureTheory ProbabilityTheory HaarQuarter BrownianSharp
open BrownianSharp.CameronMartinCover
open scoped NNReal ENNReal

namespace BrownianSharp.CameronMartinEntropyLower

/-- The native Gaussian cutoff argument gives the exact dyadic entropy lower
bound at the corresponding uniform radius.  The confinement estimate remains
an explicit hypothesis; this theorem does not assert a small-ball bound. -/
theorem native_entropyNumber_ge_of_confinement
    {d n M k : ℕ} [Nonempty (LayerIndex d n)]
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (t : Fin M → HaarQuarter.BrownianCubeAnchor d)
    (ε : ℝ) (hε : 0 < ε) (q : ℝ≥0∞)
    (hconf : (Measure.pi
      (fun _ : Fin (Fintype.card (LayerIndex d n)) => ProbabilityTheory.gaussianReal 0 1))
      {x | ‖rowEvaluation (nativeGridMatrix e t) x‖ ≤ ε} ≤ q)
    (hmass : ((2 ^ (k - 1) : ℕ) : ℝ≥0∞) * q < (3 / 4 : ℝ≥0∞)) :
    ENNReal.ofNNReal (⟨ε / (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)), by positivity⟩ : ℝ≥0)
      ≤ HaarQuarter.TheoremD.entropyNumber k
        (CameronMartin.KdUnitCube d) := by
  have hcover := BrownianSharp.CameronMartinCover.nativeCameronMartin_externalCoveringNumber_gt e t ε hε q
    (2 ^ (k - 1)) hconf hmass
  have hcover' : ((2 ^ (k - 1) : ℕ) : ℕ∞) <
      Metric.externalCoveringNumber
        (⟨ε / (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)), by positivity⟩ : ℝ≥0)
        (CameronMartin.KdUnitCube d) := by
    simpa using hcover
  exact BrownianSharp.periodicEntropyNumber_ge_of_covering_gt k
    (CameronMartin.KdUnitCube d)
    ⟨ε / (2 * Real.sqrt (Fintype.card (LayerIndex d n) : ℝ)), by positivity⟩
    hcover'

end BrownianSharp.CameronMartinEntropyLower
