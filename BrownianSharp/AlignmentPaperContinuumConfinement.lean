import BrownianSharp.AlignmentPaperContinuumHulls
import BrownianSharp.AlignmentPaperSupportedRows
import BrownianSharp.EventualRates

/-! The literal cube-field event and the normalized continuum-row event.
The variance estimate is an explicit intermediate input here; the separate
hull-shell argument must discharge it before an unconditional endpoint. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperContinuumConfinement
open AlignmentPaperContinuumGoodRegion AlignmentPaperContinuumHulls
open AlignmentPaperSpatialExponential AlignmentPaperSupportedRows

/-- The actual finite Gaussian atom synthesis, evaluated on the real cube. -/
def cubeSynthesis {d n : ℕ} (z : LayerIndex d n → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ a : LayerIndex d n, smoothCubeAtom x a * z a

end BrownianSharp.AlignmentPaperContinuumConfinement
