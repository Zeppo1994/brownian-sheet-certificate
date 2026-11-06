import BrownianSharp.CameronMartin
import BrownianSharp.NativeProjection
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import BrownianSharp.IndependentComparison
import BrownianSharp.ProbabilisticCover
import BrownianSharp.Statistics
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic

/-!
# Cameron--Martin covering lower bound from native confinement

A finite native Haar coefficient ball has substantial standard-Gaussian mass and maps into the
actual restricted-cube Cameron--Martin image.  Anderson's inequality bounds every translated
finite-grid path ball by the centered confinement probability.  The resulting entropy lower
bound is conditional only on that explicit confinement estimate.
-/

noncomputable section

open MeasureTheory ProbabilityTheory HaarQuarter
open scoped BigOperators NNReal ENNReal RealInnerProductSpace

namespace BrownianSharp.CameronMartinCover

/-- Reindex a standard coefficient vector by a finite equivalence to the native layer. -/
def reindexNative {d n : ℕ} (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (x : Fin (Fintype.card (LayerIndex d n)) → ℝ) : LayerIndex d n → ℝ :=
  fun a => x (e.symm a)

end BrownianSharp.CameronMartinCover
