import BrownianSharp.PeriodicCover
import BrownianSharp.SmoothLayer

/-! Exact identification of the periodized smooth native atoms with the
finite midpoint samples used in the covariance calculation. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp
open BrownianSharp.Torus

/-- The same native Haar rectangle addresses specify the smooth tensor atoms. -/
def periodicNativeAtomIndex {d n : ℕ} (a : LayerIndex d n) : PeriodicCover.AtomIndex d where
  depth := layerIndexDepth a
  cell := layerIndexCell a
  valid := layerIndexCell_lt a

def periodicNativeAtom {d n : ℕ} (a : LayerIndex d n) : RealPeriodic d :=
  PeriodicCover.periodizedDyadicAtom (periodicNativeAtomIndex a)

theorem periodizedDyadicAtom1_unit_interval (s j : ℕ) (hj : j < 2 ^ s)
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    PeriodicCover.periodizedDyadicAtom1 s j hj (x : UnitAddCircle) =
      smoothAtom ((2 : ℝ) ^ s * x - (j : ℝ)) := by
  change AddCircle.liftIco (1 : ℝ) 0
    (fun y => smoothAtom ((2 : ℝ) ^ s * y - (j : ℝ))) (x : UnitAddCircle) = _
  exact AddCircle.liftIco_zero_coe_apply hx

end BrownianSharp
