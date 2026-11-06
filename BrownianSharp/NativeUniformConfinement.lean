import BrownianSharp.NativeVarianceBound
import BrownianSharp.NativeStatisticProperties
import BrownianSharp.NativeScale
import BrownianSharp.EventualRates
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import BrownianSharp.Statement
import BrownianSharp.Interpolation
import BrownianSharp.CameronMartinCover

/-! Actual native Gaussian grid confinement, independent of the full-sheet
comparison, for the Cameron--Martin entropy application. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp
open HaarQuarter

/-- The literal unnormalized native coefficient field on its deterministic
good midpoint grid. -/
def nativeGoodUniformEvent (d n : ℕ) (ε : ℝ) : Set (LayerIndex d n → ℝ) :=
  {x | ∀ q : NativeGoodGrid d n,
    |∑ a, nativeLayerRowCoefficient q.val a * x a| ≤ ε}

end BrownianSharp
