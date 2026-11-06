import BrownianSharp.SmoothGaussian
import BrownianSharp.ActualConcentration
import BrownianSharp.NativeShellSum
import BrownianSharp.GaussianPairMoments
import Mathlib.Probability.Moments.Covariance
import BrownianSharp.ShellVariance
import BrownianSharp.NativeStatisticProperties
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
import BrownianSharp.PeriodicNativeGrid

/-! The conditional smooth-grid confinement event is inherited by the full
finite periodic synthesis because its midpoint samples are exactly the rows
used in the covariance proof. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp
open BrownianSharp.Torus

/-- Finite periodic synthesis from the independent layer coordinates. -/
def smoothPeriodicSynthesis {d n : ℕ} (x : LayerIndex d n → ℝ)
    (z : UnitAddTorus (Fin d)) : ℝ :=
  ∑ a : LayerIndex d n, x a • periodicNativeAtom a z

end BrownianSharp
