import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
import BrownianSharp.DyadicRealCells

/-! Deterministic integrated one-dimensional Haar tents. -/

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace HaarQuarter

/-- Continuous positive-part version of the midpoint tent. -/
noncomputable def continuousIntegratedTent (a b x : ℝ) : ℝ :=
  max 0 (min (x - a) (b - x))

@[fun_prop]
theorem continuous_continuousIntegratedTent (a b : ℝ) :
    Continuous (continuousIntegratedTent a b) := by
  unfold continuousIntegratedTent
  fun_prop

end HaarQuarter
