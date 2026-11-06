import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
import BrownianSharp.DyadicRealCells

open MeasureTheory
open scoped BigOperators

namespace HaarQuarter

noncomputable def realDyadicLeft (r k : ℕ) : ℝ := (k : ℝ) / (2 : ℝ) ^ r

noncomputable def realDyadicMid (r k : ℕ) : ℝ := ((k : ℝ) + (1 / 2 : ℝ)) / (2 : ℝ) ^ r

noncomputable def realDyadicRight (r k : ℕ) : ℝ := ((k : ℝ) + 1) / (2 : ℝ) ^ r

end HaarQuarter
