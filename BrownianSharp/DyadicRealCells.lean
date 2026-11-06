import BrownianSharp.DyadicDigitBridge
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open MeasureTheory

namespace HaarQuarter

noncomputable def realDyadicCell (l c : ℕ) : Set ℝ :=
  Set.Ico ((c : ℝ) / (2 : ℝ) ^ l) (((c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ l)

noncomputable def realDyadicLeftHalf (l c : ℕ) : Set ℝ :=
  Set.Ico ((2 * c : ℕ) / (2 : ℝ) ^ (l + 1))
    (((2 * c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (l + 1))

noncomputable def realDyadicRightHalf (l c : ℕ) : Set ℝ :=
  Set.Ico (((2 * c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (l + 1))
    (((2 * c + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (l + 1))

end HaarQuarter
