import BrownianSharp.Statement

/-! Uniform-constant versions of the Brownian sheet targets. The constants are
chosen from the dimension before quantifying over the probability-space
realization of the sheet. -/

open MeasureTheory

namespace BrownianSharp
open HaarQuarter

/-- The manuscript-strength ordinary-log bound: dimension-only constants
work for every realization of a Brownian sheet on the cube. -/
def UniformSharpLogStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : BrownianSheetOnCube d Ω P) (ε : ℝ),
      0 < ε → ε ≤ ε₀ →
        c * sharpRate d ε ≤ -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε})

end BrownianSharp
