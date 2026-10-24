import BrownianSharp.Statement

/-! Uniform-constant versions of the Brownian sheet targets. The constants are
chosen from the dimension before quantifying over the probability-space
realization of the sheet. The older `SharpLogStatement` and
`SharpProbabilityStatement` remain available for compatibility. -/

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

/-- The equivalent dimension-uniform probability form. -/
def UniformSharpProbabilityStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : BrownianSheetOnCube d Ω P) (ε : ℝ),
      0 < ε → ε ≤ ε₀ →
        P.real {ω | ‖B.path ω‖ ≤ ε} ≤ Real.exp (-c * sharpRate d ε)

theorem uniformSharp_statements_iff :
    UniformSharpProbabilityStatement ↔ UniformSharpLogStatement := by
  constructor
  · intro h d hd
    obtain ⟨c, ε₀, hc, hε₀, hsmall, hbound⟩ := h d hd
    refine ⟨c, ε₀, hc, hε₀, hsmall, ?_⟩
    intro Ω _ P _ B ε hε hε₀'
    exact (probability_bound_iff_log_bound B ε c hε).mp
      (hbound Ω P B ε hε hε₀')
  · intro h d hd
    obtain ⟨c, ε₀, hc, hε₀, hsmall, hbound⟩ := h d hd
    refine ⟨c, ε₀, hc, hε₀, hsmall, ?_⟩
    intro Ω _ P _ B ε hε hε₀'
    exact (probability_bound_iff_log_bound B ε c hε).mpr
      (hbound Ω P B ε hε hε₀')

end BrownianSharp
