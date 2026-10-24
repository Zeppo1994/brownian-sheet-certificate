import BrownianSharp.BrownianSheetCopyDifferenceLaw
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic

/-!
The literal target of the independent Brownian certificate.  This module
reuses the continuous Brownian-sheet interface and positivity proof from the
existing certificate.  Defining a target does not prove it.
-/

open MeasureTheory

namespace BrownianSharp

open HaarQuarter

/-- Proposed sharp rate, with natural exponent `2*d-1`. -/
noncomputable def sharpRate (d : ℕ) (ε : ℝ) : ℝ :=
  ε⁻¹ ^ 2 * (Real.log ε⁻¹) ^ (2 * d - 1)

/-- The intended probability statement, with no analytic theorem as a premise. -/
def SharpProbabilityStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSheetOnCube d Ω P),
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        P.real {ω | ‖B.path ω‖ ≤ ε} ≤ Real.exp (-c * sharpRate d ε)

/-- The intended ordinary negative-log statement. -/
def SharpLogStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSheetOnCube d Ω P),
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        c * sharpRate d ε ≤ -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε})

/-- Reuse the existing theorem ensuring this is an ordinary real logarithm
of a strictly positive small-ball probability. -/
theorem probability_bound_iff_log_bound
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (B : BrownianSheetOnCube d Ω P)
    (ε c : ℝ) (hε : 0 < ε) :
    (P.real {ω | ‖B.path ω‖ ≤ ε} ≤ Real.exp (-c * sharpRate d ε)) ↔
      c * sharpRate d ε ≤ -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε}) := by
  have hp := B.smallBall_probability_pos hε
  rw [← Real.log_le_log_iff hp (Real.exp_pos _), Real.log_exp]
  constructor <;> intro h <;> linarith

/-- The negative-log profile is antitone in the radius. Positivity, needed
for monotonicity of the ordinary logarithm, comes from existing machinery. -/
theorem smallBall_profile_antitone
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (B : BrownianSheetOnCube d Ω P)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    -Real.log (P.real {ω | ‖B.path ω‖ ≤ y}) ≤
      -Real.log (P.real {ω | ‖B.path ω‖ ≤ x}) := by
  have hp := B.smallBall_probability_pos hx
  have hprob : P.real {ω | ‖B.path ω‖ ≤ x} ≤ P.real {ω | ‖B.path ω‖ ≤ y} := by
    exact measureReal_mono (fun ω hω => hω.trans hxy) (by finiteness)
  exact neg_le_neg (Real.log_le_log hp hprob)

/-- The two literal sharp targets are equivalent, using positivity of the
original full sheet rather than an extended-log convention. -/
theorem sharp_statements_iff : SharpProbabilityStatement ↔ SharpLogStatement := by
  constructor
  · intro h d hd Ω _ P _ B
    obtain ⟨c, ε₀, hc, hε₀, hε₀small, hbound⟩ := h d hd Ω P B
    refine ⟨c, ε₀, hc, hε₀, hε₀small, ?_⟩
    intro ε hε hsmall
    exact (probability_bound_iff_log_bound B ε c hε).mp (hbound ε hε hsmall)
  · intro h d hd Ω _ P _ B
    obtain ⟨c, ε₀, hc, hε₀, hε₀small, hbound⟩ := h d hd Ω P B
    refine ⟨c, ε₀, hc, hε₀, hε₀small, ?_⟩
    intro ε hε hsmall
    exact (probability_bound_iff_log_bound B ε c hε).mpr (hbound ε hε hsmall)

end BrownianSharp
