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

end BrownianSharp
