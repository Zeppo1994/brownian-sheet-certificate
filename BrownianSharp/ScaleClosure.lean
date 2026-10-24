import BrownianSharp.Statement
import BrownianSharp.Interpolation

/-!
The complete all-radius closure for the literal Brownian target. The remaining
probabilistic work is displayed as `DiscreteSheetBound`; this reduction does
not assert that input or certify the sharp theorem unconditionally.
-/

open MeasureTheory

namespace BrownianSharp
open HaarQuarter

/-- The precise discrete full-sheet estimate still to be derived from the
native-layer covariance calculation and convex concentration. -/
def DiscreteSheetBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ (Ω : Type) [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : BrownianSheetOnCube d Ω P),
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, 2 * d ≤ N ∧
      ∀ n : ℕ, N ≤ n →
        P.real {ω | ‖B.path ω‖ ≤ sharpRadius d a n} ≤
          Real.exp (-b * nativeDimension d n)

/-- Once the discrete estimate is proved, no extra regularity assumption on
the unknown small-ball profile is needed for the ordinary-log sharp target. -/
theorem discreteSheetBound_implies_sharpLog (hDiscrete : DiscreteSheetBound) :
    SharpLogStatement := by
  intro d hd Ω _ P _ B
  obtain ⟨a, b, ha, hb, N, hN, hdiscrete⟩ := hDiscrete d hd Ω P B
  let c : ℝ := ((a ^ 2 / (Nat.factorial (d - 1) : ℝ) ^ 2) * b /
      (2 * (1 + |Real.log a|) ^ (2 * (d - 1) + 1)))
  let ε₀ : ℝ := min (sharpRadius d a N) (Real.exp (-2))
  have hc : 0 < c := by dsimp [c]; positivity
  have hNpos : 0 < N := by omega
  have hRadius : 0 < sharpRadius d a N := sharpRadius_pos hd ha hNpos
  have hε₀ : 0 < ε₀ := lt_min hRadius (Real.exp_pos _)
  have hε₀bound : ε₀ < Real.exp (-1) := by
    exact (min_le_right _ _).trans_lt (Real.exp_lt_exp.mpr (by norm_num))
  refine ⟨c, ε₀, hc, hε₀, hε₀bound, ?_⟩
  intro ε hε hsmall
  have hεle1 : ε ≤ 1 := by
    have hexp : Real.exp (-2) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    exact hsmall.trans ((min_le_right _ _).trans hexp)
  have hεN : ε ≤ sharpRadius d a N := hsmall.trans (min_le_left _ _)
  have hscale : ∀ n : ℕ, (N : ℝ) ≤ n →
      b * nativeDimension d n ≤
        -Real.log (P.real {ω | ‖B.path ω‖ ≤ sharpRadius d a n}) := by
    intro n hn
    have hnNat : N ≤ n := by exact_mod_cast hn
    have hrpos := sharpRadius_pos hd ha (lt_of_lt_of_le hNpos hnNat)
    have hp := B.smallBall_probability_pos hrpos
    have hlog := Real.log_le_log hp (hdiscrete n hnNat)
    rw [Real.log_exp] at hlog
    linarith
  have hresult := discrete_bound_implies_sharp
    (fun r => -Real.log (P.real {ω | ‖B.path ω‖ ≤ r})) hd hN ha hb
    hscale (fun _ _ hx hxy => smallBall_profile_antitone B hx hxy)
    hε hεle1 hεN
  have hexponent : 2 * (d - 1) + 1 = 2 * d - 1 := by omega
  simpa [c, sharpRate, hexponent, mul_assoc] using hresult

/-- Probability and ordinary-log forms follow from the same discrete input. -/
theorem discreteSheetBound_implies_sharpProbability (hDiscrete : DiscreteSheetBound) :
    SharpProbabilityStatement :=
  sharp_statements_iff.mpr (discreteSheetBound_implies_sharpLog hDiscrete)

end BrownianSharp
