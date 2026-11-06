import BrownianSharp.UniformSharpStatement
import BrownianSharp.GaussianEhrhardCertified
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

/-! Dimension-uniform constants for the literal Brownian-sheet event. All
scale constants are chosen before the probability-space realization; the
only random-object-dependent step is the already-proved projection comparison.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BrownianSharp
open HaarQuarter

/-- Uniform scale closure for all realizations of the original sheet. -/
theorem uniformSharpLog_of_uniformDiscreteSheetBound
    (hDiscrete : ∀ d : ℕ, 2 ≤ d → ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∃ N : ℕ, 2 * d ≤ N ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : BrownianSheetOnCube d Ω P) (n : ℕ), N ≤ n →
          P.real {ω | ‖B.path ω‖ ≤ sharpRadius d a n} ≤
            Real.exp (-b * nativeDimension d n)) :
    UniformSharpLogStatement := by
  intro d hd
  obtain ⟨a, b, ha, hb, N, hN, hdiscrete⟩ := hDiscrete d hd
  let c : ℝ := ((a ^ 2 / (Nat.factorial (d - 1) : ℝ) ^ 2) * b /
      (2 * (1 + |Real.log a|) ^ (2 * (d - 1) + 1)))
  let ε₀ : ℝ := min (sharpRadius d a N) (Real.exp (-2))
  have hc : 0 < c := by dsimp [c]; positivity
  have hNpos : 0 < N := by omega
  have hRadius : 0 < sharpRadius d a N := sharpRadius_pos hd ha hNpos
  have hε₀ : 0 < ε₀ := lt_min hRadius (Real.exp_pos _)
  have hε₀bound : ε₀ < Real.exp (-1) :=
    (min_le_right _ _).trans_lt (Real.exp_lt_exp.mpr (by norm_num))
  refine ⟨c, ε₀, hc, hε₀, hε₀bound, ?_⟩
  intro Ω _ P _ B ε hε hsmall
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
    have hlog := Real.log_le_log hp (hdiscrete Ω P B n hnNat)
    rw [Real.log_exp] at hlog
    linarith
  have hresult := discrete_bound_implies_sharp
    (fun r => -Real.log (P.real {ω | ‖B.path ω‖ ≤ r})) hd hN ha hb
    hscale (fun _ _ hx hxy => smallBall_profile_antitone B hx hxy)
    hε hεle1 hεN
  have hexponent : 2 * (d - 1) + 1 = 2 * d - 1 := by omega
  simpa [c, sharpRate, hexponent, mul_assoc] using hresult

end BrownianSharp

end
