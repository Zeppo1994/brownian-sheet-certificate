import BrownianSharp.SmoothResolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic

/-! Deterministic endpoint interface for the periodic Besov route.

This file records the exact summability obligation needed after a blockwise
decay/Young estimate.  It does not claim that the Gaussian coefficient-box
event or its block budget has been established; those analytic inputs remain
explicit in any downstream use.
-/

open scoped ENNReal
open MeasureTheory

namespace BrownianSharp

/-- A pointwise block envelope with the corresponding `ℓ^θ` budget puts the
actual ENNReal-parameter Besov ball in its literal smooth-resolution sense.
The `θ = ∞` branch is handled by its defining supremum condition. -/
theorem besovUnitBall_of_weightedBlockNorm_le_envelope
    {d : ℕ} (p : ℝ≥0∞) (r : ℝ) (θ : ℝ≥0∞)
    (f : BrownianSharp.Torus.RealPeriodic d)
    (hθ : 1 ≤ θ)
    (A : (Fin d → ℕ) → ℝ≥0∞)
    (hbudget : if θ = ∞ then (∀ s, A s ≤ 1) else
      ∑' s : Fin d → ℕ, (A s) ^ θ.toReal ≤ 1)
    (hblock : ∀ s, SmoothResolution.weightedBlockNorm p r s f ≤ A s) :
    SmoothResolution.BesovUnitBall p r θ f := by
  by_cases htop : θ = ∞
  · simp only [SmoothResolution.BesovUnitBall, htop, ↓reduceIte]
    have hA : ∀ s, A s ≤ 1 := by simpa [htop] using hbudget
    intro s
    exact (hblock s).trans (hA s)
  · simp only [SmoothResolution.BesovUnitBall, htop, ↓reduceIte]
    have hsum := hbudget
    simp only [htop, ↓reduceIte] at hsum
    calc
      ∑' s : Fin d → ℕ,
          (SmoothResolution.weightedBlockNorm p r s f) ^ θ.toReal ≤
        ∑' s : Fin d → ℕ, (A s) ^ θ.toReal := by
          apply ENNReal.tsum_le_tsum
          intro s
          have hθreal : 0 < θ.toReal := ENNReal.toReal_pos
            (ne_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ≥0∞) < 1) hθ)) htop
          exact (ENNReal.rpow_le_rpow_iff hθreal).2 (hblock s)
      _ ≤ 1 := hsum

/-- A pointwise bound for one smooth block controls its literal `L∞`
weighted block norm on the normalized torus. -/
theorem weightedBlockNorm_top_le_of_pointwise_bound
    {d : ℕ} (r : ℝ) (s : Fin d → ℕ)
    (f : BrownianSharp.Torus.RealPeriodic d) (B : ℝ)
    (hB : 0 ≤ B)
    (hbound : ∀ x : UnitAddTorus (Fin d),
      ‖SmoothResolution.block s f x‖ ≤ B) :
    SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r s f ≤
      ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (s i : ℝ)) * B) := by
  let μ : Measure (UnitAddTorus (Fin d)) := volume
  have hess : eLpNormEssSup (fun x => SmoothResolution.block s f x) μ ≤
      ENNReal.ofReal B :=
    eLpNormEssSup_le_of_ae_bound (ae_of_all μ hbound)
  have htop : eLpNorm (fun x => SmoothResolution.block s f x)
      (⊤ : ℝ≥0∞) μ ≤ ENNReal.ofReal B := by
    rw [eLpNorm_exponent_top
      (SmoothResolution.block s f).continuous.aestronglyMeasurable]
    exact hess
  unfold SmoothResolution.weightedBlockNorm
  calc
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) *
        ENNReal.ofReal B := mul_le_mul_of_nonneg_left htop bot_le
    _ = ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (s i : ℝ)) * B) := by
      rw [ENNReal.ofReal_mul (by positivity)]

end BrownianSharp
