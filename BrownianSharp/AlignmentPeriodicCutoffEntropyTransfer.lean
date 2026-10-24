import BrownianSharp.AlignmentPeriodicScaledClassTransfer
import BrownianSharp.AlignmentOperatorPeriodic

/-! Entropy-rate transfer from the certified concrete Besov balls.
This is a scaling lemma; an arbitrary-cutoff caller must discharge its
unit-ball inclusion rather than assuming norm equivalence. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPeriodicCutoffEntropyTransfer
open BrownianSharp.Torus
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentPeriodicScaledClassTransfer

theorem entropy_lower_of_scaled_besov_ball {d : ℕ} (hd : 2 ≤ d)
    (p : ℝ≥0∞) (hp : 1 < p) (r : ℝ) (hpr : p.toReal⁻¹ < r)
    (θ : ℝ≥0∞) (hθ : 1 ≤ θ) (J : Set (RealPeriodic d))
    (c : ℝ) (hc : 0 < c)
    (hball : ∀ f : RealPeriodic d,
      SmoothResolution.BesovUnitBall p r θ f → c • f ∈ J) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (C * logarithmicIndexRate r
        ((r + 1 / 2 - θ.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k (Latest.periodicLInfinityImage J) := by
  obtain ⟨C, hC, k₀, hk₀, hbase⟩ :=
    AlignmentOperatorPeriodic.periodic_mixed_entropy_certified d hd p hp r hpr θ hθ
  refine ⟨c * C, mul_pos hc hC, k₀, hk₀, ?_⟩
  intro k hk
  have hsub := scaled_periodicImage_subset J
    {f : RealPeriodic d | SmoothResolution.BesovUnitBall p r θ f} c hball
  have hsource := (hbase k hk).2.1
  change ENNReal.ofReal (C * logarithmicIndexRate r
    ((r + 1 / 2 - θ.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) ≤
      HaarQuarter.TheoremD.entropyNumber k
        (Latest.periodicLInfinityImage
          {f : RealPeriodic d | SmoothResolution.BesovUnitBall p r θ f}) at hsource
  have h := entropyNumber_ge_of_scaled_subset
    (Latest.periodicLInfinityImage J)
    (Latest.periodicLInfinityImage
      {f : RealPeriodic d | SmoothResolution.BesovUnitBall p r θ f})
    c (C * logarithmicIndexRate r
      ((r + 1 / 2 - θ.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k)
    hc (mul_nonneg hC.le (AlignmentWidthRates.logarithmicIndexRate_nonneg _ _ _)) hsub k hsource
  simpa only [mul_assoc] using h

end BrownianSharp.AlignmentPeriodicCutoffEntropyTransfer
