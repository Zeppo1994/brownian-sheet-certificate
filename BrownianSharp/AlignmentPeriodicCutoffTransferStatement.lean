import BrownianSharp.AlignmentPeriodicCutoffClasses
import BrownianSharp.AlignmentOperatorStatements

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPeriodicCutoffTransferStatement
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.Torus
open BrownianSharp.AlignmentGaussianRates

def BesovScaleTransferStatement : Prop :=
  ∀ (φ ψ : AdmissibleCutoff) (d : ℕ) (p : ℝ≥0∞), 1 ≤ p →
    ∀ r : ℝ, 0 ≤ r → ∀ θ : ℝ≥0∞, 1 ≤ θ →
      ∃ c : ℝ, 0 < c ∧ ∀ f : RealPeriodic d,
        BesovUnitBall ψ p r θ f → BesovUnitBall φ p r θ (c • f)

def PeriodicMixedEntropyStatement : Prop :=
  ∀ (φ : AdmissibleCutoff) (d : ℕ), 2 ≤ d →
    ∀ p : ℝ≥0∞, 1 < p → ∀ r : ℝ, p.toReal⁻¹ < r →
      ∀ θ : ℝ≥0∞, 1 ≤ θ →
        ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
          (p ≠ ⊤ → ENNReal.ofReal (c * logarithmicIndexRate r
            (r * (d - 1 : ℕ) + 1 / 2) k) ≤
            HaarQuarter.TheoremD.entropyNumber k (Latest.periodicLInfinityImage
              {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f})) ∧
          ENNReal.ofReal (c * logarithmicIndexRate r
            ((r + 1 / 2 - θ.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) ≤
            HaarQuarter.TheoremD.entropyNumber k (Latest.periodicLInfinityImage
              {f : RealPeriodic d | BesovUnitBall φ p r θ f}) ∧
          ENNReal.ofReal (c * logarithmicIndexRate r
            ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) k) ≤
            HaarQuarter.TheoremD.entropyNumber k (Latest.periodicLInfinityImage
              {f : RealPeriodic d | NikolskyUnitBall φ p r f})

def PeriodicWidthStatement : Prop :=
  ∀ (φ : AdmissibleCutoff) (d : ℕ), 2 ≤ d →
    ∀ p : ℝ≥0∞, 2 ≤ p → ∀ r : ℝ, 1 / 2 < r →
      (p ≠ ⊤ → AlignmentOperatorStatements.twoSidedWidthRate
        (Latest.periodicLInfinityImage
          {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f})
        r (r * (d - 1 : ℕ) + 1 / 2)) ∧
      AlignmentOperatorStatements.twoSidedWidthRate
        (Latest.periodicLInfinityImage
          {f : RealPeriodic d | NikolskyUnitBall φ p r f})
        r ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2)

end BrownianSharp.AlignmentPeriodicCutoffTransferStatement
