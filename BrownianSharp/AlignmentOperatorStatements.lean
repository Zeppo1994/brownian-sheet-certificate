import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.AlignmentOperatorNumbers

/-!
Literal operator-number targets of the manuscript.
Operator Kolmogorov numbers allow dimension strictly less than their index;
periodic entropy is measured in the actual L-infinity ambient space.
The actual image balls and concrete smooth resolution are retained.
-/
noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators ENNReal
namespace BrownianSharp.AlignmentOperatorStatements
open BrownianSharp.AlignmentGaussianRates
open HaarQuarter.TheoremD
open BrownianSharp.Latest (minimumMultiplicity fractionalIntegrationBall periodicLInfinityImage)

def periodicEmbeddingEntropy {d : ℕ} (k : ℕ) (K : Set (Torus.RealPeriodic d)) : ℝ≥0∞ :=
  HaarQuarter.TheoremD.entropyNumber k (Latest.periodicLInfinityImage K)

/-- Theorem 4.1: all three mixed-smoothness entropy lower bounds, with one
common constant and threshold for each displayed parameter tuple. -/

def PeriodicMixedEntropyStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ p : ENNReal, 1 < p →
    ∀ r : ℝ, p.toReal⁻¹ < r → ∀ θ : ENNReal, 1 ≤ θ →
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      (p ≠ ⊤ → ENNReal.ofReal (c * logarithmicIndexRate r
        (r*(d-1:ℕ)+1/2) k) ≤ periodicEmbeddingEntropy k
          {f : Torus.RealPeriodic d | SmoothResolution.SobolevUnitBall p.toReal r f}) ∧
      ENNReal.ofReal (c * logarithmicIndexRate r
        ((r+1/2-θ.toReal⁻¹)*(d-1:ℕ)+1/2) k) ≤
          periodicEmbeddingEntropy k
            {f : Torus.RealPeriodic d | SmoothResolution.BesovUnitBall p r θ f} ∧
      ENNReal.ofReal (c * logarithmicIndexRate r
        ((r+1/2)*(d-1:ℕ)+1/2) k) ≤
          periodicEmbeddingEntropy k
            {f : Torus.RealPeriodic d | SmoothResolution.NikolskyUnitBall p r f}

def twoSidedWidthRate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (r a : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
    ENNReal.ofReal (c*logarithmicIndexRate r a k) ≤
      AlignmentOperatorNumbers.operatorKolmogorovNumber K k ∧
    AlignmentOperatorNumbers.operatorKolmogorovNumber K k ≤
      ENNReal.ofReal (C*logarithmicIndexRate r a k)

def PeriodicWidthStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ p : ENNReal, 2 ≤ p → ∀ r : ℝ, 1/2 < r →
    (p ≠ ⊤ → twoSidedWidthRate
      (periodicLInfinityImage {f : Torus.RealPeriodic d |
        SmoothResolution.SobolevUnitBall p.toReal r f}) r (r*(d-1:ℕ)+1/2)) ∧
    twoSidedWidthRate
      (periodicLInfinityImage {f : Torus.RealPeriodic d |
        SmoothResolution.NikolskyUnitBall p r f}) r ((r+1/2)*(d-1:ℕ)+1/2)

end BrownianSharp.AlignmentOperatorStatements
