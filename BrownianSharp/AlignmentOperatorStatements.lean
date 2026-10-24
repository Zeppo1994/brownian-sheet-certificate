import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.AlignmentOperatorNumbers

/-!
Literal main targets for the externally revised operator-number manuscript.
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

def CameronMartinEntropyWidthStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧
    0 < t₀ ∧ t₀ < Real.exp (-1) ∧
    (∀ t : ℝ, 0 < t → t ≤ t₀ →
      Metric.externalCoveringNumber t.toNNReal (CameronMartin.KdUnitCube d) ≠ ⊤ ∧
      c * cmCoveringRate d t ≤ logCoveringNumber (CameronMartin.KdUnitCube d) t ∧
      logCoveringNumber (CameronMartin.KdUnitCube d) t ≤ C * cmCoveringRate d t) ∧
    ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * cmIndexRate d k) ≤ entropyNumber k (CameronMartin.KdUnitCube d) ∧
      entropyNumber k (CameronMartin.KdUnitCube d) ≤ ENNReal.ofReal (C * cmIndexRate d k) ∧
      ENNReal.ofReal (c * cmIndexRate d k) ≤ AlignmentOperatorNumbers.operatorKolmogorovNumber (CameronMartin.KdUnitCube d) k ∧
      AlignmentOperatorNumbers.operatorKolmogorovNumber (CameronMartin.KdUnitCube d) k ≤ ENNReal.ofReal (C * cmIndexRate d k)

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

def FractionalEntropyWidthStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ a : Fin d → ℝ, (∀ i, 1/2 < a i) →
    ∀ r : ℝ, ∀ ν : ℕ, 2 ≤ ν → minimumMultiplicity a r ν →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*logarithmicIndexRate r (r*(ν-1:ℕ)+1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k (fractionalIntegrationBall a) ∧
      HaarQuarter.TheoremD.entropyNumber k (fractionalIntegrationBall a) ≤
        ENNReal.ofReal (C*logarithmicIndexRate r (r*(ν-1:ℕ)+1/2) k) ∧
      ENNReal.ofReal (c*logarithmicIndexRate r (r*(ν-1:ℕ)+1/2) k) ≤
        AlignmentOperatorNumbers.operatorKolmogorovNumber (fractionalIntegrationBall a) k ∧
      AlignmentOperatorNumbers.operatorKolmogorovNumber (fractionalIntegrationBall a) k ≤
        ENNReal.ofReal (C*logarithmicIndexRate r (r*(ν-1:ℕ)+1/2) k)

def LatestMainResultsStatement : Prop :=
  CameronMartinEntropyWidthStatement ∧
  PeriodicMixedEntropyStatement ∧ PeriodicWidthStatement ∧
  FractionalEntropyWidthStatement ∧
  Latest.BrownianTwoSidedStatement ∧ Latest.FractionalSheetStatement ∧
  Latest.IntegratedSheetStatement

end BrownianSharp.AlignmentOperatorStatements
