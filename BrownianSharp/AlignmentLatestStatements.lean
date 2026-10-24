import BrownianSharp.ExtendedStatements
import BrownianSharp.AlignmentGaussianRates
import BrownianSharp.AlignmentFractionalKernel
import BrownianSharp.AlignmentContinuousLInfinity

/-!
# Literal targets for the latest Claude manuscript
These propositions state the new scope. Defining or checking a target does
not certify it; completion requires a proof of LatestMainResultsStatement.
The original three-result certificate remains separately named.
-/
noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators ENNReal
namespace BrownianSharp.Latest
open BrownianSharp.AlignmentGaussianRates

def minimumMultiplicity {d : ℕ} (a : Fin d → ℝ) (r : ℝ) (ν : ℕ) : Prop := by
  classical
  exact (∀ i, r ≤ a i) ∧ (Finset.univ.filter (fun i => a i=r)).card=ν

def fractionalTensorKernel {d : ℕ} (a : Fin d → ℝ)
    (t : BrownianCubeAnchor d) (u : Fin d → ℝ) : ℝ :=
  ∏ i, if u i < t.val i then
    (Real.Gamma (a i))⁻¹ * (t.val i-u i) ^ (a i-1) else 0

def fractionalIntegrationValue {d : ℕ} (a : Fin d → ℝ)
    (g : CameronMartin.UnitCubeL2 d) (t : BrownianCubeAnchor d) : ℝ :=
  ∫ u, fractionalTensorKernel a t u * g u
    ∂((Measure.pi fun _ : Fin d => (volume : Measure ℝ)).restrict
      (CameronMartin.unitCubeSet d))

/-- The actual Gamma-normalized tensor RL integration image, described in
the intended continuous-function ambient space by its pointwise integral. -/
def fractionalIntegrationBall {d : ℕ} (a : Fin d → ℝ) :
    Set C(BrownianCubeAnchor d, ℝ) :=
  {f | ∃ g : CameronMartin.UnitCubeL2 d, ‖g‖ ≤ 1 ∧
    ∀ t, fractionalIntegrationValue a g t = f t}

def PeriodicMixedEntropyStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ p : ENNReal, 1 < p →
    ∀ r : ℝ, p.toReal⁻¹ < r → ∀ θ : ENNReal, 1 ≤ θ →
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      (p ≠ ⊤ → ENNReal.ofReal (c * logarithmicIndexRate r
        (r*(d-1:ℕ)+1/2) k) ≤ HaarQuarter.TheoremD.entropyNumber k
          {f : Torus.RealPeriodic d | SmoothResolution.SobolevUnitBall p.toReal r f}) ∧
      ENNReal.ofReal (c * logarithmicIndexRate r
        ((r+1/2-θ.toReal⁻¹)*(d-1:ℕ)+1/2) k) ≤
          HaarQuarter.TheoremD.entropyNumber k
            {f : Torus.RealPeriodic d | SmoothResolution.BesovUnitBall p r θ f} ∧
      ENNReal.ofReal (c * logarithmicIndexRate r
        ((r+1/2)*(d-1:ℕ)+1/2) k) ≤
          HaarQuarter.TheoremD.entropyNumber k
            {f : Torus.RealPeriodic d | SmoothResolution.NikolskyUnitBall p r f}

def periodicLInfinityImage {d : ℕ} (K : Set (Torus.RealPeriodic d)) :
    Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
  (ContinuousMap.toLp ⊤ volume ℝ) '' K

def twoSidedWidthRate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (r a : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
    ENNReal.ofReal (c*logarithmicIndexRate r a k) ≤
      HaarQuarter.TheoremD.Width.kolmogorovWidth K k ∧
    HaarQuarter.TheoremD.Width.kolmogorovWidth K k ≤
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
        HaarQuarter.TheoremD.Width.kolmogorovWidth (fractionalIntegrationBall a) k ∧
      HaarQuarter.TheoremD.Width.kolmogorovWidth (fractionalIntegrationBall a) k ≤
        ENNReal.ofReal (C*logarithmicIndexRate r (r*(ν-1:ℕ)+1/2) k)

def smallBallRate (q a ε : ℝ) : ℝ :=
  ε⁻¹ ^ q * (Real.log ε⁻¹) ^ a

def BrownianTwoSidedStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ c C ε₀ : ℝ,
    0<c ∧ 0<C ∧ 0<ε₀ ∧ ε₀<Real.exp (-1) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : BrownianSheetOnCube d Ω P) (ε : ℝ), 0<ε → ε≤ε₀ →
        c*sharpRate d ε ≤ -Real.log (P.real {ω | ‖B.path ω‖≤ε}) ∧
        -Real.log (P.real {ω | ‖B.path ω‖≤ε}) ≤ C*sharpRate d ε

def FractionalSheetStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ H : Fin d → ℝ, (∀ i, 0<H i ∧ H i<1) →
    ∀ h : ℝ, ∀ ν : ℕ, 2≤ν → minimumMultiplicity H h ν →
    ∃ c C ε₀ : ℝ, 0<c ∧ 0<C ∧ 0<ε₀ ∧ ε₀<Real.exp (-1) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : FractionalBrownianSheetOnCube d Ω P), B.H=H →
      ∀ ε : ℝ, 0<ε → ε≤ε₀ →
        c*smallBallRate h⁻¹ ((ν-1:ℕ)+(ν:ℝ)/(2*h)) ε ≤
          -Real.log (P.real {ω | ‖B.path ω‖≤ε}) ∧
        -Real.log (P.real {ω | ‖B.path ω‖≤ε}) ≤
          C*smallBallRate h⁻¹ ((ν-1:ℕ)+(ν:ℝ)/(2*h)) ε

def IntegratedSheetStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ m : Fin d → ℕ, ∀ m₀ ν : ℕ,
    2≤ν → minimumMultiplicity (fun i => (m i:ℝ)) (m₀:ℝ) ν →
    ∃ c C ε₀ : ℝ, 0<c ∧ 0<C ∧ 0<ε₀ ∧ ε₀<Real.exp (-1) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : BrownianSheetOnCube d Ω P) (ε : ℝ), 0<ε → ε≤ε₀ →
        c*smallBallRate (2/(2*(m₀:ℝ)+1))
          ((ν-1:ℕ)+(ν:ℝ)/(2*(m₀:ℝ)+1)) ε ≤
          -Real.log (P.real {ω | ‖integrateSheetPath m (B.path ω)‖≤ε}) ∧
        -Real.log (P.real {ω | ‖integrateSheetPath m (B.path ω)‖≤ε}) ≤
          C*smallBallRate (2/(2*(m₀:ℝ)+1))
            ((ν-1:ℕ)+(ν:ℝ)/(2*(m₀:ℝ)+1)) ε

def LatestMainResultsStatement : Prop :=
  CameronMartinEntropyWidthStatement ∧
  PeriodicMixedEntropyStatement ∧ PeriodicWidthStatement ∧
  FractionalEntropyWidthStatement ∧
  BrownianTwoSidedStatement ∧ FractionalSheetStatement ∧ IntegratedSheetStatement

end BrownianSharp.Latest
