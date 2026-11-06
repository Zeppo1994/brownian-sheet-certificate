import BrownianSharp.Statement
import BrownianSharp.UniformSharpStatement
import BrownianSharp.CameronMartin
import BrownianSharp.SmoothResolution
import BrownianSharp.TheoremDEntropyPacking
import BrownianSharp.KolmogorovWidth

/-!
Literal targets for all three theorems in sources/main_sheet.tex. These are
propositions, not assertions that the proposed theorems have been proved.
The periodic targets use the explicit smooth resolution rather than silently
substituting the v10 hard-block norms. The Cameron--Martin set uses the
actual restricted-cube L2 image, identified with the ambient feature image by
`CameronMartin.KdUnitCube_eq_Kd`.
-/
noncomputable section
open scoped NNReal ENNReal
open HaarQuarter.TheoremD

namespace BrownianSharp

def logarithmicIndexRate (r a : ℝ) (k : ℕ) : ℝ :=
  (k : ℝ) ^ (-r) * (Real.log (k : ℝ)) ^ a

def cmIndexRate (d k : ℕ) : ℝ :=
  logarithmicIndexRate 1 ((d : ℝ) - 1 / 2) k

/-- Theorem 4.1: all three mixed-smoothness entropy lower bounds, with one
common constant and threshold for each displayed parameter tuple. -/
def PeriodicMixedEntropyStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ p r : ℝ, 1 < p → p⁻¹ < r →
    ∀ θ : ENNReal, 1 ≤ θ → ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ,
      2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c * logarithmicIndexRate r
          (r * (d - 1 : ℕ) + 1 / 2) k) ≤
            entropyNumber k {f : Torus.RealPeriodic d |
              SmoothResolution.SobolevUnitBall p r f} ∧
        ENNReal.ofReal (c * logarithmicIndexRate r
          ((r + 1 / 2 - θ.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) ≤
            entropyNumber k {f : Torus.RealPeriodic d |
              SmoothResolution.BesovUnitBall (ENNReal.ofReal p) r θ f} ∧
        ENNReal.ofReal (c * logarithmicIndexRate r
          ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) k) ≤
            entropyNumber k {f : Torus.RealPeriodic d |
              SmoothResolution.NikolskyUnitBall (ENNReal.ofReal p) r f}

end BrownianSharp
