import BrownianSharp.AlignmentPaperPeriodic
import BrownianSharp.AlignmentPeriodicCutoffClasses
import BrownianSharp.AlignmentPeriodicAdmissibleCutoff
import BrownianSharp.QuarterScale
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Entropy decay for the literal periodic Sobolev unit ball, extracted from
its proved sharp upper rate. This is the analytic input to the compact-closure
argument in `AlignmentPaperEntropyCompactness`. -/

noncomputable section
open Filter
open scoped ENNReal Topology

namespace BrownianSharp.AlignmentPaperPeriodicEntropyDecay

open BrownianSharp.AlignmentPaperPeriodic
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentWidthRates
open BrownianSharp.Latest
open BrownianSharp.Torus

/-- The entropy numbers of the actual L-infinity image of the smooth periodic
Sobolev-2 unit ball tend to zero whenever `r>1/2`. -/
theorem smoothSobolev_entropy_tendsto_zero {d : ℕ} (hd : 2 ≤ d)
    {r : ℝ} (hr : 1/2 < r) :
    ∀ ε : NNReal, 0 < ε → ∃ k : ℕ,
      HaarQuarter.TheoremD.entropyNumber k
        (periodicLInfinityImage
          {f : RealPeriodic d | SobolevUnitBall smoothResolutionCutoff 2 r f}) <
        (ε : ℝ≥0∞) := by
  obtain ⟨hSob, _hNik⟩ := periodic_entropy_upper_certified
    smoothResolutionCutoff d hd (2 : ℝ≥0∞) (by norm_num) r hr
  obtain ⟨C, hC, k₀, hk₀, hupper⟩ := hSob (by norm_num)
  have hrate : Tendsto (fun k : ℕ => logarithmicIndexRate r
      (r * (d - 1 : ℕ) + 1 / 2) k) atTop (𝓝 0) := by
    have h := HaarQuarter.log_weighted_power_tendsto_zero (-r)
      (r * (d - 1 : ℕ) + 1 / 2) (by linarith)
    change Tendsto ((fun x : ℝ => x ^ (-r) * (Real.log x) ^
      (r * (d - 1 : ℕ) + 1 / 2)) ∘ Nat.cast) atTop (𝓝 0)
    exact h.comp tendsto_natCast_atTop_atTop
  have hscaled : Tendsto (fun k : ℕ => C * logarithmicIndexRate r
      (r * (d - 1 : ℕ) + 1 / 2) k) atTop (𝓝 0) := by
    simpa using hrate.const_mul C
  intro ε hε
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (hscaled.eventually (Iio_mem_nhds hεR))
  let k := max k₀ N
  refine ⟨k, ?_⟩
  have hk₀ : k₀ ≤ k := le_max_left _ _
  have hkN : N ≤ k := le_max_right _ _
  have hreal := hN k hkN
  have hupper' := hupper k hk₀
  have hnonneg : 0 ≤ C * logarithmicIndexRate r
      (r * (d - 1 : ℕ) + 1 / 2) k :=
    mul_nonneg hC.le (logarithmicIndexRate_nonneg _ _ _)
  have hlt : ENNReal.ofReal (C * logarithmicIndexRate r
      (r * (d - 1 : ℕ) + 1 / 2) k) < ENNReal.ofReal (ε : ℝ) :=
    (ENNReal.ofReal_lt_ofReal_iff hεR).2 hreal
  exact (hupper'.trans_lt hlt).trans_le (by simp)

end BrownianSharp.AlignmentPaperPeriodicEntropyDecay
