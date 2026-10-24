import BrownianSharp.IndexMultipleRate
import BrownianSharp.PeriodicNativeCover

/-! Actual covering obstructions at a fixed index multiple imply the exact
power-log entropy rate. The analytic class-mass input remains explicit. -/
noncomputable section
open scoped ENNReal NNReal
namespace BrownianSharp

/-- Index multiples absorb an arbitrary fixed confinement exponent, with no
loss in the sharp logarithmic power. -/
theorem periodic_entropy_rate_of_cover_at_multiple
    {X : Type*} [PseudoEMetricSpace X] (K : Set X)
    {d s k₀ : ℕ} (hd : 2 ≤ d) (hs : 1 ≤ s) (hk₀ : 2 ≤ k₀)
    (r β η : ℝ) (hr : 0 < r) (hη : 0 < η)
    (hcover : ∀ (k : ℕ) (hk : k₀ ≤ k),
      ((2^(k-1):ℕ):ℕ∞) < Metric.externalCoveringNumber
        ⟨η * periodicNativeRadius d (nativeEntropyCrossing d (s*k) (by omega)) r β,
          (mul_pos hη (periodicNativeRadius_pos
            (nativeEntropyCrossing_bracket hd (by nlinarith [hk] : 2 ≤ s*k)).1)).le⟩ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^
        (r*((d-1:ℕ):ℝ)+(1/2+β*((d-1:ℕ):ℝ)))) ≤
          HaarQuarter.TheoremD.entropyNumber k K := by
  let α : ℝ := r*((d-1:ℕ):ℝ)+(1/2+β*((d-1:ℕ):ℝ))
  obtain ⟨c₁,hc₁,hmul⟩ := exists_index_multiple_rate_lower s hs r α
  let B : ℝ := periodicNativeRateConstant d r β
  have hB : 0 < B := periodicNativeRateConstant_pos hd r β
  refine ⟨η*B*c₁, by positivity, ?_⟩
  intro k hk
  have hk2 : 2 ≤ k := hk₀.trans hk
  have hsk : 2 ≤ s*k := by nlinarith
  let q := nativeEntropyCrossing d (s*k) (by omega)
  have hq : 0 < q := (nativeEntropyCrossing_bracket hd hsk).1
  have hnum := periodicNativeRadius_ge_rate r β hd hsk hr
  have hscale : (η*B*c₁)*(k:ℝ)^(-r)*(Real.log (k:ℝ))^α ≤
      η*periodicNativeRadius d q r β := by
    calc
      _ = (η*B)*(c₁*(k:ℝ)^(-r)*(Real.log (k:ℝ))^α) := by ring
      _ ≤ (η*B)*(((s*k:ℕ):ℝ)^(-r)*(Real.log ((s*k:ℕ):ℝ))^α) :=
        mul_le_mul_of_nonneg_left (hmul k hk2) (mul_pos hη hB).le
      _ = η*(B*((s*k:ℕ):ℝ)^(-r)*(Real.log ((s*k:ℕ):ℝ))^α) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hnum hη.le
  have hent := periodicEntropyNumber_ge_of_covering_gt k K
    ⟨η*periodicNativeRadius d q r β, (mul_pos hη (periodicNativeRadius_pos hq)).le⟩
    (hcover k hk)
  have hscale' := ENNReal.ofReal_le_ofReal hscale
  have hδ : ENNReal.ofReal (η*periodicNativeRadius d q r β) =
      (↑(NNReal.mk (η*periodicNativeRadius d q r β)
        (mul_pos hη (periodicNativeRadius_pos hq)).le) : ℝ≥0∞) :=
    ENNReal.ofReal_eq_coe_nnreal _
  rw [hδ] at hscale'
  exact hscale'.trans hent

end BrownianSharp
