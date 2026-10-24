import BrownianSharp.PeriodicMixedFinal
import BrownianSharp.AlignmentEndpointYoung
import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.AlignmentIsometricEntropy
import BrownianSharp.UnitTorusMeasure

noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentLatestPeriodicEntropy
open BrownianSharp.Latest

/-- The new ENNReal target agrees with the legacy certified statement at
every finite spatial exponent. -/
theorem periodicMixedEntropy_finite_exponent
    {d : ℕ} (hd : 2≤d) (p : ENNReal) (hp : 1<p) (hptop : p≠⊤)
    (r : ℝ) (hpr : p.toReal⁻¹<r) (θ : ENNReal) (hθ : 1≤θ) :
    ∃ c : ℝ, 0<c ∧ ∃ k₀ : ℕ, 2≤k₀ ∧ ∀ k : ℕ, k₀≤k →
      (p≠⊤ → ENNReal.ofReal (c*logarithmicIndexRate r (r*(d-1:ℕ)+1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          {f : Torus.RealPeriodic d | SmoothResolution.SobolevUnitBall p.toReal r f}) ∧
      ENNReal.ofReal (c*logarithmicIndexRate r
        ((r+1/2-θ.toReal⁻¹)*(d-1:ℕ)+1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          {f : Torus.RealPeriodic d | SmoothResolution.BesovUnitBall p r θ f} ∧
      ENNReal.ofReal (c*logarithmicIndexRate r
        ((r+1/2)*(d-1:ℕ)+1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          {f : Torus.RealPeriodic d | SmoothResolution.NikolskyUnitBall p r f} := by
  have hpR : 1<p.toReal := by
    simpa only [ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop).2 hp
  obtain ⟨c,hc,k₀,hk₀,h⟩ :=
    periodicMixedEntropy_certified d hd p.toReal r hpR hpr θ hθ
  refine ⟨c,hc,k₀,hk₀,?_⟩
  intro k hk
  obtain ⟨hs,hb,hn⟩ := h k hk
  refine ⟨fun _ => hs,?_,?_⟩
  · simpa only [ENNReal.ofReal_toReal hptop] using hb
  · simpa only [ENNReal.ofReal_toReal hptop] using hn


open MeasureTheory
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) := by
  rw [unitAddCircle_volume_eq_haar]
  infer_instance

theorem periodic_entropy_lower_to_LInfinity {d : ℕ}
    (K : Set (Torus.RealPeriodic d)) (k : ℕ) (u : ℝ)
    (hu : ENNReal.ofReal u ≤ HaarQuarter.TheoremD.entropyNumber k K) :
    ENNReal.ofReal (u/2) ≤ HaarQuarter.TheoremD.entropyNumber k
      (Latest.periodicLInfinityImage K) := by
  let f := AlignmentAmbientWidth.continuousToLInfinity
    (volume : Measure (UnitAddTorus (Fin d)))
  have h := AlignmentIsometricEntropy.entropy_lower_under_isometry
    f f.isometry K k u hu
  exact h


/-- The complete periodic entropy assertion of the latest manuscript,
including the newly certified infinite spatial exponent. -/
theorem latest_periodicMixedEntropy_certified : Latest.PeriodicMixedEntropyStatement := by
  intro d hd p hp r hpr θ hθ
  by_cases hptop : p=⊤
  · subst p
    have hr : 0<r := by simpa using hpr
    let m : ℕ := ⌈r+2⌉₊
    let K : ℕ := m+m
    have hm : r+2≤(m:ℝ) := Nat.le_ceil _
    have hm1 : 1≤m := by
      have hm1r : (1:ℝ)≤m := by linarith
      exact_mod_cast hm1r
    have hK : Even K := ⟨m,rfl⟩
    have hKpos : 0<K := by dsimp [K]; omega
    have hrK : r<(K:ℝ) := by dsimp [K]; push_cast; linarith
    obtain ⟨cB,hcB,kB,hkB,hB⟩ :=
      endpoint_periodic_besov_entropy_rate hd r θ hr hθ K hK hKpos hrK
    obtain ⟨cN,hcN,kN,hkN,hN⟩ :=
      endpoint_periodic_nikolsky_entropy_rate hd r hr K hK hKpos hrK
    let c := min cB cN
    refine ⟨c,lt_min hcB hcN,max kB kN,hkB.trans (le_max_left _ _),?_⟩
    intro k hk
    have hkB' : kB≤k := (le_max_left kB kN).trans hk
    have hkN' : kN≤k := (le_max_right kB kN).trans hk
    have hnonneg : ∀ a : ℝ, 0≤logarithmicIndexRate r a k := by
      intro a
      exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (Real.rpow_nonneg (Real.log_natCast_nonneg _) _)
    refine ⟨fun h => (h rfl).elim,?_,?_⟩
    · have hexp : r*((d-1:ℕ):ℝ)+(1/2+(1/2-1/θ.toReal)*((d-1:ℕ):ℝ)) =
          (r+1/2-θ.toReal⁻¹)*((d-1:ℕ):ℝ)+1/2 := by rw [one_div]; ring
      have hB' : ENNReal.ofReal (cB*logarithmicIndexRate r
          ((r+1/2-θ.toReal⁻¹)*(d-1:ℕ)+1/2) k) ≤
          HaarQuarter.TheoremD.entropyNumber k
            {f : Torus.RealPeriodic d | SmoothResolution.BesovUnitBall ⊤ r θ f} := by
        simpa only [logarithmicIndexRate,← mul_assoc,hexp] using hB k hkB'
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_left cB cN) (hnonneg _))).trans hB'
    · have hN' : ENNReal.ofReal (cN*logarithmicIndexRate r
          ((r+1/2)*(d-1:ℕ)+1/2) k) ≤
          HaarQuarter.TheoremD.entropyNumber k
            {f : Torus.RealPeriodic d | SmoothResolution.NikolskyUnitBall ⊤ r f} := by
        simpa only [logarithmicIndexRate,← mul_assoc] using hN k hkN'
      exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (min_le_right cB cN) (hnonneg _))).trans hN'
  · exact periodicMixedEntropy_finite_exponent hd p hp hptop r hpr θ hθ

end BrownianSharp.AlignmentLatestPeriodicEntropy
