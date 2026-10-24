import BrownianSharp.NativeSmoothSobolevExpectedRate
import BrownianSharp.NativeBesovEnergyRate
import BrownianSharp.Statement

/-! Assemble the three periodic entropy bounds at one constant and one
threshold. The Nikolsky estimate is an explicit input so the conjunction
does not silently assume or disguise the remaining endpoint argument. -/

noncomputable section
set_option maxHeartbeats 1200000
open scoped ENNReal

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution

private theorem logarithmicIndexRate_nonneg {k : ℕ} (hk : 2 ≤ k)
    (r a : ℝ) : 0 ≤ logarithmicIndexRate r a k := by
  unfold logarithmicIndexRate
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hlog : 0 ≤ Real.log (k:ℝ) := Real.log_nonneg hk1
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg hlog _)

private theorem logarithmicIndexRate_mul_eq (c r a : ℝ) (k : ℕ) :
    c * logarithmicIndexRate r a k =
      c * (k:ℝ)^(-r) * (Real.log (k:ℝ))^a := by
  unfold logarithmicIndexRate
  ring

private theorem actualBesovEntropyForFiniteTheta
    {d : ℕ} (hd : 2 ≤ d) (p theta r : ℝ)
    (hp : 1 < p) (htheta : 1 ≤ theta) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * (k : ℝ)^(-r) * (Real.log (k:ℝ))^
        ((r+1/2-theta⁻¹)*((d-1:ℕ):ℝ)+1/2)) ≤
        HaarQuarter.TheoremD.entropyNumber k
          {f : RealPeriodic d | BesovUnitBall (ENNReal.ofReal p) r
            (ENNReal.ofReal theta) f} := by
  let K : ℕ := Nat.ceil (r + 2)
  have hceil : r + 2 ≤ (K:ℝ) := by exact_mod_cast Nat.le_ceil (r+2)
  have hK : 1 ≤ K := by
    have : (1:ℝ) ≤ (K:ℝ) := by linarith
    exact_mod_cast this
  have hgap : 2*r < 2*(K:ℝ)-1 := by linarith
  obtain ⟨C,hCpos,hC⟩ := exists_smoothAtom_iteratedDeriv_bound K
  exact NativeBesovEnergyRate.periodicBesov_entropy_of_actual_native_energy
    hd hK C hC p theta r hp htheta hr hgap

private theorem periodicMixedEntropyStatement_of_nikolsky
    (hNikol : ∀ d : ℕ, 2 ≤ d → ∀ p r : ℝ, 1 < p → p⁻¹ < r →
      ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c * logarithmicIndexRate r
          ((r+1/2)*((d-1:ℕ):ℝ)+1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          {f : RealPeriodic d | NikolskyUnitBall (ENNReal.ofReal p) r f}) :
    PeriodicMixedEntropyStatement := by
  intro d hd p r hp hpr θ hθ
  obtain ⟨cS,hcS,kS,hkS,hS⟩ :=
    periodicSobolev_entropy_of_actual_native_expected_rate hd p r hp
      (lt_trans (inv_pos.mpr (by linarith)) hpr)
  obtain ⟨cN,hcN,kN,hkN,hN⟩ := hNikol d hd p r hp hpr
  by_cases htop : θ = ⊤
  · have hthetaReal : θ.toReal = 0 := by simp [htop]
    have hbesovEq :
        {f : RealPeriodic d | BesovUnitBall (ENNReal.ofReal p) r θ f} =
          {f : RealPeriodic d | NikolskyUnitBall (ENNReal.ofReal p) r f} := by
      ext f
      simp [NikolskyUnitBall, BesovUnitBall, htop]
    let c := min cS cN
    let k₀ := max kS kN
    have hc : 0 < c := by dsimp [c]; exact lt_min hcS hcN
    have hk₀ : 2 ≤ k₀ := by dsimp [k₀]; exact le_max_of_le_left hkS
    refine ⟨c,hc,k₀,hk₀,?_⟩
    intro k hk
    have hkS' : kS ≤ k := le_trans (le_max_left _ _) hk
    have hkN' : kN ≤ k := le_trans (le_max_right _ _) hk
    have hcS' : c ≤ cS := by dsimp [c]; exact min_le_left _ _
    have hcN' : c ≤ cN := by dsimp [c]; exact min_le_right _ _
    have hs := hS k hkS'
    have hn := hN k hkN'
    have hk2 : 2 ≤ k := le_trans hk₀ hk
    have hrateEq : logarithmicIndexRate r
        ((r+1/2-θ.toReal⁻¹)*((d-1:ℕ):ℝ)+1/2) k =
        logarithmicIndexRate r ((r+1/2)*((d-1:ℕ):ℝ)+1/2) k := by
      rw [hthetaReal]
      simp
    have hbes : ENNReal.ofReal (c * logarithmicIndexRate r
        ((r+1/2-θ.toReal⁻¹)*((d-1:ℕ):ℝ)+1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          {f : RealPeriodic d | BesovUnitBall (ENNReal.ofReal p) r θ f} := by
      have hscaled : ENNReal.ofReal (c * logarithmicIndexRate r
          ((r+1/2)*((d-1:ℕ):ℝ)+1/2) k) ≤
          HaarQuarter.TheoremD.entropyNumber k
            {f : RealPeriodic d | NikolskyUnitBall (ENNReal.ofReal p) r f} := by
        exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcN'
          (logarithmicIndexRate_nonneg hk2 r
            ((r+1/2)*((d-1:ℕ):ℝ)+1/2)))).trans hn
      have hmulRate : c * logarithmicIndexRate r
          ((r+1/2-θ.toReal⁻¹)*((d-1:ℕ):ℝ)+1/2) k =
          c * logarithmicIndexRate r ((r+1/2)*((d-1:ℕ):ℝ)+1/2) k :=
        congrArg (fun x : ℝ => c*x) hrateEq
      rw [hmulRate]
      simpa [hbesovEq] using hscaled
    refine ⟨?_, hbes, ?_⟩
    ·
      have hscaled := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hcS'
          (logarithmicIndexRate_nonneg hk2 r (r*((d-1:ℕ):ℝ)+1/2)))
      have hs' : ENNReal.ofReal (cS * logarithmicIndexRate r
          (r*((d-1:ℕ):ℝ)+1/2) k) ≤
          HaarQuarter.TheoremD.entropyNumber k
            {f : RealPeriodic d | SobolevUnitBall p r f} := by
        rw [logarithmicIndexRate_mul_eq]
        exact hs
      exact hscaled.trans hs'
    · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcN'
        (logarithmicIndexRate_nonneg hk2 r ((r+1/2)*((d-1:ℕ):ℝ)+1/2)))).trans hn
  · have hθfinite : θ ≠ ⊤ := htop
    have hθofReal : ENNReal.ofReal θ.toReal = θ := ENNReal.ofReal_toReal hθfinite
    have hθreal : 1 ≤ θ.toReal := by
      exact ENNReal.toReal_mono hθfinite hθ
    obtain ⟨cB,hcB,kB,hkB,hB⟩ := actualBesovEntropyForFiniteTheta
      hd p θ.toReal r hp hθreal (lt_trans (inv_pos.mpr (by linarith)) hpr)
    let c := min cS (min cB cN)
    let k₀ := max kS (max kB kN)
    have hc : 0 < c := by dsimp [c]; exact lt_min hcS (lt_min hcB hcN)
    have hk₀ : 2 ≤ k₀ := by
      dsimp [k₀]
      exact le_trans hkS (le_max_left _ _)
    refine ⟨c,hc,k₀,hk₀,?_⟩
    intro k hk
    have hk2 : 2 ≤ k := le_trans hk₀ hk
    have hkS' : kS ≤ k := le_trans (le_max_left _ _) hk
    have hkB' : kB ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
    have hkN' : kN ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
    have hcS' : c ≤ cS := by dsimp [c]; exact min_le_left _ _
    have hcB' : c ≤ cB := by dsimp [c]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hcN' : c ≤ cN := by dsimp [c]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hs := hS k hkS'
    have hb := hB k hkB'
    have hn := hN k hkN'
    have hbes : ENNReal.ofReal (c * logarithmicIndexRate r
        ((r+1/2-θ.toReal⁻¹)*((d-1:ℕ):ℝ)+1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          {f : RealPeriodic d | BesovUnitBall (ENNReal.ofReal p) r θ f} := by
      have hb' : ENNReal.ofReal (cB * logarithmicIndexRate r
          ((r+1/2-(θ.toReal)⁻¹)*((d-1:ℕ):ℝ)+1/2) k) ≤
          HaarQuarter.TheoremD.entropyNumber k
            {f : RealPeriodic d | BesovUnitBall (ENNReal.ofReal p) r
              (ENNReal.ofReal θ.toReal) f} := by
        rw [logarithmicIndexRate_mul_eq]
        exact hb
      have hscaled := (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcB'
        (logarithmicIndexRate_nonneg hk2 r
          ((r+1/2-(θ.toReal)⁻¹)*((d-1:ℕ):ℝ)+1/2)))).trans hb'
      simpa only [hθofReal] using hscaled
    refine ⟨?_, hbes, ?_⟩
    · have hscaled := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hcS'
          (logarithmicIndexRate_nonneg hk2 r (r*((d-1:ℕ):ℝ)+1/2)))
      have hs' : ENNReal.ofReal (cS * logarithmicIndexRate r
          (r*((d-1:ℕ):ℝ)+1/2) k) ≤
          HaarQuarter.TheoremD.entropyNumber k
            {f : RealPeriodic d | SobolevUnitBall p r f} := by
        rw [logarithmicIndexRate_mul_eq]
        exact hs
      exact hscaled.trans hs'
    · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hcN'
        (logarithmicIndexRate_nonneg hk2 r ((r+1/2)*((d-1:ℕ):ℝ)+1/2)))).trans hn

theorem periodic_mixed_entropy_of_actual_finite_theta_and_nikolsky
    (hNikol : ∀ d : ℕ, 2 ≤ d → ∀ p r : ℝ, 1 < p → p⁻¹ < r →
      ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c * logarithmicIndexRate r
          ((r+1/2)*((d-1:ℕ):ℝ)+1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          {f : RealPeriodic d | NikolskyUnitBall (ENNReal.ofReal p) r f}) :
    PeriodicMixedEntropyStatement := periodicMixedEntropyStatement_of_nikolsky hNikol

end BrownianSharp
