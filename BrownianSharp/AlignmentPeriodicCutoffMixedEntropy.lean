import BrownianSharp.AlignmentPeriodicCutoffTransferStatement
import BrownianSharp.AlignmentPeriodicCutoffEntropyTransfer
import BrownianSharp.AlignmentPeriodicCutoffSobolevEmbedding
import BrownianSharp.AlignmentPeriodicCutoffSobolevBridges

/-! Discharge arbitrary-cutoff mixed entropy from an explicit Besov scale
transfer hypothesis and the concrete-cutoff entropy bounds. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPeriodicCutoffMixedEntropy

open BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicCutoffTransferStatement
open BrownianSharp.AlignmentPeriodicCutoffEntropyTransfer
open BrownianSharp.AlignmentPeriodicCutoffSobolevEmbedding
open BrownianSharp.AlignmentPeriodicCutoffSobolevBridges
open BrownianSharp.AlignmentGaussianRates

private theorem cutoff_sobolev_entropy_of_transfer
    (htransfer : BesovScaleTransferStatement)
    {d : ℕ} (hd : 2 ≤ d) (φ : AdmissibleCutoff)
    (p : ℝ≥0∞) (hp : 1 < p) (hptop : p ≠ ⊤)
    (r : ℝ) (hpr : p.toReal⁻¹ < r) :
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * logarithmicIndexRate r
        (r * (d - 1 : ℕ) + 1 / 2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k (Latest.periodicLInfinityImage
          {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f}) := by
  have hpR : 1 < p.toReal := by
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hptop).2 hp
  have hr : 0 ≤ r := by
    have hi : 0 ≤ p.toReal⁻¹ := by positivity
    linarith
  by_cases hge : 2 ≤ p.toReal
  · obtain ⟨ct,hct,hmap⟩ := htransfer φ smoothResolutionCutoff d p hp.le r hr
      (2:ℝ≥0∞) (by norm_num)
    have hball : ∀ f : RealPeriodic d,
        SmoothResolution.BesovUnitBall p r 2 f →
          ct • f ∈ {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f} := by
      intro f hf
      have hs : BesovUnitBall smoothResolutionCutoff p r 2 f := by
        simpa using hf
      have ht := hmap f hs
      have hcast : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hptop
      have ht' : BesovUnitBall φ (ENNReal.ofReal p.toReal) r 2 (ct • f) := by
        simpa [hcast] using ht
      exact besov_two_implies_sobolev φ p.toReal hge r (ct • f) ht'
    obtain ⟨C,hC,k₀,hk₀,hent⟩ := entropy_lower_of_scaled_besov_ball hd p hp r hpr
      2 (by norm_num) {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f} ct hct hball
    refine ⟨C,hC,k₀,hk₀,?_⟩
    intro k hk
    have hrate : logarithmicIndexRate r
        ((r + 1 / 2 - (2:ℝ≥0∞).toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k =
        logarithmicIndexRate r (r * (d - 1 : ℕ) + 1 / 2) k := by
      simp [logarithmicIndexRate]
    simpa [hrate] using hent k hk
  · have hp2 : p.toReal ≤ 2 := le_of_not_ge hge
    have hhalf : (1:ℝ) / 2 < r := by
      have hinv : (1:ℝ) / 2 ≤ p.toReal⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le (by linarith [hpR]) hp2
      linarith
    have h2real : (ENNReal.ofReal 2).toReal = 2 := by simp
    have hpr2 : (ENNReal.ofReal 2).toReal⁻¹ < r := by simpa [h2real] using hhalf
    obtain ⟨ct,hct,hmap⟩ := htransfer φ smoothResolutionCutoff d
      (ENNReal.ofReal 2) (by norm_num) r (le_of_lt (by linarith [hhalf]))
      (2:ℝ≥0∞) (by norm_num)
    have hball : ∀ f : RealPeriodic d,
        SmoothResolution.BesovUnitBall (ENNReal.ofReal 2) r 2 f →
          ct • f ∈ {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f} := by
      intro f hf
      have hs : BesovUnitBall smoothResolutionCutoff (ENNReal.ofReal 2) r 2 f := by
        simpa using hf
      have ht := hmap f hs
      have ht' : BesovUnitBall φ 2 r 2 (ct • f) := by simpa using ht
      have ht2 : SobolevUnitBall φ 2 r (ct • f) :=
        (sobolev_two_iff_besov_two φ r (ct • f)).2 ht'
      exact sobolev_unitBall_mono φ (lt_trans (by norm_num) hpR) hp2 r
        (ct • f) ht2
    obtain ⟨C,hC,k₀,hk₀,hent⟩ := entropy_lower_of_scaled_besov_ball hd
      (ENNReal.ofReal 2) (by norm_num) r hpr2 2 (by norm_num)
      {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f} ct hct hball
    refine ⟨C,hC,k₀,hk₀,?_⟩
    intro k hk
    have hrate : logarithmicIndexRate r
        ((r + 1 / 2 - (2:ℝ≥0∞).toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k =
        logarithmicIndexRate r (r * (d - 1 : ℕ) + 1 / 2) k := by
      simp [logarithmicIndexRate]
    simpa [hrate] using hent k hk

theorem periodic_mixed_entropy_of_transfer
    (htransfer : BesovScaleTransferStatement) :
    BrownianSharp.AlignmentPeriodicCutoffTransferStatement.PeriodicMixedEntropyStatement := by
  intro φ d hd p hp r hpr θ hθ
  have hr : 0 ≤ r := by
    have hi : 0 ≤ p.toReal⁻¹ := by positivity
    linarith
  obtain ⟨cB,hcB,hmapB⟩ := htransfer φ smoothResolutionCutoff d p
    (le_of_lt hp) r hr θ hθ
  have hballB : ∀ f : RealPeriodic d,
      SmoothResolution.BesovUnitBall p r θ f →
        cB • f ∈ {f : RealPeriodic d | BesovUnitBall φ p r θ f} := by
    intro f hf
    have hs : BesovUnitBall smoothResolutionCutoff p r θ f := by simpa using hf
    exact hmapB f hs
  obtain ⟨CB,hCB,kB₀,hkB₀,hBentropy⟩ := entropy_lower_of_scaled_besov_ball
    hd p hp r hpr θ hθ
    {f : RealPeriodic d | BesovUnitBall φ p r θ f} cB hcB hballB

  obtain ⟨cN,hcN,hmapN⟩ := htransfer φ smoothResolutionCutoff d p
    (le_of_lt hp) r hr ⊤ (by simp)
  have hballN : ∀ f : RealPeriodic d,
      SmoothResolution.BesovUnitBall p r ⊤ f →
        cN • f ∈ {f : RealPeriodic d | NikolskyUnitBall φ p r f} := by
    intro f hf
    have hs : BesovUnitBall smoothResolutionCutoff p r ⊤ f := by simpa using hf
    have ht := hmapN f hs
    simpa [NikolskyUnitBall] using ht
  obtain ⟨CN,hCN,kN,hkN,hNentropy⟩ := entropy_lower_of_scaled_besov_ball
    hd p hp r hpr ⊤ (by simp)
    {f : RealPeriodic d | NikolskyUnitBall φ p r f} cN hcN hballN

  by_cases hptop : p = ⊤
  · let c := min CB CN
    let k₀ := max kB₀ kN
    have hc : 0 < c := by dsimp [c]; exact lt_min hCB hCN
    have hk₀ : 2 ≤ k₀ := by dsimp [k₀]; exact le_max_of_le_left hkB₀
    refine ⟨c,hc,k₀,hk₀,?_⟩
    intro k hk
    have hkB' : kB₀ ≤ k := le_trans (le_max_left _ _) hk
    have hkN' : kN ≤ k := le_trans (le_max_right _ _) hk
    have hcB' : c ≤ CB := by dsimp [c]; exact min_le_left _ _
    have hcN' : c ≤ CN := by dsimp [c]; exact min_le_right _ _
    have hBe := hBentropy k hkB'
    have hNe := hNentropy k hkN'
    have hrateB : 0 ≤ logarithmicIndexRate r
        ((r + 1 / 2 - θ.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k :=
      AlignmentWidthRates.logarithmicIndexRate_nonneg r _ k
    have hrateN : 0 ≤ logarithmicIndexRate r
        ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) k :=
      AlignmentWidthRates.logarithmicIndexRate_nonneg r _ k
    have hB' := (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcB' hrateB)).trans hBe
    have hNe' : ENNReal.ofReal (CN * logarithmicIndexRate r
        ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          (Latest.periodicLInfinityImage {f : RealPeriodic d | NikolskyUnitBall φ p r f}) := by
      simpa using hNe
    have hN' := (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcN' hrateN)).trans hNe'
    refine ⟨?_, ?_, ?_⟩
    · intro hnot
      exact False.elim (hnot hptop)
    · exact hB'
    · exact hN'
  · obtain ⟨cS,hcS,kS,hkS,hSentropy⟩ := cutoff_sobolev_entropy_of_transfer
      htransfer hd φ p hp hptop r hpr
    let c := min CB (min cS CN)
    let k₀ := max kB₀ (max kS kN)
    have hc : 0 < c := by dsimp [c]; exact lt_min hCB (lt_min hcS hCN)
    have hk₀ : 2 ≤ k₀ := by
      dsimp [k₀]
      exact le_trans hkB₀ (le_max_left _ _)
    refine ⟨c,hc,k₀,hk₀,?_⟩
    intro k hk
    have hkB' : kB₀ ≤ k := le_trans (le_max_left _ _) hk
    have hkS' : kS ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
    have hkN' : kN ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
    have hcB' : c ≤ CB := by dsimp [c]; exact min_le_left _ _
    have hcS' : c ≤ cS := by dsimp [c]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hcN' : c ≤ CN := by dsimp [c]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have hBe := hBentropy k hkB'
    have hSe := hSentropy k hkS'
    have hNe := hNentropy k hkN'
    have hk2 : 2 ≤ k := le_trans hk₀ hk
    have hrateB : 0 ≤ logarithmicIndexRate r
        ((r + 1 / 2 - θ.toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k :=
      AlignmentWidthRates.logarithmicIndexRate_nonneg r _ k
    have hrateS : 0 ≤ logarithmicIndexRate r
        (r * (d - 1 : ℕ) + 1 / 2) k :=
      AlignmentWidthRates.logarithmicIndexRate_nonneg r _ k
    have hrateN : 0 ≤ logarithmicIndexRate r
        ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) k :=
      AlignmentWidthRates.logarithmicIndexRate_nonneg r _ k
    have hB' := (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcB' hrateB)).trans hBe
    have hS' := (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcS' hrateS)).trans hSe
    have hNe' : ENNReal.ofReal (CN * logarithmicIndexRate r
        ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          (Latest.periodicLInfinityImage {f : RealPeriodic d | NikolskyUnitBall φ p r f}) := by
      simpa using hNe
    have hN' := (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcN' hrateN)).trans hNe'
    exact ⟨(fun _ => hS'),hB',hN'⟩

end BrownianSharp.AlignmentPeriodicCutoffMixedEntropy
