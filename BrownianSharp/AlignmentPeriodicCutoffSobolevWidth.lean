import BrownianSharp.AlignmentPeriodicCutoffSobolevBridges
import BrownianSharp.AlignmentPeriodicCutoffTransferStatement
import BrownianSharp.AlignmentPeriodicScaledClassTransfer
import BrownianSharp.AlignmentLatestPeriodicWidths
import BrownianSharp.AlignmentAuditPeriodicBoundedness
import BrownianSharp.AlignmentScaledWidthRates

/-! Conditional width closure for Sobolev balls built from any admissible
cutoff. The only analytic input beyond the fixed-resolution theorem is the
cutoff Besov scale-transfer statement and the matching entropy lower bound. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPeriodicCutoffSobolevWidth

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicCutoffTransferStatement
open BrownianSharp.AlignmentPeriodicCutoffSobolevBridges
open BrownianSharp.AlignmentLatestPeriodicWidths
open BrownianSharp.AlignmentAuditPeriodicBoundedness
open BrownianSharp.AlignmentPeriodicScaledClassTransfer
open BrownianSharp.AlignmentScaledSetWidth
open BrownianSharp.AlignmentScaledWidthRates
open BrownianSharp.AlignmentOperatorStatements

private instance (d : ℕ) : MeasurableSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := borel _
private instance (d : ℕ) : BorelSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := ⟨rfl⟩

/-- Once the cutoff Besov norms are uniformly transferable and their entropy
lower bound is known, every finite spatial exponent Sobolev ball has the sharp
strict-index width rate in the actual global `L∞` ambient. -/
theorem periodic_cutoff_sobolev_width_of_transfer_and_entropy
    (htransfer : BesovScaleTransferStatement)
    (hEntropy : BrownianSharp.AlignmentPeriodicCutoffTransferStatement.PeriodicMixedEntropyStatement)
    {φ : AdmissibleCutoff} {d : ℕ} (hd : 2 ≤ d)
    {p : ℝ≥0∞} (hp : 2 ≤ p) (hptop : p ≠ ⊤)
    {r : ℝ} (hr : 1 / 2 < r) :
    AlignmentOperatorStatements.twoSidedWidthRate
      (Latest.periodicLInfinityImage
        {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f})
      r (r * (d - 1 : ℕ) + 1 / 2) := by
  have hpReal : (2 : ℝ) ≤ p.toReal := by
    have h := (ENNReal.toReal_le_toReal (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hptop).2 hp
    simpa only [ENNReal.toReal_ofNat] using h
  have hpOne : (1 : ℝ) < p.toReal := by linarith
  have hpEntropy : (1 : ℝ≥0∞) < p := lt_of_lt_of_le (by norm_num) hp
  have hpinv : p.toReal⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpReal)
  have hpr : p.toReal⁻¹ < r := hpinv.trans_lt hr
  obtain ⟨cEntropy, hcEntropy, kEntropy, hkEntropy, hEntropyAt⟩ :=
    hEntropy φ d hd p hpEntropy r hpr ⊤ le_top
  let K : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    Latest.periodicLInfinityImage
      {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f}
  let J : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    Latest.periodicLInfinityImage
      {f : RealPeriodic d | SobolevUnitBall smoothResolutionCutoff 2 r f}
  have hEntropyK : ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ENNReal.ofReal (c * logarithmicIndexRate r
        (r * (d - 1 : ℕ) + 1 / 2) k) ≤
          HaarQuarter.TheoremD.entropyNumber k K := by
    refine ⟨cEntropy, hcEntropy, kEntropy, ?_⟩
    intro k hk
    exact (hEntropyAt k hk).1 hptop
  obtain ⟨cTransfer, hcTransfer, hTransferAt⟩ :=
    htransfer smoothResolutionCutoff φ d (2 : ℝ≥0∞) (by norm_num)
      r (by linarith) (2 : ℝ≥0∞) (by norm_num)
  let A : ℝ := cTransfer⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : K ⊆ scalarImage A J := by
    apply periodicImage_subset_scalarImage
      {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f}
      {f : RealPeriodic d | SobolevUnitBall smoothResolutionCutoff 2 r f}
      A hA
    intro f hf
    have hSob2 : SobolevUnitBall φ 2 r f :=
      sobolev_unitBall_mono φ (by norm_num : 0 < (2 : ℝ)) hpReal r f hf
    have hBesovPhi : BesovUnitBall φ 2 r 2 f :=
      (sobolev_two_iff_besov_two φ r f).1 hSob2
    have hBesovFixed : BesovUnitBall smoothResolutionCutoff 2 r 2
        (cTransfer • f) := hTransferAt f hBesovPhi
    have hSobFixed : SobolevUnitBall smoothResolutionCutoff 2 r
        (cTransfer • f) :=
      (sobolev_two_iff_besov_two smoothResolutionCutoff r
        (cTransfer • f)).2 hBesovFixed
    simpa [A] using hSobFixed
  have hzeroJ : HaarQuarter.TheoremD.Width.kolmogorovWidth J 0 ≤
      ENNReal.ofReal (periodicNikolskyRadius d r) := by
    simpa [J] using
      sobolev_linf_width_zero_le_of_exponent (d := d)
        (p := (2 : ℝ)) (by norm_num) r hr
  obtain ⟨CWidth, hCWidth, nWidth, hWidth⟩ :=
    periodic_sobolev_width_upper hd (2 : ℝ) r (by norm_num) hr
  have hWidthJ : ∀ n, nWidth ≤ n →
      HaarQuarter.TheoremD.Width.kolmogorovWidth J n ≤
        ENNReal.ofReal (CWidth * logarithmicIndexRate r
          (r * (d - 1 : ℕ) + 1 / 2) n) := by
    intro n hn
    simpa [J, SobolevUnitBall_fixed] using hWidth n hn
  have hLegacy : Latest.twoSidedWidthRate K r
      (r * (d - 1 : ℕ) + 1 / 2) := by
    exact twoSidedWidthRate_of_entropy_lower_and_scaled_width_upper
      K J A (periodicNikolskyRadius d r) r
      (r * (d - 1 : ℕ) + 1 / 2) hK hA
      (periodicNikolsky_radius_nonneg (d := d) hr) hzeroJ
      (by linarith) (by positivity) hEntropyK
      ⟨CWidth, hCWidth, nWidth, hWidthJ⟩
  exact operator_width_rate_of_legacy K r
    (r * (d - 1 : ℕ) + 1 / 2) (by linarith) (by positivity) hLegacy

end BrownianSharp.AlignmentPeriodicCutoffSobolevWidth
