import BrownianSharp.AlignmentPeriodicCutoffTransferStatement
import BrownianSharp.AlignmentPeriodicScaledClassTransfer
import BrownianSharp.AlignmentLatestNikolskyWidths
import BrownianSharp.AlignmentScaledWidthRates
import BrownianSharp.AlignmentAuditPeriodicBoundedness
import BrownianSharp.AlignmentOperatorStatements

/-! Conditional arbitrary-cutoff Nikolsky width theorem. The analytic inputs
are exactly the cutoff scale-transfer statement and mixed entropy statement. -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPeriodicCutoffNikolskyWidth

open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicCutoffTransferStatement
open BrownianSharp.AlignmentPeriodicScaledClassTransfer
open BrownianSharp.AlignmentLatestNikolskyWidths
open BrownianSharp.AlignmentScaledWidthRates
open BrownianSharp.AlignmentAuditPeriodicBoundedness
open BrownianSharp.AlignmentOperatorStatements
open BrownianSharp.SmoothResolution
open BrownianSharp.Torus
open BrownianSharp.Latest
open HaarQuarter.TheoremD.Width

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) := by
  rw [unitAddCircle_volume_eq_haar]
  infer_instance
local instance (d : ℕ) : MeasurableSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := borel _
local instance (d : ℕ) : BorelSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := ⟨rfl⟩

/-- For every admissible cutoff, the sharp periodic Nikolsky width rate follows
from cutoff-independent Besov scaling and the corresponding entropy lower
bound. The width upper estimate is transferred from the concrete certified
cutoff by a positive scalar dilation. -/
theorem nikolsky_twoSided_width_of_cutoff_transfer_and_entropy
    (hTransfer : BesovScaleTransferStatement)
    (hEntropy : AlignmentPeriodicCutoffTransferStatement.PeriodicMixedEntropyStatement)
    (φ : AdmissibleCutoff) {d : ℕ} (hd : 2 ≤ d)
    (p : ℝ≥0∞) (hp : 2 ≤ p) (r : ℝ) (hr : 1 / 2 < r) :
    AlignmentOperatorStatements.twoSidedWidthRate
      (Latest.periodicLInfinityImage
        {f : RealPeriodic d | NikolskyUnitBall φ p r f})
      r ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) := by
  have hp1 : (1 : ℝ≥0∞) < p := lt_of_lt_of_le (by norm_num) hp
  have hpinv : p.toReal⁻¹ < r := by
    by_cases htop : p = ⊤
    · simpa [htop] using (show (0 : ℝ) < r by linarith)
    · have hpR : (2 : ℝ) ≤ p.toReal := by
        have h := (ENNReal.toReal_le_toReal
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) htop).2 hp
        simpa only [ENNReal.toReal_ofNat] using h
      have hinv : p.toReal⁻¹ ≤ (1 / 2 : ℝ) := by
        simpa only [one_div] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpR
      exact hinv.trans_lt hr
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨cEntropy, hcEntropy, k₀, hk₀, hEntropyBounds⟩ :=
    hEntropy φ d hd p hp1 r hpinv ⊤ le_top
  let K : Set (RealPeriodic d) := {f | NikolskyUnitBall φ p r f}
  let J : Set (RealPeriodic d) := {f | SmoothResolution.NikolskyUnitBall p r f}
  have hEntropyLower : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ENNReal.ofReal (c * logarithmicIndexRate r
        ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) n) ≤
        HaarQuarter.TheoremD.entropyNumber n (Latest.periodicLInfinityImage K) := by
    refine ⟨cEntropy, hcEntropy, k₀, ?_⟩
    intro n hn
    exact (hEntropyBounds n hn).2.2
  obtain ⟨cScale, hcScale, hScale⟩ :=
    hTransfer smoothResolutionCutoff φ d p (by exact le_trans (by norm_num) hp)
      r hr0 ⊤ le_top
  have hscaledClass : ∀ f ∈ K, cScale • f ∈ J := by
    intro f hf
    have hh := hScale f hf
    simpa [J, SmoothResolution.NikolskyUnitBall] using hh
  let A : ℝ := cScale⁻¹
  have hA : 0 < A := by dsimp [A]; exact inv_pos.mpr hcScale
  have hKimage : Latest.periodicLInfinityImage K ⊆
      (fun x : Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d))) => A • x) ''
        Latest.periodicLInfinityImage J := by
    apply periodicImage_subset_scalarImage K J A hA
    intro f hf
    have hh := hscaledClass f hf
    simpa [A, inv_inv] using hh
  have hzeroJ : kolmogorovWidth (Latest.periodicLInfinityImage J) 0 ≤
      ENNReal.ofReal (periodicNikolskyRadius d r) := by
    simpa [J] using nikolsky_linf_width_zero_le_of_exponent hp r hr
  obtain ⟨Cwidth, hCwidth, n₀, hUpperJ⟩ :=
    periodic_nikolsky_width_upper hd p hp r hr
  have hUpperJ' : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      kolmogorovWidth (Latest.periodicLInfinityImage J) n ≤
        ENNReal.ofReal (C * logarithmicIndexRate r
          ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) n) := by
    refine ⟨Cwidth, hCwidth, n₀, ?_⟩
    intro n hn
    simpa [J] using hUpperJ n hn
  have hlegacy : Latest.twoSidedWidthRate
      (Latest.periodicLInfinityImage K) r
      ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) :=
    twoSidedWidthRate_of_entropy_lower_and_scaled_width_upper
      (Latest.periodicLInfinityImage K) (Latest.periodicLInfinityImage J)
      A (periodicNikolskyRadius d r) r
      ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2)
      hKimage hA (periodicNikolsky_radius_nonneg (d := d) hr)
      hzeroJ (by linarith) (by positivity) hEntropyLower hUpperJ'
  exact operator_width_rate_of_legacy
    (Latest.periodicLInfinityImage K) r
    ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2)
    (by linarith) (by positivity) hlegacy

end BrownianSharp.AlignmentPeriodicCutoffNikolskyWidth

