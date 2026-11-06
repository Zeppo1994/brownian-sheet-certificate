import BrownianSharp.AlignmentPaperMeanZeroBesovEntropy
import BrownianSharp.AlignmentPeriodicCutoffYoung
import BrownianSharp.AlignmentPeriodicScaledClassTransfer

/-! Remark 3.3 for every admissible cutoff: the coordinatewise mean-zero part of the
`φ`-Besov unit ball has the same two-sided entropy rate in `L∞(T^d)`, with constants
depending on `φ, d, p, r, θ`. The lower bound transfers the fixed-resolution result through
the cutoff scale transfer (a constant amplitude factor); the upper bound is inclusion in the
full `φ`-Besov ball. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperMeanZeroBesovCutoff

open BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPaperMeanZeroBesovEntropy (CoordinatewiseMeanZero)

/-- Coordinatewise mean-zero functions in the Besov unit ball of the cutoff `φ`. -/
def MeanZeroBesovCutoffClass {d : ℕ} (φ : AdmissibleCutoff) (p : ℝ≥0∞) (r : ℝ)
    (θ : ℝ≥0∞) : Set (RealPeriodic d) :=
  {f | AlignmentPeriodicCutoffClasses.BesovUnitBall φ p r θ f ∧ CoordinatewiseMeanZero f}

/-- Remark 3.3 for an arbitrary admissible cutoff `φ`. -/
theorem meanZeroBesovCutoff_entropy_two_sided_LInfinity
    (φ : AdmissibleCutoff) {d : ℕ} (hd : 2 ≤ d) (r : ℝ) (θ p : ℝ≥0∞)
    (hr : 1/2 < r) (htop : θ ≠ ⊤) (hθ : 2 ≤ θ.toReal) (hp : 2 ≤ p) :
    AlignmentPaperPeriodic.twoSidedEntropyRate
      (Latest.periodicLInfinityImage (MeanZeroBesovCutoffClass (d := d) φ p r θ))
      r ((r+1/2-1/θ.toReal)*(d-1:ℕ)+1/2) := by
  have hθenn : 2 ≤ θ :=
    (ENNReal.toReal_le_toReal (by norm_num : (2:ℝ≥0∞) ≠ ⊤) htop).1 hθ
  obtain ⟨c, hc, hmap⟩ := AlignmentPeriodicCutoffYoung.cutoffBesovScaleTransfer_certified
    φ smoothResolutionCutoff d p (le_trans (by norm_num) hp) r (by linarith) θ
    (le_trans (by norm_num) hθenn)
  obtain ⟨⟨cFull, cUp, hcFull, hcUp, kFull, hkFull, hFull⟩, _⟩ :=
    AlignmentPaperPeriodicComplete.periodicBesov_entropy_width_equivalent φ hd hp hr hθenn
  obtain ⟨cLow, hcLow, kLow, hkLow, hLow⟩ :=
    AlignmentPaperMeanZeroBesovEntropy.meanZeroBesov_entropy_lower_LInfinity hd r θ p hr
      htop hθ hp
  have hsub : ∀ f ∈ AlignmentPaperMeanZeroBesovEntropy.MeanZeroBesovClass (d := d) p r θ,
      c • f ∈ MeanZeroBesovCutoffClass φ p r θ := by
    rintro f ⟨hf, hmean⟩
    refine ⟨hmap f ((AlignmentPeriodicCutoffClasses.BesovUnitBall_fixed p r θ f).2 hf),
      fun i x => ?_⟩
    simp [integral_const_mul, hmean i x]
  have hrate : ∀ k : ℕ, 0 ≤ BrownianSharp.logarithmicIndexRate r
      ((r+1/2-1/θ.toReal)*(d-1:ℕ)+1/2) k :=
    fun k => AlignmentWidthRates.logarithmicIndexRate_nonneg r _ k
  refine ⟨min (c * cLow) cFull, cUp, lt_min (mul_pos hc hcLow) hcFull, hcUp,
    max kLow kFull, hkLow.trans (le_max_left _ _), fun k hk => ?_⟩
  have hkl : kLow ≤ k := (le_max_left _ _).trans hk
  have hkf : kFull ≤ k := (le_max_right _ _).trans hk
  refine ⟨?_, ?_⟩
  · have := AlignmentPeriodicScaledClassTransfer.entropyNumber_ge_of_scaled_subset
      (Latest.periodicLInfinityImage (MeanZeroBesovCutoffClass (d := d) φ p r θ))
      (Latest.periodicLInfinityImage
        (AlignmentPaperMeanZeroBesovEntropy.MeanZeroBesovClass (d := d) p r θ))
      c _ hc (mul_nonneg hcLow.le (hrate k))
      (AlignmentPeriodicScaledClassTransfer.scaled_periodicImage_subset _ _ c hsub) k
      (by simpa using hLow k hkl)
    exact (ENNReal.ofReal_le_ofReal (by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (min_le_left _ _) (hrate k))).trans this
  · refine (AlignmentPeriodicFeatureEntropy.entropyNumber_mono ?_ k).trans
      (by simpa using (hFull k hkf).2)
    rintro g ⟨f, hf, rfl⟩
    exact ⟨f, hf.1, rfl⟩

end BrownianSharp.AlignmentPaperMeanZeroBesovCutoff
