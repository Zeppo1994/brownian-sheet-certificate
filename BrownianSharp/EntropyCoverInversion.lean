import BrownianSharp.ExtendedStatements
import BrownianSharp.TheoremDEntropyPacking

open scoped ENNReal NNReal

namespace BrownianSharp

variable {X : Type*} [PseudoEMetricSpace X]

/-- An entropy radius strictly below `ρ` provides a covering at radius `ρ`
with the same dyadic budget. The proof uses only the defining infimum and
monotonicity of external covering numbers. -/
theorem externalCover_le_of_entropyNumber_lt
    (k : ℕ) (K : Set X) (ρ : ℝ≥0)
    (h : HaarQuarter.TheoremD.entropyNumber k K < (ρ : ℝ≥0∞)) :
    Metric.externalCoveringNumber ρ K ≤ ((2 ^ (k - 1) : ℕ) : ℕ∞) := by
  by_contra hcover
  have hρle : (ρ : ℝ≥0∞) ≤ HaarQuarter.TheoremD.entropyNumber k K := by
    unfold HaarQuarter.TheoremD.entropyNumber
    apply le_sInf
    rintro r ⟨r', rfl, hbudget⟩
    by_contra hnot
    have hrr : r' < ρ := by exact_mod_cast (lt_of_not_ge hnot)
    have hmono := Metric.externalCoveringNumber_anti (X := X) (A := K)
      (le_of_lt hrr)
    exact hcover (hmono.trans hbudget)
  exact (not_lt_of_ge hρle) h

/-- A cover at radius `ρ` bounds the entropy number by that radius. -/
theorem entropyNumber_le_of_externalCover_le
    (k : ℕ) (K : Set X) (ρ : ℝ≥0)
    (h : Metric.externalCoveringNumber ρ K ≤ ((2 ^ (k - 1) : ℕ) : ℕ∞)) :
    HaarQuarter.TheoremD.entropyNumber k K ≤ (ρ : ℝ≥0∞) := by
  unfold HaarQuarter.TheoremD.entropyNumber
  exact sInf_le ⟨ρ, rfl, h⟩

/-- If the entropy number is strictly above a radius, the dyadic budget cannot
cover at that radius. -/
theorem externalCover_gt_of_radius_lt_entropyNumber
    (k : ℕ) (K : Set X) (ρ : ℝ≥0)
    (h : (ρ : ℝ≥0∞) < HaarQuarter.TheoremD.entropyNumber k K) :
    ((2 ^ (k - 1) : ℕ) : ℕ∞) < Metric.externalCoveringNumber ρ K := by
  by_contra hcover
  have hle : HaarQuarter.TheoremD.entropyNumber k K ≤ (ρ : ℝ≥0∞) :=
    entropyNumber_le_of_externalCover_le k K ρ (le_of_not_gt hcover)
  exact (not_lt_of_ge hle) h

/-- Candidate entropy indices on either side of a radius immediately yield
the corresponding logarithmic covering bounds. This isolates the remaining
analytic calibration (`k` as a function of the inverse radius) from the
dyadic entropy/cover conversion. -/
theorem log_toNat_cover_bounds_of_entropy_bracket
    (K : Set X) (ρ : ℝ≥0) (kL kU : ℕ)
    (hlower : (ρ : ℝ≥0∞) < HaarQuarter.TheoremD.entropyNumber kL K)
    (hupper : HaarQuarter.TheoremD.entropyNumber kU K < (ρ : ℝ≥0∞)) :
    Metric.externalCoveringNumber ρ K ≠ ⊤ ∧
      ((kL - 1 : ℕ) : ℝ) * Real.log 2 <
        Real.log ((Metric.externalCoveringNumber ρ K).toNat : ℝ) ∧
      Real.log ((Metric.externalCoveringNumber ρ K).toNat : ℝ) ≤
        ((kU - 1 : ℕ) : ℝ) * Real.log 2 := by
  have hcoverL := externalCover_gt_of_radius_lt_entropyNumber kL K ρ hlower
  have hcoverU := externalCover_le_of_entropyNumber_lt kU K ρ hupper
  have hfinite : Metric.externalCoveringNumber ρ K ≠ ⊤ := by
    exact ne_top_of_le_ne_top (by simp) hcoverU
  have hNatL : 2 ^ (kL - 1) < (Metric.externalCoveringNumber ρ K).toNat := by
    rw [← ENat.natCast_toNat hfinite] at hcoverL
    exact_mod_cast hcoverL
  have hNatU : (Metric.externalCoveringNumber ρ K).toNat ≤ 2 ^ (kU - 1) := by
    rw [← ENat.natCast_toNat hfinite] at hcoverU
    exact_mod_cast hcoverU
  have hlogL : Real.log ((2 ^ (kL - 1) : ℕ) : ℝ) <
      Real.log ((Metric.externalCoveringNumber ρ K).toNat : ℝ) := by
    apply Real.log_lt_log (by positivity)
    exact_mod_cast hNatL
  have hlogU : Real.log ((Metric.externalCoveringNumber ρ K).toNat : ℝ) ≤
      Real.log ((2 ^ (kU - 1) : ℕ) : ℝ) := by
    by_cases hz : (Metric.externalCoveringNumber ρ K).toNat = 0
    · simp [hz]
      positivity
    · apply Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hz)
      exact_mod_cast hNatU
  have hpowL : Real.log ((2 ^ (kL - 1) : ℕ) : ℝ) =
      ((kL - 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [show ((2 ^ (kL - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (kL - 1) by norm_cast,
      Real.log_pow]
  have hpowU : Real.log ((2 ^ (kU - 1) : ℕ) : ℝ) =
      ((kU - 1 : ℕ) : ℝ) * Real.log 2 := by
    rw [show ((2 ^ (kU - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (kU - 1) by norm_cast,
      Real.log_pow]
  refine ⟨hfinite, ?_, ?_⟩
  · rw [← hpowL]
    exact hlogL
  · rw [← hpowU]
    exact hlogU

end BrownianSharp
