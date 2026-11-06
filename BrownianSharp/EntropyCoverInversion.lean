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

end BrownianSharp
