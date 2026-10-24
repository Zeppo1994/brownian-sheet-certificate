import BrownianSharp.AlignmentScaledSetWidth
import BrownianSharp.AlignmentWidthRates
import BrownianSharp.AlignmentOperatorStatements
import BrownianSharp.AlignmentOperatorNumbers
import BrownianSharp.AlignmentOperatorWidthIndexShift

/-! Generic assembly lemmas for scaling a known width upper bound and then
combining it with an entropy lower bound. -/

noncomputable section
open scoped ENNReal

namespace BrownianSharp.AlignmentScaledWidthRates

open BrownianSharp.AlignmentScaledSetWidth
open BrownianSharp.AlignmentWidthRates
open BrownianSharp.AlignmentOperatorStatements
open BrownianSharp.AlignmentOperatorNumbers
open BrownianSharp.AlignmentOperatorWidthIndexShift
open BrownianSharp.Latest
open HaarQuarter.TheoremD.Width

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A rate upper bound for a model set transfers through positive dilation and
inclusion; combining it with an entropy lower bound gives the two-sided
Kolmogorov-width rate for the target set. -/
theorem twoSidedWidthRate_of_entropy_lower_and_scaled_width_upper
    [CompleteSpace X] [MeasurableSpace X] [BorelSpace X]
    (K J : Set X) (A R s a : ℝ)
    (hK : K ⊆ scalarImage A J) (hA : 0 < A) (hR : 0 ≤ R)
    (hzeroJ : kolmogorovWidth J 0 ≤ ENNReal.ofReal R)
    (hs : 0 < s) (ha : 0 ≤ a)
    (hEntropy : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ENNReal.ofReal (c * logarithmicIndexRate s a n) ≤
        HaarQuarter.TheoremD.entropyNumber n K)
    (hUpperJ : ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      kolmogorovWidth J n ≤ ENNReal.ofReal (C * logarithmicIndexRate s a n)) :
    Latest.twoSidedWidthRate K s a := by
  have hzeroK : kolmogorovWidth K 0 ≤ ENNReal.ofReal (A * R) :=
    kolmogorovWidth_le_of_subset_scalarImage A R hK 0 hA hR hzeroJ
  obtain ⟨C, hC, n₀, hU⟩ := hUpperJ
  have hUpperK : ∃ C' : ℝ, 0 < C' ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      kolmogorovWidth K n ≤ ENNReal.ofReal (C' * logarithmicIndexRate s a n) := by
    refine ⟨A * C, mul_pos hA hC, n₀, ?_⟩
    intro n hn
    calc
      kolmogorovWidth K n ≤
          ENNReal.ofReal (A * (C * logarithmicIndexRate s a n)) :=
        kolmogorovWidth_le_of_subset_scalarImage A
          (C * logarithmicIndexRate s a n) hK n hA
          (mul_nonneg hC.le (logarithmicIndexRate_nonneg s a n)) (hU n hn)
      _ = ENNReal.ofReal ((A * C) * logarithmicIndexRate s a n) := by
        congr 1
        ring
  exact twoSidedWidthRate_of_entropy_lower_and_width_upper K s a (A * R)
    hs ha (mul_nonneg hA.le hR) hzeroK hEntropy hUpperK

/-- Convert the legacy width-index convention (`rank ≤ m`) to the manuscript's
strict operator convention (`rank < k`), with the necessary one-index shift. -/
theorem operator_width_rate_of_legacy
    (K : Set X) (r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a)
    (hlegacy : Latest.twoSidedWidthRate K r a) :
    AlignmentOperatorStatements.twoSidedWidthRate K r a := by
  obtain ⟨c, C, hc, hC, k₀, hk₀, hwidth⟩ := hlegacy
  let k₁ := max (k₀ + 1) 3
  have hk₁ : 3 ≤ k₁ := by dsimp [k₁]; omega
  have hk₀' : k₀ + 1 ≤ k₁ := by dsimp [k₁]; exact le_max_left _ _
  obtain ⟨c', C', hc', hC', hshift⟩ :=
    twoSided_width_index_shift K r a hr ha c C hc hC k₁ hk₁ (by
      intro k hk
      have hkm : k₀ ≤ k - 1 := by omega
      exact hwidth (k - 1) hkm)
  refine ⟨c', C', hc', hC', k₁, by omega, ?_⟩
  intro k hk
  have hkpos : 1 ≤ k := by omega
  have hEq := operatorKolmogorovNumber_eq_width_pred K hkpos
  simpa only [hEq] using hshift k hk

end BrownianSharp.AlignmentScaledWidthRates

