import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! Numerical summability for the geometric rank allocation used in the
multilevel DKLL upper estimate. -/

open scoped BigOperators

namespace BrownianSharp.DKLLRankAllocation

/-- The decay factor corresponding to allocating a fraction `2^(-j/2)` of
the base rank to the `j`th coarser Haar layer. -/
noncomputable def layerRatio : ℝ := Real.sqrt (1 / 2)

theorem layerRatio_nonneg : 0 ≤ layerRatio := by
  simp [layerRatio]

theorem layerRatio_pos : 0 < layerRatio := by
  apply Real.sqrt_pos.2
  norm_num

theorem layerRatio_lt_one : layerRatio < 1 := by
  change Real.sqrt (1 / 2 : ℝ) < 1
  rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
  norm_num

/-- A polynomial multiplicity times the dyadic square-root allocation is
summable. This is the geometric-series estimate needed to sum the squared
errors over all high Haar grades. -/
theorem summable_polynomial_layer_ratio (k : ℕ) :
    Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ k * layerRatio ^ j) := by
  have hq : ‖layerRatio‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg layerRatio_nonneg]
    exact layerRatio_lt_one
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ k * layerRatio ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one k hq
  have hshift : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ k * layerRatio ^ (j + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr hbase
  have hratio := hshift.mul_left layerRatio⁻¹
  have heq (j : ℕ) :
      ((j + 1 : ℕ) : ℝ) ^ k * layerRatio ^ j =
        layerRatio⁻¹ * (((j + 1 : ℕ) : ℝ) ^ k * layerRatio ^ (j + 1)) := by
    rw [pow_succ]
    field_simp [ne_of_gt layerRatio_pos]
  convert hratio using 1
  · funext j
    exact heq j

/-- The finite sum of the layer multiplicities is bounded by the corresponding
infinite geometric-polynomial budget. -/
theorem finite_polynomial_layer_ratio_le (k J : ℕ) :
    (∑ j ∈ Finset.range J,
      ((j + 1 : ℕ) : ℝ) ^ k * layerRatio ^ j) ≤
      ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ k * layerRatio ^ j := by
  apply (summable_polynomial_layer_ratio k).sum_le_tsum
  intro j hj
  positivity [layerRatio_nonneg]

/-- Closed geometric budget for all layer errors of polynomial degree `k`. -/
noncomputable def layerBudget (k : ℕ) : ℝ :=
  ∑' j : ℕ, ((j + 1 : ℕ) : ℝ) ^ k * layerRatio ^ j

theorem layerBudget_nonneg (k : ℕ) : 0 ≤ layerBudget k := by
  unfold layerBudget
  exact tsum_nonneg fun j => by positivity [layerRatio_nonneg]

theorem finite_layer_budget (k J : ℕ) :
    (∑ j ∈ Finset.range J,
      ((j + 1 : ℕ) : ℝ) ^ k * layerRatio ^ j) ≤ layerBudget k := by
  simpa [layerBudget] using finite_polynomial_layer_ratio_le k J

/-- Integer rank allocated to the `j`th high-grade block, obtained by taking
the floor of the square-root geometric profile. -/
noncomputable def allocatedRank (D j : ℕ) : ℕ :=
  ⌊(D : ℝ) * layerRatio ^ j⌋₊

theorem allocatedRank_le_profile (D j : ℕ) :
    (allocatedRank D j : ℝ) ≤ (D : ℝ) * layerRatio ^ j := by
  unfold allocatedRank
  apply Nat.floor_le
  positivity [layerRatio_nonneg]

/-- Whenever a profile entry is at least two, flooring loses at most a factor
of two. This is the lower budget needed by finite-dimensional KGG estimates. -/
theorem half_profile_le_allocatedRank (D j : ℕ)
    (hlarge : 2 ≤ (D : ℝ) * layerRatio ^ j) :
    (D : ℝ) * layerRatio ^ j / 2 ≤ (allocatedRank D j : ℝ) := by
  have hnonneg : 0 ≤ (D : ℝ) * layerRatio ^ j := by positivity [layerRatio_nonneg]
  have hfloor := Nat.self_sub_floor_lt_one (a := (D : ℝ) * layerRatio ^ j)
  have hfloor' : (D : ℝ) * layerRatio ^ j - (allocatedRank D j : ℝ) < 1 := by
    simpa [allocatedRank] using hfloor
  have hbound : (D : ℝ) * layerRatio ^ j - 1 ≤ (allocatedRank D j : ℝ) := by
    linarith
  linarith

/-- Adding one to the integer budget absorbs the floor loss uniformly, even
when the geometric profile is smaller than two. This is the useful form for
finite-dimensional widths, whose denominator is `rank + 1`. -/
theorem half_profile_le_allocatedRank_add_one (D j : ℕ) :
    (D : ℝ) * layerRatio ^ j / 2 ≤ (allocatedRank D j : ℝ) + 1 := by
  by_cases hlarge : 2 ≤ (D : ℝ) * layerRatio ^ j
  · exact (half_profile_le_allocatedRank D j hlarge).trans (by linarith)
  · have hsmall : (D : ℝ) * layerRatio ^ j < 2 := by linarith
    have hnonneg : 0 ≤ (D : ℝ) * layerRatio ^ j := by positivity [layerRatio_nonneg]
    have hrank : 0 ≤ (allocatedRank D j : ℝ) := by positivity
    linarith

/-- Total cost of the square-root geometric rank allocation is at most four
times its base rank. -/
theorem sum_allocatedRank_le (D J : ℕ) :
    (∑ j ∈ Finset.range J, allocatedRank D j) ≤ 4 * D := by
  have hq : layerRatio ≤ 3 / 4 := by
    rw [show (3 / 4 : ℝ) = Real.sqrt (9 / 16) by norm_num]
    apply Real.sqrt_le_sqrt
    norm_num [layerRatio]
  have hqsum : ∀ J : ℕ,
      (∑ j ∈ Finset.range J, layerRatio ^ j) ≤ 4 := by
    intro J
    have hs := summable_geometric_of_lt_one layerRatio_nonneg layerRatio_lt_one
    have hsum := hs.sum_le_tsum (Finset.range J)
      (fun _ _ => by positivity [layerRatio_nonneg])
    have htsum : (∑' j : ℕ, layerRatio ^ j) = (1 - layerRatio)⁻¹ := by
      rw [tsum_geometric_of_lt_one layerRatio_nonneg layerRatio_lt_one]
    rw [htsum] at hsum
    have hden : (1 : ℝ) / 4 ≤ 1 - layerRatio := by linarith
    have hinv : (1 - layerRatio)⁻¹ ≤ 4 := by
      rw [show (4 : ℝ) = 1 / (1 / 4 : ℝ) by norm_num, ← one_div]
      exact (one_div_le_one_div (by linarith : 0 < 1 - layerRatio)
        (by norm_num : (0 : ℝ) < 1 / 4)).2 hden
    exact hsum.trans hinv
  have hsum_real :
      (∑ j ∈ Finset.range J, (allocatedRank D j : ℝ)) ≤ 4 * D := by
    calc
      _ ≤ ∑ j ∈ Finset.range J, (D : ℝ) * layerRatio ^ j := by
        apply Finset.sum_le_sum
        intro j hj
        exact allocatedRank_le_profile D j
      _ = (D : ℝ) * ∑ j ∈ Finset.range J, layerRatio ^ j := by rw [Finset.mul_sum]
      _ ≤ (D : ℝ) * 4 := by gcongr; exact hqsum J
      _ = 4 * (D : ℝ) := by ring
  exact_mod_cast hsum_real

/-- Allocate half the base rank to the geometric tail; combined with an exact
low-grade space of rank at most `D`, the total rank remains within `4D`. -/
theorem sum_half_allocatedRank_le (D J : ℕ) :
    (∑ j ∈ Finset.range J, allocatedRank (D / 2) j) ≤ 2 * D := by
  calc
    _ ≤ 4 * (D / 2) := sum_allocatedRank_le (D / 2) J
    _ ≤ 2 * D := by omega

theorem low_plus_half_allocatedRank_le (D lowRank J : ℕ)
    (hlow : lowRank ≤ D) :
    lowRank + (∑ j ∈ Finset.range J, allocatedRank (D / 2) j) ≤ 4 * D := by
  have hhigh := sum_half_allocatedRank_le D J
  omega

/-- The shifted geometric rank budget has a denominator comparable to the
base rank times its profile. The `D ≥ 4` case is the natural range for the
dyadic Haar dimensions used in the high-grade estimate. -/
theorem allocated_denominator_lower (D j : ℕ) (hD : 4 ≤ D) :
    (D : ℝ) * layerRatio ^ j / 8 ≤
      (allocatedRank (D / 2) j : ℝ) + 1 := by
  have hfloor := half_profile_le_allocatedRank_add_one (D / 2) j
  have hdiv : D ≤ 4 * (D / 2) := by omega
  have hdivR : (D : ℝ) ≤ 4 * ((D / 2 : ℕ) : ℝ) := by exact_mod_cast hdiv
  have hdivR' : (D : ℝ) / 4 ≤ ((D / 2 : ℕ) : ℝ) := by nlinarith
  have hprofile : (D : ℝ) / 4 * layerRatio ^ j ≤
      ((D / 2 : ℕ) : ℝ) * layerRatio ^ j := by
    exact mul_le_mul_of_nonneg_right hdivR'
      (pow_nonneg layerRatio_nonneg _)
  have hlow : ((D / 2 : ℕ) : ℝ) * layerRatio ^ j / 2 ≤
      (allocatedRank (D / 2) j : ℝ) + 1 := hfloor
  have htarget : (D : ℝ) * layerRatio ^ j / 8 =
      ((D : ℝ) / 4 * layerRatio ^ j) / 2 := by ring
  rw [htarget]
  exact (div_le_div_of_nonneg_right hprofile (by norm_num : (0 : ℝ) ≤ 2)).trans hlow

/-- A pointwise polynomial-geometric estimate on squared block errors sums to
the dimension-dependent constant `layerBudget k`, with no dependence on the
number of retained levels. -/
theorem sum_squared_layer_errors_le (k J : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (err : ℕ → ℝ)
    (herr : ∀ j ∈ Finset.range J,
      (err j) ^ 2 ≤ C * (((j + 1 : ℕ) : ℝ) ^ k * layerRatio ^ j)) :
    (∑ j ∈ Finset.range J, (err j) ^ 2) ≤ C * layerBudget k := by
  calc
    _ ≤ ∑ j ∈ Finset.range J,
        C * (((j + 1 : ℕ) : ℝ) ^ k * layerRatio ^ j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact herr j hj
    _ = C * ∑ j ∈ Finset.range J,
        ((j + 1 : ℕ) : ℝ) ^ k * layerRatio ^ j := by
      rw [Finset.mul_sum]
    _ ≤ C * layerBudget k :=
      mul_le_mul_of_nonneg_left (finite_layer_budget k J) hC

end BrownianSharp.DKLLRankAllocation
