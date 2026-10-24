import BrownianSharp.DKLLRankAllocation
import Mathlib.Tactic

/-! Numerical summation of a dyadic high-grade error profile. This is the
scalar endpoint needed after the finite-layer orthogonal approximation has
supplied the per-layer estimates. -/

open scoped BigOperators

namespace BrownianSharp.DKLLFiniteLayerRate

noncomputable section

def dyadicSquare (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹ ^ 2

theorem dyadicSquare_nonneg (n : ℕ) : 0 ≤ dyadicSquare n := by
  unfold dyadicSquare
  positivity

theorem dyadicSquare_pos (n : ℕ) : 0 < dyadicSquare n := by
  unfold dyadicSquare
  positivity

/-- The exact normalization occurring in the KGG layer estimate cancels the
base Haar-layer dimension: `log M · 2⁻ⁿ Sₙ / (2ⁿ Sₙ)` is the squared
dyadic scale times `log M`. -/
theorem normalized_base_factor_le {n : ℕ} (S D M G : ℝ)
    (hS : 0 < S)
    (hD : D = (2 : ℝ) ^ n * S)
    (hlog : M ≤ G * ((n : ℝ) + 1)) :
    M * (((2 : ℝ) ^ n)⁻¹ * S / D) ≤
      G * ((n : ℝ) + 1) * dyadicSquare n := by
  have hpow : 0 < (2 : ℝ) ^ n := by positivity
  have hratio : ((2 : ℝ) ^ n)⁻¹ * S / D = dyadicSquare n := by
    rw [hD]
    unfold dyadicSquare
    field_simp
  rw [hratio]
  exact mul_le_mul_of_nonneg_right hlog (dyadicSquare_nonneg n)

/-- If the grid logarithm and base rank have already been absorbed into the
base factor `b`, polynomial multiplicity across Haar grades sums to the
dimension-only budget `layerBudget`. The terminal sampling remainder is
included at the same scale. -/
theorem total_squared_error_bound {d n J : ℕ}
    (A G T b : ℝ) (hA : 0 ≤ A) (hT : 0 ≤ T)
    (hb : 0 ≤ b)
    (hbupper : b ≤ G * ((n : ℝ) + 1) * dyadicSquare n)
    (err : ℕ → ℝ) (tail : ℝ)
    (herr : ∀ j ∈ Finset.range J,
      (err j) ^ 2 ≤ A * b *
        (((j + 1 : ℕ) : ℝ) ^ d * BrownianSharp.DKLLRankAllocation.layerRatio ^ j))
    (htail : tail ^ 2 ≤ T * dyadicSquare n) :
    (∑ j ∈ Finset.range J, (err j) ^ 2) ≤
        (A * G * BrownianSharp.DKLLRankAllocation.layerBudget d) *
          (((n : ℝ) + 1) * dyadicSquare n) ∧
      tail ^ 2 ≤ T * (((n : ℝ) + 1) * dyadicSquare n) := by
  have hbudget := BrownianSharp.DKLLRankAllocation.sum_squared_layer_errors_le
    d J (A * b) (mul_nonneg hA hb) err herr
  have hlayer :
      (∑ j ∈ Finset.range J, (err j) ^ 2) ≤
        (A * G * BrownianSharp.DKLLRankAllocation.layerBudget d) *
          (((n : ℝ) + 1) * dyadicSquare n) := by
    calc
      _ ≤ A * b * BrownianSharp.DKLLRankAllocation.layerBudget d := by
        simpa [mul_assoc] using hbudget
      _ ≤ (A * G * BrownianSharp.DKLLRankAllocation.layerBudget d) *
          (((n : ℝ) + 1) * dyadicSquare n) := by
        have hfac : 0 ≤ A * BrownianSharp.DKLLRankAllocation.layerBudget d :=
          mul_nonneg hA (BrownianSharp.DKLLRankAllocation.layerBudget_nonneg d)
        have hmul := mul_le_mul_of_nonneg_left hbupper hfac
        nlinarith [hmul]
  have htail' : tail ^ 2 ≤ T * (((n : ℝ) + 1) * dyadicSquare n) := by
    have hnp : 1 ≤ ((n : ℝ) + 1) := by
      exact_mod_cast (show 1 ≤ n + 1 by omega)
    have hmul := mul_le_mul_of_nonneg_right hnp (mul_nonneg hT (dyadicSquare_nonneg n))
    nlinarith [htail]
  exact ⟨hlayer, htail'⟩

end
end BrownianSharp.DKLLFiniteLayerRate
