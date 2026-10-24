import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
Concrete spectral-weight comparison for the tensor-product Matérn remark.

For positive smoothness, the Matérn precision weight
`(κ² + ξ²)^s` is uniformly comparable to the Bessel-potential weight
`(1 + ξ²)^s`; this is the scalar analytic step behind the full-line
Sobolev/RKHS comparison. This file does not assert the covariance-feature
identification or restriction theorem.
-/

noncomputable section

namespace BrownianSharp.AlignmentMaternSpectralWeights

def maternPrecisionWeight (κ s ξ : ℝ) : ℝ := (κ ^ 2 + ξ ^ 2) ^ s

def besselPrecisionWeight (s ξ : ℝ) : ℝ := (1 + ξ ^ 2) ^ s

/-- Uniform equivalence of the one-dimensional Matérn and Bessel precision
weights. The constants depend on the fixed range parameter `κ` and order `s`,
but not on frequency `ξ`. -/
theorem matern_precision_weight_comparable
    (κ s ξ : ℝ) (hκ : 0 < κ) (hs : 0 < s) :
    Real.rpow (min 1 (κ ^ 2)) s * besselPrecisionWeight s ξ ≤
        maternPrecisionWeight κ s ξ ∧
      maternPrecisionWeight κ s ξ ≤
        Real.rpow (max 1 (κ ^ 2)) s * besselPrecisionWeight s ξ := by
  have hlow : min 1 (κ ^ 2) * (1 + ξ ^ 2) ≤ κ ^ 2 + ξ ^ 2 := by
    by_cases h : κ ^ 2 ≤ 1
    · rw [min_eq_right h]
      nlinarith [sq_nonneg ξ]
    · rw [min_eq_left (le_of_not_ge h)]
      nlinarith [sq_nonneg ξ]
  have hupp : κ ^ 2 + ξ ^ 2 ≤ max 1 (κ ^ 2) * (1 + ξ ^ 2) := by
    by_cases h : κ ^ 2 ≤ 1
    · rw [max_eq_left h]
      nlinarith [sq_nonneg ξ]
    · rw [max_eq_right (le_of_not_ge h)]
      nlinarith [sq_nonneg ξ]
  have hmin : 0 < min 1 (κ ^ 2) := lt_min (by norm_num) (sq_pos_of_pos hκ)
  have hmax : 0 < max 1 (κ ^ 2) := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hb : 0 < 1 + ξ ^ 2 := by positivity
  have hm : 0 < κ ^ 2 + ξ ^ 2 := by positivity
  constructor
  · calc
      Real.rpow (min 1 (κ ^ 2)) s * besselPrecisionWeight s ξ
          = Real.rpow (min 1 (κ ^ 2) * (1 + ξ ^ 2)) s := by
              simpa [besselPrecisionWeight] using
                (Real.mul_rpow hmin.le hb.le).symm
      _ ≤ Real.rpow (κ ^ 2 + ξ ^ 2) s :=
        Real.rpow_le_rpow (by positivity) hlow hs.le
      _ = maternPrecisionWeight κ s ξ := rfl
  · calc
      maternPrecisionWeight κ s ξ = Real.rpow (κ ^ 2 + ξ ^ 2) s := rfl
      _ ≤ Real.rpow (max 1 (κ ^ 2) * (1 + ξ ^ 2)) s :=
        Real.rpow_le_rpow (by positivity) hupp hs.le
      _ = Real.rpow (max 1 (κ ^ 2)) s * besselPrecisionWeight s ξ := by
        simpa [besselPrecisionWeight] using Real.mul_rpow hmax.le hb.le

end BrownianSharp.AlignmentMaternSpectralWeights
