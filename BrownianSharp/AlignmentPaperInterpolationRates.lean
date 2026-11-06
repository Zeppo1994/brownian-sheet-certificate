import BrownianSharp.AlignmentPaperSequenceSplit
import BrownianSharp.AlignmentWidthRates

noncomputable section
namespace BrownianSharp.AlignmentPaperInterpolationRates

theorem logarithmicIndexRate_geometric_mean
    (r a₀ a₁ w C₀ C₁ : ℝ) (h₀ : 0 < C₀) (h₁ : 0 < C₁)
    (k : ℕ) (hk : 2 ≤ k) :
    (C₀ * logarithmicIndexRate r a₀ k) ^ w *
      (C₁ * logarithmicIndexRate r a₁ k) ^ (1 - w) =
      (C₀ ^ w * C₁ ^ (1 - w)) *
        logarithmicIndexRate r (w * a₀ + (1 - w) * a₁) k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hlog : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hrate (a : ℝ) : 0 < logarithmicIndexRate r a k :=
    AlignmentWidthRates.logarithmicIndexRate_pos r a hk
  have hlograte (a : ℝ) :
      Real.log (logarithmicIndexRate r a k) =
        -r * Real.log (k : ℝ) + a * Real.log (Real.log (k : ℝ)) := by
    unfold logarithmicIndexRate
    rw [Real.log_mul (Real.rpow_pos_of_pos hkR _).ne'
      (Real.rpow_pos_of_pos hlog _).ne', Real.log_rpow hkR, Real.log_rpow hlog]
  rw [Real.rpow_def_of_pos (mul_pos h₀ (hrate a₀)),
    Real.rpow_def_of_pos (mul_pos h₁ (hrate a₁)),
    Real.rpow_def_of_pos h₀, Real.rpow_def_of_pos h₁]
  rw [Real.log_mul h₀.ne' (hrate a₀).ne', Real.log_mul h₁.ne' (hrate a₁).ne',
    hlograte a₀, hlograte a₁]
  rw [← Real.exp_add, ← Real.exp_add]
  rw [← Real.exp_log (hrate (w * a₀ + (1 - w) * a₁))]
  rw [← Real.exp_add, hlograte]
  congr 1
  ring

theorem besov_interpolation_log_exponent (r θ D : ℝ) (hθ : θ ≠ 0) :
    (2 / θ) * (r * D + 1 / 2) +
      (1 - 2 / θ) * ((r + 1 / 2) * D + 1 / 2) =
      (r + 1 / 2 - 1 / θ) * D + 1 / 2 := by
  field_simp
  ring

end BrownianSharp.AlignmentPaperInterpolationRates
