import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith

/-!
# Strict quarter-scale decay

This certifies the asymptotic arithmetic of the error bounds, not the analytic
estimates that supply those bounds. Logarithmic exponents are arbitrary fixed
real numbers, hence may depend on a fixed dimension.
-/

open Filter
open scoped Topology

namespace HaarQuarter

theorem alignment_exponent_negative_iff (η : ℝ) :
    2 * η - 1 / 2 < 0 ↔ η < 1 / 4 := by
  constructor <;> intro h <;> linarith

theorem quartic_exponent_negative_iff (η : ℝ) :
    4 * η - 1 < 0 ↔ η < 1 / 4 := by
  constructor <;> intro h <;> linarith

/-- Every fixed logarithmic power is dominated by a strictly negative power. -/
theorem log_weighted_power_tendsto_zero (a k : ℝ) (ha : a < 0) :
    Tendsto (fun x : ℝ => x ^ a * (Real.log x) ^ k) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop k (neg_pos.mpr ha)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp [Real.rpow_neg (le_of_lt hx), div_eq_mul_inv, mul_comm]

theorem alignment_error_tendsto_zero (η k : ℝ) (hη : η < 1 / 4) :
    Tendsto (fun x : ℝ => x ^ (2 * η - 1 / 2) * (Real.log x) ^ k)
      atTop (𝓝 0) :=
  log_weighted_power_tendsto_zero _ _ ((alignment_exponent_negative_iff η).mpr hη)

theorem quartic_error_tendsto_zero (η k : ℝ) (hη : η < 1 / 4) :
    Tendsto (fun x : ℝ => x ^ (4 * η - 1) * (Real.log x) ^ k)
      atTop (𝓝 0) :=
  log_weighted_power_tendsto_zero _ _ ((quartic_exponent_negative_iff η).mpr hη)

/-- The exact `log(e x)` shift occurring in the accepted error estimates. -/
theorem log_e_weighted_power_tendsto_zero (a k : ℝ) (ha : a < 0) :
    Tendsto (fun x : ℝ => x ^ a * (Real.log (Real.exp 1 * x)) ^ k)
      atTop (𝓝 0) := by
  have hscale : Tendsto (fun x : ℝ => Real.exp 1 * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (Real.exp_pos 1)).mpr tendsto_id
  have hcomp := (log_weighted_power_tendsto_zero a k ha).comp hscale
  have hzero := hcomp.const_mul ((Real.exp 1) ^ a)⁻¹
  simp only [mul_zero] at hzero
  apply hzero.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_apply]
  rw [Real.mul_rpow (le_of_lt (Real.exp_pos 1)) (le_of_lt hx)]
  simp [← mul_assoc]

/-- The actual integer-depth alignment error tends to zero. -/
theorem alignment_error_nat_tendsto_zero (η k : ℝ) (hη : η < 1 / 4) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (2 * η - 1 / 2) *
      (Real.log (Real.exp 1 * (N : ℝ))) ^ k) atTop (𝓝 0) :=
  (log_e_weighted_power_tendsto_zero _ _
    ((alignment_exponent_negative_iff η).mpr hη)).comp tendsto_natCast_atTop_atTop

theorem quartic_error_nat_tendsto_zero (η k : ℝ) (hη : η < 1 / 4) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (4 * η - 1) *
      (Real.log (Real.exp 1 * (N : ℝ))) ^ k) atTop (𝓝 0) :=
  (log_e_weighted_power_tendsto_zero _ _
    ((quartic_exponent_negative_iff η).mpr hη)).comp tendsto_natCast_atTop_atTop

end HaarQuarter
