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

/-- Every fixed logarithmic power is dominated by a strictly negative power. -/
theorem log_weighted_power_tendsto_zero (a k : ℝ) (ha : a < 0) :
    Tendsto (fun x : ℝ => x ^ a * (Real.log x) ^ k) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop k (neg_pos.mpr ha)).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp [Real.rpow_neg (le_of_lt hx), div_eq_mul_inv, mul_comm]

end HaarQuarter
