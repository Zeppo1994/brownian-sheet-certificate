import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
An explicit elementary sufficient condition for the exponentially small
near-zero error in the p-th-root repair. This removes an informal comparison
between an exponential and a reciprocal dimension.
-/

namespace BrownianSharp

/-- If p² ≤ √D and D is large enough in terms of c and C, the first convex
concentration remainder is at most D⁻¹. -/
theorem exponential_remainder_le_inv_dimension
    {D p c C : ℝ} (hD : 0 < D) (hp : 0 < p) (hc : 0 < c) (hC : 0 < C)
    (hpSmall : p ^ 2 ≤ Real.sqrt D)
    (hlarge : 4 * C ≤ c * Real.sqrt (Real.sqrt D)) :
    Real.exp (-c * D / (C * p ^ 2)) ≤ 1 / D := by
  let R : ℝ := Real.sqrt D
  let t : ℝ := Real.sqrt R
  have hR : 0 < R := Real.sqrt_pos.mpr hD
  have ht : 0 < t := Real.sqrt_pos.mpr hR
  have hRsq : R ^ 2 = D := Real.sq_sqrt hD.le
  have htsq : t ^ 2 = R := Real.sq_sqrt hR.le
  have hlogt : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht
  have hlogD : Real.log D ≤ 4 * t := by
    have heq : Real.log D = 4 * Real.log t := by
      rw [← hRsq, Real.log_pow, ← htsq, Real.log_pow]
      ring
    rw [heq]
    linarith
  have hct : 4 * t ≤ c * R / C := by
    have hmul := mul_le_mul_of_nonneg_right hlarge ht.le
    rw [le_div_iff₀ hC]
    dsimp [t, R] at htsq ⊢
    nlinarith [hmul]
  have hratio : R / C ≤ D / (C * p ^ 2) := by
    apply (div_le_div_iff₀ hC (mul_pos hC (sq_pos_of_pos hp))).2
    have hmul := mul_le_mul_of_nonneg_left hpSmall hR.le
    dsimp [R] at hmul ⊢
    nlinarith [Real.sq_sqrt hD.le]
  have hexponent : Real.log D ≤ c * D / (C * p ^ 2) := by
    calc
      Real.log D ≤ 4 * t := hlogD
      _ ≤ c * R / C := hct
      _ ≤ c * D / (C * p ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_left hratio hc.le
        simpa [mul_div_assoc] using hmul
  calc
    Real.exp (-c * D / (C * p ^ 2)) ≤ Real.exp (-Real.log D) := by
      have heq : -c * D / (C * p ^ 2) = -(c * D / (C * p ^ 2)) := by ring
      rw [heq]
      exact Real.exp_le_exp.mpr (neg_le_neg hexponent)
    _ = 1 / D := by rw [Real.exp_neg, Real.exp_log hD]; simp [one_div]

end BrownianSharp
