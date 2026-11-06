import BrownianSharp.GaussianRows
import BrownianSharp.Moments

/-!
Transfer the independent-coordinate high-moment envelope to an independent
pair of standard Gaussian random variables on an arbitrary probability space.
This is the distributional bridge used after orthogonalizing two Gaussian rows.
-/

open MeasureTheory ProbabilityTheory

namespace BrownianSharp

/-- Integer-power form of the standard Gaussian moment-root bound:
`E|G|^(2k) ≤ (sqrt(2k))^(2k)`. -/
theorem standardGaussian_evenMoment_le_sqrt_power (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) ≤
      (Real.sqrt (2 * k : ℝ)) ^ (2 * k) := by
  rw [standardGaussian_evenMoment]
  have hdf : Nat.doubleFactorial (2 * k - 1) ≤ (2 * k) ^ k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
        have hrec : Nat.doubleFactorial (2 * (k + 1) - 1) =
            (2 * k + 1) * Nat.doubleFactorial (2 * k - 1) := by
          simpa [Nat.mul_add, Nat.mul_one, Nat.sub_add_comm] using
            Nat.doubleFactorial_add_one (2 * k)
        rw [hrec]
        calc
          (2 * k + 1) * Nat.doubleFactorial (2 * k - 1) ≤
              (2 * k + 2) * ((2 * k) ^ k) := by
            exact Nat.mul_le_mul (by omega) ih
          _ ≤ (2 * k + 2) * (2 * k + 2) ^ k := by
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) k)
          _ = (2 * (k + 1)) ^ (k + 1) := by
            rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_succ]
            ring
  have hdfR : (Nat.doubleFactorial (2 * k - 1) : ℝ) ≤ (2 * k : ℝ) ^ k := by
    exact_mod_cast hdf
  have hsqrt : (Real.sqrt (2 * k : ℝ)) ^ 2 = 2 * k :=
    Real.sq_sqrt (by positivity)
  calc
    (Nat.doubleFactorial (2 * k - 1) : ℝ) ≤ (2 * k : ℝ) ^ k := hdfR
    _ = (Real.sqrt (2 * k : ℝ)) ^ (2 * k) := by
      rw [pow_mul, hsqrt]

end BrownianSharp
