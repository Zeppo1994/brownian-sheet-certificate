import BrownianSharp.CubeSamplingExtension

/-! The positive sampling extension at depth `2n` has remainder of order
`2^-n`, below the sharp `sqrt(n+1) 2^-n` width scale. -/
noncomputable section
namespace BrownianSharp

theorem cubeSampling_doubleDepth_error (d n : ℕ) :
    Real.sqrt ((d:ℝ)*(2*((2:ℝ)^(2*n))⁻¹))=
      Real.sqrt (2*(d:ℝ))*((2:ℝ)^n)⁻¹ := by
  have hpow : (2:ℝ)^(2*n)=((2:ℝ)^n)^2 := by
    rw [← pow_mul]
    congr 1
    omega
  have heq : (d:ℝ)*(2*((2:ℝ)^(2*n))⁻¹)=
      (2*(d:ℝ))*(((2:ℝ)^n)⁻¹)^2 := by
    rw [hpow]
    field_simp
  rw [heq,Real.sqrt_mul (by positivity),Real.sqrt_sq_eq_abs,
    abs_of_pos (by positivity : (0:ℝ)<((2:ℝ)^n)⁻¹)]

theorem cubeSampling_doubleDepth_error_le (d n : ℕ) :
    Real.sqrt ((d:ℝ)*(2*((2:ℝ)^(2*n))⁻¹))≤
      Real.sqrt (2*(d:ℝ))*Real.sqrt ((n:ℝ)+1)/(2:ℝ)^n := by
  rw [cubeSampling_doubleDepth_error]
  have hs : (1:ℝ)≤Real.sqrt ((n:ℝ)+1) := by
    have h := Real.sqrt_le_sqrt (show (1:ℝ)≤(n:ℝ)+1 by linarith [show (0:ℝ)≤(n:ℝ) from Nat.cast_nonneg n])
    simpa using h
  have hmul := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (Real.sqrt_nonneg (2*(d:ℝ))) (inv_nonneg.mpr (by positivity : (0:ℝ)≤2^n)))
  convert hmul using 1 <;> ring

end BrownianSharp
