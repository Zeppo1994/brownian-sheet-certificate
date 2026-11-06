import BrownianSharp.ShapeGrowth
import BrownianSharp.Moments

/-! Scalar summation of the literal continuum hull-shell envelope.
The budget is the existing convergent polynomial/geometric series. -/
noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperContinuumShellBudget

/-- The exponential half-decay and the exact dyadic shell volume combine
into the geometric ratio used in the proved shell budget. -/
theorem half_exp_log_two_half :
    (1 / 2 : ℝ) * Real.exp (Real.log 2 / 2) = Real.sqrt (1 / 2 : ℝ) := by
  have he : Real.exp (Real.log 2 / 2) ^ 2 = 2 := by
    rw [← Real.exp_nat_mul]
    convert Real.exp_log (by norm_num : (0:ℝ) < 2) using 1 <;> congr 1 <;> ring
  symm
  apply (Real.sqrt_eq_iff_mul_self_eq (by norm_num : (0:ℝ) ≤ 1/2)
    (by positivity : 0 ≤ (1/2:ℝ)*Real.exp (Real.log 2/2))).2
  nlinarith

theorem shell_volume_exp_half (n h d : ℕ) :
    (1 / 2 : ℝ) ^ (n + h + d) *
      Real.exp ((Real.log 2 / 2) * ((h:ℝ)+1)) =
    (1 / 2 : ℝ) ^ (n + d) * Real.exp (Real.log 2 / 2) *
      (Real.sqrt (1 / 2 : ℝ)) ^ h := by
  have hidx : n+h+d = (n+d)+h := by omega
  rw [hidx, pow_add]
  have he : Real.exp ((Real.log 2/2)*((h:ℝ)+1)) =
      (Real.exp (Real.log 2/2))^h * Real.exp (Real.log 2/2) := by
    rw [mul_add, mul_one, Real.exp_add, mul_comm (Real.log 2/2) (h:ℝ), Real.exp_nat_mul]
  rw [he, ← half_exp_log_two_half, mul_pow]
  ring

/-- A single actual shell grade is dominated by a constant times the
polynomial-geometric summand. The dimension-dependent composition count
is absorbed using the existing sharp polynomial count bound. -/
theorem continuum_grade_envelope_le {d : ℕ} (hd : 1 ≤ d)
    (n h : ℕ) (p L : ℝ) :
    hyperbolicCount d (n+h) * (1/2:ℝ)^(n+h+d) *
      (2*p^2 * (L * (Nat.factorial (d-1):ℝ) *
        (((h:ℝ)+1)/((n:ℝ)+1))^(d-1))^2 *
        Real.exp ((Real.log 2/2)*((h:ℝ)+1))) ≤
    (2*p^2 * (L*(Nat.factorial (d-1):ℝ))^2 *
      (1/2:ℝ)^(n+d) * Real.exp (Real.log 2/2) /
      ((n:ℝ)+1)^(d-1)) *
      (((h:ℝ)+1)^(3*(d-1)) * (Real.sqrt (1/2:ℝ))^h) := by
  have hc := hyperbolicCount_add_upper_product hd n h
  have hnonneg : 0 ≤ (1/2:ℝ)^(n+h+d) *
      (2*p^2 * (L * (Nat.factorial (d-1):ℝ) *
        (((h:ℝ)+1)/((n:ℝ)+1))^(d-1))^2 *
        Real.exp ((Real.log 2/2)*((h:ℝ)+1))) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hc hnonneg
  calc
    _ ≤ (((n:ℝ)+1)^(d-1) * ((h:ℝ)+1)^(d-1)) *
        ((1/2:ℝ)^(n+h+d) *
        (2*p^2 * (L * (Nat.factorial (d-1):ℝ) *
          (((h:ℝ)+1)/((n:ℝ)+1))^(d-1))^2 *
          Real.exp ((Real.log 2/2)*((h:ℝ)+1)))) := by
            simpa only [mul_assoc] using hmul
    _ = _ := by
      rw [show (1/2:ℝ)^(n+h+d) *
          (2*p^2 * (L * (Nat.factorial (d-1):ℝ) *
            (((h:ℝ)+1)/((n:ℝ)+1))^(d-1))^2 *
            Real.exp ((Real.log 2/2)*((h:ℝ)+1))) =
          (2*p^2 * (L * (Nat.factorial (d-1):ℝ) *
            (((h:ℝ)+1)/((n:ℝ)+1))^(d-1))^2) *
          ((1/2:ℝ)^(n+h+d) * Real.exp ((Real.log 2/2)*((h:ℝ)+1))) by ring]
      rw [shell_volume_exp_half, div_pow, mul_pow]
      have hn : ((n:ℝ)+1)^(d-1) ≠ 0 := by positivity
      rw [show 3*(d-1) = (d-1)+(d-1)+(d-1) by omega, pow_add, pow_add]
      field_simp
      <;> ring

/-- Every finite prefix of continuum grade envelopes has one explicit
finite budget. No convergence or variance hypothesis is passed in. -/
theorem continuum_grade_partial_sum_le {d : ℕ} (hd : 1 ≤ d)
    (n N : ℕ) (p L : ℝ) :
    (∑ h ∈ Finset.range (N+1),
      hyperbolicCount d (n+h) * (1/2:ℝ)^(n+h+d) *
      (2*p^2 * (L * (Nat.factorial (d-1):ℝ) *
        (((h:ℝ)+1)/((n:ℝ)+1))^(d-1))^2 *
        Real.exp ((Real.log 2/2)*((h:ℝ)+1)))) ≤
    (2*p^2 * (L*(Nat.factorial (d-1):ℝ))^2 *
      (1/2:ℝ)^(n+d) * Real.exp (Real.log 2/2) /
      ((n:ℝ)+1)^(d-1)) * shellPolynomialBudget (d-1) := by
  calc
    _ ≤ ∑ h ∈ Finset.range (N+1),
        (2*p^2 * (L*(Nat.factorial (d-1):ℝ))^2 *
          (1/2:ℝ)^(n+d) * Real.exp (Real.log 2/2) /
          ((n:ℝ)+1)^(d-1)) *
          (((h:ℝ)+1)^(3*(d-1)) * (Real.sqrt (1/2:ℝ))^h) := by
            apply Finset.sum_le_sum
            intro h hh
            exact continuum_grade_envelope_le hd n h p L
    _ = (2*p^2 * (L*(Nat.factorial (d-1):ℝ))^2 *
          (1/2:ℝ)^(n+d) * Real.exp (Real.log 2/2) /
          ((n:ℝ)+1)^(d-1)) *
          (∑ h ∈ Finset.range (N+1),
            ((h:ℝ)+1)^(3*(d-1)) * (Real.sqrt (1/2:ℝ))^h) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (shellPolynomial_partial_le_budget (d-1) N)
      (by positivity)

end BrownianSharp.AlignmentPaperContinuumShellBudget
