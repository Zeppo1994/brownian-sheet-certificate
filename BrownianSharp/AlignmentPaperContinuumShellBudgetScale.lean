import BrownianSharp.AlignmentPaperContinuumShellBudget

/-! Normalize the convergent continuum shell budget to the literal layer
cardinality `2^n * S_n`. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperContinuumShellBudgetScale
open AlignmentPaperContinuumShellBudget

def continuumShellConstant (d : ℕ) (L : ℝ) : ℝ :=
  2 * (L*(Nat.factorial (d-1):ℝ))^2 * (1/2:ℝ)^d *
    Real.exp (Real.log 2/2) * shellPolynomialBudget (d-1)

theorem shellPolynomialBudget_pos (q : ℕ) : 0 < shellPolynomialBudget q := by
  have hb := shellPolynomial_partial_le_budget q 0
  norm_num at hb
  exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 1) hb

theorem continuumShellConstant_pos (d : ℕ) {L : ℝ} (hL : 0 < L) :
    0 < continuumShellConstant d L := by
  unfold continuumShellConstant
  have hb := shellPolynomialBudget_pos (d-1)
  positivity

/-- The finite continuum shell sum has the intended inverse-layer-cardinality
scale. Its constant depends only on dimension and the fixed overlap factor. -/
theorem continuum_grade_partial_sum_le_layer_card {d : ℕ} (hd : 1 ≤ d)
    (n N : ℕ) (p L : ℝ) :
    (∑ h ∈ Finset.range (N+1),
      hyperbolicCount d (n+h) * (1/2:ℝ)^(n+h+d) *
      (2*p^2 * (L * (Nat.factorial (d-1):ℝ) *
        (((h:ℝ)+1)/((n:ℝ)+1))^(d-1))^2 *
        Real.exp ((Real.log 2/2)*((h:ℝ)+1)))) ≤
    continuumShellConstant d L * p^2 /
      ((2:ℝ)^n * hyperbolicCount d n) := by
  have hSn := hyperbolicCount_pos (n:=n) hd
  have htwo : 0 < (2:ℝ)^n := by positivity
  have hn : 0 < ((n:ℝ)+1)^(d-1) := by positivity
  have hc := hyperbolicCount_upper_shift hd n
  have hb := (shellPolynomialBudget_pos (d-1)).le
  have hnum : 0 ≤ continuumShellConstant d L * p^2 := by
    unfold continuumShellConstant
    positivity
  calc
    _ ≤ (2*p^2 * (L*(Nat.factorial (d-1):ℝ))^2 *
        (1/2:ℝ)^(n+d) * Real.exp (Real.log 2/2) /
        ((n:ℝ)+1)^(d-1)) * shellPolynomialBudget (d-1) :=
      continuum_grade_partial_sum_le hd n N p L
    _ = continuumShellConstant d L * p^2 /
        ((2:ℝ)^n * ((n:ℝ)+1)^(d-1)) := by
      unfold continuumShellConstant
      rw [pow_add]
      simp only [div_pow, one_pow]
      field_simp
      <;> ring
    _ ≤ _ := by
      apply (div_le_div_iff₀ (mul_pos htwo hn) (mul_pos htwo hSn)).2
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hc htwo.le) hnum

end BrownianSharp.AlignmentPaperContinuumShellBudgetScale
