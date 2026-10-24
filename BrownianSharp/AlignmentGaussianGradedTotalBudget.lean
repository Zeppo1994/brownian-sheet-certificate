import BrownianSharp.AlignmentGaussianGradedBudgets
import BrownianSharp.AlignmentGaussianDiagonalCoordinates

noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentGaussianGradedTotalBudget
open AlignmentGaussianGradedBudgets AlignmentGaussianDiagonalCoordinates
open AlignmentGeometricRanks AlignmentFractionalSharpBudgets

theorem strict_shifted_polynomial_tail_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (k N M : ℕ) :
    (∑ j ∈ Finset.range M, ((N+1+j+1:ℕ):ℝ)^k*q^(N+1+j)) ≤
      q^N*((N+1:ℕ):ℝ)^k*polynomialBudget q k := by
  have hs := shifted_polynomial_geometric_sum_le hq0 hq1 k N (M+1)
  rw [Finset.sum_range_succ'] at hs
  have heq :
      (∑ j ∈ Finset.range M, ((N+(j+1)+1:ℕ):ℝ)^k*q^(N+(j+1))) =
      ∑ j ∈ Finset.range M, ((N+1+j+1:ℕ):ℝ)^k*q^(N+1+j) := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  rw [heq] at hs
  have h0 : 0 ≤ ((N+0+1:ℕ):ℝ)^k*q^(N+0) := by positivity
  linarith

theorem contracted_total_energy_sum_le {q η : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hη : η^2=q/2) (k N M : ℕ) :
    (∑ g ∈ Finset.range (N+1+M), (contractionScale η N g)^2 *
      (((g+1:ℕ):ℝ)^k*q^g)) ≤
      q^N*((N+1:ℕ):ℝ)^k*
        (polynomialBudget (1/2) 0 + polynomialBudget q k) := by
  rw [Finset.sum_range_add]
  have hlo :
      (∑ g ∈ Finset.range (N+1), (contractionScale η N g)^2 *
        (((g+1:ℕ):ℝ)^k*q^g)) ≤
      q^N*((N+1:ℕ):ℝ)^k*polynomialBudget (1/2) 0 := by
    have heq : (∑ g : Fin (N+1), (η^(N-g.val))^2 *
        (((g.val+1:ℕ):ℝ)^k*q^g.val)) =
      ∑ g ∈ Finset.range (N+1), (contractionScale η N g)^2 *
        (((g+1:ℕ):ℝ)^k*q^g) := by
      rw [← Fin.sum_univ_eq_sum_range (fun g : ℕ =>
        (contractionScale η N g)^2*(((g+1:ℕ):ℝ)^k*q^g)) (N+1)]
      apply Finset.sum_congr rfl
      intro g hg
      simp only [contractionScale, if_pos (Nat.le_of_lt_succ g.isLt)]
    rw [← heq]
    exact contracted_low_energy_sum_le hq0 hη k N
  have hhi :
      (∑ j ∈ Finset.range M, (contractionScale η N (N+1+j))^2 *
        (((N+1+j+1:ℕ):ℝ)^k*q^(N+1+j))) ≤
      q^N*((N+1:ℕ):ℝ)^k*polynomialBudget q k := by
    simp only [contractionScale, show ∀j : ℕ, ¬ N+1+j ≤ N from by omega,
      if_false, one_pow, one_mul]
    exact strict_shifted_polynomial_tail_le hq0 hq1 k N M
  calc
    _ ≤ q^N*((N+1:ℕ):ℝ)^k*polynomialBudget (1/2) 0 +
      q^N*((N+1:ℕ):ℝ)^k*polynomialBudget q k := add_le_add hlo hhi
    _ = _ := by ring

end BrownianSharp.AlignmentGaussianGradedTotalBudget
