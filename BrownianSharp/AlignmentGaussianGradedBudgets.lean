import BrownianSharp.AlignmentFractionalSharpBudgets
import Mathlib.Data.Fin.Rev

/-! Dimension-free finite sums for graded Gaussian diagonal contraction. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentGaussianGradedBudgets
open AlignmentGeometricRanks AlignmentFractionalSharpBudgets

theorem reflected_profile_sum_le_budget (k N : ℕ) :
    (∑ g : Fin (N+1), (((N-g.val+1:ℕ):ℝ)^k) * (1/2:ℝ)^(N-g.val)) ≤
      polynomialBudget (1/2) k := by
  have heq : (∑ g : Fin (N+1), (((N-g.val+1:ℕ):ℝ)^k) * (1/2:ℝ)^(N-g.val)) =
      ∑ g : Fin (N+1), (((g.val+1:ℕ):ℝ)^k) * (1/2:ℝ)^g.val := by
    simpa [Fin.revPerm, Fin.rev, Nat.add_sub_add_right] using
      (Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (N+1)))
        (fun g : Fin (N+1) => (((g.val+1:ℕ):ℝ)^k)*(1/2:ℝ)^g.val))
  rw [heq, Fin.sum_univ_eq_sum_range
    (fun g : ℕ => (((g+1:ℕ):ℝ)^k)*(1/2:ℝ)^g) (N+1)]
  exact Summable.sum_le_tsum (Finset.range (N+1)) (fun j hj => by positivity)
    (summable_polynomial_geometric (q:=1/2) (by norm_num) (by norm_num) k)

theorem contracted_layer_energy_identity {q η : ℝ} (hq : 0 < q)
    (hη : η^2=q/2) {N g : ℕ} (hg : g ≤ N) :
    (η^(N-g))^2*q^g = q^N*(1/2:ℝ)^(N-g) := by
  rw [← pow_mul, Nat.mul_comm (N-g) 2, pow_mul, hη, div_pow]
  have hpow : q^N = q^(N-g)*q^g := by
    rw [← pow_add, Nat.sub_add_cancel hg]
  rw [hpow, one_div_pow]
  ring

theorem contracted_low_energy_sum_le {q η : ℝ} (hq : 0 < q)
    (hη : η^2=q/2) (k N : ℕ) :
    (∑ g : Fin (N+1), (η^(N-g.val))^2 *
      (((g.val+1:ℕ):ℝ)^k*q^g.val)) ≤
      q^N*((N+1:ℕ):ℝ)^k*polynomialBudget (1/2) 0 := by
  calc
    _ ≤ ∑ g : Fin (N+1), q^N*((N+1:ℕ):ℝ)^k*(1/2:ℝ)^(N-g.val) := by
      apply Finset.sum_le_sum
      intro g hg
      have hgN := Nat.le_of_lt_succ g.isLt
      have hp : (((g.val+1:ℕ):ℝ)^k) ≤ ((N+1:ℕ):ℝ)^k := by
        exact pow_le_pow_left₀ (by positivity)
          (by exact_mod_cast Nat.add_le_add_right hgN 1) k
      rw [show (η^(N-g.val))^2*(((g.val+1:ℕ):ℝ)^k*q^g.val) =
        (((g.val+1:ℕ):ℝ)^k)*((η^(N-g.val))^2*q^g.val) by ring,
        contracted_layer_energy_identity hq hη hgN]
      nlinarith [mul_le_mul_of_nonneg_right hp
        (mul_nonneg (pow_nonneg hq.le N) (by positivity : 0≤(1/2:ℝ)^(N-g.val)))]
    _ = q^N*((N+1:ℕ):ℝ)^k *
        (∑ g : Fin (N+1), (1/2:ℝ)^(N-g.val)) := by rw [Finset.mul_sum]
    _ ≤ q^N*((N+1:ℕ):ℝ)^k*polynomialBudget (1/2) 0 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using reflected_profile_sum_le_budget 0 N

theorem reverse_dimension_weight_identity {N g : ℕ} (hg : g ≤ N) :
    (2:ℝ)^g = (2:ℝ)^N*(1/2:ℝ)^(N-g) := by
  have hpow : (2:ℝ)^N = (2:ℝ)^(N-g)*(2:ℝ)^g := by
    rw [← pow_add,Nat.sub_add_cancel hg]
  rw [hpow,one_div_pow]
  field_simp

theorem low_grade_dilation_cost_sum_le (k N : ℕ) :
    (∑ g : Fin (N+1), ((N-g.val:ℕ):ℝ) *
      ((2:ℝ)^g.val * ((g.val+1:ℕ):ℝ)^k)) ≤
      (2:ℝ)^N*((N+1:ℕ):ℝ)^k*polynomialBudget (1/2) 1 := by
  calc
    _ ≤ ∑ g : Fin (N+1), (2:ℝ)^N*((N+1:ℕ):ℝ)^k *
        (((N-g.val+1:ℕ):ℝ)*(1/2:ℝ)^(N-g.val)) := by
      apply Finset.sum_le_sum
      intro g hg
      have hgN := Nat.le_of_lt_succ g.isLt
      have hp : ((g.val+1:ℕ):ℝ)^k ≤ ((N+1:ℕ):ℝ)^k := by
        exact pow_le_pow_left₀ (by positivity)
          (by exact_mod_cast Nat.add_le_add_right hgN 1) k
      rw [reverse_dimension_weight_identity hgN]
      have hdiff : ((N-g.val:ℕ):ℝ) ≤ ((N-g.val+1:ℕ):ℝ) := by
        exact_mod_cast Nat.le_succ (N-g.val)
      calc
        _ ≤ ((N-g.val+1:ℕ):ℝ) *
          (((2:ℝ)^N*(1/2:ℝ)^(N-g.val))*((N+1:ℕ):ℝ)^k) := by gcongr
        _ = _ := by ring
    _ = (2:ℝ)^N*((N+1:ℕ):ℝ)^k *
        (∑ g : Fin (N+1), (((N-g.val+1:ℕ):ℝ)*(1/2:ℝ)^(N-g.val))) := by
          rw [Finset.mul_sum]
    _ ≤ (2:ℝ)^N*((N+1:ℕ):ℝ)^k*polynomialBudget (1/2) 1 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using reflected_profile_sum_le_budget 1 N

end BrownianSharp.AlignmentGaussianGradedBudgets
