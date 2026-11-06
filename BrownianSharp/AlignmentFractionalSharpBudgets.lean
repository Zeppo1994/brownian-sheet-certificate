import BrownianSharp.AlignmentGeometricRanks
import Mathlib.Tactic

/-! Scalar depth choices for the sharp fractional width construction. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentFractionalSharpBudgets
open AlignmentGeometricRanks

/-- Linear sampling depth absorbs the actual Holder modulus at the sharp
function-error scale. -/
theorem exists_linear_depth_mesh_budget {γ r : ℝ} (hγ : 0 < γ) (hr : 0 < r) :
    ∃ K : ℕ, 0 < K ∧ ∀ n : ℕ,
      (2 * ((2:ℝ)^(K*(n+1)))⁻¹)^γ ≤ (2:ℝ)^(-r*n) := by
  let K : ℕ := Nat.ceil (r/γ) + 1
  have hK : 0 < K := by dsimp [K]; omega
  have hKγ : r+γ ≤ γ*(K:ℝ) := by
    have hc := Nat.le_ceil (r/γ)
    have hc' : r/γ ≤ ((K:ℝ)-1) := by
      dsimp [K]
      push_cast
      linarith
    have hm := (div_le_iff₀ hγ).mp hc'
    nlinarith
  refine ⟨K,hK,?_⟩
  intro n
  have hid : 2 * ((2:ℝ)^(K*(n+1)))⁻¹ =
      (2:ℝ)^(1-((K*(n+1):ℕ):ℝ)) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one, Real.rpow_natCast]
    rfl
  rw [hid, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  push_cast
  nlinarith

/-- Polynomial-geometric tails retain their starting exponential scale. -/
theorem shifted_polynomial_geometric_sum_le {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) (k T M : ℕ) :
    (∑ j ∈ Finset.range M, ((T+j+1:ℕ):ℝ)^k * q^(T+j)) ≤
      q^T * ((T+1:ℕ):ℝ)^k * polynomialBudget q k := by
  have hpoint (j : ℕ) : ((T+j+1:ℕ):ℝ)^k * q^(T+j) ≤
      (q^T * ((T+1:ℕ):ℝ)^k) * (((j+1:ℕ):ℝ)^k * q^j) := by
    have hpoly : ((T+j+1:ℕ):ℝ) ≤ ((T+1:ℕ):ℝ)*((j+1:ℕ):ℝ) := by
      push_cast
      nlinarith
    calc
      _ ≤ (((T+1:ℕ):ℝ)*((j+1:ℕ):ℝ))^k * q^(T+j) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hpoly k) (by positivity)
      _ = _ := by rw [mul_pow, pow_add]; ring
  have hs := (summable_polynomial_geometric hq0 hq1 k).sum_le_tsum
    (s:=Finset.range M) (fun j hj => by positivity)
  calc
    _ ≤ ∑ j ∈ Finset.range M,
        (q^T * ((T+1:ℕ):ℝ)^k) * (((j+1:ℕ):ℝ)^k * q^j) :=
      Finset.sum_le_sum fun j hj => hpoint j
    _ = (q^T * ((T+1:ℕ):ℝ)^k) *
        (∑ j ∈ Finset.range M, ((j+1:ℕ):ℝ)^k * q^j) := by rw [Finset.mul_sum]
    _ ≤ q^T * ((T+1:ℕ):ℝ)^k * polynomialBudget q k :=
      mul_le_mul_of_nonneg_left hs (by positivity)

/-- Convert the actual fractional dyadic profile to a geometric series. -/
theorem dyadic_decay_eq_pow (β : ℝ) (n : ℕ) :
    (2:ℝ)^(-β*(n:ℝ)) = ((2:ℝ)^(-β))^n := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]

end BrownianSharp.AlignmentFractionalSharpBudgets
