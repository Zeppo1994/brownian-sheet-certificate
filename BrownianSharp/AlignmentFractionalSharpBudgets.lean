import BrownianSharp.AlignmentGeometricRanks
import Mathlib.Tactic

/-! Scalar depth choices for the sharp fractional width construction. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentFractionalSharpBudgets
open AlignmentGeometricRanks

private theorem polynomial_half_power_bound (k n : ℕ) :
    (((n+1:ℕ):ℝ)^k) * (1/2:ℝ)^n ≤ polynomialBudget (1/2) k := by
  have hs := summable_polynomial_geometric (q:= (1/2:ℝ)) (by norm_num) (by norm_num) k
  exact hs.le_tsum n (fun m hm => by positivity)

/-- A sufficiently large linear cutoff makes a polynomial-weighted feature
variance tail smaller than the desired dyadic sharp squared error. -/
theorem exists_linear_depth_tail_budget {β r : ℝ} (hβ : 0 < β) (hr : 0 < r)
    (k : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (2:ℝ)^(-β * (K*(n+1):ℕ)) * ((K*(n+1)+1:ℕ):ℝ)^k ≤
        C * (2:ℝ)^(-2*r*n) * ((n+1:ℕ):ℝ) := by
  let K : ℕ := Nat.ceil ((2*r+1)/β) + 1
  have hK : 0 < K := by dsimp [K]; omega
  have hKβ : 2*r+1 ≤ β*(K:ℝ) := by
    have hc := Nat.le_ceil ((2*r+1)/β)
    have hc' : (2*r+1)/β ≤ (K:ℝ) := by
      dsimp [K]
      push_cast
      linarith
    exact (div_le_iff₀ hβ).mp hc' |>.trans_eq (mul_comm _ _)
  let B := polynomialBudget (1/2) k
  let C := 1 + ((K+1:ℕ):ℝ)^k * B
  have hB : 0 ≤ B := polynomialBudget_nonneg (by norm_num) k
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨K,hK,C,hC,?_⟩
  intro n
  have hdepth : ((K*(n+1)+1:ℕ):ℝ) ≤ ((K+1:ℕ):ℝ)*((n+1:ℕ):ℝ) := by
    push_cast
    nlinarith
  have hexp : -β * ((K*(n+1):ℕ):ℝ) ≤ -2*r*n - n := by
    push_cast
    nlinarith
  have hp : (2:ℝ)^(-β * ((K*(n+1):ℕ):ℝ)) ≤
      (2:ℝ)^(-2*r*n) * (1/2:ℝ)^n := by
    calc
      _ ≤ (2:ℝ)^(-2*r*n - n) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = (2:ℝ)^(-2*r*n) * (1/2:ℝ)^n := by
        rw [sub_eq_add_neg, Real.rpow_add (by norm_num)]
        congr 1
        rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
        simp [one_div, inv_pow]
  have hpoly := polynomial_half_power_bound k n
  have hscaled : (2:ℝ)^(-β * ((K*(n+1):ℕ):ℝ)) *
      ((K*(n+1)+1:ℕ):ℝ)^k ≤
      ((K+1:ℕ):ℝ)^k * B * (2:ℝ)^(-2*r*n) := by
    calc
      _ ≤ ((2:ℝ)^(-2*r*n) * (1/2:ℝ)^n) *
          ((((K+1:ℕ):ℝ)*((n+1:ℕ):ℝ))^k) := by
            apply mul_le_mul hp (pow_le_pow_left₀ (by positivity) hdepth k)
              (by positivity) (by positivity)
      _ = ((K+1:ℕ):ℝ)^k *
          ((((n+1:ℕ):ℝ)^k) * (1/2:ℝ)^n) * (2:ℝ)^(-2*r*n) := by
            rw [mul_pow]
            ring
      _ ≤ ((K+1:ℕ):ℝ)^k * B * (2:ℝ)^(-2*r*n) := by
        gcongr
  have hcoef : ((K+1:ℕ):ℝ)^k * B ≤ C := by dsimp [C]; linarith
  have hn : (1:ℝ) ≤ ((n+1:ℕ):ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  calc
    _ ≤ ((K+1:ℕ):ℝ)^k * B * (2:ℝ)^(-2*r*n) := hscaled
    _ ≤ C * (2:ℝ)^(-2*r*n) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ C * (2:ℝ)^(-2*r*n) * ((n+1:ℕ):ℝ) :=
      le_mul_of_one_le_right (by positivity) hn

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

/-- A linear cutoff absorbs every finite polynomial-geometric feature tail,
with one constant uniform in the eventual rectangular truncation depth. -/
theorem exists_linear_depth_tail_sum_budget {β r : ℝ}
    (hβ : 0 < β) (hr : 0 < r) (k : ℕ) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 < C ∧ ∀ n M : ℕ,
      (∑ j ∈ Finset.range M,
        (2:ℝ)^(-β*((K*(n+1)+j:ℕ):ℝ)) *
          ((K*(n+1)+j+1:ℕ):ℝ)^k) ≤
        C * (2:ℝ)^(-2*r*n) * ((n+1:ℕ):ℝ) := by
  let q : ℝ := (2:ℝ)^(-β)
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  obtain ⟨K,hK,C,hC,hbound⟩ := exists_linear_depth_tail_budget hβ hr k
  let B := polynomialBudget q k
  have hB : 0 ≤ B := polynomialBudget_nonneg hq0.le k
  refine ⟨K,hK,C*(B+1),by positivity,?_⟩
  intro n M
  have hs := shifted_polynomial_geometric_sum_le hq0 hq1 k (K*(n+1)) M
  have heq : (∑ j ∈ Finset.range M,
        (2:ℝ)^(-β*((K*(n+1)+j:ℕ):ℝ)) *
          ((K*(n+1)+j+1:ℕ):ℝ)^k) =
      ∑ j ∈ Finset.range M,
        ((K*(n+1)+j+1:ℕ):ℝ)^k * q^(K*(n+1)+j) := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [dyadic_decay_eq_pow]
    ring
  rw [heq]
  calc
    _ ≤ q^(K*(n+1)) * ((K*(n+1)+1:ℕ):ℝ)^k * B := hs
    _ = (2:ℝ)^(-β*((K*(n+1):ℕ):ℝ)) *
        ((K*(n+1)+1:ℕ):ℝ)^k * B := by rw [dyadic_decay_eq_pow]
    _ ≤ (C * (2:ℝ)^(-2*r*n) * ((n+1:ℕ):ℝ)) * B :=
      mul_le_mul_of_nonneg_right (hbound n) hB
    _ ≤ (C*(B+1)) * (2:ℝ)^(-2*r*n) * ((n+1:ℕ):ℝ) := by
      nlinarith [mul_nonneg (show 0 ≤ C*(2:ℝ)^(-2*r*n)*((n+1:ℕ):ℝ) by positivity)
        (show 0 ≤ B+1-B by linarith)]

end BrownianSharp.AlignmentFractionalSharpBudgets
