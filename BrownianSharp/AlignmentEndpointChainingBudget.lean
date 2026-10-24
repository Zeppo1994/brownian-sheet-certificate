import BrownianSharp.AlignmentGeometricRanks
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentEndpointChainingBudget

private def q : ℝ := (2:ℝ)^(-((1:ℝ)/2))

theorem q_pos : 0<q := by
  dsimp [q]
  exact Real.rpow_pos_of_pos (by norm_num) _

theorem q_lt_one : q<1 := by
  dsimp [q]
  rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0:ℝ)<2)]
  exact Or.inl ⟨by norm_num, by norm_num⟩

theorem q_eq_half_rpow : q = (2:ℝ)^(-((1:ℝ)/2)) := by
  dsimp [q]

theorem q_pow_eq_half_rpow (n : ℕ) :
    q^n = (2:ℝ)^(-((n:ℝ)/2)) := by
  rw [q_eq_half_rpow, ← Real.rpow_natCast]
  rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  congr 1
  norm_cast
  ring

private def polynomialSequence (k : ℕ) : ℝ := ((k+2:ℕ):ℝ)*q^k

set_option maxHeartbeats 1000000 in
theorem polynomialSequence_summable : Summable polynomialSequence := by
  have hp := BrownianSharp.AlignmentGeometricRanks.summable_polynomial_geometric
    q_pos q_lt_one 2
  have hle : ∀ k : ℕ, polynomialSequence k ≤ 2*((k+1:ℕ):ℝ)^2*q^k := by
    intro k
    unfold polynomialSequence
    have hk : ((k+2:ℕ):ℝ) ≤ 2*((k+1:ℕ):ℝ)^2 := by
      have hk' : (k:ℝ)+2 ≤ 2*((k:ℝ)+1)^2 := by
        push_cast
        nlinarith [sq_nonneg ((k:ℝ)-1)]
      simpa [Nat.cast_add, Nat.cast_ofNat] using hk'
    have hqk : 0≤q^k := pow_nonneg q_pos.le k
    exact mul_le_mul_of_nonneg_right hk hqk
  have hmajor : Summable (fun k : ℕ => 2*((k+1:ℕ):ℝ)^2*q^k) := by
    simpa only [mul_assoc] using hp.mul_left 2
  exact hmajor.of_nonneg_of_le (fun k => mul_nonneg (by positivity)
    (pow_nonneg q_pos.le k)) hle

noncomputable def polynomialConstant : ℝ := ∑' k : ℕ, polynomialSequence k

theorem polynomialConstant_pos : 0<polynomialConstant := by
  have hs := polynomialSequence_summable
  have hterm' : 0 < ∑ k ∈ Finset.range 1, polynomialSequence k := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    change 0 < (2:ℝ)*q^0
    simp
  have hsum := hs.sum_le_tsum (Finset.range 1) (fun k _ => by
    unfold polynomialSequence
    exact mul_nonneg (by positivity) (pow_nonneg q_pos.le k))
  unfold polynomialConstant at hsum ⊢
  exact lt_of_lt_of_le hterm' hsum

private theorem sqrt_index_bound (n k : ℕ) :
    Real.sqrt (((n+k:ℕ):ℝ)+2) ≤ Real.sqrt ((n+1:ℕ):ℝ) * ((k+2:ℕ):ℝ) := by
  have hidx : ((n+k:ℕ):ℝ)+2 ≤ ((n+1:ℕ):ℝ) * ((k+2:ℕ):ℝ)^2 := by
    have hn : (0:ℝ)≤n := by positivity
    have hk : (0:ℝ)≤k := by positivity
    have hlin : ((n+k:ℕ):ℝ)+2 ≤ ((n+1:ℕ):ℝ) * ((k+2:ℕ):ℝ) := by
      push_cast
      nlinarith [mul_nonneg hn hk]
    calc
      ((n+k:ℕ):ℝ)+2 ≤ ((n+1:ℕ):ℝ) * ((k+2:ℕ):ℝ) := hlin
      _ ≤ ((n+1:ℕ):ℝ) * ((k+2:ℕ):ℝ)^2 := by
        apply mul_le_mul_of_nonneg_left
        · have hk2 : (1:ℝ) ≤ ((k+2:ℕ):ℝ) := by
            exact_mod_cast (show 1 ≤ k+2 by omega)
          nlinarith
        · positivity
  have hsqrt := Real.sqrt_le_sqrt hidx
  have hsqrtprod : Real.sqrt (((n+1:ℕ):ℝ) * ((k+2:ℕ):ℝ)^2) =
      Real.sqrt ((n+1:ℕ):ℝ) * ((k+2:ℕ):ℝ) := by
    rw [Real.sqrt_mul (by positivity : 0≤((n+1:ℕ):ℝ))]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
  rw [hsqrtprod] at hsqrt
  exact hsqrt

/-- The same index estimate with a fixed dimension factor carried in the
first-level scale. -/
theorem sqrt_dimension_index_bound (d n k : ℕ) :
    Real.sqrt (((d+2:ℕ):ℝ) * (((n+k:ℕ):ℝ)+2)) ≤
      Real.sqrt (((d+2:ℕ):ℝ) * ((n+1:ℕ):ℝ)) * ((k+2:ℕ):ℝ) := by
  calc
    Real.sqrt (((d+2:ℕ):ℝ) * (((n+k:ℕ):ℝ)+2)) =
        Real.sqrt ((d+2:ℕ):ℝ) * Real.sqrt (((n+k:ℕ):ℝ)+2) := by
          rw [Real.sqrt_mul (by positivity)]
    _ ≤ Real.sqrt ((d+2:ℕ):ℝ) *
        (Real.sqrt ((n+1:ℕ):ℝ) * ((k+2:ℕ):ℝ)) :=
      mul_le_mul_of_nonneg_left (sqrt_index_bound n k) (Real.sqrt_nonneg _)
    _ = Real.sqrt (((d+2:ℕ):ℝ) * ((n+1:ℕ):ℝ)) * ((k+2:ℕ):ℝ) := by
      rw [Real.sqrt_mul (by positivity)]
      ring

private theorem chainTerm_eq_q (n k : ℕ) :
    (2:ℝ)^(-(((n+k:ℕ):ℝ)/2)) * Real.sqrt (((n+k:ℕ):ℝ)+2) =
      q^n * (q^k * Real.sqrt (((n+k:ℕ):ℝ)+2)) := by
  rw [← q_pow_eq_half_rpow (n+k), pow_add]
  ring

/-- The chaining increments are summable for every starting level. -/
theorem summable_chaining_tail (n₀ : ℕ) :
    Summable (fun k : ℕ =>
      (2:ℝ)^(-(((n₀+k:ℕ):ℝ)/2)) * Real.sqrt (((n₀+k:ℕ):ℝ)+2)) := by
  have hpoly := polynomialSequence_summable
  have hdom : ∀ k : ℕ,
      (2:ℝ)^(-(((n₀+k:ℕ):ℝ)/2)) * Real.sqrt (((n₀+k:ℕ):ℝ)+2) ≤
        q^n₀ * Real.sqrt ((n₀+1:ℕ):ℝ) * polynomialSequence k := by
    intro k
    rw [chainTerm_eq_q]
    unfold polynomialSequence
    have hsqrt := sqrt_index_bound n₀ k
    have hqk : 0≤q^k := pow_nonneg q_pos.le k
    have hqn : 0≤q^n₀ := pow_nonneg q_pos.le n₀
    calc
      q^n₀ * (q^k * Real.sqrt (((n₀+k:ℕ):ℝ)+2)) ≤
          q^n₀ * (q^k * (Real.sqrt ((n₀+1:ℕ):ℝ) * ((k+2:ℕ):ℝ))) := by
            gcongr
      _ = q^n₀ * Real.sqrt ((n₀+1:ℕ):ℝ) * (((k+2:ℕ):ℝ)*q^k) := by
        ring
  have hnonneg : ∀ k : ℕ,
      0≤(2:ℝ)^(-(((n₀+k:ℕ):ℝ)/2)) * Real.sqrt (((n₀+k:ℕ):ℝ)+2) := by
    intro k
    positivity
  have hmajor : Summable (fun k => q^n₀ * Real.sqrt ((n₀+1:ℕ):ℝ) * polynomialSequence k) :=
    hpoly.mul_left _
  exact hmajor.of_nonneg_of_le hnonneg hdom

/-- Uniform Gaussian chaining budget: the tail is a fixed constant times its
first-level scale. -/
theorem chaining_tail_le (n₀ : ℕ) :
    (∑' k : ℕ,
      (2:ℝ)^(-(((n₀+k:ℕ):ℝ)/2)) * Real.sqrt (((n₀+k:ℕ):ℝ)+2)) ≤
      polynomialConstant * (2:ℝ)^(-((n₀:ℝ)/2)) * Real.sqrt ((n₀+1:ℕ):ℝ) := by
  have hs := summable_chaining_tail n₀
  have hpoly := polynomialSequence_summable
  have hdom : ∀ k : ℕ,
      (2:ℝ)^(-(((n₀+k:ℕ):ℝ)/2)) * Real.sqrt (((n₀+k:ℕ):ℝ)+2) ≤
        q^n₀ * Real.sqrt ((n₀+1:ℕ):ℝ) * polynomialSequence k := by
    intro k
    rw [chainTerm_eq_q]
    unfold polynomialSequence
    have hsqrt := sqrt_index_bound n₀ k
    have hqk : 0≤q^k := pow_nonneg q_pos.le k
    have hqn : 0≤q^n₀ := pow_nonneg q_pos.le n₀
    calc
      q^n₀ * (q^k * Real.sqrt (((n₀+k:ℕ):ℝ)+2)) ≤
          q^n₀ * (q^k * (Real.sqrt ((n₀+1:ℕ):ℝ) * ((k+2:ℕ):ℝ))) := by
            gcongr
      _ = q^n₀ * Real.sqrt ((n₀+1:ℕ):ℝ) * (((k+2:ℕ):ℝ)*q^k) := by ring
  have hmajor : Summable (fun k => q^n₀ * Real.sqrt ((n₀+1:ℕ):ℝ) * polynomialSequence k) :=
    hpoly.mul_left _
  calc
    _ ≤ ∑' k : ℕ, q^n₀ * Real.sqrt ((n₀+1:ℕ):ℝ) * polynomialSequence k :=
      hs.tsum_le_tsum hdom hmajor
    _ = q^n₀ * Real.sqrt ((n₀+1:ℕ):ℝ) * polynomialConstant := by
      rw [tsum_mul_left]
      rfl
    _ = polynomialConstant * (2:ℝ)^(-((n₀:ℝ)/2)) * Real.sqrt ((n₀+1:ℕ):ℝ) := by
      rw [q_pow_eq_half_rpow]
      ring

end BrownianSharp.AlignmentEndpointChainingBudget
