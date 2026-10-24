import BrownianSharp.ShapeGrowth

/-!
# Finite hyperbolic Haar energy tail

This module sums the existing per-grade Haar coefficient estimate over any
finite omitted range, retaining the sharp `2^-N (N+1)^(d-1)` prefactor.
-/

open scoped BigOperators

namespace BrownianSharp.AlignmentGaussianHaarTail

private theorem shifted_polynomial_le {N h q : ℕ} :
    ((N + h + 2 : ℝ) ^ q) ≤
      ((N + 1 : ℝ) ^ q) * ((h + 2 : ℝ) ^ q) := by
  have hsum : (N + h + 2 : ℝ) ≤ (N + 1 : ℝ) * (h + 2 : ℝ) := by
    push_cast
    nlinarith [Nat.zero_le N, Nat.zero_le h]
  calc
    _ ≤ ((N + 1 : ℝ) * (h + 2 : ℝ)) ^ q :=
      pow_le_pow_left₀ (by positivity) hsum q
    _ = _ := mul_pow _ _ _

/-- A finite tail of tensor-Haar feature energy has the sharp dyadic
exponential factor. The remaining finite polynomial-geometric sum is
explicit, so it can be bounded by any convenient convergent-series budget. -/
theorem finite_hyperbolic_energy_tail_bound (d N M : ℕ) (hd : 1 ≤ d) :
    (∑ h ∈ Finset.range M,
      (Nat.choose (N + 1 + h + d - 1) (d - 1) : ℝ) /
        (2 : ℝ) ^ (N + 1 + h)) ≤
      ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N *
        (∑ h ∈ Finset.range M,
          ((h + 2 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ (h + 1)) := by
  let q := d - 1
  have hterm (h : ℕ) :
      (Nat.choose (N + 1 + h + d - 1) (d - 1) : ℝ) /
        (2 : ℝ) ^ (N + 1 + h) ≤
      (((N + 1 : ℝ) ^ q) / (2 : ℝ) ^ N) *
        (((h + 2 : ℝ) ^ q) / (2 : ℝ) ^ (h + 1)) := by
    have hcount := hyperbolicCount_upper_shift hd (N + 1 + h)
    have hchoose : (Nat.choose (N + 1 + h + d - 1) (d - 1) : ℝ) ≤
        (N + h + 2 : ℝ) ^ q := by
      have htop : N + 1 + h + d - 1 = (N + 1 + h) + d - 1 := by omega
      rw [htop]
      convert hcount using 1 <;>
        simp [hyperbolicCount, q, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm, Nat.cast_add, Nat.cast_one] <;> ring
    have hpoly := shifted_polynomial_le (N := N) (h := h) (q := q)
    have hden : (2 : ℝ) ^ (N + 1 + h) =
        (2 : ℝ) ^ N * (2 : ℝ) ^ (h + 1) := by
      rw [show N + 1 + h = N + (h + 1) by omega, pow_add]
    rw [hden]
    calc
      _ ≤ ((N + h + 2 : ℝ) ^ q) /
          ((2 : ℝ) ^ N * (2 : ℝ) ^ (h + 1)) :=
            div_le_div_of_nonneg_right hchoose (by positivity)
      _ ≤ (((N + 1 : ℝ) ^ q) * ((h + 2 : ℝ) ^ q)) /
          ((2 : ℝ) ^ N * (2 : ℝ) ^ (h + 1)) :=
            div_le_div_of_nonneg_right hpoly (by positivity)
      _ = _ := by field_simp <;> ring
  calc
    _ ≤ ∑ h ∈ Finset.range M,
        (((N + 1 : ℝ) ^ q) / (2 : ℝ) ^ N) *
          (((h + 2 : ℝ) ^ q) / (2 : ℝ) ^ (h + 1)) := by
          apply Finset.sum_le_sum
          intro h hh
          exact hterm h
    _ = _ := by rw [Finset.mul_sum]

end BrownianSharp.AlignmentGaussianHaarTail
