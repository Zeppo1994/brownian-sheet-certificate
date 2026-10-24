import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

/-! Finite telescoping identity for the Fejér second-difference coefficients. -/

open scoped BigOperators

namespace BrownianSharp

theorem fejer_secondDifference_telescope (c : ℕ → ℂ) (J k : ℕ) (hk : k ≤ J) :
    (∑ j ∈ Finset.range J,
      ((j + 1 - k : ℕ) : ℂ) * (c j - 2 * c (j + 1) + c (j + 2))) =
      c k - ((J + 1 - k : ℕ) : ℂ) * c J + ((J - k : ℕ) : ℂ) * c (J + 1) := by
  induction J generalizing k with
  | zero =>
      have hk0 : k = 0 := by omega
      subst k
      simp
  | succ J ih =>
      by_cases hle : k ≤ J
      · have hstep := ih k hle
        rw [Finset.sum_range_succ]
        rw [hstep]
        have h1 : k ≤ J + 1 := by omega
        have h2 : k ≤ J := hle
        have hc1 : ((J + 1 - k : ℕ) : ℂ) = (J + 1 : ℂ) - k := by
          rw [Nat.cast_sub h1]
          simp
        have hc2 : ((J - k : ℕ) : ℂ) = (J : ℂ) - k := by
          rw [Nat.cast_sub h2]
        rw [hc1, hc2]
        have hc3 : ((J + 2 - k : ℕ) : ℂ) = (J + 2 : ℂ) - k := by
          rw [Nat.cast_sub (by omega)]
          simp
        rw [hc3]
        ring
      · have hkEq : k = J + 1 := by omega
        subst k
        have hsum : (∑ j ∈ Finset.range (J + 1),
            ((j + 1 - (J + 1) : ℕ) : ℂ) *
              (c j - 2 * c (j + 1) + c (j + 2))) = 0 := by
          apply Finset.sum_eq_zero
          intro j hj
          have hjlt : j < J + 1 := Finset.mem_range.mp hj
          have hzero : j + 1 - (J + 1) = 0 := by omega
          simp [hzero]
        rw [hsum]
        simp

theorem fejer_secondDifference_telescope_of_tail_zero
    (c : ℕ → ℂ) (J k : ℕ) (hk : k ≤ J)
    (hcJ : c J = 0) (hcJ1 : c (J + 1) = 0) :
    (∑ j ∈ Finset.range J,
      ((j + 1 - k : ℕ) : ℂ) * (c j - 2 * c (j + 1) + c (j + 2))) = c k := by
  rw [fejer_secondDifference_telescope c J k hk, hcJ, hcJ1]
  simp

end BrownianSharp
