import BrownianSharp.AlignmentEndpointChainingBudget
import BrownianSharp.AlignmentFractionalSharpBudgets

/-! Summable Gaussian chaining tails at any positive Hölder exponent. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentHolderChainingBudget
open AlignmentGeometricRanks AlignmentFractionalSharpBudgets

def holderDecay (h : ℝ) : ℝ := (2:ℝ)^(-h)
def holderTailConstant (h : ℝ) : ℝ := 2*polynomialBudget (holderDecay h) 1

theorem holderDecay_pos (h : ℝ) : 0 < holderDecay h := by
  unfold holderDecay
  positivity

theorem holderDecay_lt_one {h : ℝ} (hh : 0 < h) : holderDecay h < 1 := by
  unfold holderDecay
  rw [← Real.rpow_zero (2:ℝ)]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)

theorem holderTailConstant_nonneg (h : ℝ) : 0 ≤ holderTailConstant h :=
  mul_nonneg (by norm_num) (polynomialBudget_nonneg (holderDecay_pos h).le 1)

theorem sqrt_index_bound (n k : ℕ) :
    Real.sqrt (((n+k:ℕ):ℝ)+2) ≤ Real.sqrt ((n+1:ℕ):ℝ)*((k+2:ℕ):ℝ) := by
  have hprod : (((n+k:ℕ):ℝ)+2) ≤ ((n+1:ℕ):ℝ)*((k+2:ℕ):ℝ) := by
    push_cast
    nlinarith
  have hsq : Real.sqrt ((k+2:ℕ):ℝ) ≤ ((k+2:ℕ):ℝ) := by
    have hs := Real.sq_sqrt (show 0 ≤ ((k+2:ℕ):ℝ) by positivity)
    have hn := Real.sqrt_nonneg ((k+2:ℕ):ℝ)
    have hk : (1:ℝ) ≤ ((k+2:ℕ):ℝ) := by exact_mod_cast (by omega : 1 ≤ k+2)
    nlinarith
  calc
    _ ≤ Real.sqrt (((n+1:ℕ):ℝ)*((k+2:ℕ):ℝ)) := Real.sqrt_le_sqrt hprod
    _ = Real.sqrt ((n+1:ℕ):ℝ)*Real.sqrt ((k+2:ℕ):ℝ) :=
      Real.sqrt_mul (by positivity) _
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)

theorem holder_tail_majorant (h : ℝ) (n k : ℕ) :
    (2:ℝ)^(-h*((n+k:ℕ):ℝ))*Real.sqrt (((n+k:ℕ):ℝ)+2) ≤
      (holderDecay h)^n * Real.sqrt ((n+1:ℕ):ℝ) *
        (2*(((k+1:ℕ):ℝ)*(holderDecay h)^k)) := by
  have hq0 : 0 ≤ holderDecay h := (holderDecay_pos h).le
  rw [dyadic_decay_eq_pow, pow_add]
  change (holderDecay h)^n*(holderDecay h)^k*Real.sqrt (((n+k:ℕ):ℝ)+2) ≤ _
  have hs := sqrt_index_bound n k
  have hk : ((k+2:ℕ):ℝ) ≤ 2*((k+1:ℕ):ℝ) := by push_cast; linarith
  calc
    _ ≤ (holderDecay h)^n*(holderDecay h)^k*
      (Real.sqrt ((n+1:ℕ):ℝ)*((k+2:ℕ):ℝ)) := by gcongr
    _ = ((holderDecay h)^n*Real.sqrt ((n+1:ℕ):ℝ)*(holderDecay h)^k) *
      ((k+2:ℕ):ℝ) := by ring
    _ ≤ ((holderDecay h)^n*Real.sqrt ((n+1:ℕ):ℝ)*(holderDecay h)^k) *
      (2*((k+1:ℕ):ℝ)) := mul_le_mul_of_nonneg_left hk (by positivity)
    _ = _ := by ring

theorem summable_holder_chaining_tail {h : ℝ} (hh : 0 < h) (n : ℕ) :
    Summable (fun k : ℕ =>
      (2:ℝ)^(-h*((n+k:ℕ):ℝ))*Real.sqrt (((n+k:ℕ):ℝ)+2)) := by
  have hs := summable_polynomial_geometric (holderDecay_pos h) (holderDecay_lt_one hh) 1
  have hm := (hs.mul_left 2).mul_left
    ((holderDecay h)^n*Real.sqrt ((n+1:ℕ):ℝ))
  apply hm.of_nonneg_of_le
  · intro k
    positivity
  · intro k
    simpa only [pow_one] using holder_tail_majorant h n k

theorem holder_chaining_tail_le {h : ℝ} (hh : 0 < h) (n : ℕ) :
    (∑' k : ℕ, (2:ℝ)^(-h*((n+k:ℕ):ℝ))*Real.sqrt (((n+k:ℕ):ℝ)+2)) ≤
      holderTailConstant h*(2:ℝ)^(-h*(n:ℝ))*Real.sqrt ((n+1:ℕ):ℝ) := by
  have hs := summable_polynomial_geometric (holderDecay_pos h) (holderDecay_lt_one hh) 1
  have hm := (hs.mul_left 2).mul_left
    ((holderDecay h)^n*Real.sqrt ((n+1:ℕ):ℝ))
  calc
    _ ≤ ∑' k : ℕ, (holderDecay h)^n*Real.sqrt ((n+1:ℕ):ℝ) *
        (2*(((k+1:ℕ):ℝ)^1*(holderDecay h)^k)) :=
      (summable_holder_chaining_tail hh n).tsum_le_tsum
        (fun k => by simpa only [pow_one] using holder_tail_majorant h n k) hm
    _ = (holderDecay h)^n*Real.sqrt ((n+1:ℕ):ℝ) *
        (2*polynomialBudget (holderDecay h) 1) := by
      rw [tsum_mul_left,tsum_mul_left]
      rfl
    _ = _ := by
      rw [dyadic_decay_eq_pow]
      dsimp [holderTailConstant,holderDecay]
      ring

end BrownianSharp.AlignmentHolderChainingBudget
