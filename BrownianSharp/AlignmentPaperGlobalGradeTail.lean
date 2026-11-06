import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import BrownianSharp.AlignmentPaperJointAdaptiveScalarSums

/-! Uniform tails for the polynomially weighted exponential grade envelope. -/

noncomputable section

open scoped BigOperators

namespace BrownianSharp.AlignmentPaperGlobalGradeTail

open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums

/-- A polynomially weighted exponential tail is bounded uniformly by an
exponential at half the decay rate, with a constant independent of the cutoff. -/
theorem polynomial_exp_tail_le {δ b : ℝ} (hδ : 0 < δ) (hb : 0 ≤ b) :
    ∃ H : ℝ, 0 < H ∧ ∀ M : ℕ,
      (∑' n : ℕ, if M ≤ n then (n + 1 : ℝ) ^ b * Real.exp (-δ * n) else 0) ≤
        H * Real.exp (-δ * (M : ℝ) / 2) := by
  let k : ℕ := Nat.ceil b
  let g : ℕ → ℝ := fun n => (n + 1 : ℝ) ^ k * Real.exp (-(δ / 2) * n)
  have hk : b ≤ (k : ℝ) := by
    dsimp [k]
    exact Nat.le_ceil b
  have hδ2 : 0 < δ / 2 := by linarith
  have hg : Summable g := by
    simpa [g, mul_comm] using summable_succ_pow_exp (k := k) hδ2
  let H : ℝ := expPolynomialTsum k (δ / 2) + 1
  have hHpos : 0 < H := by
    dsimp [H]
    have hnonneg : 0 ≤ expPolynomialTsum k (δ / 2) := by
      unfold expPolynomialTsum
      exact tsum_nonneg fun n => by positivity
    linarith
  have hpoint (M n : ℕ) :
      (if M ≤ n then (n + 1 : ℝ) ^ b * Real.exp (-δ * n) else 0) ≤
        Real.exp (-δ * (M : ℝ) / 2) * g n := by
    by_cases hMn : M ≤ n
    · rw [if_pos hMn]
      have hnbase : 1 ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.le_add_left 1 n
      have hpoly : (n + 1 : ℝ) ^ b ≤ (n + 1 : ℝ) ^ (k : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnbase hk
      have hexp : Real.exp (-δ * (n : ℝ)) ≤
          Real.exp (-δ * (M : ℝ) / 2) * Real.exp (-(δ / 2) * n) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hMn' : (M : ℝ) ≤ n := by exact_mod_cast hMn
        nlinarith [hδ]
      have hpolyNat : (n + 1 : ℝ) ^ (k : ℝ) = (n + 1 : ℝ) ^ k := by
        rw [Real.rpow_natCast]
      dsimp [g]
      calc
        (n + 1 : ℝ) ^ b * Real.exp (-δ * n) ≤
            (n + 1 : ℝ) ^ (k : ℝ) *
              (Real.exp (-δ * (M : ℝ) / 2) * Real.exp (-(δ / 2) * n)) :=
          mul_le_mul hpoly hexp (by positivity) (by positivity)
        _ = Real.exp (-δ * (M : ℝ) / 2) *
              ((n + 1 : ℝ) ^ k * Real.exp (-(δ / 2) * n)) := by
          rw [hpolyNat]
          ring
    · rw [if_neg hMn]
      positivity
  refine ⟨H, hHpos, fun M => ?_⟩
  have hdom : Summable (fun n : ℕ => Real.exp (-δ * (M : ℝ) / 2) * g n) :=
    hg.mul_left _
  have hsum : Summable
      (fun n : ℕ => if M ≤ n then (n + 1 : ℝ) ^ b * Real.exp (-δ * n) else 0) :=
    Summable.of_nonneg_of_le (fun n => by split_ifs <;> positivity)
      (hpoint M) hdom
  have htsum := Summable.tsum_le_tsum (hpoint M) hsum hdom
  have hsumg :
      (∑' n : ℕ, Real.exp (-δ * (M : ℝ) / 2) * g n) =
        Real.exp (-δ * (M : ℝ) / 2) * expPolynomialTsum k (δ / 2) := by
    rw [hg.tsum_mul_left]
    rfl
  calc
    (∑' n : ℕ, if M ≤ n then (n + 1 : ℝ) ^ b * Real.exp (-δ * n) else 0)
        ≤ Real.exp (-δ * (M : ℝ) / 2) * expPolynomialTsum k (δ / 2) := by
          rw [← hsumg]
          exact htsum
    _ ≤ H * Real.exp (-δ * (M : ℝ) / 2) := by
      dsimp [H]
      have he : 0 ≤ Real.exp (-δ * (M : ℝ) / 2) := (Real.exp_pos _).le
      nlinarith [mul_nonneg he (show 0 ≤ (1 : ℝ) by norm_num)]

end BrownianSharp.AlignmentPaperGlobalGradeTail
