import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Tactic

/-!
This module formalizes the Gaussian moment input to Step 4 of the Brownian
sheet sharp small-ball candidate. It proves all scalar standard-Gaussian raw
moments from the mgf and an all-order covariance envelope in an independent
Gaussian representation. The envelope uses a direct binomial majorant; it does
not assert the sharper all-order Hermite covariance identity. It does not
assert a concentration theorem or the Brownian-sheet conclusion.
-/

open scoped BigOperators
open Filter Asymptotics
open MeasureTheory ProbabilityTheory

namespace BrownianSharp

/-- Polynomial factor multiplying the standard Gaussian mgf after repeated
differentiation. The recursion is exactly the product rule applied to
`exp (t^2 / 2)`. -/
noncomputable def gaussianMgfDerivativePolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 => (gaussianMgfDerivativePolynomial n).derivative +
      Polynomial.X * gaussianMgfDerivativePolynomial n

/-- Differentiating the mgf derivative polynomial lowers its index with the
expected Gaussian coefficient. -/
theorem gaussianMgfDerivativePolynomial_derivative (n : ℕ) :
    (gaussianMgfDerivativePolynomial (n + 1)).derivative =
      (n + 1 : ℝ) • gaussianMgfDerivativePolynomial n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          norm_num [gaussianMgfDerivativePolynomial]
      | succ n =>
          have h1 := ih n (by omega)
          by_cases hn : n = 0
          · subst n
            norm_num [gaussianMgfDerivativePolynomial]
            module
          · have h0 := ih (n - 1) (by omega)
            have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
            have hcast : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hsub
            have h0' : (gaussianMgfDerivativePolynomial n).derivative =
                (n : ℝ) • gaussianMgfDerivativePolynomial (n - 1) := by
              rw [hsub, hcast] at h0
              exact h0
            have h1' : (gaussianMgfDerivativePolynomial (n + 1)).derivative.derivative =
                (n + 1 : ℝ) • (gaussianMgfDerivativePolynomial n).derivative := by
              rw [← Polynomial.derivative_smul]
              exact congrArg Polynomial.derivative h1
            change ((gaussianMgfDerivativePolynomial (n + 1)).derivative +
                Polynomial.X * gaussianMgfDerivativePolynomial (n + 1)).derivative = _
            rw [Polynomial.derivative_add, Polynomial.derivative_mul,
              Polynomial.derivative_X, one_mul, h1', h1, h0']
            rw [gaussianMgfDerivativePolynomial]
            rw [h0']
            simp only [smul_add, smul_smul, one_smul]
            simp_rw [Polynomial.smul_eq_C_mul]
            simp only [Polynomial.C_add, Polynomial.C_mul, map_pow, map_natCast]
            push_cast
            ring

theorem iteratedDeriv_standardGaussian_mgf (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => Real.exp (t ^ 2 / 2)) =
      fun t => (gaussianMgfDerivativePolynomial n).eval t * Real.exp (t ^ 2 / 2) := by
  induction n with
  | zero =>
      funext t
      simp [gaussianMgfDerivativePolynomial]
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
      have hpoly : deriv (fun x : ℝ =>
          (gaussianMgfDerivativePolynomial n).eval x) =
          fun x => (gaussianMgfDerivativePolynomial n).derivative.eval x := by
        funext x
        exact (gaussianMgfDerivativePolynomial n).hasDerivAt x |>.deriv
      have hexp : deriv (fun x : ℝ => Real.exp (x ^ 2 / 2)) =
          fun x => x * Real.exp (x ^ 2 / 2) := by
        funext x
        rw [_root_.deriv_exp (by fun_prop)]
        simp [deriv_div_const, deriv_fun_pow]
        ring
      rw [hpoly, hexp]
      rw [gaussianMgfDerivativePolynomial]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
      ring_nf

/-- All raw moments of a standard real Gaussian are obtained from the
corresponding iterated derivative of its mgf. This gives an actual integral
identity for every natural exponent, not only the low-order base cases. -/
theorem standardGaussian_moment (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂gaussianReal (0 : ℝ) (1 : NNReal)) =
      (gaussianMgfDerivativePolynomial n).eval 0 := by
  have hm := ProbabilityTheory.iteratedDeriv_mgf_zero
    (X := id) (μ := gaussianReal (0 : ℝ) (1 : NNReal)) (n := n) (by simp)
  have hm' : iteratedDeriv n (mgf id (gaussianReal (0 : ℝ) (1 : NNReal))) 0 =
      (∫ x : ℝ, x ^ n ∂gaussianReal (0 : ℝ) (1 : NNReal)) := by
    simpa using hm
  rw [← hm']
  change iteratedDeriv n (mgf (fun x : ℝ => x)
    (gaussianReal (0 : ℝ) (1 : NNReal))) 0 = _
  rw [ProbabilityTheory.mgf_fun_id_gaussianReal]
  have hf : (fun t : ℝ => Real.exp (0 * t + ((1 : NNReal) : ℝ) * t ^ 2 / 2)) =
      fun t => Real.exp (t ^ 2 / 2) := by
    funext t
    simp
  rw [hf]
  rw [iteratedDeriv_standardGaussian_mgf]
  simp [gaussianMgfDerivativePolynomial]

/-- The all-order scalar moment recurrence `E[G^(n+2)] = (n+1) E[G^n]`. -/
theorem standardGaussian_moment_succ_succ (n : ℕ) :
    (∫ x : ℝ, x ^ (n + 2) ∂gaussianReal (0 : ℝ) (1 : NNReal)) =
      (n + 1 : ℝ) * (∫ x : ℝ, x ^ n ∂gaussianReal (0 : ℝ) (1 : NNReal)) := by
  rw [standardGaussian_moment (n + 2), standardGaussian_moment n]
  rw [gaussianMgfDerivativePolynomial]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
  rw [gaussianMgfDerivativePolynomial_derivative n]
  simp

/-- Explicit even moments, with the usual double-factorial normalization. -/
theorem standardGaussian_evenMoment (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) =
      (Nat.doubleFactorial (2 * k - 1) : ℝ) := by
  induction k with
  | zero =>
      rw [standardGaussian_moment 0]
      norm_num [gaussianMgfDerivativePolynomial]
  | succ k ih =>
      have hexp : 2 * (k + 1) = (2 * k) + 2 := by omega
      rw [hexp, standardGaussian_moment_succ_succ (2 * k), ih]
      have hdf : Nat.doubleFactorial (2 * (k + 1) - 1) =
          (2 * k + 1) * Nat.doubleFactorial (2 * k - 1) := by
        simpa [Nat.mul_add, Nat.mul_one, Nat.sub_add_comm] using
          Nat.doubleFactorial_add_one (2 * k)
      have hdfR : (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) =
          (2 * k + 1 : ℝ) * (Nat.doubleFactorial (2 * k - 1) : ℝ) := by
        exact_mod_cast hdf
      have hidx : 2 * (k + 1) - 1 = 2 * k + 2 - 1 := by omega
      rw [hidx] at hdfR
      push_cast at hdfR ⊢
      rw [← hdfR]

/-- The even standard-normal moment in ordinary factorial notation. -/
theorem standardGaussian_evenMoment_factorial (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) =
      (Nat.factorial (2 * k) : ℝ) /
        ((2 : ℝ) ^ k * (Nat.factorial k : ℝ)) := by
  cases k with
  | zero => norm_num [standardGaussian_evenMoment]
  | succ k =>
    rw [standardGaussian_evenMoment]
    have hidx : (2 * (k + 1) - 1) + 1 = 2 * (k + 1) := by omega
    have hfact : Nat.factorial (2 * (k + 1)) =
        Nat.doubleFactorial (2 * (k + 1)) * Nat.doubleFactorial (2 * (k + 1) - 1) := by
      simpa [hidx] using Nat.factorial_eq_mul_doubleFactorial (2 * (k + 1) - 1)
    have hdf := Nat.doubleFactorial_two_mul (k + 1)
    have hfactR : (Nat.factorial (2 * (k + 1)) : ℝ) =
        (2 : ℝ) ^ (k + 1) * (Nat.factorial (k + 1) : ℝ) *
          (Nat.doubleFactorial (2 * (k + 1) - 1) : ℝ) := by
      rw [hfact, hdf]
      push_cast
      ring
    rw [hfactR]
    field_simp

/-- Polynomially weighted geometric shells are summable. The factor
`(h+1)^(3q)` is the envelope left by the native prefix correlation count. -/
theorem shellPolynomialSummable (q : ℕ) :
    Summable (fun h : ℕ => ((h + 1 : ℝ) ^ (3 * q)) *
      (Real.sqrt (1 / 2 : ℝ)) ^ h) := by
  have hr : ‖Real.sqrt (1 / 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    nlinarith
  have hu : (fun h : ℕ => (((h + 1) ^ (3 * q) : ℕ) : ℝ)) =O[atTop]
      (fun h : ℕ => ((h ^ (3 * q) : ℕ) : ℝ)) := by
    apply IsBigO.of_bound ((2 : ℝ) ^ (3 * q))
    filter_upwards [eventually_atTop.2 ⟨1, fun h hh => hh⟩] with h hh
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ (((h + 1) ^ (3 * q) : ℕ) : ℝ)),
      abs_of_nonneg (by positivity : 0 ≤ ((h ^ (3 * q) : ℕ) : ℝ))]
    have hle : h + 1 ≤ 2 * h := by omega
    have hpow : (h + 1) ^ (3 * q) ≤ (2 * h) ^ (3 * q) :=
      Nat.pow_le_pow_left hle _
    calc
      (↑((h + 1) ^ (3 * q)) : ℝ) ≤ (↑((2 * h) ^ (3 * q)) : ℝ) := by
        exact_mod_cast hpow
      _ = 2 ^ (3 * q) * ↑(h ^ (3 * q)) := by push_cast; ring
  have hs := summable_norm_mul_geometric_of_norm_lt_one
    (k := 3 * q) hr (u := fun h : ℕ => (h + 1) ^ (3 * q)) hu
  have hr_eq : Real.sqrt (1 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).2
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  convert hs using 1
  ext h
  simp only [norm_mul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity :
    0 ≤ (((h + 1) ^ (3 * q) : ℕ) : ℝ))]
  simp [abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Nat.cast_pow, Nat.cast_add, mul_comm]

/-- The convergent shell envelope has an explicit, non-hypothetical budget:
its value is the `tsum` of the polynomial-geometric series. -/
noncomputable def shellPolynomialBudget (q : ℕ) : ℝ :=
  ∑' h : ℕ, ((h + 1 : ℝ) ^ (3 * q)) *
    (Real.sqrt (1 / 2 : ℝ)) ^ h

/-- Every finite prefix of the Step 4 shell envelope is bounded by its actual
convergent infinite sum. -/
theorem shellPolynomial_partial_le_budget (q N : ℕ) :
    (∑ h ∈ Finset.range (N + 1), ((h + 1 : ℝ) ^ (3 * q)) *
      (Real.sqrt (1 / 2 : ℝ)) ^ h) ≤ shellPolynomialBudget q := by
  unfold shellPolynomialBudget
  exact (shellPolynomialSummable q).sum_le_tsum (Finset.range (N + 1))
    (fun h _ => by positivity)

end BrownianSharp
