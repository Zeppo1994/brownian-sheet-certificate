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

/-- The fourth raw moment of the standard real Gaussian, obtained by
differentiating its explicit mgf. This is a genuine Gaussian integral
calculation, used as a base case for the bivariate square-covariance identity. -/
theorem standardGaussian_fourthMoment :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal (0 : ℝ) (1 : NNReal)) = 3 := by
  have hm := ProbabilityTheory.iteratedDeriv_mgf_zero
    (X := id) (μ := gaussianReal (0 : ℝ) (1 : NNReal)) (n := 4) (by simp)
  have hm' : iteratedDeriv 4 (mgf id (gaussianReal (0 : ℝ) (1 : NNReal))) 0 =
      (∫ x : ℝ, x ^ 4 ∂gaussianReal (0 : ℝ) (1 : NNReal)) := by
    simpa using hm
  rw [← hm']
  change iteratedDeriv 4 (mgf (fun x : ℝ => x)
    (gaussianReal (0 : ℝ) (1 : NNReal))) 0 = 3
  rw [ProbabilityTheory.mgf_fun_id_gaussianReal]
  let f : ℝ → ℝ := fun t => Real.exp (t ^ 2 / 2)
  have d1 : deriv f = fun t => t * f t := by
    funext t
    dsimp [f]
    rw [_root_.deriv_exp (by fun_prop)]
    simp [deriv_div_const, deriv_fun_pow]
    ring_nf
  have d2 : deriv (fun t => t * f t) = fun t => (1 + t ^ 2) * f t := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    simp [d1, f, deriv_fun_pow]
    ring_nf
  have d3 : deriv (fun t => (1 + t ^ 2) * f t) =
      fun t => (3 * t + t ^ 3) * f t := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    simp [d1, f, deriv_fun_pow]
    ring
  have dp : deriv (fun t : ℝ => 3 * t + t ^ 3) =
      fun t => 3 + 3 * t ^ 2 := by
    funext t
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_const_mul_field]
    have hid : deriv (fun x : ℝ => x) = fun _ => (1 : ℝ) := by
      funext x
      simp
    rw [hid]
    rw [deriv_fun_pow]
    · simp
    · fun_prop
  have d4 : deriv (fun t => (3 * t + t ^ 3) * f t) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * f t := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    rw [dp, d1]
    dsimp [f]
    ring
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_succ]
  rw [iteratedDeriv_zero]
  have hf : (fun t : ℝ => Real.exp (0 * t + ((1 : NNReal) : ℝ) * t ^ 2 / 2)) = f := by
    funext t
    simp [f]
  rw [hf]
  change deriv (deriv (deriv (deriv f))) 0 = 3
  rw [d1, d2, d3, d4]
  norm_num [f]

/-- The standard Gaussian second moment, obtained from its variance. -/
theorem standardGaussian_secondMoment :
    (∫ x : ℝ, x ^ 2 ∂gaussianReal (0 : ℝ) (1 : NNReal)) = 1 := by
  have hv := ProbabilityTheory.variance_fun_id_gaussianReal
    (μ := (0 : ℝ)) (v := (1 : NNReal))
  rw [variance_eq_integral measurable_id'.aemeasurable] at hv
  simpa using hv

/-- The third raw moment vanishes, again by differentiating the explicit mgf. -/
theorem standardGaussian_thirdMoment :
    (∫ x : ℝ, x ^ 3 ∂gaussianReal (0 : ℝ) (1 : NNReal)) = 0 := by
  have hm := ProbabilityTheory.iteratedDeriv_mgf_zero
    (X := id) (μ := gaussianReal (0 : ℝ) (1 : NNReal)) (n := 3) (by simp)
  have hm' : iteratedDeriv 3 (mgf id (gaussianReal (0 : ℝ) (1 : NNReal))) 0 =
      (∫ x : ℝ, x ^ 3 ∂gaussianReal (0 : ℝ) (1 : NNReal)) := by
    simpa using hm
  rw [← hm']
  change iteratedDeriv 3 (mgf (fun x : ℝ => x)
    (gaussianReal (0 : ℝ) (1 : NNReal))) 0 = 0
  rw [ProbabilityTheory.mgf_fun_id_gaussianReal]
  let f : ℝ → ℝ := fun t => Real.exp (t ^ 2 / 2)
  have d1 : deriv f = fun t => t * f t := by
    funext t
    dsimp [f]
    rw [_root_.deriv_exp (by fun_prop)]
    simp [deriv_div_const, deriv_fun_pow]
    ring_nf
  have d2 : deriv (fun t => t * f t) = fun t => (1 + t ^ 2) * f t := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    simp [d1, f]
    ring
  have d3 : deriv (fun t => (1 + t ^ 2) * f t) =
      fun t => (3 * t + t ^ 3) * f t := by
    funext t
    rw [deriv_fun_mul (by fun_prop) (by fun_prop)]
    simp [d1, f]
    ring
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ,
    iteratedDeriv_zero]
  have hf : (fun t : ℝ => Real.exp (0 * t + ((1 : NNReal) : ℝ) * t ^ 2 / 2)) = f := by
    funext t
    simp [f]
  rw [hf]
  change deriv (deriv (deriv f)) 0 = 0
  rw [d1, d2, d3]
  norm_num [f]

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

/-- Odd standard Gaussian moments vanish. -/
theorem standardGaussian_oddMoment (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k + 1) ∂gaussianReal (0 : ℝ) (1 : NNReal)) = 0 := by
  induction k with
  | zero =>
      simpa using standardGaussian_moment 1
  | succ k ih =>
      have hexp : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
      rw [hexp, standardGaussian_moment_succ_succ (2 * k + 1), ih]
      ring

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

/-- Every mixed monomial moment on the independent standard-Gaussian product
measure factors into the two scalar moments. This is the all-order product
calculation used to expand powers of a correlated Gaussian representation. -/
theorem independentGaussian_mixedMoment (a b : ℕ) :
    (∫ z : ℝ × ℝ, z.1 ^ a * z.2 ^ b
      ∂(gaussianReal (0 : ℝ) (1 : NNReal)).prod
        (gaussianReal (0 : ℝ) (1 : NNReal))) =
      (gaussianMgfDerivativePolynomial a).eval 0 *
        (gaussianMgfDerivativePolynomial b).eval 0 := by
  let γ := gaussianReal (0 : ℝ) (1 : NNReal)
  have hpow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) γ := by
    have h0 : 0 ∈ interior (integrableExpSet id γ) := by
      rw [integrableExpSet_id_gaussianReal]
      simp
    exact integrable_pow_of_mem_interior_integrableExpSet h0 n
  change (∫ z : ℝ × ℝ, (fun x : ℝ => x ^ a) z.1 *
    (fun y : ℝ => y ^ b) z.2 ∂(γ.prod γ)) = _
  rw [integral_prod_mul (μ := γ) (ν := γ)
    (f := fun x : ℝ => x ^ a) (g := fun y : ℝ => y ^ b)]
  rw [standardGaussian_moment a, standardGaussian_moment b]

/-- Concrete sixth and eighth moments read off from the all-order mgf
derivative polynomial. -/
theorem standardGaussian_sixthMoment :
    (∫ x : ℝ, x ^ 6 ∂gaussianReal (0 : ℝ) (1 : NNReal)) = 15 := by
  rw [standardGaussian_moment]
  norm_num [gaussianMgfDerivativePolynomial]

theorem standardGaussian_eighthMoment :
    (∫ x : ℝ, x ^ 8 ∂gaussianReal (0 : ℝ) (1 : NNReal)) = 105 := by
  rw [standardGaussian_moment]
  norm_num [gaussianMgfDerivativePolynomial]

/-- On a product of two independent standard Gaussians, a linear combination
has the exact mixed square moment used by the correlation base case. -/
theorem independentGaussian_squareLinear_moment (rho sigma : ℝ) :
    (∫ z : ℝ × ℝ, z.1 ^ 2 * (rho * z.1 + sigma * z.2) ^ 2
      ∂(gaussianReal (0 : ℝ) (1 : NNReal)).prod
        (gaussianReal (0 : ℝ) (1 : NNReal))) = 3 * rho ^ 2 + sigma ^ 2 := by
  let γ := gaussianReal (0 : ℝ) (1 : NNReal)
  have hpow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) γ := by
    have h0 : 0 ∈ interior (integrableExpSet id γ) := by
      rw [integrableExpSet_id_gaussianReal]
      simp
    exact integrable_pow_of_mem_interior_integrableExpSet h0 n
  have hA : Integrable (fun z : ℝ × ℝ => rho ^ 2 * z.1 ^ 4)
      (γ.prod γ) := by
    exact ((hpow 4).comp_fst γ).const_mul _
  have hB : Integrable (fun z : ℝ × ℝ =>
      (2 * rho * sigma) * (z.1 ^ 3 * z.2)) (γ.prod γ) := by
    simpa only [pow_one] using
      ((hpow 3).mul_prod (hpow 1)).const_mul (2 * rho * sigma)
  have hC : Integrable (fun z : ℝ × ℝ => sigma ^ 2 * (z.1 ^ 2 * z.2 ^ 2))
      (γ.prod γ) := by
    exact ((hpow 2).mul_prod (hpow 2)).const_mul _
  have hpoly : ∀ z : ℝ × ℝ,
      z.1 ^ 2 * (rho * z.1 + sigma * z.2) ^ 2 =
        rho ^ 2 * z.1 ^ 4 + ((2 * rho * sigma) * (z.1 ^ 3 * z.2) +
          sigma ^ 2 * (z.1 ^ 2 * z.2 ^ 2)) := by
    intro z
    ring
  calc
    _ = ∫ z : ℝ × ℝ,
        rho ^ 2 * z.1 ^ 4 + ((2 * rho * sigma) * (z.1 ^ 3 * z.2) +
          sigma ^ 2 * (z.1 ^ 2 * z.2 ^ 2)) ∂(γ.prod γ) := by
            apply integral_congr_ae
            filter_upwards [] with z
            exact hpoly z
    _ = rho ^ 2 * (∫ z : ℝ × ℝ, z.1 ^ 4 ∂(γ.prod γ)) +
        (2 * rho * sigma) * (∫ z : ℝ × ℝ, z.1 ^ 3 * z.2 ∂(γ.prod γ)) +
        sigma ^ 2 * (∫ z : ℝ × ℝ, z.1 ^ 2 * z.2 ^ 2 ∂(γ.prod γ)) := by
          calc
            _ = (∫ z : ℝ × ℝ, rho ^ 2 * z.1 ^ 4 ∂(γ.prod γ)) +
                (∫ z : ℝ × ℝ,
                  (2 * rho * sigma) * (z.1 ^ 3 * z.2) +
                    sigma ^ 2 * (z.1 ^ 2 * z.2 ^ 2) ∂(γ.prod γ)) := by
                      exact integral_add hA (hB.add hC)
            _ = _ := by
                  rw [integral_add hB hC, integral_const_mul, integral_const_mul,
                    integral_const_mul]
                  ring
    _ = 3 * rho ^ 2 + sigma ^ 2 := by
      have hAint : (∫ z : ℝ × ℝ, z.1 ^ 4 ∂(γ.prod γ)) = 3 := by
        change (∫ z : ℝ × ℝ, (fun x : ℝ => x ^ 4) z.1 ∂(γ.prod γ)) = 3
        rw [integral_fun_fst (μ := γ) (ν := γ) (f := fun x : ℝ => x ^ 4)]
        simp [γ, standardGaussian_fourthMoment]
      have hBint : (∫ z : ℝ × ℝ, z.1 ^ 3 * z.2 ∂(γ.prod γ)) = 0 := by
        change (∫ z : ℝ × ℝ, (fun x : ℝ => x ^ 3) z.1 *
          (fun y : ℝ => y) z.2 ∂(γ.prod γ)) = 0
        rw [integral_prod_mul (μ := γ) (ν := γ)
          (f := fun x : ℝ => x ^ 3) (g := fun y : ℝ => y)]
        simp [γ, standardGaussian_thirdMoment,
          ProbabilityTheory.integral_id_gaussianReal]
      have hCint : (∫ z : ℝ × ℝ, z.1 ^ 2 * z.2 ^ 2 ∂(γ.prod γ)) = 1 := by
        change (∫ z : ℝ × ℝ, (fun x : ℝ => x ^ 2) z.1 *
          (fun y : ℝ => y ^ 2) z.2 ∂(γ.prod γ)) = 1
        rw [integral_prod_mul (μ := γ) (ν := γ)
          (f := fun x : ℝ => x ^ 2) (g := fun y : ℝ => y ^ 2)]
        simp [γ, standardGaussian_secondMoment]
      rw [hAint, hBint, hCint]
      ring

/-- The second moment of a linear combination of two independent standard
Gaussians, proved by the same product-integral expansion as the square
covariance calculation. -/
theorem independentGaussian_linear_secondMoment (rho sigma : ℝ) :
    (∫ z : ℝ × ℝ, (rho * z.1 + sigma * z.2) ^ 2
      ∂(gaussianReal (0 : ℝ) (1 : NNReal)).prod
        (gaussianReal (0 : ℝ) (1 : NNReal))) = rho ^ 2 + sigma ^ 2 := by
  let γ := gaussianReal (0 : ℝ) (1 : NNReal)
  have hpow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) γ := by
    have h0 : 0 ∈ interior (integrableExpSet id γ) := by
      rw [integrableExpSet_id_gaussianReal]
      simp
    exact integrable_pow_of_mem_interior_integrableExpSet h0 n
  have hA : Integrable (fun z : ℝ × ℝ => rho ^ 2 * z.1 ^ 2) (γ.prod γ) :=
    ((hpow 2).comp_fst γ).const_mul _
  have hB : Integrable (fun z : ℝ × ℝ => (2 * rho * sigma) * (z.1 * z.2))
      (γ.prod γ) := by
    simpa only [pow_one] using ((hpow 1).mul_prod (hpow 1)).const_mul (2 * rho * sigma)
  have hC : Integrable (fun z : ℝ × ℝ => sigma ^ 2 * z.2 ^ 2) (γ.prod γ) := by
    simpa only [integral_fun_snd] using ((hpow 2).comp_snd γ).const_mul _
  have hpoly : ∀ z : ℝ × ℝ,
      (rho * z.1 + sigma * z.2) ^ 2 =
        rho ^ 2 * z.1 ^ 2 + ((2 * rho * sigma) * (z.1 * z.2) +
          sigma ^ 2 * z.2 ^ 2) := by
    intro z
    ring
  calc
    _ = ∫ z : ℝ × ℝ,
        rho ^ 2 * z.1 ^ 2 + ((2 * rho * sigma) * (z.1 * z.2) +
          sigma ^ 2 * z.2 ^ 2) ∂(γ.prod γ) := by
            apply integral_congr_ae
            filter_upwards [] with z
            exact hpoly z
    _ = rho ^ 2 * (∫ z : ℝ × ℝ, z.1 ^ 2 ∂(γ.prod γ)) +
        (2 * rho * sigma) * (∫ z : ℝ × ℝ, z.1 * z.2 ∂(γ.prod γ)) +
        sigma ^ 2 * (∫ z : ℝ × ℝ, z.2 ^ 2 ∂(γ.prod γ)) := by
          calc
            _ = (∫ z : ℝ × ℝ, rho ^ 2 * z.1 ^ 2 ∂(γ.prod γ)) +
                (∫ z : ℝ × ℝ,
                  (2 * rho * sigma) * (z.1 * z.2) + sigma ^ 2 * z.2 ^ 2
                    ∂(γ.prod γ)) := integral_add hA (hB.add hC)
            _ = _ := by
                  rw [integral_add hB hC, integral_const_mul, integral_const_mul,
                    integral_const_mul]
                  ring
    _ = rho ^ 2 + sigma ^ 2 := by
      have h1 : (∫ z : ℝ × ℝ, z.1 ^ 2 ∂(γ.prod γ)) = 1 := by
        change (∫ z : ℝ × ℝ, (fun x : ℝ => x ^ 2) z.1 ∂(γ.prod γ)) = 1
        rw [integral_fun_fst (μ := γ) (ν := γ) (f := fun x : ℝ => x ^ 2)]
        simp [γ, standardGaussian_secondMoment]
      have hcross : (∫ z : ℝ × ℝ, z.1 * z.2 ∂(γ.prod γ)) = 0 := by
        change (∫ z : ℝ × ℝ, (fun x : ℝ => x) z.1 * (fun y : ℝ => y) z.2
          ∂(γ.prod γ)) = 0
        rw [integral_prod_mul (μ := γ) (ν := γ)
          (f := fun x : ℝ => x) (g := fun y : ℝ => y)]
        simp [γ, ProbabilityTheory.integral_id_gaussianReal]
      have h2 : (∫ z : ℝ × ℝ, z.2 ^ 2 ∂(γ.prod γ)) = 1 := by
        change (∫ z : ℝ × ℝ, (fun y : ℝ => y ^ 2) z.2 ∂(γ.prod γ)) = 1
        rw [integral_fun_snd (μ := γ) (ν := γ) (f := fun y : ℝ => y ^ 2)]
        simp [γ, standardGaussian_secondMoment]
      rw [h1, hcross, h2]
      ring

/-- Genuine covariance calculation for two correlated standard Gaussian
variables in their independent-normal representation. -/
theorem correlatedGaussian_squareCovariance (rho : ℝ) (hrho : rho ^ 2 ≤ 1) :
    (∫ z : ℝ × ℝ, z.1 ^ 2 * (rho * z.1 + Real.sqrt (1 - rho ^ 2) * z.2) ^ 2
      ∂(gaussianReal (0 : ℝ) (1 : NNReal)).prod
        (gaussianReal (0 : ℝ) (1 : NNReal))) - 1 = 2 * rho ^ 2 := by
  have hsigma : (Real.sqrt (1 - rho ^ 2)) ^ 2 = 1 - rho ^ 2 := by
    rw [Real.sq_sqrt]
    linarith
  rw [independentGaussian_squareLinear_moment]
  rw [hsigma]
  ring

/-- A nontrivial higher-order correlated Gaussian check. The eighth-, sixth-,
and fourth-moment terms are integrated against the independent product
measure, producing the exact polynomial in the two coefficients. -/
theorem independentGaussian_fourthPower_moment (rho sigma : ℝ) :
    (∫ z : ℝ × ℝ, z.1 ^ 4 * (rho * z.1 + sigma * z.2) ^ 4
      ∂(gaussianReal (0 : ℝ) (1 : NNReal)).prod
        (gaussianReal (0 : ℝ) (1 : NNReal))) =
      105 * rho ^ 4 + 90 * rho ^ 2 * sigma ^ 2 + 9 * sigma ^ 4 := by
  let γ := gaussianReal (0 : ℝ) (1 : NNReal)
  have hpow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) γ := by
    have h0 : 0 ∈ interior (integrableExpSet id γ) := by
      rw [integrableExpSet_id_gaussianReal]
      simp
    exact integrable_pow_of_mem_interior_integrableExpSet h0 n
  have hA : Integrable (fun z : ℝ × ℝ => rho ^ 4 * z.1 ^ 8) (γ.prod γ) :=
    ((hpow 8).comp_fst γ).const_mul _
  have hB : Integrable (fun z : ℝ × ℝ => (4 * rho ^ 3 * sigma) * (z.1 ^ 7 * z.2))
      (γ.prod γ) := by
    simpa only [pow_one] using ((hpow 7).mul_prod (hpow 1)).const_mul _
  have hC : Integrable (fun z : ℝ × ℝ => (6 * rho ^ 2 * sigma ^ 2) *
      (z.1 ^ 6 * z.2 ^ 2)) (γ.prod γ) := by
    exact ((hpow 6).mul_prod (hpow 2)).const_mul _
  have hD : Integrable (fun z : ℝ × ℝ => (4 * rho * sigma ^ 3) *
      (z.1 ^ 5 * z.2 ^ 3)) (γ.prod γ) := by
    exact ((hpow 5).mul_prod (hpow 3)).const_mul _
  have hE : Integrable (fun z : ℝ × ℝ => sigma ^ 4 * (z.1 ^ 4 * z.2 ^ 4))
      (γ.prod γ) := by
    exact ((hpow 4).mul_prod (hpow 4)).const_mul _
  have hpoly : ∀ z : ℝ × ℝ,
      z.1 ^ 4 * (rho * z.1 + sigma * z.2) ^ 4 =
        rho ^ 4 * z.1 ^ 8 + ((4 * rho ^ 3 * sigma) * (z.1 ^ 7 * z.2) +
          ((6 * rho ^ 2 * sigma ^ 2) * (z.1 ^ 6 * z.2 ^ 2) +
            ((4 * rho * sigma ^ 3) * (z.1 ^ 5 * z.2 ^ 3) +
              sigma ^ 4 * (z.1 ^ 4 * z.2 ^ 4)))) := by
    intro z
    ring
  calc
    _ = ∫ z : ℝ × ℝ,
        rho ^ 4 * z.1 ^ 8 + ((4 * rho ^ 3 * sigma) * (z.1 ^ 7 * z.2) +
          ((6 * rho ^ 2 * sigma ^ 2) * (z.1 ^ 6 * z.2 ^ 2) +
            ((4 * rho * sigma ^ 3) * (z.1 ^ 5 * z.2 ^ 3) +
              sigma ^ 4 * (z.1 ^ 4 * z.2 ^ 4)))) ∂(γ.prod γ) := by
                apply integral_congr_ae
                filter_upwards [] with z
                exact hpoly z
    _ = rho ^ 4 * (∫ z : ℝ × ℝ, z.1 ^ 8 ∂(γ.prod γ)) +
        (4 * rho ^ 3 * sigma) * (∫ z : ℝ × ℝ, z.1 ^ 7 * z.2 ∂(γ.prod γ)) +
        (6 * rho ^ 2 * sigma ^ 2) *
          (∫ z : ℝ × ℝ, z.1 ^ 6 * z.2 ^ 2 ∂(γ.prod γ)) +
        (4 * rho * sigma ^ 3) * (∫ z : ℝ × ℝ, z.1 ^ 5 * z.2 ^ 3 ∂(γ.prod γ)) +
        sigma ^ 4 * (∫ z : ℝ × ℝ, z.1 ^ 4 * z.2 ^ 4 ∂(γ.prod γ)) := by
          calc
            _ = (∫ z : ℝ × ℝ, rho ^ 4 * z.1 ^ 8 ∂(γ.prod γ)) +
                (∫ z : ℝ × ℝ,
                  (4 * rho ^ 3 * sigma) * (z.1 ^ 7 * z.2) +
                    ((6 * rho ^ 2 * sigma ^ 2) * (z.1 ^ 6 * z.2 ^ 2) +
                      ((4 * rho * sigma ^ 3) * (z.1 ^ 5 * z.2 ^ 3) +
                        sigma ^ 4 * (z.1 ^ 4 * z.2 ^ 4))) ∂(γ.prod γ)) :=
                          integral_add hA (hB.add (hC.add (hD.add hE)))
            _ = _ := by
                  have h1 : (∫ z : ℝ × ℝ,
                      (4 * rho ^ 3 * sigma) * (z.1 ^ 7 * z.2) +
                        ((6 * rho ^ 2 * sigma ^ 2) * (z.1 ^ 6 * z.2 ^ 2) +
                          ((4 * rho * sigma ^ 3) * (z.1 ^ 5 * z.2 ^ 3) +
                            sigma ^ 4 * (z.1 ^ 4 * z.2 ^ 4))) ∂(γ.prod γ)) =
                      (∫ z : ℝ × ℝ, (4 * rho ^ 3 * sigma) * (z.1 ^ 7 * z.2)
                        ∂(γ.prod γ)) +
                      (∫ z : ℝ × ℝ,
                        (6 * rho ^ 2 * sigma ^ 2) * (z.1 ^ 6 * z.2 ^ 2) +
                          ((4 * rho * sigma ^ 3) * (z.1 ^ 5 * z.2 ^ 3) +
                            sigma ^ 4 * (z.1 ^ 4 * z.2 ^ 4)) ∂(γ.prod γ)) := by
                    exact integral_add hB (hC.add (hD.add hE))
                  have h2 : (∫ z : ℝ × ℝ,
                      (6 * rho ^ 2 * sigma ^ 2) * (z.1 ^ 6 * z.2 ^ 2) +
                        ((4 * rho * sigma ^ 3) * (z.1 ^ 5 * z.2 ^ 3) +
                          sigma ^ 4 * (z.1 ^ 4 * z.2 ^ 4)) ∂(γ.prod γ)) =
                      (∫ z : ℝ × ℝ, (6 * rho ^ 2 * sigma ^ 2) *
                        (z.1 ^ 6 * z.2 ^ 2) ∂(γ.prod γ)) +
                      (∫ z : ℝ × ℝ,
                        (4 * rho * sigma ^ 3) * (z.1 ^ 5 * z.2 ^ 3) +
                          sigma ^ 4 * (z.1 ^ 4 * z.2 ^ 4) ∂(γ.prod γ)) := by
                    exact integral_add hC (hD.add hE)
                  have h3 : (∫ z : ℝ × ℝ,
                      (4 * rho * sigma ^ 3) * (z.1 ^ 5 * z.2 ^ 3) +
                        sigma ^ 4 * (z.1 ^ 4 * z.2 ^ 4) ∂(γ.prod γ)) =
                      (∫ z : ℝ × ℝ, (4 * rho * sigma ^ 3) *
                        (z.1 ^ 5 * z.2 ^ 3) ∂(γ.prod γ)) +
                      (∫ z : ℝ × ℝ, sigma ^ 4 * (z.1 ^ 4 * z.2 ^ 4)
                        ∂(γ.prod γ)) := integral_add hD hE
                  rw [h1, h2, h3, integral_const_mul, integral_const_mul,
                    integral_const_mul, integral_const_mul, integral_const_mul]
                  ring
    _ = 105 * rho ^ 4 + 90 * rho ^ 2 * sigma ^ 2 + 9 * sigma ^ 4 := by
      have h8 : (∫ z : ℝ × ℝ, z.1 ^ 8 ∂(γ.prod γ)) = 105 := by
        change (∫ z : ℝ × ℝ, (fun x : ℝ => x ^ 8) z.1 ∂(γ.prod γ)) = 105
        rw [integral_fun_fst (μ := γ) (ν := γ) (f := fun x : ℝ => x ^ 8)]
        simp [γ, standardGaussian_eighthMoment]
      have h71 : (∫ z : ℝ × ℝ, z.1 ^ 7 * z.2 ∂(γ.prod γ)) = 0 := by
        change (∫ z : ℝ × ℝ, (fun x : ℝ => x ^ 7) z.1 *
          (fun y : ℝ => y) z.2 ∂(γ.prod γ)) = 0
        rw [integral_prod_mul (μ := γ) (ν := γ)
          (f := fun x : ℝ => x ^ 7) (g := fun y : ℝ => y)]
        rw [standardGaussian_moment 7]
        norm_num [gaussianMgfDerivativePolynomial]
      have h62 : (∫ z : ℝ × ℝ, z.1 ^ 6 * z.2 ^ 2 ∂(γ.prod γ)) = 15 := by
        change (∫ z : ℝ × ℝ, (fun x : ℝ => x ^ 6) z.1 *
          (fun y : ℝ => y ^ 2) z.2 ∂(γ.prod γ)) = 15
        rw [integral_prod_mul (μ := γ) (ν := γ)
          (f := fun x : ℝ => x ^ 6) (g := fun y : ℝ => y ^ 2)]
        simp [γ, standardGaussian_sixthMoment, standardGaussian_secondMoment]
      have h53 : (∫ z : ℝ × ℝ, z.1 ^ 5 * z.2 ^ 3 ∂(γ.prod γ)) = 0 := by
        change (∫ z : ℝ × ℝ, (fun x : ℝ => x ^ 5) z.1 *
          (fun y : ℝ => y ^ 3) z.2 ∂(γ.prod γ)) = 0
        rw [integral_prod_mul (μ := γ) (ν := γ)
          (f := fun x : ℝ => x ^ 5) (g := fun y : ℝ => y ^ 3)]
        rw [standardGaussian_moment 5]
        norm_num [gaussianMgfDerivativePolynomial]
      have h44 : (∫ z : ℝ × ℝ, z.1 ^ 4 * z.2 ^ 4 ∂(γ.prod γ)) = 9 := by
        change (∫ z : ℝ × ℝ, (fun x : ℝ => x ^ 4) z.1 *
          (fun y : ℝ => y ^ 4) z.2 ∂(γ.prod γ)) = 9
        rw [integral_prod_mul (μ := γ) (ν := γ)
          (f := fun x : ℝ => x ^ 4) (g := fun y : ℝ => y ^ 4)]
        simp [γ, standardGaussian_fourthMoment]
        ring
      rw [h8, h71, h62, h53, h44]
      ring

/-- The fourth-power covariance polynomial for a correlated standard Gaussian
pair. Its normalized coefficients are precisely the first two Hermite terms. -/
theorem correlatedGaussian_fourthPowerCovariance (rho : ℝ) (hrho : rho ^ 2 ≤ 1) :
    (∫ z : ℝ × ℝ, z.1 ^ 4 *
        (rho * z.1 + Real.sqrt (1 - rho ^ 2) * z.2) ^ 4
      ∂(gaussianReal (0 : ℝ) (1 : NNReal)).prod
        (gaussianReal (0 : ℝ) (1 : NNReal))) - 9 =
      72 * rho ^ 2 + 24 * rho ^ 4 := by
  have hsigma : (Real.sqrt (1 - rho ^ 2)) ^ 2 = 1 - rho ^ 2 := by
    rw [Real.sq_sqrt]
    linarith
  have hsigma4 : (Real.sqrt (1 - rho ^ 2)) ^ 4 = (1 - rho ^ 2) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsigma]
  rw [independentGaussian_fourthPower_moment, hsigma, hsigma4]
  ring

/-- The normalized fourth-power Gaussian covariance is exactly the two-term
Hermite polynomial `8 ρ² + (8/3) ρ⁴`. -/
theorem correlatedGaussian_fourthPowerCovariance_normalized (rho : ℝ)
    (hrho : rho ^ 2 ≤ 1) :
    ((∫ z : ℝ × ℝ, z.1 ^ 4 *
        (rho * z.1 + Real.sqrt (1 - rho ^ 2) * z.2) ^ 4
      ∂(gaussianReal (0 : ℝ) (1 : NNReal)).prod
        (gaussianReal (0 : ℝ) (1 : NNReal))) - 9) / 9 =
      8 * rho ^ 2 + (8 / 3 : ℝ) * rho ^ 4 := by
  rw [correlatedGaussian_fourthPowerCovariance rho hrho]
  ring

/-- All-order binomial expansion of a mixed moment of the independent
standard-Gaussian representation `rho * g + sigma * z`.  This is the
measure-theoretic bridge needed to turn the scalar moment recurrence into
high-order correlated Gaussian estimates. -/
theorem independentGaussian_linear_power_moment (p : ℕ) (rho sigma : ℝ) :
    (∫ z : ℝ × ℝ, z.1 ^ p * (rho * z.1 + sigma * z.2) ^ p
      ∂(gaussianReal (0 : ℝ) (1 : NNReal)).prod
        (gaussianReal (0 : ℝ) (1 : NNReal))) =
      ∑ j ∈ Finset.range (p + 1),
        rho ^ j * sigma ^ (p - j) * (p.choose j : ℝ) *
          ((∫ x : ℝ, x ^ (p + j) ∂gaussianReal (0 : ℝ) (1 : NNReal)) *
            (∫ y : ℝ, y ^ (p - j) ∂gaussianReal (0 : ℝ) (1 : NNReal))) := by
  let γ := gaussianReal (0 : ℝ) (1 : NNReal)
  let f : ℕ → ℝ × ℝ → ℝ := fun j z =>
    (rho ^ j * sigma ^ (p - j) * (p.choose j : ℝ)) *
      (z.1 ^ (p + j) * z.2 ^ (p - j))
  have hpow (n : ℕ) : Integrable (fun x : ℝ => x ^ n) γ := by
    have h0 : 0 ∈ interior (integrableExpSet id γ) := by
      rw [integrableExpSet_id_gaussianReal]
      simp
    exact integrable_pow_of_mem_interior_integrableExpSet h0 n
  have hf : ∀ j ∈ Finset.range (p + 1), Integrable (f j) (γ.prod γ) := by
    intro j hj
    have hprod := (hpow (p + j)).mul_prod (hpow (p - j))
    exact hprod.const_mul _
  have hpoly : ∀ z : ℝ × ℝ,
      z.1 ^ p * (rho * z.1 + sigma * z.2) ^ p =
        ∑ j ∈ Finset.range (p + 1), f j z := by
    intro z
    dsimp [f]
    rw [add_pow]
    rw [Finset.mul_sum (Finset.range (p + 1))
      (fun j => (rho * z.1) ^ j * (sigma * z.2) ^ (p - j) * (p.choose j : ℝ))
      (z.1 ^ p)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ p := by
      have := Finset.mem_range.mp hj
      omega
    simp only [mul_pow]
    calc
      z.1 ^ p * (rho ^ j * z.1 ^ j * (sigma ^ (p - j) * z.2 ^ (p - j)) *
          (p.choose j : ℝ)) =
          rho ^ j * sigma ^ (p - j) * (p.choose j : ℝ) *
            (z.1 ^ p * z.1 ^ j * z.2 ^ (p - j)) := by ring
      _ = rho ^ j * sigma ^ (p - j) * (p.choose j : ℝ) *
            (z.1 ^ (p + j) * z.2 ^ (p - j)) := by rw [← pow_add]
  calc
    _ = ∫ z : ℝ × ℝ, ∑ j ∈ Finset.range (p + 1), f j z ∂(γ.prod γ) := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hpoly z
    _ = ∑ j ∈ Finset.range (p + 1), ∫ z : ℝ × ℝ, f j z ∂(γ.prod γ) :=
      integral_finsetSum _ (fun j hj => hf j hj)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      dsimp [f]
      rw [integral_const_mul, integral_prod_mul (μ := γ) (ν := γ)
        (f := fun x : ℝ => x ^ (p + j)) (g := fun y : ℝ => y ^ (p - j))]

/-- Discrete log-convexity of factorial, in a symmetric shifted form. -/
theorem factorial_symmetric_shift_le (k m : ℕ) (hm : m ≤ k) :
    (Nat.factorial k) * (Nat.factorial k) ≤
      (Nat.factorial (k + m)) * (Nat.factorial (k - m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm' : m ≤ k := by omega
    have ih := ih hm'
    have htail : Nat.factorial (k - m) = (k - m) * Nat.factorial (k - m - 1) := by
      have hidx : k - m = (k - m - 1) + 1 := by omega
      rw [hidx, Nat.factorial_succ]
      congr 1 <;> omega
    have htop : Nat.factorial (k + (m + 1)) =
        (k + m + 1) * Nat.factorial (k + m) := by
      rw [show k + (m + 1) = (k + m) + 1 by omega, Nat.factorial_succ]
    have hcoeff : k - m ≤ k + m + 1 := by omega
    rw [htop, show k - (m + 1) = k - m - 1 by omega]
    calc
      Nat.factorial k * Nat.factorial k ≤
          Nat.factorial (k + m) * ((k - m) * Nat.factorial (k - m - 1)) := by
        rw [← htail]
        exact ih
      _ ≤ ((k + m + 1) * Nat.factorial (k + m)) *
          Nat.factorial (k - m - 1) := by
        have hmul := Nat.mul_le_mul_right (Nat.factorial (k - m - 1))
          (Nat.mul_le_mul_left (Nat.factorial (k + m)) hcoeff)
        nlinarith

/-- Bounding a factorial block by the largest factor in the block. -/
theorem factorial_shift_le_pow (p m : ℕ) :
    Nat.factorial (p + 2 * m) ≤
      Nat.factorial p * (p + 2 * m) ^ (2 * m) := by
  have hfac := Nat.factorial_mul_descFactorial (show 2 * m ≤ p + 2 * m by omega)
  have hdf := Nat.descFactorial_le_pow (p + 2 * m) (2 * m)
  have hcast :
      Nat.factorial p * Nat.descFactorial (p + 2 * m) (2 * m) =
        Nat.factorial (p + 2 * m) := by
    simpa [Nat.add_sub_cancel_left] using hfac
  rw [← hcast]
  exact Nat.mul_le_mul_left _ hdf

/-- Combined numerator inequality for the normalized even-power covariance
coefficient. It is the factorial form of the Hermite-term Taylor bound. -/
theorem factorial_even_coefficient_numerator_bound (k m : ℕ) (hm : m ≤ k) :
    Nat.factorial (2 * k + 2 * m) * Nat.factorial k * Nat.factorial k ≤
      Nat.factorial (2 * k) * (4 * k) ^ (2 * m) *
        Nat.factorial (k + m) * Nat.factorial (k - m) := by
  have hshift := factorial_shift_le_pow (2 * k) m
  have hbase : 2 * k + 2 * m ≤ 4 * k := by omega
  have hpow : (2 * k + 2 * m) ^ (2 * m) ≤ (4 * k) ^ (2 * m) :=
    Nat.pow_le_pow_left hbase (2 * m)
  have hfactorial : Nat.factorial (2 * k + 2 * m) ≤
      Nat.factorial (2 * k) * (4 * k) ^ (2 * m) := by
    exact le_trans hshift (Nat.mul_le_mul_left _ hpow)
  have hconvex := factorial_symmetric_shift_le k m hm
  have hmul := Nat.mul_le_mul hfactorial hconvex
  nlinarith

/-- The normalized coefficient in the direct binomial moment expansion is
bounded by the corresponding even Taylor coefficient. -/
theorem normalizedBinomialMomentCoefficient_le (k m : ℕ) (hm : m ≤ k) :
    (((Nat.factorial (2 * k + 2 * m) : ℝ) *
        (Nat.factorial k : ℝ) ^ 2) /
      ((Nat.factorial (2 * m) : ℝ) * (Nat.factorial (k + m) : ℝ) *
        (Nat.factorial (k - m) : ℝ) * (Nat.factorial (2 * k) : ℝ))) ≤
      (4 * k : ℝ) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) := by
  have hnum := factorial_even_coefficient_numerator_bound k m hm
  have hnumR : (Nat.factorial (2 * k + 2 * m) : ℝ) *
        (Nat.factorial k : ℝ) * (Nat.factorial k : ℝ) ≤
      (Nat.factorial (2 * k) : ℝ) * (4 * k : ℝ) ^ (2 * m) *
        (Nat.factorial (k + m) : ℝ) * (Nat.factorial (k - m) : ℝ) := by
    exact_mod_cast hnum
  have hden : 0 < (Nat.factorial (2 * m) : ℝ) *
      (Nat.factorial (k + m) : ℝ) * (Nat.factorial (k - m) : ℝ) *
      (Nat.factorial (2 * k) : ℝ) := by positivity
  rw [div_le_iff₀ hden]
  field_simp
  have hmul := mul_le_mul_of_nonneg_right hnumR (le_of_lt (show
    0 < (Nat.factorial (2 * m) : ℝ) by positivity))
  nlinarith

/-- The normalized even term in the independent binomial expansion simplifies
to the factorial coefficient bounded above by
`normalizedBinomialMomentCoefficient_le`. -/
theorem normalizedEvenBinomialMomentCoefficient_eq (k m : ℕ) (hm : m ≤ k) :
    (Nat.choose (2 * k) (2 * m) : ℝ) *
      (∫ x : ℝ, x ^ (2 * (k + m)) ∂gaussianReal (0 : ℝ) (1 : NNReal)) *
      (∫ y : ℝ, y ^ (2 * (k - m)) ∂gaussianReal (0 : ℝ) (1 : NNReal)) /
      ((∫ z : ℝ, z ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) ^ 2) =
    (((Nat.factorial (2 * k + 2 * m) : ℝ) *
        (Nat.factorial k : ℝ) * (Nat.factorial k : ℝ)) /
      ((Nat.factorial (2 * m) : ℝ) * (Nat.factorial (k + m) : ℝ) *
        (Nat.factorial (k - m) : ℝ) * (Nat.factorial (2 * k) : ℝ))) := by
  have hmom₁ := standardGaussian_evenMoment_factorial (k + m)
  have hmom₂ := standardGaussian_evenMoment_factorial (k - m)
  have hmom₃ := standardGaussian_evenMoment_factorial k
  have hchooseN := Nat.choose_mul_factorial_mul_factorial (show 2 * m ≤ 2 * k by omega)
  have hidx : 2 * k - 2 * m = 2 * (k - m) := by omega
  have hchoose : (Nat.choose (2 * k) (2 * m) : ℝ) *
      (Nat.factorial (2 * m) : ℝ) *
      (Nat.factorial (2 * (k - m)) : ℝ) = (Nat.factorial (2 * k) : ℝ) := by
    have hchooseN' : Nat.choose (2 * k) (2 * m) * Nat.factorial (2 * m) *
        Nat.factorial (2 * k - 2 * m) = Nat.factorial (2 * k) := hchooseN
    rw [hidx] at hchooseN'
    exact_mod_cast hchooseN'
  rw [hmom₁, hmom₂, hmom₃]
  field_simp
  have hpow : (k + m) + (k - m) = 2 * k := by omega
  have hpowR : (2 : ℝ) ^ (k + m) * (2 : ℝ) ^ (k - m) =
      ((2 : ℝ) ^ k) ^ 2 := by
    rw [← pow_add, hpow]
    calc
      (2 : ℝ) ^ (2 * k) = (2 : ℝ) ^ (k * 2) := by
        rw [show 2 * k = k * 2 by omega]
      _ = ((2 : ℝ) ^ k) ^ 2 := by rw [pow_mul]
  have hchoose' := congrArg (fun x : ℝ =>
    x * (Nat.factorial (2 * (k + m)) : ℝ)) hchoose
  calc
    _ = (((Nat.choose (2 * k) (2 * m) : ℝ) *
        (Nat.factorial (2 * m) : ℝ) *
        (Nat.factorial (2 * (k - m)) : ℝ) *
        (Nat.factorial (2 * (k + m)) : ℝ)) * ((2 : ℝ) ^ k) ^ 2) := by ring
    _ = (((Nat.factorial (2 * k) : ℝ) *
        (Nat.factorial (2 * (k + m)) : ℝ)) * ((2 : ℝ) ^ k) ^ 2) := by
      rw [hchoose']
    _ = ((2 : ℝ) ^ (k + m) * (2 : ℝ) ^ (k - m) *
        (Nat.factorial (2 * k) : ℝ) *
        (Nat.factorial (2 * k + 2 * m) : ℝ)) := by
      rw [hpowR, show 2 * (k + m) = 2 * k + 2 * m by omega]
      ring

/-- Each even-indexed term of the direct product-Gaussian expansion has the
dimension-free Taylor coefficient bound. -/
theorem normalizedEvenBinomialMomentCoefficient_le (k m : ℕ) (hm : m ≤ k) :
    (Nat.choose (2 * k) (2 * m) : ℝ) *
      (∫ x : ℝ, x ^ (2 * (k + m)) ∂gaussianReal (0 : ℝ) (1 : NNReal)) *
      (∫ y : ℝ, y ^ (2 * (k - m)) ∂gaussianReal (0 : ℝ) (1 : NNReal)) /
      ((∫ z : ℝ, z ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) ^ 2) ≤
    (4 * k : ℝ) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) := by
  rw [normalizedEvenBinomialMomentCoefficient_eq k m hm]
  convert normalizedBinomialMomentCoefficient_le k m hm using 1 <;> ring

/-- The zeroth normalized coefficient is one. -/
theorem normalizedEvenBinomialMomentCoefficient_zero (k : ℕ) :
    (Nat.choose (2 * k) 0 : ℝ) *
      (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) *
      (∫ y : ℝ, y ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) /
      ((∫ z : ℝ, z ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) ^ 2) = 1 := by
  have hmom := standardGaussian_evenMoment (k)
  rw [Nat.choose_zero_right, hmom]
  have hpos : 0 < (Nat.doubleFactorial (2 * k - 1) : ℝ) := by positivity
  field_simp
  norm_num

/-- Every finite nonnegative exponential Taylor sum is bounded by the
exponential. -/
theorem exp_taylor_partial_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (∑ n ∈ Finset.range N, x ^ n / (Nat.factorial n : ℝ)) ≤ Real.exp x := by
  exact Real.sum_le_exp_of_nonneg hx N

/-- A tail beginning at quadratic order is bounded by `x² exp x`. -/
theorem exp_taylor_quadratic_tail_le (x : ℝ) (hx : 0 ≤ x) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ)) ≤ x ^ 2 * Real.exp x := by
  have hterm (n : ℕ) :
      x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) ≤
        x ^ 2 * (x ^ n / (Nat.factorial n : ℝ)) := by
    have hfac : (Nat.factorial n : ℝ) ≤ Nat.factorial (n + 2) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hdiv : x ^ n / (Nat.factorial (n + 2) : ℝ) ≤
        x ^ n / (Nat.factorial n : ℝ) :=
      div_le_div_of_nonneg_left (pow_nonneg hx _) (by positivity) hfac
    calc
      x ^ (n + 2) / (Nat.factorial (n + 2) : ℝ) =
          x ^ 2 * (x ^ n / (Nat.factorial (n + 2) : ℝ)) := by
        rw [pow_add]
        ring
      _ ≤ x ^ 2 * (x ^ n / (Nat.factorial n : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv (sq_nonneg x)
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        x ^ 2 * (x ^ n / (Nat.factorial n : ℝ)) :=
      Finset.sum_le_sum fun n hn => hterm n
    _ = x ^ 2 * ∑ n ∈ Finset.range N, x ^ n / (Nat.factorial n : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ x ^ 2 * Real.exp x := by
      exact mul_le_mul_of_nonneg_left (exp_taylor_partial_le x hx N) (sq_nonneg x)

/-- Splitting a finite Taylor sum into even indices is proved by induction,
using only that every odd-indexed summand vanishes. -/
theorem sum_range_even_of_odd_zero (k : ℕ) (f : ℕ → ℝ)
    (hodd : ∀ m, f (2 * m + 1) = 0) :
    (∑ j ∈ Finset.range (2 * k + 1), f j) =
      ∑ m ∈ Finset.range (k + 1), f (2 * m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (∑ j ∈ Finset.range (2 * (k + 1) + 1), f j) =
          (∑ j ∈ Finset.range (2 * k + 1), f j) +
            f (2 * k + 1) + f (2 * k + 2) := by
        rw [show 2 * (k + 1) + 1 = ((2 * k + 1) + 1) + 1 by omega,
          Finset.sum_range_succ, Finset.sum_range_succ]
      _ = ∑ m ∈ Finset.range (k + 1 + 1), f (2 * m) := by
        rw [ih, hodd]
        rw [Finset.sum_range_succ (fun m => f (2 * m)) (k + 1)]
        simp [show 2 * (k + 1) = 2 * k + 2 by omega]

/-- The sum over even indices is bounded by the full nonnegative partial sum. -/
theorem sum_range_even_le (k : ℕ) (f : ℕ → ℝ)
    (hf : ∀ n, 0 ≤ f n) :
    (∑ m ∈ Finset.range (k + 1), f (2 * m)) ≤
      ∑ j ∈ Finset.range (2 * k + 1), f j := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hleft : (∑ m ∈ Finset.range (k + 1 + 1), f (2 * m)) =
        (∑ m ∈ Finset.range (k + 1), f (2 * m)) + f (2 * k + 2) := by
      rw [Finset.sum_range_succ (fun m => f (2 * m)) (k + 1)]
      simp [show 2 * (k + 1) = 2 * k + 2 by omega]
    have hright : (∑ j ∈ Finset.range (2 * (k + 1) + 1), f j) =
        (∑ j ∈ Finset.range (2 * k + 1), f j) + f (2 * k + 1) + f (2 * k + 2) := by
      rw [show 2 * (k + 1) + 1 = (2 * k + 2) + 1 by omega,
        Finset.sum_range_succ f (2 * k + 2),
        Finset.sum_range_succ f (2 * k + 1)]
    rw [hleft, hright]
    calc
      (∑ m ∈ Finset.range (k + 1), f (2 * m)) + f (2 * k + 2) ≤
          (∑ j ∈ Finset.range (2 * k + 1), f j) + f (2 * k + 2) :=
        add_le_add_left ih _
      _ ≤ (∑ j ∈ Finset.range (2 * k + 1), f j) + f (2 * k + 1) + f (2 * k + 2) := by
        linarith [hf (2 * k + 1)]

/-- The even exponential Taylor partial sum is bounded by `exp x`. -/
theorem exp_taylor_even_partial_le (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (∑ m ∈ Finset.range (k + 1), x ^ (2 * m) /
      (Nat.factorial (2 * m) : ℝ)) ≤ Real.exp x := by
  calc
    _ ≤ ∑ n ∈ Finset.range (2 * k + 1),
        x ^ n / (Nat.factorial n : ℝ) :=
      sum_range_even_le k (fun n => x ^ n / (Nat.factorial n : ℝ))
        (fun n => by positivity)
    _ ≤ Real.exp x := exp_taylor_partial_le x hx (2 * k + 1)

/-- The positive even Taylor terms, starting at degree two, are bounded by
`x² exp x`. -/
theorem exp_taylor_even_tail_le (x : ℝ) (hx : 0 ≤ x) (k : ℕ) :
    (∑ m ∈ Finset.range k,
      x ^ (2 * (m + 1)) / (Nat.factorial (2 * (m + 1)) : ℝ)) ≤
      x ^ 2 * Real.exp x := by
  have hterm (m : ℕ) :
      x ^ (2 * (m + 1)) / (Nat.factorial (2 * (m + 1)) : ℝ) ≤
        x ^ 2 * (x ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) := by
    have hfac : (Nat.factorial (2 * m) : ℝ) ≤ Nat.factorial (2 * (m + 1)) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hdiv : x ^ (2 * m) / (Nat.factorial (2 * (m + 1)) : ℝ) ≤
        x ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) :=
      div_le_div_of_nonneg_left (pow_nonneg hx _) (by positivity) hfac
    have hexp : 2 * (m + 1) = 2 * m + 2 := by omega
    calc
      x ^ (2 * (m + 1)) / (Nat.factorial (2 * (m + 1)) : ℝ) =
          x ^ 2 * (x ^ (2 * m) / (Nat.factorial (2 * (m + 1)) : ℝ)) := by
        rw [hexp, pow_add]
        ring
      _ ≤ x ^ 2 * (x ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) :=
        mul_le_mul_of_nonneg_left hdiv (sq_nonneg x)
  calc
    _ ≤ ∑ m ∈ Finset.range k,
        x ^ 2 * (x ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) :=
      Finset.sum_le_sum fun m hm => hterm m
    _ = x ^ 2 * ∑ m ∈ Finset.range k,
        x ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ x ^ 2 * Real.exp x := by
      have hprefix :
          (∑ m ∈ Finset.range k, x ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) ≤
            Real.exp x := by
        cases k with
        | zero => exact le_of_lt (Real.exp_pos x)
        | succ k => simpa using exp_taylor_even_partial_le x hx k
      exact mul_le_mul_of_nonneg_left hprefix (sq_nonneg x)

/-- The even-order correlated raw moment is an actual finite sum over even
binomial indices. Odd terms vanish by the proved scalar Gaussian moment
calculation; this statement is unconditional in the real coefficients. -/
theorem independentGaussian_evenPower_binomialExpansion (k : ℕ) (rho sigma : ℝ) :
    (∫ z : ℝ × ℝ, z.1 ^ (2 * k) * (rho * z.1 + sigma * z.2) ^ (2 * k)
      ∂(gaussianReal (0 : ℝ) (1 : NNReal)).prod
        (gaussianReal (0 : ℝ) (1 : NNReal))) =
      ∑ m ∈ Finset.range (k + 1),
        rho ^ (2 * m) * sigma ^ (2 * (k - m)) * ((2 * k).choose (2 * m) : ℝ) *
          ((∫ x : ℝ, x ^ (2 * (k + m)) ∂gaussianReal (0 : ℝ) (1 : NNReal)) *
            (∫ y : ℝ, y ^ (2 * (k - m)) ∂gaussianReal (0 : ℝ) (1 : NNReal))) := by
  let γ := gaussianReal (0 : ℝ) (1 : NNReal)
  let term : ℕ → ℝ := fun j =>
    rho ^ j * sigma ^ (2 * k - j) * ((2 * k).choose j : ℝ) *
      ((∫ x : ℝ, x ^ (2 * k + j) ∂γ) *
        (∫ y : ℝ, y ^ (2 * k - j) ∂γ))
  have hodd (m : ℕ) : term (2 * m + 1) = 0 := by
    dsimp [term]
    have hidx : 2 * k + (2 * m + 1) = 2 * (k + m) + 1 := by omega
    rw [hidx, standardGaussian_oddMoment]
    simp
  rw [independentGaussian_linear_power_moment (2 * k) rho sigma]
  rw [sum_range_even_of_odd_zero k term hodd]
  apply Finset.sum_congr rfl
  intro m hm
  have hmle : m ≤ k := by
    have := Finset.mem_range.mp hm
    omega
  have hsub : 2 * k - 2 * m = 2 * (k - m) := by omega
  have hadd : 2 * k + 2 * m = 2 * (k + m) := by omega
  dsimp [term, γ]
  rw [hsub, hadd]

/-- High-order normalized covariance envelope from the actual independent
Gaussian binomial expansion. The factor `4` is the cost of the direct
binomial majorant; no Hermite covariance identity is assumed. -/
theorem correlatedGaussian_evenPowerCovariance_bound (k : ℕ) (rho : ℝ)
    (hrho : rho ^ 2 ≤ 1) :
    ((∫ z : ℝ × ℝ, z.1 ^ (2 * k) *
          (rho * z.1 + Real.sqrt (1 - rho ^ 2) * z.2) ^ (2 * k)
        ∂(gaussianReal (0 : ℝ) (1 : NNReal)).prod
          (gaussianReal (0 : ℝ) (1 : NNReal))) /
      ((∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) ^ 2)) - 1 ≤
      ((4 * k : ℝ) * |rho|) ^ 2 * Real.exp ((4 * k : ℝ) * |rho|) := by
  let γ := gaussianReal (0 : ℝ) (1 : NNReal)
  let sigma := Real.sqrt (1 - rho ^ 2)
  let M : ℝ := ∫ x : ℝ, x ^ (2 * k) ∂γ
  let coeff : ℕ → ℝ := fun m =>
    ((2 * k).choose (2 * m) : ℝ) *
      (∫ x : ℝ, x ^ (2 * (k + m)) ∂γ) *
      (∫ y : ℝ, y ^ (2 * (k - m)) ∂γ) / M ^ 2
  let term : ℕ → ℝ := fun m =>
    rho ^ (2 * m) * sigma ^ (2 * (k - m)) * coeff m
  let x : ℝ := (4 * k : ℝ) * |rho|
  have hM : 0 < M := by
    dsimp [M, γ]
    rw [standardGaussian_evenMoment]
    positivity
  have hsigma0 : 0 ≤ sigma := Real.sqrt_nonneg _
  have hsigma1 : sigma ≤ 1 := by
    dsimp [sigma]
    rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg rho]
  have hx : 0 ≤ x := by positivity
  have hnorm :
      (∫ z : ℝ × ℝ, z.1 ^ (2 * k) *
          (rho * z.1 + sigma * z.2) ^ (2 * k)
        ∂(γ.prod γ)) / M ^ 2 =
        ∑ m ∈ Finset.range (k + 1), term m := by
    have hexp := independentGaussian_evenPower_binomialExpansion k rho sigma
    calc
      _ = (∑ m ∈ Finset.range (k + 1),
          rho ^ (2 * m) * sigma ^ (2 * (k - m)) *
            ((2 * k).choose (2 * m) : ℝ) *
              ((∫ x : ℝ, x ^ (2 * (k + m)) ∂γ) *
                (∫ y : ℝ, y ^ (2 * (k - m)) ∂γ))) / M ^ 2 := by
          rw [hexp]
      _ = ∑ m ∈ Finset.range (k + 1),
          (rho ^ (2 * m) * sigma ^ (2 * (k - m)) *
            ((2 * k).choose (2 * m) : ℝ) *
              ((∫ x : ℝ, x ^ (2 * (k + m)) ∂γ) *
                (∫ y : ℝ, y ^ (2 * (k - m)) ∂γ))) / M ^ 2 := by
          rw [Finset.sum_div]
      _ = ∑ m ∈ Finset.range (k + 1), term m := by
          apply Finset.sum_congr rfl
          intro m hm
          dsimp [term, coeff]
          ring
  have hcoeff0 : coeff 0 = 1 := by
    dsimp [coeff, M, γ]
    exact normalizedEvenBinomialMomentCoefficient_zero k
  have hbase : term 0 = sigma ^ (2 * k) := by
    dsimp [term, coeff, M, γ]
    rw [normalizedEvenBinomialMomentCoefficient_zero k]
    ring
  have hbasele : term 0 ≤ 1 := by
    rw [hbase]
    exact pow_le_one₀ hsigma0 hsigma1
  have hterm (m : ℕ) (hm : m ∈ Finset.range k) :
      term (m + 1) ≤ x ^ (2 * (m + 1)) /
        (Nat.factorial (2 * (m + 1)) : ℝ) := by
    have hmle : m + 1 ≤ k := by
      have := Finset.mem_range.mp hm
      omega
    have hC := normalizedEvenBinomialMomentCoefficient_le k (m + 1) hmle
    have hCpos : 0 ≤ coeff (m + 1) := by
      dsimp [coeff, M, γ]
      rw [standardGaussian_evenMoment (k + (m + 1)),
        standardGaussian_evenMoment (k - (m + 1)), standardGaussian_evenMoment k]
      positivity
    have hsigmaPow : sigma ^ (2 * (k - (m + 1))) ≤ 1 :=
      pow_le_one₀ hsigma0 hsigma1
    have hrhopos : 0 ≤ rho ^ (2 * (m + 1)) := by
      rw [show 2 * (m + 1) = (m + 1) * 2 by omega, pow_mul]
      exact sq_nonneg _
    have hrhoPow : rho ^ (2 * (m + 1)) = |rho| ^ (2 * (m + 1)) := by
      calc
        rho ^ (2 * (m + 1)) = |rho ^ (2 * (m + 1))| :=
          (abs_of_nonneg hrhopos).symm
        _ = |rho| ^ (2 * (m + 1)) := by rw [abs_pow]
    have hC' : coeff (m + 1) ≤
        (4 * k : ℝ) ^ (2 * (m + 1)) /
          (Nat.factorial (2 * (m + 1)) : ℝ) := by
      simpa [coeff, M, γ] using hC
    calc
      term (m + 1) = rho ^ (2 * (m + 1)) *
          (sigma ^ (2 * (k - (m + 1))) * coeff (m + 1)) := by ring
      _ ≤ rho ^ (2 * (m + 1)) * coeff (m + 1) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa using mul_le_mul_of_nonneg_right hsigmaPow hCpos)
          hrhopos
      _ = |rho| ^ (2 * (m + 1)) * coeff (m + 1) := by rw [hrhoPow]
      _ ≤ |rho| ^ (2 * (m + 1)) *
          ((4 * k : ℝ) ^ (2 * (m + 1)) /
            (Nat.factorial (2 * (m + 1)) : ℝ)) :=
        mul_le_mul_of_nonneg_left hC' (pow_nonneg (abs_nonneg rho) _)
      _ = x ^ (2 * (m + 1)) /
          (Nat.factorial (2 * (m + 1)) : ℝ) := by
        dsimp [x]
        field_simp
        rw [← mul_pow]
        ring
  have htail : (∑ m ∈ Finset.range k, term (m + 1)) ≤
      x ^ 2 * Real.exp x := by
    calc
      _ ≤ ∑ m ∈ Finset.range k,
          x ^ (2 * (m + 1)) /
            (Nat.factorial (2 * (m + 1)) : ℝ) :=
        Finset.sum_le_sum fun m hm => hterm m hm
      _ ≤ x ^ 2 * Real.exp x := exp_taylor_even_tail_le x hx k
  have hsplit : (∑ m ∈ Finset.range (k + 1), term m) =
      term 0 + ∑ m ∈ Finset.range k, term (m + 1) := by
    rw [Finset.sum_range_succ']
    ring
  rw [show Real.sqrt (1 - rho ^ 2) = sigma by rfl, hnorm, hsplit]
  calc
    (term 0 + ∑ m ∈ Finset.range k, term (m + 1)) - 1 =
        (∑ m ∈ Finset.range k, term (m + 1)) + (term 0 - 1) := by ring
    _ ≤ ∑ m ∈ Finset.range k, term (m + 1) := by linarith
    _ ≤ x ^ 2 * Real.exp x := htail


/-- The coefficient occurring in the normalized even-Gaussian moment
covariance identity. `falling` is supplied explicitly so the statement does
not depend on a choice of factorial convention. -/
noncomputable def hermiteMomentCoefficient (_k m : ℕ) (falling : ℝ) : ℝ :=
  (4 : ℝ) ^ m * falling ^ 2 / (Nat.factorial (2 * m) : ℝ)

/-- The descending factorial is bounded by the corresponding ordinary power. -/
theorem fallingFactorial_taylor_bound (k m : ℕ) :
    (2 : ℝ) ^ m * (k.descFactorial m : ℝ) ≤ (2 * k : ℝ) ^ m := by
  have hfall : (k.descFactorial m : ℝ) ≤ (k : ℝ) ^ m := by
    exact_mod_cast Nat.descFactorial_le_pow k m
  calc
    (2 : ℝ) ^ m * (k.descFactorial m : ℝ) ≤ (2 : ℝ) ^ m * (k : ℝ) ^ m := by
      gcongr
    _ = (2 * k : ℝ) ^ m := by rw [← mul_pow]

/-- Positivity of every Hermite covariance coefficient, provided the falling
factorial is nonnegative. -/
theorem hermiteMomentCoefficient_nonneg (k m : ℕ) (falling : ℝ) :
    0 ≤ hermiteMomentCoefficient k m falling := by
  unfold hermiteMomentCoefficient
  positivity

/-- The Hermite coefficient is bounded by its corresponding even Taylor
coefficient once the elementary falling-factorial estimate
`2^m (k)_m ≤ (2k)^m` is supplied. The hypothesis is separated out so the
factorial normalization and division are checked in Lean. -/
theorem hermiteMomentCoefficient_le_taylor
    (k m : ℕ) (falling : ℝ)
    (hfalling : 0 ≤ falling)
    (hbound : (2 : ℝ) ^ m * falling ≤ (2 * k : ℝ) ^ m) :
    hermiteMomentCoefficient k m falling ≤
      (2 * k : ℝ) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) := by
  have hfact : 0 < (Nat.factorial (2 * m) : ℝ) := by positivity
  have hnum : (4 : ℝ) ^ m * falling ^ 2 ≤ (2 * k : ℝ) ^ (2 * m) := by
    have hsq : ((2 : ℝ) ^ m * falling) ^ 2 ≤ ((2 * k : ℝ) ^ m) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg (by positivity) hfalling) (by positivity)).mpr hbound
    have hleft : ((2 : ℝ) ^ m * falling) ^ 2 =
        (4 : ℝ) ^ m * falling ^ 2 := by
      rw [mul_pow]
      congr 1
      calc
        ((2 : ℝ) ^ m) ^ 2 = 2 ^ (m * 2) := by rw [← pow_mul]
        _ = 2 ^ (2 * m) := by congr 1; omega
        _ = ((2 : ℝ) ^ 2) ^ m := by rw [← pow_mul]
        _ = 4 ^ m := by norm_num
    have hright : ((2 * k : ℝ) ^ m) ^ 2 = (2 * k : ℝ) ^ (2 * m) := by
      rw [← pow_mul]
      congr 1
      omega
    calc
      (4 : ℝ) ^ m * falling ^ 2 = ((2 : ℝ) ^ m * falling) ^ 2 := hleft.symm
      _ ≤ ((2 * k : ℝ) ^ m) ^ 2 := hsq
      _ = (2 * k : ℝ) ^ (2 * m) := hright
  unfold hermiteMomentCoefficient
  rw [div_le_div_iff₀ hfact hfact]
  nlinarith

/-- The coefficient bound for the actual natural descending factorial. -/
theorem naturalHermiteCoefficient_le_taylor (k m : ℕ) :
    hermiteMomentCoefficient k m (k.descFactorial m : ℝ) ≤
      (2 * k : ℝ) ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) := by
  apply hermiteMomentCoefficient_le_taylor
  · exact_mod_cast Nat.cast_nonneg (k.descFactorial m)
  · exact fallingFactorial_taylor_bound k m

/-- A finite coefficientwise domination passes to the corresponding
polynomial sum. This is the exact finite-sum step used to compare the Hermite
series with the even Taylor polynomial of `cosh`. -/
theorem sum_hermite_coeff_le_sum_taylor
    (k : ℕ) (x : ℝ) (coeff : ℕ → ℝ)
    (hcoeff : ∀ m ∈ Finset.range (k + 1),
      0 ≤ coeff m ∧ coeff m ≤ x ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)) :
    (∑ m ∈ Finset.range (k + 1), coeff m) ≤
      ∑ m ∈ Finset.range (k + 1),
        x ^ (2 * m) / (Nat.factorial (2 * m) : ℝ) := by
  apply Finset.sum_le_sum
  intro m hm
  exact (hcoeff m hm).2

/-- The Gaussian-correlation identity in coefficient form. This definition is
the finite Hermite polynomial on the right-hand side; a separate derivation
from Gaussian integrals is intentionally required before using it as an
identity for random variables. -/
noncomputable def hermiteCovariancePolynomial (k : ℕ) (rho : ℝ)
    (falling : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (k + 1),
    hermiteMomentCoefficient k m (falling m) * rho ^ (2 * m)

/-- The elementary power-series budget needed by the high-power estimate is
kept explicit: it applies to any nonnegative sequence dominated by a
geometrically summable polynomial envelope. The constant `budget` is the
already evaluated envelope sum, so this lemma makes no implicit convergence
claim. -/
theorem finite_weighted_correlation_budget
    (N : ℕ) (term envelope : ℕ → ℝ) (budget : ℝ)
    (hterm : ∀ h ∈ Finset.range (N + 1), 0 ≤ term h ∧ term h ≤ envelope h)
    (henvelope : ∑ h ∈ Finset.range (N + 1), envelope h ≤ budget) :
    ∑ h ∈ Finset.range (N + 1), term h ≤ budget := by
  calc
    ∑ h ∈ Finset.range (N + 1), term h ≤
        ∑ h ∈ Finset.range (N + 1), envelope h := by
          apply Finset.sum_le_sum
          intro h hh
          exact (hterm h hh).2
    _ ≤ budget := henvelope

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
