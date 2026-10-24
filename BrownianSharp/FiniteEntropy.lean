import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite-law entropy controls the mean

Source: unrestricted quarter-gain proof, Section 4, Lemma T2.
The finite Gibbs inequality and its entropy–variance consequence are proved
here. The exponential budget is an explicit hypothesis: deriving it for the
one-axis predictable sign process is a separate, still pending obligation.
-/

open scoped BigOperators

namespace HaarQuarter

/-- A finite probability law with full support. -/
structure PositiveLaw (ι : Type*) [Fintype ι] where
  mass : ι → ℝ
  positive : ∀ i, 0 < mass i
  total : ∑ i, mass i = 1

def mean {ι : Type*} [Fintype ι] (P : PositiveLaw ι) (F : ι → ℝ) : ℝ :=
  ∑ i, P.mass i * F i

noncomputable def relativeEntropy {ι : Type*} [Fintype ι] (P Q : PositiveLaw ι) : ℝ :=
  ∑ i, P.mass i * Real.log (P.mass i / Q.mass i)

theorem mean_linear {ι : Type*} [Fintype ι] (P : PositiveLaw ι)
    (a b : ℝ) (F G : ι → ℝ) :
    mean P (fun i => a * F i + b * G i) = a * mean P F + b * mean P G := by
  unfold mean
  calc
    _ = ∑ i, (a * (P.mass i * F i) + b * (P.mass i * G i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Gibbs' variational inequality in the normalization needed for T2. -/
theorem gibbs_of_exp_budget {ι : Type*} [Fintype ι] (P Q : PositiveLaw ι)
    (F : ι → ℝ) (hbudget : mean Q (fun i => Real.exp (F i)) ≤ 1) :
    mean P F ≤ relativeEntropy P Q := by
  have hpoint : ∀ i, P.mass i * (F i - Real.log (P.mass i / Q.mass i)) ≤
      Q.mass i * Real.exp (F i) - P.mass i := by
    intro i
    have hp := P.positive i
    have hq := Q.positive i
    have he := Real.exp_pos (F i)
    have hlog : Real.log (Q.mass i * Real.exp (F i) / P.mass i) =
        F i - Real.log (P.mass i / Q.mass i) := by
      rw [Real.log_div (mul_ne_zero hq.ne' he.ne') hp.ne',
        Real.log_mul hq.ne' he.ne', Real.log_exp, Real.log_div hp.ne' hq.ne']
      ring
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos (mul_pos hq he) hp)) (le_of_lt hp)
    rw [hlog] at h
    have hcancel : P.mass i * (Q.mass i * Real.exp (F i) / P.mass i - 1) =
        Q.mass i * Real.exp (F i) - P.mass i := by
      field_simp
    rw [hcancel] at h
    exact h
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hbound : mean P F - relativeEntropy P Q ≤
      mean Q (fun i => Real.exp (F i)) - 1 := by
    simpa only [mul_sub, Finset.sum_sub_distrib, P.total, mean, relativeEntropy] using hsum
  linarith

theorem relativeEntropy_nonneg {ι : Type*} [Fintype ι] (P Q : PositiveLaw ι) :
    0 ≤ relativeEntropy P Q := by
  have hbudget : mean Q (fun _ => Real.exp 0) ≤ 1 := by
    simp [mean, Q.total]
  simpa [mean] using gibbs_of_exp_budget P Q (fun _ => 0) hbudget

/-- Finite entropy–variance control, conditional on the exponential budget. -/
theorem mean_abs_le_sqrt_entropy_variance {ι : Type*} [Fintype ι]
    (P Q : PositiveLaw ι) (G A : ι → ℝ) (hA : ∀ i, 0 ≤ A i)
    (hbudget : ∀ s : ℝ,
      mean Q (fun i => Real.exp (s * G i + (-(s ^ 2) / 2) * A i)) ≤ 1) :
    |mean P G| ≤ Real.sqrt (2 * relativeEntropy P Q * mean P A) := by
  let m := mean P G
  let q := mean P A
  let K := relativeEntropy P Q
  have hq : 0 ≤ q :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (P.positive i)) (hA i))
  have hquad : ∀ s : ℝ, s * m + (-(s ^ 2) / 2) * q ≤ K := by
    intro s
    have h := gibbs_of_exp_budget P Q
      (fun i => s * G i + (-(s ^ 2) / 2) * A i) (hbudget s)
    rw [mean_linear] at h
    exact h
  have hsquare : m ^ 2 ≤ 2 * K * q := by
    by_cases hzero : q = 0
    · have hm : m = 0 := by
        by_contra hmne
        have h := hquad ((K + 1) / m)
        rw [hzero, mul_zero, add_zero, div_mul_cancel₀ (K + 1) hmne] at h
        linarith
      simp [hm, hzero]
    · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hzero)
      have h := hquad (m / q)
      have hidentity : (m / q) * m + (-(m / q) ^ 2 / 2) * q = m ^ 2 / (2 * q) := by
        field_simp
        ring
      rw [hidentity] at h
      have hmul := (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hqpos)).mp h
      nlinarith
  exact Real.abs_le_sqrt hsquare

end HaarQuarter
