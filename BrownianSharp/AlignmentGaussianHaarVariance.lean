import BrownianSharp.AlignmentGaussianHaarProjection
import BrownianSharp.AlignmentGeometricRanks

open scoped BigOperators
open HaarQuarter BrownianSharp.CameronMartin

namespace BrownianSharp.AlignmentGaussianHaarProjection

private theorem sum_two_pow_range_le (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (2 : ℝ) ^ n) ≤ (2 : ℝ) ^ (N + 1) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
      rw [show Nat.succ N + 1 = (N + 1) + 1 by omega,
        Finset.sum_range_succ]
      have h := ih
      rw [show N + 1 = Nat.succ N by omega] at h
      calc
        (∑ n ∈ Finset.range (N + 1), (2 : ℝ) ^ n) + (2 : ℝ) ^ (N + 1)
            ≤ (2 : ℝ) ^ (N + 1) + (2 : ℝ) ^ (N + 1) := add_le_add h le_rfl
        _ = (2 : ℝ) ^ (N + 2) := by norm_num [pow_succ]; ring

private theorem varianceTerm_le_low {d N n : ℕ} (hd : 1 ≤ d) (hn : n ≤ N) :
    gradeScale N n ^ 2 *
        ((Nat.choose (n + d - 1) (d - 1) : ℝ) / (2 : ℝ) ^ n) ≤
      ((N + 1 : ℝ) ^ (d - 1)) * (2 : ℝ) ^ n / (2 : ℝ) ^ (2 * N) := by
  have hchoose := hyperbolicCount_upper_shift hd n
  have hchoose' : (Nat.choose (n + d - 1) (d - 1) : ℝ) ≤
      ((n : ℝ) + 1) ^ (d - 1) := by
    simpa [hyperbolicCount] using hchoose
  have hnpoly : ((n : ℝ) + 1) ^ (d - 1) ≤ (N + 1 : ℝ) ^ (d - 1) := by
    apply pow_le_pow_left₀ (by positivity)
    exact_mod_cast Nat.add_le_add_right hn 1
  have hscale : gradeScale N n = 1 / (2 : ℝ) ^ (N - n) := by
    simp [gradeScale, hn]
  rw [hscale]
  let a : ℝ := (2 : ℝ) ^ (N - n)
  let b : ℝ := (2 : ℝ) ^ n
  have hpow : a ^ 2 * b ^ 2 = (2 : ℝ) ^ (2 * N) := by
    dsimp [a, b]
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    omega
  have hcoeff := hchoose'.trans hnpoly
  calc
    (1 / (2 : ℝ) ^ (N - n)) ^ 2 *
        ((Nat.choose (n + d - 1) (d - 1) : ℝ) / (2 : ℝ) ^ n) =
      (Nat.choose (n + d - 1) (d - 1) : ℝ) / (a ^ 2 * b) := by
        dsimp [a, b]
        field_simp
        <;> ring
    _ ≤ ((N + 1 : ℝ) ^ (d - 1)) / (a ^ 2 * b) :=
      div_le_div_of_nonneg_right hcoeff (by positivity)
    _ = ((N + 1 : ℝ) ^ (d - 1)) * b / (a ^ 2 * b ^ 2) := by
      field_simp
      <;> ring
    _ = ((N + 1 : ℝ) ^ (d - 1)) * (2 : ℝ) ^ n /
        (2 : ℝ) ^ (2 * N) := by rw [hpow]

private noncomputable def gradeVarianceTerm (d N n : ℕ) : ℝ :=
  gradeScale N n ^ 2 *
    ((Nat.choose (n + d - 1) (d - 1) : ℝ) / (2 : ℝ) ^ n)

private theorem low_grade_variance_sum_le (d N J : ℕ) (hd : 1 ≤ d)
    (hJ : J ≤ N + 1) :
    (∑ n ∈ Finset.range J, gradeVarianceTerm d N n) ≤
      2 * ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N := by
  have hterm : ∀ n ∈ Finset.range J,
      gradeVarianceTerm d N n ≤
        ((N + 1 : ℝ) ^ (d - 1)) * (2 : ℝ) ^ n / (2 : ℝ) ^ (2 * N) := by
    intro n hn
    apply varianceTerm_le_low hd
    have : n < N + 1 := lt_of_lt_of_le (Finset.mem_range.mp hn) hJ
    omega
  calc
    (∑ n ∈ Finset.range J, gradeVarianceTerm d N n) ≤
        ∑ n ∈ Finset.range J,
          ((N + 1 : ℝ) ^ (d - 1)) * (2 : ℝ) ^ n / (2 : ℝ) ^ (2 * N) :=
      Finset.sum_le_sum hterm
    _ = ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ (2 * N) *
          ∑ n ∈ Finset.range J, (2 : ℝ) ^ n := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      ring
    _ ≤ ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ (2 * N) *
          (2 : ℝ) ^ (N + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hsubset := Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun n : ℕ => (2 : ℝ) ^ n)
        (Finset.range_mono hJ)
        (by intro n hmem hnot; exact pow_nonneg (show (0 : ℝ) ≤ (2 : ℝ) by norm_num) n)
      exact hsubset.trans (sum_two_pow_range_le N)
    _ = 2 * ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N := by
      have hp : (2 : ℝ) ^ (2 * N) = (2 : ℝ) ^ N * (2 : ℝ) ^ N := by
        rw [← pow_add]
        congr 1
        omega
      rw [hp, show (N + 1 : ℕ) = N + 1 by rfl, pow_succ]
      field_simp
      <;> ring

private theorem high_grade_variance_sum_le (d N J : ℕ) (hd : 1 ≤ d)
    (hJ : N + 1 ≤ J) :
    (∑ n ∈ Finset.range (J - (N + 1)), gradeVarianceTerm d N (N + 1 + n)) ≤
      ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N *
        BrownianSharp.AlignmentGeometricRanks.polynomialBudget (1 / 2) (d - 1) := by
  let K := J - (N + 1)
  have htail := BrownianSharp.AlignmentGaussianHaarTail.finite_hyperbolic_energy_tail_bound
    d N K hd
  have hterm : ∀ h ∈ Finset.range K,
      gradeVarianceTerm d N (N + 1 + h) ≤
        ((Nat.choose (N + 1 + h + d - 1) (d - 1) : ℝ) /
          (2 : ℝ) ^ (N + 1 + h)) := by
    intro h hh
    have hscale : gradeScale N (N + 1 + h) = 1 := by
      simp [gradeScale]
      omega
    rw [gradeVarianceTerm, hscale]
    simp [Nat.add_comm (N + 1) h]
  calc
    (∑ n ∈ Finset.range K, gradeVarianceTerm d N (N + 1 + n)) ≤
        ∑ h ∈ Finset.range K,
          (Nat.choose (N + 1 + h + d - 1) (d - 1) : ℝ) /
            (2 : ℝ) ^ (N + 1 + h) := Finset.sum_le_sum hterm
    _ ≤ ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N *
          ∑ h ∈ Finset.range K,
            ((h + 2 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ (h + 1) := htail
    _ ≤ ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N *
          BrownianSharp.AlignmentGeometricRanks.polynomialBudget (1 / 2) (d - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      let f : ℕ → ℝ := fun j => ((j + 1 : ℕ) : ℝ) ^ (d - 1) * (1 / 2 : ℝ) ^ j
      have hsum := BrownianSharp.AlignmentGeometricRanks.summable_polynomial_geometric
        (q := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (d - 1)
      have hshift : Summable (fun h : ℕ => f (h + 1)) :=
        (summable_nat_add_iff 1).2 hsum
      have hfinite := hshift.sum_le_tsum (s := Finset.range K) (by intro h hh; positivity)
      have hident : (∑ h ∈ Finset.range K,
          ((h + 2 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ (h + 1)) =
          ∑ h ∈ Finset.range K, f (h + 1) := by
        apply Finset.sum_congr rfl
        intro h hh
        simp only [f]
        push_cast
        rw [one_div_pow]
        ring
      have hdrop : (∑' h : ℕ, f (h + 1)) ≤ ∑' j : ℕ, f j := by
        have hsplit := hsum.sum_add_tsum_nat_add 1
        calc
          _ ≤ (∑ j ∈ Finset.range 1, f j) + ∑' h : ℕ, f (h + 1) :=
            le_add_of_nonneg_left (by positivity)
          _ = ∑' j : ℕ, f j := by simpa [f] using hsplit
      have hfinite' : (∑ h ∈ Finset.range K,
          ((h + 2 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ (h + 1)) ≤
          ∑' h : ℕ, f (h + 1) := by rw [hident]; exact hfinite
      calc
        _ ≤ ∑' h : ℕ, f (h + 1) := hfinite'
        _ ≤ ∑' j : ℕ, f j := hdrop
        _ = BrownianSharp.AlignmentGeometricRanks.polynomialBudget (1 / 2) (d - 1) := rfl

theorem grade_scaled_variance_sum_uniform (d N M : ℕ) (hd : 0 < d) :
    (∑ n : Fin (d * M + 1),
      gradeScale N n.val ^ 2 *
        ((Nat.choose (n.val + d - 1) (d - 1) : ℝ) / (2 : ℝ) ^ n.val)) ≤
      ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N *
        (2 + BrownianSharp.AlignmentGeometricRanks.polynomialBudget (1 / 2) (d - 1)) := by
  classical
  let J := d * M + 1
  have hsum : (∑ n : Fin (d * M + 1),
      gradeScale N n.val ^ 2 *
        ((Nat.choose (n.val + d - 1) (d - 1) : ℝ) / (2 : ℝ) ^ n.val)) =
      ∑ n ∈ Finset.range J, gradeVarianceTerm d N n := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp [J, gradeVarianceTerm]
  rw [hsum]
  by_cases hlow : J ≤ N + 1
  · have h := low_grade_variance_sum_le d N J (by omega) hlow
    have hbudget := BrownianSharp.AlignmentGeometricRanks.polynomialBudget_nonneg
      (q := (1 / 2 : ℝ)) (by norm_num) (d - 1)
    have hpref : 0 ≤ ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N := by positivity
    calc
      _ ≤ 2 * ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N := h
      _ = ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N * 2 := by ring
      _ ≤ ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N *
          (2 + BrownianSharp.AlignmentGeometricRanks.polynomialBudget (1 / 2) (d - 1)) :=
        mul_le_mul_of_nonneg_left (by linarith) hpref
  · have hlarge : N + 1 ≤ J := by omega
    rw [show J = (N + 1) + (J - (N + 1)) by omega, Finset.sum_range_add]
    have hlow' := low_grade_variance_sum_le d N (N + 1) (by omega) le_rfl
    have hhigh := high_grade_variance_sum_le d N J (by omega) hlarge
    have hpref : 0 ≤ ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N := by positivity
    calc
      (∑ n ∈ Finset.range (N + 1), gradeVarianceTerm d N n) +
        ∑ n ∈ Finset.range (J - (N + 1)),
          gradeVarianceTerm d N (N + 1 + n) ≤
        2 * ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N +
        ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N *
          BrownianSharp.AlignmentGeometricRanks.polynomialBudget (1 / 2) (d - 1) :=
            add_le_add hlow' hhigh
      _ = ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N *
          (2 + BrownianSharp.AlignmentGeometricRanks.polynomialBudget (1 / 2) (d - 1)) := by ring

theorem grade_scaled_feature_variance_uniform {d N M : ℕ} (hd : 0 < d)
    (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    ‖gradeScaledFeature (N := N) (M := M)
        (⟨brownianSheetBoxIndicatorLp t,
          brownianCubeBoxIndicator_mem ⟨t, ht⟩⟩ : brownianCubeBoxSpan d)‖ ^ 2 ≤
      ((N + 1 : ℝ) ^ (d - 1)) / (2 : ℝ) ^ N *
        (2 + BrownianSharp.AlignmentGeometricRanks.polynomialBudget (1 / 2) (d - 1)) := by
  exact (grade_scaled_feature_variance_le hd t ht).trans
    (grade_scaled_variance_sum_uniform d N M hd)


end BrownianSharp.AlignmentGaussianHaarProjection
