import Mathlib.Analysis.SpecialFunctions.Exp
import BrownianSharp.AlignmentPaperJointDictionary

/-! Scalar estimates for the dyadic multiscale entropy chain. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperJointAdaptiveScalarSums

open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.AlignmentPaperLpDvpBlockCover
open BrownianSharp.AlignmentPaperLpDvpReconstruction

theorem shapeGrid_card_eq {d n : ℕ} (r : Shape d n) :
    Fintype.card (ShapeGrid r) = 2 ^ (n + 3 * d) := by
  classical
  have hprofile : (∑ i : Fin d, r.1 i) = n := by
    have hr := r.2
    rw [Finset.mem_finsuppAntidiag] at hr
    simpa using hr.1
  have hsum : (∑ i : Fin d, (r.1 i + 1)) = n + d := by
    calc
      _ = (∑ i : Fin d, r.1 i) + ∑ i : Fin d, (1 : ℕ) := by
        rw [Finset.sum_add_distrib]
      _ = n + d := by simp [hprofile]
  change Fintype.card (∀ i : Fin d, Fin (shapeBandwidth r i * 4)) = _
  rw [Fintype.card_pi]
  simp_rw [Fintype.card_fin]
  change (∏ i : Fin d, (2 ^ (r.1 i + 1) * 4)) = _
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  simp only [Finset.prod_const, Fintype.card_fin]
  rw [hsum]
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [← pow_add]
  congr 1
  omega

theorem jointSampleDimension_eq_grid_formula {d n : ℕ} :
    JointSampleDimension d n =
      2 ^ (n + 3 * d + 1) * Fintype.card (Shape d n) := by
  classical
  change Fintype.card (Σ r : Shape d n, ShapeGrid r × Bool) = _
  rw [Fintype.card_sigma]
  calc
    (∑ r : Shape d n, Fintype.card (ShapeGrid r × Bool)) =
        ∑ r : Shape d n, 2 ^ (n + 3 * d + 1) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hgrid := shapeGrid_card_eq r
      rw [Fintype.card_prod, Fintype.card_bool, hgrid, pow_succ]
    _ = 2 ^ (n + 3 * d + 1) * Fintype.card (Shape d n) := by
      simp [Finset.sum_const, mul_comm]

theorem jointSampleDimension_upper_envelope {d n : ℕ} (hd : 1 ≤ d) :
    (JointSampleDimension d n : ℝ) ≤
      (2 : ℝ) ^ (3 * d + 1) * (2 : ℝ) ^ n * (n + 1 : ℝ) ^ (d - 1) := by
  rw [jointSampleDimension_eq_grid_formula, shape_card d n (by omega : 0 < d)]
  push_cast
  have hcount : hyperbolicCount d n ≤ ((n : ℝ) + 1) ^ (d - 1) :=
    hyperbolicCount_upper_shift hd n
  have hnonneg : 0 ≤ (2 : ℝ) ^ (3 * d + 1) * (2 : ℝ) ^ n := by positivity
  have hcount' : (Nat.choose (n + d - 1) (d - 1) : ℝ) ≤
      (n + 1 : ℝ) ^ (d - 1) := by
    simpa [hyperbolicCount] using hcount
  have hpow : (2 : ℝ) ^ (n + 3 * d + 1) =
      (2 : ℝ) ^ (3 * d + 1) * (2 : ℝ) ^ n := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  exact mul_le_mul_of_nonneg_left hcount' hnonneg

theorem jointSampleDimension_lower_envelope {d n : ℕ} (hd : 1 ≤ d) :
    ((2 : ℝ) ^ (3 * d + 1) / (Nat.factorial (d - 1) : ℝ)) *
      (2 : ℝ) ^ n * (n + 1 : ℝ) ^ (d - 1) ≤
        (JointSampleDimension d n : ℝ) := by
  rw [jointSampleDimension_eq_grid_formula, shape_card d n (by omega : 0 < d)]
  push_cast
  have hcount : ((n : ℝ) + 1) ^ (d - 1) /
      (Nat.factorial (d - 1) : ℝ) ≤ hyperbolicCount d n :=
    hyperbolicCount_lower_shift hd n
  have hnonneg : 0 ≤ (2 : ℝ) ^ (3 * d + 1) * (2 : ℝ) ^ n := by positivity
  have hcount' : ((n + 1 : ℝ) ^ (d - 1) /
      (Nat.factorial (d - 1) : ℝ)) ≤
      (Nat.choose (n + d - 1) (d - 1) : ℝ) := by
    simpa [hyperbolicCount] using hcount
  have hpow : (2 : ℝ) ^ (n + 3 * d + 1) =
      (2 : ℝ) ^ (3 * d + 1) * (2 : ℝ) ^ n := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow]
  have hmul := mul_le_mul_of_nonneg_left hcount' hnonneg
  convert hmul using 1 <;> ring

theorem dictionaryDimension_eq_grid_formula {d n : ℕ} :
    DictionaryDimension d n = 2 * (4 * 2 ^ (n + 1)) ^ d := by
  change Fintype.card (Fin d → Fin (2 ^ (n + 1) * 4)) * 2 = _
  rw [Fintype.card_fun]
  simp only [Fintype.card_fin]
  rw [mul_comm (2 ^ (n + 1)) 4]
  ring

def dictionaryGradeBase (d : ℕ) : ℕ := 2 ^ d

def dictionaryGradePrefactor (d : ℕ) : ℕ := 2 ^ (3 * d + 1)

theorem dictionaryDimension_eq_grade_envelope {d n : ℕ} :
    DictionaryDimension d n = dictionaryGradePrefactor d *
      dictionaryGradeBase d ^ n := by
  rw [dictionaryDimension_eq_grid_formula]
  dsimp [dictionaryGradePrefactor, dictionaryGradeBase]
  have hpow : 4 * 2 ^ (n + 1) = 2 ^ (n + 3) := by
    rw [pow_succ, pow_add]
    ring
  rw [hpow]
  calc
    2 * (2 ^ (n + 3)) ^ d = 2 * 2 ^ ((n + 3) * d) := by rw [← pow_mul]
    _ = 2 ^ 1 * 2 ^ ((n + 3) * d) := by norm_num
    _ = 2 ^ (1 + (n + 3) * d) := by rw [← pow_add]
    _ = 2 ^ ((3 * d + 1) + d * n) := by congr 1 <;> ring
    _ = 2 ^ (3 * d + 1) * 2 ^ (d * n) := by rw [pow_add]
    _ = 2 ^ (3 * d + 1) * (2 ^ d) ^ n := by rw [← pow_mul]

def powTwoSum (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j

def weightedPowTwoSum (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j * ((J - j : ℕ) : ℝ)

def dyadicStageCost (J : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1),
    (2 : ℝ) ^ j * (f j + ((J - j : ℕ) : ℝ))

def geometricHalfSum (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), ((1 : ℝ) / 2) ^ j

def dyadicRadiusSum (J : ℕ) (ε : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (J + 1), ε * ((1 : ℝ) / 2) ^ j

def expPolynomialTsum (k : ℕ) (δ : ℝ) : ℝ :=
  ∑' j : ℕ, (j + 1 : ℝ) ^ k * Real.exp (-δ * j)

theorem powTwoSum_le (J : ℕ) : powTwoSum J ≤ 2 * (2 : ℝ) ^ J := by
  induction J with
  | zero => simp [powTwoSum]
  | succ J ih =>
      have hsum : powTwoSum (J + 1) = powTwoSum J + (2 : ℝ) ^ (J + 1) := by
        simp [powTwoSum, Finset.sum_range_succ, Nat.add_assoc]
      rw [hsum, pow_succ]
      nlinarith [ih, pow_pos (by norm_num : (0 : ℝ) < 2) J]

theorem weightedPowTwoSum_le (J : ℕ) :
    weightedPowTwoSum J ≤ 2 * (2 : ℝ) ^ J := by
  induction J with
  | zero => simp [weightedPowTwoSum]
  | succ J ih =>
      have hsum : weightedPowTwoSum (J + 1) =
          weightedPowTwoSum J + powTwoSum J := by
        unfold weightedPowTwoSum powTwoSum
        rw [show J + 1 + 1 = J + 2 by omega]
        rw [Finset.sum_range_succ]
        simp only [Nat.sub_self, Nat.cast_zero, mul_zero, add_zero]
        calc
          (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j * ((J + 1 - j : ℕ) : ℝ)) =
              ∑ j ∈ Finset.range (J + 1),
                ((2 : ℝ) ^ j * ((J - j : ℕ) : ℝ) + (2 : ℝ) ^ j) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hj' : j ≤ J := by simp only [Finset.mem_range] at hj; omega
            have heq : J + 1 - j = (J - j) + 1 := by omega
            rw [heq, Nat.cast_add, Nat.cast_one]
            ring
          _ = weightedPowTwoSum J + powTwoSum J := by
            rw [Finset.sum_add_distrib]
            rfl
      rw [hsum]
      have hp : 0 ≤ powTwoSum J := by
        unfold powTwoSum
        positivity
      have hpw : (0 : ℝ) < (2 : ℝ) ^ J := pow_pos (by norm_num) _
      rw [pow_succ]
      nlinarith [ih, powTwoSum_le J]

theorem dyadicStageCost_le {J : ℕ} {L : ℝ} (hL : 1 ≤ L)
    (f : ℕ → ℝ)
    (hf : ∀ j ∈ Finset.range (J + 1), f j ≤ L + ((J - j : ℕ) : ℝ)) :
    dyadicStageCost J f ≤ 6 * (2 : ℝ) ^ J * L := by
  unfold dyadicStageCost
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1),
        (2 : ℝ) ^ j * (L + 2 * ((J - j : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      have hpow : 0 ≤ (2 : ℝ) ^ j := by positivity
      have hterm := hf j hj
      nlinarith [mul_le_mul_of_nonneg_left hterm hpow]
    _ = L * powTwoSum J + 2 * weightedPowTwoSum J := by
      calc
        _ = (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j * L) +
            (∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j *
              (2 * ((J - j : ℕ) : ℝ))) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib]
        _ = L * powTwoSum J + 2 * weightedPowTwoSum J := by
          congr 1
          · unfold powTwoSum
            calc
              _ = ∑ j ∈ Finset.range (J + 1), L * (2 : ℝ) ^ j := by
                apply Finset.sum_congr rfl
                intro j hj
                ring
              _ = L * ∑ j ∈ Finset.range (J + 1), (2 : ℝ) ^ j := by
                rw [Finset.mul_sum]
          · unfold weightedPowTwoSum
            calc
              _ = ∑ j ∈ Finset.range (J + 1),
                  (2 * ((2 : ℝ) ^ j * ((J - j : ℕ) : ℝ))) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    ring
              _ = 2 * ∑ j ∈ Finset.range (J + 1),
                  (2 : ℝ) ^ j * ((J - j : ℕ) : ℝ) := by rw [Finset.mul_sum]
    _ ≤ L * (2 * (2 : ℝ) ^ J) + 2 * (2 * (2 : ℝ) ^ J) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (powTwoSum_le J) (by linarith)
      · exact mul_le_mul_of_nonneg_left (weightedPowTwoSum_le J) (by norm_num)
    _ ≤ 6 * (2 : ℝ) ^ J * L := by
      have hp : 0 ≤ (2 : ℝ) ^ J := by positivity
      nlinarith

theorem geometricHalfSum_eq (J : ℕ) :
    geometricHalfSum J = 2 - ((1 : ℝ) / 2) ^ J := by
  induction J with
  | zero => norm_num [geometricHalfSum]
  | succ J ih =>
      have hs : geometricHalfSum (J + 1) =
          geometricHalfSum J + ((1 : ℝ) / 2) ^ (J + 1) := by
        simp [geometricHalfSum, Finset.sum_range_succ, Nat.add_assoc]
      rw [hs, ih, pow_succ]
      ring

theorem dyadicRadiusSum_le (J : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    dyadicRadiusSum J ε ≤ 2 * ε := by
  unfold dyadicRadiusSum
  have hgeom : geometricHalfSum J ≤ 2 := by
    rw [geometricHalfSum_eq]
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2) J]
  calc
    _ = (∑ j ∈ Finset.range (J + 1), ((1 : ℝ) / 2) ^ j) * ε := by
      calc
        _ = ∑ j ∈ Finset.range (J + 1), ((1 : ℝ) / 2) ^ j * ε := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = (∑ j ∈ Finset.range (J + 1), ((1 : ℝ) / 2) ^ j) * ε := by
          rw [Finset.sum_mul]
    _ = ε * geometricHalfSum J := by rw [geometricHalfSum]; ring
    _ ≤ ε * 2 := mul_le_mul_of_nonneg_left hgeom hε
    _ = 2 * ε := by ring

theorem dyadic_log_envelope {J D j : ℕ} (hJD : 2 ^ J ≤ D) (hjJ : j ≤ J) :
    Real.log (Real.exp 1 * (D : ℝ) / (2 : ℝ) ^ j) ≤
      Real.log (Real.exp 1 * (D : ℝ) / (2 : ℝ) ^ J) + ((J - j : ℕ) : ℝ) := by
  have hD : 0 < (D : ℝ) := by
    have : 0 < (2 : ℝ) ^ J := by positivity
    exact lt_of_lt_of_le this (by exact_mod_cast hJD)
  have hpow : 0 < (2 : ℝ) ^ J := by positivity
  have hjpow : (2 : ℝ) ^ J = (2 : ℝ) ^ j * (2 : ℝ) ^ (J - j) := by
    rw [← pow_add]
    congr 1
    omega
  have heq : Real.exp 1 * (D : ℝ) / (2 : ℝ) ^ j =
      (Real.exp 1 * (D : ℝ) / (2 : ℝ) ^ J) * (2 : ℝ) ^ (J - j) := by
    rw [hjpow]
    field_simp
  rw [heq, Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hlog2 : Real.log 2 ≤ 1 := by
    apply (Real.log_le_iff_le_exp (by norm_num)).2
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hgap : 0 ≤ ((J - j : ℕ) : ℝ) := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hlog2 hgap]

theorem dyadicLogStageCost_le {J D : ℕ} (hJD : 2 ^ J ≤ D) :
    dyadicStageCost J (fun j => Real.log
      (Real.exp 1 * (D : ℝ) / (2 : ℝ) ^ j)) ≤
      6 * (2 : ℝ) ^ J * Real.log
        (Real.exp 1 * (D : ℝ) / (2 : ℝ) ^ J) := by
  have hL : 1 ≤ Real.log (Real.exp 1 * (D : ℝ) / (2 : ℝ) ^ J) := by
    have hD : (2 : ℝ) ^ J ≤ (D : ℝ) := by exact_mod_cast hJD
    have ht : Real.exp 1 ≤ Real.exp 1 * (D : ℝ) / (2 : ℝ) ^ J := by
      rw [le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ J)]
      nlinarith [Real.exp_pos (1 : ℝ)]
    have := Real.log_le_log (Real.exp_pos (1 : ℝ)) ht
    simpa using this
  apply dyadicStageCost_le hL
  intro j hj
  have hjJ : j ≤ J := by
    simp only [Finset.mem_range] at hj
    omega
  exact dyadic_log_envelope hJD hjJ

theorem lowGradeAllocationCost_le {N q : ℕ} {dim : ℕ → ℝ} {U c : ℝ}
    (hU : 0 ≤ U) (hc : 0 < c)
    (hupper : ∀ n : ℕ, dim n ≤ U * (2 : ℝ) ^ n * (n + 1 : ℝ) ^ q)
    (hlower : c * (2 : ℝ) ^ N * (N + 1 : ℝ) ^ q ≤ dim N) :
    (∑ n ∈ Finset.range (N + 1), dim n * (1 + ((N - n : ℕ) : ℝ))) ≤
      (4 * U / c) * dim N := by
  have hpoly : ∀ n ∈ Finset.range (N + 1),
      (n + 1 : ℝ) ^ q ≤ (N + 1 : ℝ) ^ q := by
    intro n hn
    have hnN : n ≤ N := by simp only [Finset.mem_range] at hn; omega
    apply pow_le_pow_left₀
    · positivity
    · exact_mod_cast Nat.add_le_add_right hnN 1
  have hsum : (∑ n ∈ Finset.range (N + 1),
      (2 : ℝ) ^ n * (1 + ((N - n : ℕ) : ℝ))) =
      powTwoSum N + weightedPowTwoSum N := by
    calc
      _ = ∑ n ∈ Finset.range (N + 1),
          ((2 : ℝ) ^ n + (2 : ℝ) ^ n * ((N - n : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        ring
      _ = _ := by
        unfold powTwoSum weightedPowTwoSum
        rw [Finset.sum_add_distrib]
  have hsumBound : (∑ n ∈ Finset.range (N + 1),
      (2 : ℝ) ^ n * (1 + ((N - n : ℕ) : ℝ))) ≤ 4 * (2 : ℝ) ^ N := by
    rw [hsum]
    nlinarith [powTwoSum_le N, weightedPowTwoSum_le N,
      pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) N]
  calc
    _ ≤ ∑ n ∈ Finset.range (N + 1),
        (U * (N + 1 : ℝ) ^ q) *
          ((2 : ℝ) ^ n * (1 + ((N - n : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro n hn
      have hfac : 0 ≤ 1 + ((N - n : ℕ) : ℝ) := by positivity
      have h1 := mul_le_mul_of_nonneg_right (hupper n) hfac
      have h2 : U * (2 : ℝ) ^ n * (n + 1 : ℝ) ^ q *
          (1 + ((N - n : ℕ) : ℝ)) ≤
          (U * (N + 1 : ℝ) ^ q) *
            ((2 : ℝ) ^ n * (1 + ((N - n : ℕ) : ℝ))) := by
        have hp := hpoly n hn
        have hpow : 0 ≤ (2 : ℝ) ^ n := by positivity
        have hcoef : 0 ≤ U * (2 : ℝ) ^ n := mul_nonneg hU hpow
        have hmul := mul_le_mul_of_nonneg_left hp hcoef
        nlinarith [mul_le_mul_of_nonneg_right hmul hfac]
      exact le_trans h1 h2
    _ = (U * (N + 1 : ℝ) ^ q) *
        (∑ n ∈ Finset.range (N + 1),
          (2 : ℝ) ^ n * (1 + ((N - n : ℕ) : ℝ))) := by
      rw [Finset.mul_sum]
    _ ≤ (U * (N + 1 : ℝ) ^ q) * (4 * (2 : ℝ) ^ N) :=
      mul_le_mul_of_nonneg_left hsumBound (by positivity)
    _ ≤ (4 * U / c) * dim N := by
      have hcoef : 0 ≤ 4 * U / c := by positivity
      have hlower' : (U * (N + 1 : ℝ) ^ q) * (4 * (2 : ℝ) ^ N) ≤
          (4 * U / c) * (c * (2 : ℝ) ^ N * (N + 1 : ℝ) ^ q) := by
        have heq : (U * (N + 1 : ℝ) ^ q) * (4 * (2 : ℝ) ^ N) =
            (4 * U / c) * (c * (2 : ℝ) ^ N * (N + 1 : ℝ) ^ q) := by
          field_simp [ne_of_gt hc]
        exact le_of_eq heq
      exact le_trans hlower' (mul_le_mul_of_nonneg_left hlower hcoef)

theorem summable_succ_pow_exp {k : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun j : ℕ => (j + 1 : ℝ) ^ k * Real.exp (-δ * j)) := by
  have hbase := Real.summable_pow_mul_exp_neg_nat_mul k hδ
  have hshift : Summable (fun j : ℕ => (j + 1 : ℝ) ^ k *
      Real.exp (-δ * (j + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun j : ℕ => (j : ℝ) ^ k *
        Real.exp (-δ * j)) 1).2 hbase
  have hmul := hshift.mul_left (Real.exp δ)
  apply hmul.congr
  intro j
  have hexp : -δ * (j : ℝ) = δ + (-δ * (j + 1)) := by ring
  rw [hexp, Real.exp_add]
  ring

theorem finite_expPolynomialSum_le_tsum {k K : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    (∑ j ∈ Finset.range K, (j + 1 : ℝ) ^ k * Real.exp (-δ * j)) ≤
      expPolynomialTsum k δ := by
  unfold expPolynomialTsum
  exact (summable_succ_pow_exp hδ).sum_le_tsum (Finset.range K)
    (fun j hj => mul_nonneg (by positivity) (Real.exp_nonneg _))

end BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
