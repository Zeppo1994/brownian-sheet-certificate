import BrownianSharp.FiniteHaarGradeEnergy
import BrownianSharp.AlignmentGaussianHaarProjection
import Mathlib.Data.Nat.Choose.Bounds

open scoped BigOperators
open HaarQuarter

namespace BrownianSharp

private theorem sum_range_pow_two (m : ℕ) :
    (∑ n ∈ Finset.range (m + 1), 2 ^ n) = 2 ^ (m + 1) - 1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      have hp : 2 ^ (m + 2) = 2 ^ (m + 1) * 2 := by
        rw [pow_succ]
      omega

private noncomputable def finiteHaarAxisCell {N : ℕ} (a : FiniteHaarAxis N) :
    Fin (2 ^ finiteHaarAxisGrade a) := by
  cases a with
  | none => exact ⟨0, by norm_num [finiteHaarAxisGrade]⟩
  | some j =>
      have hle : 2 ^ j.1.val ≤ 2 ^ (j.1.val + 1) := by
        rw [pow_succ]
        omega
      exact Fin.castLE hle j.2

private noncomputable def finiteHaarGradeLayerToLayerIndex {d N n : ℕ}
    (a : FiniteHaarGradeLayer d N n) : LayerIndex d n := by
  classical
  let profile : Fin d → ℕ := fun i => finiteHaarAxisGrade (a.1 i)
  have hsum : ∑ i : Fin d, profile i = n := by
    simpa [profile, finiteHaarGrade] using a.2
  let shape : Shape d n := by
    refine ⟨Finsupp.equivFunOnFinite.symm profile, ?_⟩
    apply Finset.mem_finsuppAntidiag'.2
    constructor
    · simpa [Finsupp.sum_fintype] using hsum
    · simp
  refine ⟨shape, ?_⟩
  intro i
  have hprof : shape.1 i = profile i := rfl
  simpa [profile, hprof] using finiteHaarAxisCell (a.1 i)

private theorem finiteHaarGradeLayerToLayerIndex_injective {d N n : ℕ} :
    Function.Injective (finiteHaarGradeLayerToLayerIndex (d := d) (N := N) (n := n)) := by
  classical
  intro a b hab
  apply Subtype.ext
  funext i
  have hgrade : finiteHaarAxisGrade (a.1 i) = finiteHaarAxisGrade (b.1 i) := by
    have h := congrArg (fun z : LayerIndex d n => layerIndexDepth z i) hab
    simpa [finiteHaarGradeLayerToLayerIndex, layerIndexDepth] using h
  cases ha : a.1 i with
  | none =>
      cases hb : b.1 i with
      | none => rfl
      | some y => simp [ha, hb, finiteHaarAxisGrade] at hgrade
  | some x =>
      cases hb : b.1 i with
      | none => simp [ha, hb, finiteHaarAxisGrade] at hgrade
      | some y =>
          have hdepth : x.1.val = y.1.val := by
            simp [ha, hb, finiteHaarAxisGrade] at hgrade
            omega
          have h := congrArg (fun z : LayerIndex d n => layerIndexCell z i) hab
          rcases x with ⟨s, j⟩
          rcases y with ⟨u, k⟩
          change (finiteHaarAxisCell (a.1 i)).val =
            (finiteHaarAxisCell (b.1 i)).val at h
          rw [ha, hb] at h
          simp [finiteHaarAxisCell] at h
          have haddr : j.val = k.val := h
          have hs : s = u := Fin.ext hdepth
          cases hs
          have hj : j = k := Fin.ext haddr
          cases hj
          rfl

theorem finiteHaarGradeLayer_card_le_layerIndex (d N n : ℕ) (hd : 0 < d) :
    Fintype.card (FiniteHaarGradeLayer d N n) ≤
      2 ^ n * Nat.choose (n + d - 1) (d - 1) := by
  classical
  calc
    Fintype.card (FiniteHaarGradeLayer d N n) ≤ Fintype.card (LayerIndex d n) :=
      Fintype.card_le_of_injective finiteHaarGradeLayerToLayerIndex
        finiteHaarGradeLayerToLayerIndex_injective
    _ = 2 ^ n * Nat.choose (n + d - 1) (d - 1) := layerIndex_card d n hd

theorem weak_composition_card_le_pow (N d n : ℕ) (hn : n ≤ N) :
    Nat.choose (n + d - 1) (d - 1) ≤ (N + d) ^ (d - 1) := by
  have hchoose := Nat.choose_le_pow (n + d - 1) (d - 1)
  have htop : n + d - 1 ≤ N + d := by omega
  exact hchoose.trans (Nat.pow_le_pow_left htop _)

/-! A finite combinatorial bound for the determinant cost of diagonal Haar
dilation.  The grade-cardinality hypothesis is stated explicitly so that the
numeric estimate can be reused with either the native Haar grade layer or an
isomorphic grade-index family. -/

theorem weighted_dyadic_grade_sum_le (N d : ℕ)
    (hchoose : ∀ n ≤ N,
      Nat.choose (n + d - 1) (d - 1) ≤ (N + d) ^ (d - 1)) :
    (∑ n ∈ Finset.range (N + 1),
      (N - n) * 2 ^ n * Nat.choose (n + d - 1) (d - 1)) ≤
      2 ^ (N + 1) * (N + d) ^ (d - 1) := by
  classical
  have hgeom : ∀ m : ℕ,
      (∑ n ∈ Finset.range (m + 1), (m - n) * 2 ^ n) ≤ 2 ^ (m + 1) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        rw [Finset.sum_range_succ]
        have hsplit :
            (∑ n ∈ Finset.range (m + 1), (m + 1 - n) * 2 ^ n) =
              (∑ n ∈ Finset.range (m + 1), (m - n) * 2 ^ n) +
                ∑ n ∈ Finset.range (m + 1), 2 ^ n := by
          calc
            (∑ n ∈ Finset.range (m + 1), (m + 1 - n) * 2 ^ n) =
                ∑ n ∈ Finset.range (m + 1), ((m - n) * 2 ^ n + 2 ^ n) := by
                  apply Finset.sum_congr rfl
                  intro n hn
                  have hn' : n ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
                  have hsub : m + 1 - n = (m - n) + 1 := by omega
                  rw [hsub]
                  ring
            _ = (∑ n ∈ Finset.range (m + 1), (m - n) * 2 ^ n) +
                ∑ n ∈ Finset.range (m + 1), 2 ^ n := by
                  rw [Finset.sum_add_distrib]
        rw [hsplit]
        have hpow : (∑ n ∈ Finset.range (m + 1), 2 ^ n) = 2 ^ (m + 1) - 1 := by
          exact sum_range_pow_two m
        rw [hpow]
        have hlast : (m + 1 - (m + 1)) * 2 ^ (m + 1) = 0 := by simp
        have hp2 : 2 ^ (m + 2) = 2 ^ (m + 1) * 2 := by rw [pow_succ]
        omega
  have hterm (n : ℕ) (hn : n ∈ Finset.range (N + 1)) :
      (N - n) * 2 ^ n * Nat.choose (n + d - 1) (d - 1) ≤
        (N - n) * 2 ^ n * (N + d) ^ (d - 1) := by
    have hnlt : n < N + 1 := Finset.mem_range.mp hn
    have hn' : n ≤ N := by omega
    exact Nat.mul_le_mul_left ((N - n) * 2 ^ n) (hchoose n hn')
  calc
    (∑ n ∈ Finset.range (N + 1),
        (N - n) * 2 ^ n * Nat.choose (n + d - 1) (d - 1)) ≤
      ∑ n ∈ Finset.range (N + 1),
        (N - n) * 2 ^ n * (N + d) ^ (d - 1) := by
          apply Finset.sum_le_sum
          intro n hn
          exact hterm n hn
    _ = (∑ n ∈ Finset.range (N + 1), (N - n) * 2 ^ n) *
        (N + d) ^ (d - 1) := by rw [Finset.sum_mul]
    _ ≤ 2 ^ (N + 1) * (N + d) ^ (d - 1) := by
      exact Nat.mul_le_mul_right _ (hgeom N)

theorem native_weighted_grade_count_le (N d M : ℕ) (hd : 0 < d) :
    (∑ n ∈ Finset.range (N + 1),
      (N - n) * Fintype.card (FiniteHaarGradeLayer d M n)) ≤
      2 ^ (N + 1) * (N + d) ^ (d - 1) := by
  classical
  have hsum := weighted_dyadic_grade_sum_le N d (fun n hn =>
    weak_composition_card_le_pow N d n hn)
  apply le_trans ?_ hsum
  apply Finset.sum_le_sum
  intro n hn
  have hcard := finiteHaarGradeLayer_card_le_layerIndex d M n hd
  simpa [Nat.mul_assoc] using Nat.mul_le_mul_left (N - n) hcard

private abbrev FiniteHaarGradeBelow (d M N : ℕ) :=
  {a : FiniteHaarIndex d M // finiteHaarGrade a ≤ N}

private noncomputable def finiteHaarGradeBelowEquiv (d M N : ℕ) :
    FiniteHaarGradeBelow d M N ≃
      Σ n : Fin (N + 1), FiniteHaarGradeLayer d M n.val where
  toFun a :=
    ⟨⟨finiteHaarGrade a.1, Nat.lt_succ_of_le a.2⟩,
      ⟨a.1, rfl⟩⟩
  invFun p :=
    ⟨p.2.1, by rw [p.2.2]; exact Nat.lt_succ_iff.mp p.1.isLt⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨n, a⟩
    apply Sigma.ext
    · apply Fin.ext
      exact a.2
    · apply (Subtype.heq_iff_coe_eq (fun x => by
        change (finiteHaarGrade x = finiteHaarGrade a.1) ↔
          (finiteHaarGrade x = n.val)
        rw [a.2])).2
      rfl

private theorem finiteHaar_grade_weight_sum_eq (N d M : ℕ) :
    (∑ a : FiniteHaarIndex d M, (N - finiteHaarGrade a)) =
      ∑ n ∈ Finset.range (N + 1),
        (N - n) * Fintype.card (FiniteHaarGradeLayer d M n) := by
  classical
  let f : FiniteHaarIndex d M → ℕ := fun a => N - finiteHaarGrade a
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun a : FiniteHaarIndex d M => finiteHaarGrade a ≤ N) f
  have hlarge :
      (∑ a : {a : FiniteHaarIndex d M // ¬ finiteHaarGrade a ≤ N}, f a.1) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    have hgt : N < finiteHaarGrade a.1 := by omega
    simp [f, Nat.sub_eq_zero_of_le (Nat.le_of_lt hgt)]
  have hbelow :
      (∑ a : FiniteHaarGradeBelow d M N, f a.1) =
        ∑ n ∈ Finset.range (N + 1),
          (N - n) * Fintype.card (FiniteHaarGradeLayer d M n) := by
    rw [Fintype.sum_equiv (finiteHaarGradeBelowEquiv d M N)
      (fun a => f a.1)
      (fun p => N - p.1.val)
      (by intro a; rfl)]
    rw [Fintype.sum_sigma]
    have hinner (i : Fin (N + 1)) :
        (Finset.univ.sum (fun z : FiniteHaarGradeLayer d M i.val =>
          N - i.val)) =
          Fintype.card (FiniteHaarGradeLayer d M i.val) * (N - i.val) := by
      rw [Finset.sum_const]
      simp only [Finset.card_univ, nsmul_eq_mul]
      norm_cast
    change (∑ i : Fin (N + 1),
      Finset.univ.sum (fun z : FiniteHaarGradeLayer d M i.val => N - i.val)) = _
    calc
      (∑ i : Fin (N + 1),
          Finset.univ.sum (fun z : FiniteHaarGradeLayer d M i.val =>
            N - i.val)) =
        ∑ i : Fin (N + 1),
          Fintype.card (FiniteHaarGradeLayer d M i.val) * (N - i.val) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hinner i
      _ = ∑ n ∈ Finset.range (N + 1),
          (N - n) * Fintype.card (FiniteHaarGradeLayer d M n) := by
            rw [Fin.sum_univ_eq_sum_range
              (fun n => Fintype.card (FiniteHaarGradeLayer d M n) * (N - n))]
            apply Finset.sum_congr rfl
            intro n hn
            exact Nat.mul_comm _ _
  calc
    (∑ a : FiniteHaarIndex d M, f a) =
        (∑ a : FiniteHaarGradeBelow d M N, f a.1) +
          ∑ a : {a : FiniteHaarIndex d M // ¬ finiteHaarGrade a ≤ N}, f a.1 :=
      hsplit.symm
    _ = ∑ n ∈ Finset.range (N + 1),
          (N - n) * Fintype.card (FiniteHaarGradeLayer d M n) := by
      rw [hlarge, add_zero, hbelow]

noncomputable def auditHaarGradeScale (N n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ (N - n)

theorem auditHaarGradeScale_eq_gradeScale (N n : ℕ) :
    auditHaarGradeScale N n = AlignmentGaussianHaarProjection.gradeScale N n := by
  rw [auditHaarGradeScale, AlignmentGaussianHaarProjection.gradeScale]
  by_cases h : n ≤ N
  · simp [h, one_div_pow]
  · have hsub : N - n = 0 := Nat.sub_eq_zero_of_le (by omega)
    simp [h, hsub]

theorem auditHaar_diagonal_scale_product_eq (N d M : ℕ) :
    (∏ a : FiniteHaarIndex d M, auditHaarGradeScale N (finiteHaarGrade a)) =
      Real.exp (-Real.log 2 *
        (∑ n ∈ Finset.range (N + 1),
          (N - n) * Fintype.card (FiniteHaarGradeLayer d M n))) := by
  classical
  simp only [auditHaarGradeScale]
  change (∏ a ∈ (Finset.univ : Finset (FiniteHaarIndex d M)),
      (1 / 2 : ℝ) ^ (N - finiteHaarGrade a)) = _
  rw [Finset.prod_pow_eq_pow_sum, finiteHaar_grade_weight_sum_eq]
  have hexp :
      Real.exp (-Real.log 2 *
        (∑ n ∈ Finset.range (N + 1),
          (N - n) * Fintype.card (FiniteHaarGradeLayer d M n))) =
        (1 / 2 : ℝ) ^
          (∑ n ∈ Finset.range (N + 1),
            (N - n) * Fintype.card (FiniteHaarGradeLayer d M n)) := by
    rw [show -Real.log 2 *
          (∑ n ∈ Finset.range (N + 1),
            (N - n) * Fintype.card (FiniteHaarGradeLayer d M n)) =
          (∑ n ∈ Finset.range (N + 1),
            (N - n) * Fintype.card (FiniteHaarGradeLayer d M n)) * (-Real.log 2) by ring]
    rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  exact hexp.symm

theorem auditHaar_diagonal_scale_product_lower (N d M : ℕ) (hd : 0 < d) :
    (∏ a : FiniteHaarIndex d M, auditHaarGradeScale N (finiteHaarGrade a)) ≥
      (1 / 2 : ℝ) ^ (2 ^ (N + 1) * (N + d) ^ (d - 1)) := by
  rw [auditHaar_diagonal_scale_product_eq]
  have hsum := native_weighted_grade_count_le N d M hd
  have hpower :
      (1 / 2 : ℝ) ^ (2 ^ (N + 1) * (N + d) ^ (d - 1)) ≤
        (1 / 2 : ℝ) ^
          (∑ n ∈ Finset.range (N + 1),
            (N - n) * Fintype.card (FiniteHaarGradeLayer d M n)) := by
    have h := one_div_pow_le_one_div_pow_of_le
      (a := (2 : ℝ)) (by norm_num : (1 : ℝ) ≤ 2) hsum
    norm_num [one_div, div_pow] at h ⊢
    exact h
  have hexp :
      Real.exp (-Real.log 2 *
        (∑ n ∈ Finset.range (N + 1),
          (N - n) * Fintype.card (FiniteHaarGradeLayer d M n))) =
        (1 / 2 : ℝ) ^
          (∑ n ∈ Finset.range (N + 1),
            (N - n) * Fintype.card (FiniteHaarGradeLayer d M n)) := by
    rw [show -Real.log 2 *
          (∑ n ∈ Finset.range (N + 1),
            (N - n) * Fintype.card (FiniteHaarGradeLayer d M n)) =
          (∑ n ∈ Finset.range (N + 1),
            (N - n) * Fintype.card (FiniteHaarGradeLayer d M n)) * (-Real.log 2) by ring]
    rw [Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hexp]
  exact hpower

theorem gradeScale_diagonal_product_lower (N d M : ℕ) (hd : 0 < d) :
    (∏ a : FiniteHaarIndex d M,
      AlignmentGaussianHaarProjection.gradeScale N (finiteHaarGrade a)) ≥
      (1 / 2 : ℝ) ^ (2 ^ (N + 1) * (N + d) ^ (d - 1)) := by
  simpa only [auditHaarGradeScale_eq_gradeScale] using
    auditHaar_diagonal_scale_product_lower N d M hd

theorem gradeScale_diagonal_product_exp_lower (N d M : ℕ) (hd : 0 < d) :
    (∏ a : FiniteHaarIndex d M,
      AlignmentGaussianHaarProjection.gradeScale N (finiteHaarGrade a)) ≥
      Real.exp (-Real.log 2 *
        (2 * (d : ℝ) ^ (d - 1) * (2 : ℝ) ^ N * (N + 1 : ℝ) ^ (d - 1))) := by
  let B : ℕ := 2 ^ (N + 1) * (N + d) ^ (d - 1)
  have hhalf := gradeScale_diagonal_product_lower N d M hd
  have hexpB : Real.exp (-Real.log 2 * (B : ℝ)) = (1 / 2 : ℝ) ^ B := by
    rw [show -Real.log 2 * (B : ℝ) = (B : ℝ) * (-Real.log 2) by ring]
    rw [Real.exp_nat_mul, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hbase : Real.exp (-Real.log 2 * (B : ℝ)) ≤
      ∏ a : FiniteHaarIndex d M,
        AlignmentGaussianHaarProjection.gradeScale N (finiteHaarGrade a) := by
    rw [hexpB]
    exact hhalf
  have hNat : N + d ≤ d * (N + 1) := by
    have hmul : N ≤ d * N := by
      calc
        N = 1 * N := by omega
        _ ≤ d * N := Nat.mul_le_mul_right N (Nat.succ_le_iff.mpr hd)
    calc
      N + d ≤ d * N + d := Nat.add_le_add_right hmul d
      _ = d * (N + 1) := by rw [Nat.mul_add, Nat.mul_one]
  have hR : (N + d : ℝ) ≤ (d : ℝ) * (N + 1) := by exact_mod_cast hNat
  have hpow : (N + d : ℝ) ^ (d - 1) ≤
      ((d : ℝ) * (N + 1)) ^ (d - 1) :=
    pow_le_pow_left₀ (by positivity) hR (d - 1)
  have hB : (B : ℝ) ≤
      2 * (d : ℝ) ^ (d - 1) * (2 : ℝ) ^ N * (N + 1 : ℝ) ^ (d - 1) := by
    dsimp [B]
    push_cast
    calc
      (2 : ℝ) ^ (N + 1) * (N + d : ℝ) ^ (d - 1) ≤
          (2 : ℝ) ^ (N + 1) * ((d : ℝ) * (N + 1)) ^ (d - 1) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = 2 * (d : ℝ) ^ (d - 1) * (2 : ℝ) ^ N *
            (N + 1 : ℝ) ^ (d - 1) := by
          rw [mul_pow, pow_succ]
          ring
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have harg :
      -(Real.log 2 *
        (2 * (d : ℝ) ^ (d - 1) * (2 : ℝ) ^ N * (N + 1 : ℝ) ^ (d - 1))) ≤
      -Real.log 2 * (B : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hB (le_of_lt hlog)
    nlinarith
  simpa [ge_iff_le] using (Real.exp_le_exp.mpr harg).trans hbase

end BrownianSharp
