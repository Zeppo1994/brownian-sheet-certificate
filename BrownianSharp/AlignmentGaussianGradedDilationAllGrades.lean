import BrownianSharp.AlignmentGaussianGradedDilationCost
import BrownianSharp.AlignmentGaussianDiagonalCoordinates
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentGaussianGradedDilationAllGrades

open BrownianSharp.AlignmentGaussianGradedDilationCost
open BrownianSharp.AlignmentGaussianDiagonalCoordinates
open BrownianSharp.AlignmentFractionalSharpBudgets
open BrownianSharp.AlignmentGeometricRanks

private def lowGradeSubtype {ι : Type*} (grade : ι → ℕ) (N : ℕ) :=
  {i : ι // grade i ≤ N}

private theorem lowFiber_card_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (grade : ι → ℕ) (N : ℕ) (g : Fin (N+1))
    [Fintype (lowGradeSubtype grade N)]
    [Fintype {i : lowGradeSubtype grade N // grade i.val = g.val}]
    [Fintype {i : ι // grade i = g.val}] :
    Fintype.card {i : lowGradeSubtype grade N // grade i.val = g.val} =
      Fintype.card {i : ι // grade i = g.val} := by
  classical
  let e : {i : lowGradeSubtype grade N // grade i.val = g.val} ≃
      {i : ι // grade i = g.val} := {
    toFun := fun i => ⟨i.val.val, i.property⟩
    invFun := fun i => ⟨⟨i.val, by rw [i.property]; exact Nat.le_of_lt_succ g.isLt⟩, i.property⟩
    left_inv := by intro i; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := by intro i; apply Subtype.ext; rfl }
  exact Fintype.card_congr e

/-- The dilation cost is unchanged by coordinates above the cutoff: those
coordinates have contraction scale one. -/
theorem finite_graded_index_dilation_cost_sum_le_all_grades
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (grade : ι → ℕ) (C : ℝ) (k N : ℕ)
    (hC : 0 ≤ C)
    (hfiber : ∀ g : Fin (N + 1),
      (Fintype.card {i : ι // grade i = g.val} : ℝ) ≤
        C * (2 : ℝ)^g.val * (((g.val + 1 : ℕ) : ℝ)^k)) :
    (∑ i : ι, ((N - grade i : ℕ) : ℝ)) ≤
      C * (2 : ℝ)^N * (((N + 1 : ℕ) : ℝ)^k) * polynomialBudget (1/2) 1 := by
  classical
  let lo := lowGradeSubtype grade N
  letI : Fintype lo := Fintype.subtype
    (Finset.univ.filter fun i : ι => grade i ≤ N) (by intro i; simp)
  letI : DecidableEq lo := Classical.decEq lo
  have hNlo : ∀ i : lo, grade i.val ≤ N := fun i => i.property
  have hfiberlo : ∀ g : Fin (N+1),
      (Fintype.card {i : lo // grade i.val = g.val} : ℝ) ≤
        C * (2 : ℝ)^g.val * (((g.val + 1 : ℕ) : ℝ)^k) := by
    intro g
    letI : Fintype {i : lo // grade i.val = g.val} := Fintype.subtype
      (Finset.univ.filter fun i : lo => grade i.val = g.val) (by intro i; simp)
    letI : Fintype {i : ι // grade i = g.val} := Fintype.subtype
      (Finset.univ.filter fun i : ι => grade i = g.val) (by intro i; simp)
    rw [lowFiber_card_eq grade N g]
    exact hfiber g
  have hlo := finite_graded_index_dilation_cost_sum_le
    (fun i : lo => grade i.val) C k N hC hNlo hfiberlo
  have hsum : (∑ i : ι, ((N-grade i:ℕ):ℝ)) =
      ∑ i : lo, ((N-grade i.val:ℕ):ℝ) := by
    classical
    let p : ι → Prop := fun i => grade i ≤ N
    have hsplit := (Fintype.sum_subtype_add_sum_subtype p
      (fun i => ((N-grade i:ℕ):ℝ))).symm
    have hhigh : (∑ i : {i : ι // ¬ p i}, ((N-grade i.val:ℕ):ℝ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hn : N < grade i.val := Nat.lt_of_not_ge i.property
      simp [Nat.sub_eq_zero_of_le hn.le]
    rw [hsplit, hhigh, add_zero]
    simpa [lo, lowGradeSubtype, p]
  rw [hsum]
  exact hlo

/-- Uniform determinant cost for finite graded frames, with no restriction on
the largest grade. -/
theorem finite_graded_diagonal_dilation_product_ge_exp_all_grades
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (grade : ι → ℕ) (C η : ℝ) (k N : ℕ)
    (hC : 0 ≤ C) (hη : 0 < η) (hη1 : η ≤ 1)
    (hfiber : ∀ g : Fin (N + 1),
      (Fintype.card {i : ι // grade i = g.val} : ℝ) ≤
        C * (2 : ℝ)^g.val * (((g.val + 1 : ℕ) : ℝ)^k)) :
    ∏ i : ι, contractionScale η N (grade i) ≥
      Real.exp (-(-Real.log η) *
        (C * (2 : ℝ)^N * (((N + 1 : ℕ) : ℝ)^k) * polynomialBudget (1/2) 1)) := by
  have hcost := finite_graded_index_dilation_cost_sum_le_all_grades
    grade C k N hC hfiber
  have hprod : (∏ i : ι, contractionScale η N (grade i)) =
      Real.exp (Real.log η * (∑ i : ι, ((N-grade i:ℕ):ℝ))) := by
    classical
    rw [show (∏ i : ι, contractionScale η N (grade i)) =
      ∏ i : ι, η^(N-grade i) by
        apply Finset.prod_congr rfl
        intro i hi
        by_cases hg : grade i ≤ N
        · simp [contractionScale, hg]
        · simp [contractionScale, hg, Nat.sub_eq_zero_of_le (Nat.le_of_not_ge hg)]]
    calc
      (∏ i : ι, η^(N-grade i)) = η^(∑ i : ι, (N-grade i)) :=
        Finset.prod_pow_eq_pow_sum Finset.univ (fun i => N-grade i) η
      _ = Real.rpow η ((∑ i : ι, (N-grade i) : ℕ) : ℝ) :=
        (Real.rpow_natCast η _).symm
      _ = Real.exp (Real.log η * (∑ i : ι, ((N-grade i:ℕ):ℝ))) := by
        exact (Real.rpow_def_of_pos hη _).trans (by
          congr 1
          simp only [Nat.cast_sum])
  have hlog : Real.log η ≤ 0 := Real.log_nonpos hη.le hη1
  rw [hprod]
  apply Real.exp_le_exp.mpr
  have hcoef : 0 ≤ -Real.log η := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hcost hcoef]

end BrownianSharp.AlignmentGaussianGradedDilationAllGrades
