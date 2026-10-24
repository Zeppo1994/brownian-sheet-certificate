import BrownianSharp.AlignmentGaussianGradedBudgets
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentGaussianGradedDilationCost

open BrownianSharp.AlignmentGaussianGradedBudgets
open BrownianSharp.AlignmentGeometricRanks

/-- Group a finite weighted sum by a natural-valued grade. -/
private theorem finite_grade_sum_eq_fiber_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (grade : ι → ℕ) (N : ℕ) (hN : ∀ i, grade i ≤ N) :
    (∑ i : ι, ((N - grade i : ℕ) : ℝ)) =
      ∑ g : Fin (N + 1),
        ((N - g.val : ℕ) : ℝ) * (Fintype.card {i : ι // grade i = g.val} : ℝ) := by
  classical
  let gradeFin (i : ι) : Fin (N + 1) := ⟨grade i, Nat.lt_succ_of_le (hN i)⟩
  have hsum := (Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset ι)) (t := (Finset.univ : Finset (Fin (N+1))))
    (g := gradeFin) (f := fun i => ((N - grade i : ℕ) : ℝ))
    (fun _ _ => Finset.mem_univ _)).symm
  calc
    (∑ i : ι, ((N - grade i : ℕ) : ℝ)) =
        ∑ g : Fin (N + 1),
          ∑ i ∈ (Finset.univ : Finset ι) with gradeFin i = g,
            ((N - grade i : ℕ) : ℝ) := hsum
    _ = ∑ g : Fin (N + 1),
        ((N - g.val : ℕ) : ℝ) * (Fintype.card {i : ι // grade i = g.val} : ℝ) := by
      apply Finset.sum_congr rfl
      intro g hg
      have hfiber :
      (∑ i ∈ (Finset.univ : Finset ι) with gradeFin i = g,
        ((N - grade i : ℕ) : ℝ)) =
      ((N - g.val : ℕ) : ℝ) * (Fintype.card {i : ι // grade i = g.val} : ℝ) := by
        have heq :
            (Finset.univ.filter (fun i : ι => gradeFin i = g)) =
              Finset.univ.filter (fun i : ι => grade i = g.val) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, gradeFin]
          rw [Fin.ext_iff]
        rw [show (∑ i ∈ (Finset.univ : Finset ι) with gradeFin i = g,
          ((N - grade i : ℕ) : ℝ)) =
            ∑ i ∈ (Finset.univ : Finset ι).filter (fun i => gradeFin i = g),
              ((N - grade i : ℕ) : ℝ) by rfl, heq]
        have hconst : ∀ i ∈ Finset.univ.filter (fun i : ι => grade i = g.val),
            ((N - grade i : ℕ) : ℝ) = ((N - g.val : ℕ) : ℝ) := by
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        rw [show (∑ i ∈ Finset.univ.filter (fun i : ι => grade i = g.val),
          ((N - grade i : ℕ) : ℝ)) =
            ∑ i ∈ Finset.univ.filter (fun i : ι => grade i = g.val),
              ((N - g.val : ℕ) : ℝ) by
          apply Finset.sum_congr rfl
          intro i hi
          exact hconst i hi]
        simp only [Finset.sum_const, nsmul_eq_mul, Fintype.card_subtype]
        ring
      exact hfiber

/-- The total dilation exponent over a finite graded index is controlled by
the universal low-grade geometric budget. The fiber bound may include any
fixed polynomial factor `(g+1)^k`. -/
theorem finite_graded_index_dilation_cost_sum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (grade : ι → ℕ) (C : ℝ) (k N : ℕ)
    (hC : 0 ≤ C) (hN : ∀ i, grade i ≤ N)
    (hfiber : ∀ g : Fin (N + 1),
      (Fintype.card {i : ι // grade i = g.val} : ℝ) ≤
        C * (2 : ℝ)^g.val * (((g.val + 1 : ℕ) : ℝ)^k)) :
    (∑ i : ι, ((N - grade i : ℕ) : ℝ)) ≤
      C * (2 : ℝ)^N * (((N + 1 : ℕ) : ℝ)^k) * polynomialBudget (1/2) 1 := by
  classical
  rw [finite_grade_sum_eq_fiber_sum grade N hN]
  calc
    _ ≤ ∑ g : Fin (N + 1), ((N - g.val : ℕ) : ℝ) *
        (C * (2 : ℝ)^g.val * (((g.val + 1 : ℕ) : ℝ)^k)) := by
      apply Finset.sum_le_sum
      intro g hg
      apply mul_le_mul_of_nonneg_left (hfiber g)
      positivity
    _ = C * (∑ g : Fin (N + 1), ((N - g.val : ℕ) : ℝ) *
        ((2 : ℝ)^g.val * (((g.val + 1 : ℕ) : ℝ)^k))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      ring
    _ ≤ C * ((2 : ℝ)^N * (((N + 1 : ℕ) : ℝ)^k) * polynomialBudget (1/2) 1) := by
      apply mul_le_mul_of_nonneg_left _ hC
      simpa using low_grade_dilation_cost_sum_le k N
    _ = _ := by ring

/-- Uniform determinant-cost lower bound for diagonal contractions by grade.
Each coordinate is scaled by `η^(N-grade)`, where `0<η≤1`. -/
theorem finite_graded_diagonal_dilation_product_ge_exp
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (grade : ι → ℕ) (C η : ℝ) (k N : ℕ)
    (hC : 0 ≤ C) (hη : 0 < η) (hη1 : η ≤ 1)
    (hN : ∀ i, grade i ≤ N)
    (hfiber : ∀ g : Fin (N + 1),
      (Fintype.card {i : ι // grade i = g.val} : ℝ) ≤
        C * (2 : ℝ)^g.val * (((g.val + 1 : ℕ) : ℝ)^k)) :
    ∏ i : ι, η^(N-grade i) ≥
      Real.exp (-(-Real.log η) *
        (C * (2 : ℝ)^N * (((N + 1 : ℕ) : ℝ)^k) * polynomialBudget (1/2) 1)) := by
  have hcost := finite_graded_index_dilation_cost_sum_le grade C k N hC hN hfiber
  have hproduct :
      (∏ i : ι, η^(N-grade i)) =
        Real.exp (Real.log η * (∑ i : ι, ((N-grade i : ℕ) : ℝ))) := by
    calc
      (∏ i : ι, η^(N-grade i)) = η^(∑ i : ι, (N-grade i)) :=
        Finset.prod_pow_eq_pow_sum Finset.univ (fun i => N-grade i) η
      _ = Real.rpow η ((∑ i : ι, (N-grade i) : ℕ) : ℝ) :=
        (Real.rpow_natCast η _).symm
      _ = Real.exp (Real.log η * (∑ i : ι, ((N-grade i : ℕ) : ℝ))) := by
        exact (Real.rpow_def_of_pos hη _).trans (by
          congr 1
          simp only [Nat.cast_sum])
  have hlog : Real.log η ≤ 0 := Real.log_nonpos hη.le hη1
  have hexponent :
      -(-Real.log η) *
          (C * (2 : ℝ)^N * (((N + 1 : ℕ) : ℝ)^k) * polynomialBudget (1/2) 1) ≤
        Real.log η * (∑ i : ι, ((N-grade i : ℕ) : ℝ)) := by
    have hcoef : 0 ≤ -Real.log η := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hcost hcoef]
  rw [hproduct]
  exact Real.exp_le_exp.mpr hexponent

end BrownianSharp.AlignmentGaussianGradedDilationCost
