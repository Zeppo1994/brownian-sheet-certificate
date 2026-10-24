import BrownianSharp.AlignmentFractionalHaarProjection
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Actual nested piecewise polynomial source spaces on the unit interval.
The basis generators are monomials restricted to dyadic source cells. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalDyadicProjection
open BrownianSharp.AlignmentFractionalHaarProjection
open BrownianSharp.AlignmentGaussianFractionalHaar

abbrev SourceL2 := BrownianSharp.AlignmentFractionalL2.UnitL2

def cellMonomialFunction (n : ℕ) (j : Fin (2^n)) (ell : ℕ) : ℝ → ℝ :=
  (sourceDyadicCell n j).indicator (fun x => x^ell)

theorem cellMonomial_memLp (n : ℕ) (j : Fin (2^n)) (ell : ℕ) :
    MemLp (cellMonomialFunction n j ell) 2
      (volume.restrict (Set.Icc (0:ℝ) 1)) := by
  apply MemLp.of_bound
    (((continuous_id.pow ell).aestronglyMeasurable).indicator measurableSet_Ico) 1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  change ‖(sourceDyadicCell n j).indicator (fun x : ℝ => x^ell) x‖ ≤ 1
  by_cases h : x ∈ sourceDyadicCell n j
  · simp only [cellMonomialFunction, Set.indicator_of_mem h, Real.norm_eq_abs]
    rw [abs_of_nonneg (pow_nonneg hx.1 ell)]
    exact pow_le_one₀ hx.1 hx.2
  · simp [cellMonomialFunction, h]

def cellMonomial (n : ℕ) (j : Fin (2^n)) (ell : ℕ) : SourceL2 :=
  (cellMonomial_memLp n j ell).toLp (cellMonomialFunction n j ell)

theorem cellMonomial_coeFn (n : ℕ) (j : Fin (2^n)) (ell : ℕ) :
    (cellMonomial n j ell : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
      cellMonomialFunction n j ell :=
  MemLp.coeFn_toLp (cellMonomial_memLp n j ell)

def piecewisePolynomials (q n : ℕ) : Submodule ℝ SourceL2 :=
  Submodule.span ℝ (Set.range (fun a : Fin (2^n) × Fin q => cellMonomial n a.1 a.2.val))

instance piecewisePolynomials_finiteDimensional (q n : ℕ) :
    FiniteDimensional ℝ (piecewisePolynomials q n) := by
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem piecewisePolynomials_finrank_le (q n : ℕ) :
    Module.finrank ℝ (piecewisePolynomials q n) ≤ q * 2^n := by
  classical
  unfold piecewisePolynomials
  calc
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun a : Fin (2^n) × Fin q => cellMonomial n a.1 a.2.val))) ≤
      (Set.range (fun a : Fin (2^n) × Fin q => cellMonomial n a.1 a.2.val)).toFinset.card :=
        finrank_span_le_card _
    _ ≤ Fintype.card (Fin (2^n) × Fin q) := by
      simpa only [Set.toFinset_card] using
        Fintype.card_range_le (fun a : Fin (2^n) × Fin q => cellMonomial n a.1 a.2.val)
    _ = q * 2^n := by simp [Nat.mul_comm]

theorem cellMonomial_parent_eq_children (n : ℕ) (j : Fin (2^n)) (ell : ℕ) :
    cellMonomial n j ell =
      cellMonomial (n+1) (sourceDyadicLeftChild j) ell +
      cellMonomial (n+1) (sourceDyadicRightChild j) ell := by
  apply Lp.ext
  have hp := cellMonomial_coeFn n j ell
  have hl := cellMonomial_coeFn (n+1) (sourceDyadicLeftChild j) ell
  have hr := cellMonomial_coeFn (n+1) (sourceDyadicRightChild j) ell
  have hadd := Lp.coeFn_add
    (cellMonomial (n+1) (sourceDyadicLeftChild j) ell)
    (cellMonomial (n+1) (sourceDyadicRightChild j) ell)
  filter_upwards [hp, hl, hr, hadd] with x hp hl hr hadd
  rw [hp, hadd, Pi.add_apply, hl, hr]
  unfold cellMonomialFunction
  rw [sourceDyadicCell_parent_eq_children n j,
    Set.indicator_union_of_disjoint
      (sourceDyadicCells_disjoint
        (AlignmentGaussianFractionalHaar.sourceDyadic_leftChild_ne_rightChild j))]

theorem piecewisePolynomials_le_succ (q n : ℕ) :
    piecewisePolynomials q n ≤ piecewisePolynomials q (n+1) := by
  apply Submodule.span_le.2
  rintro f ⟨⟨j,ell⟩,rfl⟩
  change cellMonomial n j ell.val ∈ piecewisePolynomials q (n+1)
  rw [cellMonomial_parent_eq_children]
  exact add_mem (Submodule.subset_span ⟨(sourceDyadicLeftChild j,ell),rfl⟩)
    (Submodule.subset_span ⟨(sourceDyadicRightChild j,ell),rfl⟩)

theorem piecewisePolynomials_mono (q : ℕ) : Monotone (piecewisePolynomials q) :=
  monotone_nat_of_le_succ (piecewisePolynomials_le_succ q)

def polynomialProjection (q n : ℕ) : SourceL2 →L[ℝ] SourceL2 :=
  (piecewisePolynomials q n).starProjection

def cellPolynomialApproximation (q n : ℕ)
    (c : Fin (2^n) → Fin q → ℝ) : SourceL2 :=
  ∑ j : Fin (2^n), ∑ ell : Fin q, c j ell • cellMonomial n j ell.val

theorem cellPolynomialApproximation_mem (q n : ℕ)
    (c : Fin (2^n) → Fin q → ℝ) :
    cellPolynomialApproximation q n c ∈ piecewisePolynomials q n := by
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.sum_mem
  intro ell hell
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(j,ell),rfl⟩

end BrownianSharp.AlignmentFractionalPolynomialSpaces
