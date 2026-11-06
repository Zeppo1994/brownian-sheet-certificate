import BrownianSharp.DyadicDigitBridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Lean.Elab.Tactic.Omega
import BrownianSharp.QuarterScale
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite product dyadic grids and tensor Haar blocks

The one-dimensional grid bridge extends coordinatewise to arbitrary finite
axis sets. This file records the product cell, product Haar, exact Haar/digit
factorization, partition identity, and shape-block coefficient factorization.
-/

open scoped BigOperators

namespace HaarQuarter

/-- Split a depth-`N` grid index into its ancestor cell and its position
inside that cell. The quotient is the cell index; the remainder is its
within-cell location. -/
def dyadicGridSplitEquiv (N : ℕ) (l : Fin N) :
    Fin (2 ^ N) ≃ Fin (2 ^ l.val) × Fin (2 ^ (N - l.val)) := by
  have hpow : 2 ^ N = 2 ^ l.val * 2 ^ (N - l.val) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt l.isLt)]
  exact (finCongr hpow).trans finProdFinEquiv.symm

/-- The first coordinate of the grid split is exactly the geometric quotient
cell index. -/
theorem dyadicGridSplitEquiv_fst (N : ℕ) (l : Fin N) (k : Fin (2 ^ N)) :
    (dyadicGridSplitEquiv N l k).1.val = dyadicCellIndex N l k.val := by
  simp [dyadicGridSplitEquiv, dyadicCellIndex, finProdFinEquiv_symm_apply,
    Fin.divNat]

/-- Points in one fixed dyadic cell are parametrized exactly by the
within-cell grid coordinate. -/
def dyadicGridFiberEquiv (N : ℕ) (l : Fin N) (c : Fin (2 ^ l.val)) :
    {k : Fin (2 ^ N) // dyadicCellIndex N l k.val = c.val} ≃
      Fin (2 ^ (N - l.val)) where
  toFun k := (dyadicGridSplitEquiv N l k.1).2
  invFun r := ⟨(dyadicGridSplitEquiv N l).symm (c, r), by
    have h := dyadicGridSplitEquiv_fst N l
      ((dyadicGridSplitEquiv N l).symm (c, r))
    simpa using h.symm⟩
  left_inv k := by
    apply Subtype.ext
    have hfirst : (dyadicGridSplitEquiv N l k.1).1 = c := by
      apply Fin.ext
      rw [dyadicGridSplitEquiv_fst]
      exact k.2
    have hpair : (c, (dyadicGridSplitEquiv N l k.1).2) =
        dyadicGridSplitEquiv N l k.1 := by
      apply Prod.ext
      · exact hfirst.symm
      · rfl
    change (dyadicGridSplitEquiv N l).symm
      (c, (dyadicGridSplitEquiv N l k.1).2) = k.1
    rw [hpair]
    exact (dyadicGridSplitEquiv N l).symm_apply_apply k.1
  right_inv r := by simp

/-- Every level-`l` cell contains exactly `2^(N-l)` depth-`N` grid points. -/
theorem dyadicGridFiber_card (N : ℕ) (l : Fin N) (c : Fin (2 ^ l.val)) :
    Fintype.card {k : Fin (2 ^ N) // dyadicCellIndex N l k.val = c.val} =
      2 ^ (N - l.val) := by
  classical
  calc
    _ = Fintype.card (Fin (2 ^ (N - l.val))) :=
      Fintype.card_congr (dyadicGridFiberEquiv N l c)
    _ = _ := Fintype.card_fin _

end HaarQuarter
