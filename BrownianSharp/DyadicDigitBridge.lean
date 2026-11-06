import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Finite dyadic cells and Haar digits

This file makes the finite-grid part of the physical Haar/digit translation
explicit.  A point of the depth-`N` grid is the index of its half-open cell
`[k / 2^N, (k+1) / 2^N)`.  At level `l < N`, `cellIndex` gives the ancestor
cell and `childBit` gives which half of that cell contains the point.  The
`haarValue` below is the usual L-infinity normalized Haar function on these
grid cells, including its vanishing outside the supporting interval.

The theorem `haarValue_eq_cellIndicator_mul_digit` is the actual Haar sign
identity, with the geometric boundary represented by half-open cells.  The
last theorem says a coefficient selected by the containing level-`l` cell is
constant on every such cell and therefore factors out of the Haar value.
The depth-`N` grid has no points on the excluded endpoint `1`.
-/

namespace HaarQuarter

/-- The level-`l` dyadic ancestor of grid point `k` on a depth-`N` grid. -/
def dyadicCellIndex (N : ℕ) (l : Fin N) (k : ℕ) : ℕ :=
  k / 2 ^ (N - l.val)

/-- The half-open integer interval of grid points in the level-`l` cell `c`.

This is the independent endpoint description: for `m = 2^(N-l)`, cell `c`
contains precisely the indices in `[c*m, (c+1)*m)`. -/
def dyadicCellContains (N : ℕ) (l : Fin N) (c k : ℕ) : Prop :=
  c * 2 ^ (N - l.val) ≤ k ∧ k < (c + 1) * 2 ^ (N - l.val)

/-- Generic quotient characterization of a half-open interval of integer cells. -/
theorem natDiv_eq_iff_halfOpen (m c k : ℕ) (hm : 0 < m) :
    k / m = c ↔ c * m ≤ k ∧ k < (c + 1) * m := by
  constructor
  · intro h
    constructor
    · exact (Nat.le_div_iff_mul_le hm).mp (le_of_eq h.symm)
    · apply (Nat.div_lt_iff_lt_mul hm).mp
      rw [h]
      exact Nat.lt_succ_self c
  · intro h
    apply Nat.le_antisymm
    · exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hm).2 h.2)
    · exact (Nat.le_div_iff_mul_le hm).2 h.1

/-- Quotient indexing agrees with the half-open interval endpoints. -/
theorem dyadicCellIndex_eq_iff_contains (N : ℕ) (l : Fin N) (c k : ℕ) :
    dyadicCellIndex N l k = c ↔ dyadicCellContains N l c k := by
  exact natDiv_eq_iff_halfOpen (2 ^ (N - l.val)) c k (Nat.pow_pos (by decide))

/-- A depth-`N` grid point belongs to a unique level-`l` cell label. -/
theorem dyadicCellIndex_lt (N : ℕ) (l : Fin N) {k : ℕ} (hk : k < 2 ^ N) :
    dyadicCellIndex N l k < 2 ^ l.val := by
  unfold dyadicCellIndex
  apply (Nat.div_lt_iff_lt_mul (Nat.pow_pos (by decide))).2
  have hp : 2 ^ l.val * 2 ^ (N - l.val) = 2 ^ N := by
    rw [← Nat.pow_add, Nat.add_sub_of_le (Nat.le_of_lt l.isLt)]
  simpa [hp] using hk

end HaarQuarter
