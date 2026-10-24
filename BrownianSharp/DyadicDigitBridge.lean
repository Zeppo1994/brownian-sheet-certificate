import BrownianSharp.SignCube
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

/-- The half of its level-`l` cell containing `k`, encoded as a Boolean. -/
def dyadicChildBit (N : ℕ) (l : Fin N) (k : ℕ) : Bool :=
  decide (k / 2 ^ (N - (l.val + 1)) % 2 = 1)

/-- The sign of the next binary digit, with left half negative and right half positive. -/
def dyadicDigit (N : ℕ) (l : Fin N) (k : ℕ) : ℝ :=
  if dyadicChildBit N l k then 1 else -1

/-- Membership in the level-`l` half-open dyadic cell indexed by `c`. -/
def dyadicCellIndicator (N : ℕ) (l : Fin N) (c k : ℕ) : ℝ :=
  if dyadicCellIndex N l k = c then 1 else 0

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

/-- The parent interval index is the quotient of the child interval index by two. -/
theorem dyadicCellIndex_eq_childIndex_div_two (N : ℕ) (l : Fin N) (k : ℕ) :
    dyadicCellIndex N l k = (k / 2 ^ (N - (l.val + 1))) / 2 := by
  unfold dyadicCellIndex
  have he : N - l.val = (N - (l.val + 1)) + 1 := by omega
  rw [he, Nat.pow_succ, ← Nat.div_div_eq_div_mul]

/-- The geometric left half of parent cell `c`, given by its half-open endpoints. -/
def dyadicLeftHalfContains (N : ℕ) (l : Fin N) (c k : ℕ) : Prop :=
  (2 * c) * 2 ^ (N - (l.val + 1)) ≤ k ∧
    k < (2 * c + 1) * 2 ^ (N - (l.val + 1))

/-- The geometric right half of parent cell `c`, given by its half-open endpoints. -/
def dyadicRightHalfContains (N : ℕ) (l : Fin N) (c k : ℕ) : Prop :=
  (2 * c + 1) * 2 ^ (N - (l.val + 1)) ≤ k ∧
    k < (2 * c + 2) * 2 ^ (N - (l.val + 1))

/-- The left-half endpoint interval is exactly the corresponding finer quotient cell. -/
theorem dyadicLeftHalfContains_iff (N : ℕ) (l : Fin N) (c k : ℕ) :
    dyadicLeftHalfContains N l c k ↔
      k / 2 ^ (N - (l.val + 1)) = 2 * c := by
  unfold dyadicLeftHalfContains
  exact (natDiv_eq_iff_halfOpen _ _ _ (Nat.pow_pos (by decide))).symm

/-- The right-half endpoint interval is exactly the corresponding finer quotient cell. -/
theorem dyadicRightHalfContains_iff (N : ℕ) (l : Fin N) (c k : ℕ) :
    dyadicRightHalfContains N l c k ↔
      k / 2 ^ (N - (l.val + 1)) = 2 * c + 1 := by
  unfold dyadicRightHalfContains
  exact (natDiv_eq_iff_halfOpen _ _ _ (Nat.pow_pos (by decide))).symm

/-- Indicators of the two geometric half-open child intervals. -/
noncomputable def dyadicLeftHalfIndicator (N : ℕ) (l : Fin N) (c k : ℕ) : ℝ := by
  classical
  exact if dyadicLeftHalfContains N l c k then 1 else 0

noncomputable def dyadicRightHalfIndicator (N : ℕ) (l : Fin N) (c k : ℕ) : ℝ := by
  classical
  exact if dyadicRightHalfContains N l c k then 1 else 0

/-- Haar defined geometrically as the right-child indicator minus the left-child indicator. -/
noncomputable def dyadicHaarFromHalfIntervals (N : ℕ) (l : Fin N) (c k : ℕ) : ℝ :=
  dyadicRightHalfIndicator N l c k - dyadicLeftHalfIndicator N l c k

/-- Distinct half-open level-`l` cells cannot contain the same grid point. -/
theorem dyadicCellContains_unique (N : ℕ) (l : Fin N) {c c' k : ℕ}
    (hc : dyadicCellContains N l c k) (hc' : dyadicCellContains N l c' k) : c = c' := by
  have h1 : dyadicCellIndex N l k = c :=
    (dyadicCellIndex_eq_iff_contains N l c k).mpr hc
  have h2 : dyadicCellIndex N l k = c' :=
    (dyadicCellIndex_eq_iff_contains N l c' k).mpr hc'
  exact h1.symm.trans h2

/-- The bounded labels of the level-`l` cells partition the depth-`N` grid. -/
theorem dyadicCellIndicator_sum_eq_one (N : ℕ) (l : Fin N) {k : ℕ}
    (hk : k < 2 ^ N) :
    (∑ c : Fin (2 ^ l.val), dyadicCellIndicator N l c.val k) = 1 := by
  classical
  let c₀ : Fin (2 ^ l.val) := ⟨dyadicCellIndex N l k, dyadicCellIndex_lt N l hk⟩
  have hterms : ∀ c : Fin (2 ^ l.val),
      dyadicCellIndicator N l c.val k = if c = c₀ then 1 else 0 := by
    intro c
    unfold dyadicCellIndicator
    by_cases h : dyadicCellIndex N l k = c.val
    · have hc : c = c₀ := Fin.ext h.symm
      simp [h, hc]
    · have hc : c ≠ c₀ := by
        intro heq
        apply h
        exact congrArg Fin.val heq |>.symm
      simp [h, hc]
  rw [Finset.sum_congr rfl (fun c _ => hterms c)]
  simp [c₀]

/-- The depth-`l` Haar function supported on cell `c`, on the depth-`N` grid. -/
def dyadicHaarValue (N : ℕ) (l : Fin N) (c k : ℕ) : ℝ :=
  if dyadicCellIndex N l k = c then dyadicDigit N l k else 0

/-- The quotient-defined Haar value is exactly right-half minus left-half. -/
theorem dyadicHaarValue_eq_halfIntervals (N : ℕ) (l : Fin N) (c k : ℕ) :
    dyadicHaarValue N l c k = dyadicHaarFromHalfIntervals N l c k := by
  classical
  let q := k / 2 ^ (N - (l.val + 1))
  have hq : q = k / 2 ^ (N - (l.val + 1)) := rfl
  have hdecomp : q = 2 * (q / 2) + q % 2 := by
    dsimp [q]
    exact (Nat.div_add_mod _ _).symm
  have hrem : q % 2 < 2 := by
    rw [hq]
    exact Nat.mod_lt _ (by decide)
  have hparent : dyadicCellIndex N l k = q / 2 := by
    rw [dyadicCellIndex_eq_childIndex_div_two, hq]
  by_cases hc : q / 2 = c
  · by_cases hr : q % 2 = 1
    · have hright : q = 2 * c + 1 := by omega
      have hrightMem : dyadicRightHalfContains N l c k := by
        rw [dyadicRightHalfContains_iff, ← hq]
        exact hright
      have hleftMem : ¬ dyadicLeftHalfContains N l c k := by
        intro hm
        have heq := (dyadicLeftHalfContains_iff N l c k).mp hm
        rw [← hq] at heq
        omega
      have hri : dyadicRightHalfIndicator N l c k = 1 := by
        simp [dyadicRightHalfIndicator, hrightMem]
      have hli : dyadicLeftHalfIndicator N l c k = 0 := by
        simp [dyadicLeftHalfIndicator, hleftMem]
      rw [dyadicHaarFromHalfIntervals, hri, hli]
      have hc' : k / 2 ^ (N - (l.val + 1)) / 2 = c := by simpa [q] using hc
      simp [dyadicHaarValue, hparent, hc', dyadicDigit, dyadicChildBit, q, hr]
    · have hr0 : q % 2 = 0 := by omega
      have hleft : q = 2 * c := by omega
      have hleftMem : dyadicLeftHalfContains N l c k := by
        rw [dyadicLeftHalfContains_iff, ← hq]
        exact hleft
      have hrightMem : ¬ dyadicRightHalfContains N l c k := by
        intro hm
        have heq := (dyadicRightHalfContains_iff N l c k).mp hm
        rw [← hq] at heq
        omega
      have hri : dyadicRightHalfIndicator N l c k = 0 := by
        simp [dyadicRightHalfIndicator, hrightMem]
      have hli : dyadicLeftHalfIndicator N l c k = 1 := by
        simp [dyadicLeftHalfIndicator, hleftMem]
      rw [dyadicHaarFromHalfIntervals, hri, hli]
      have hc' : k / 2 ^ (N - (l.val + 1)) / 2 = c := by simpa [q] using hc
      simp [dyadicHaarValue, hparent, hc', dyadicDigit, dyadicChildBit, q, hr0]
  · have hleftMem : ¬ dyadicLeftHalfContains N l c k := by
      intro hm
      have heq := (dyadicLeftHalfContains_iff N l c k).mp hm
      rw [← hq] at heq
      omega
    have hrightMem : ¬ dyadicRightHalfContains N l c k := by
      intro hm
      have heq := (dyadicRightHalfContains_iff N l c k).mp hm
      rw [← hq] at heq
      omega
    have hri : dyadicRightHalfIndicator N l c k = 0 := by
      simp [dyadicRightHalfIndicator, hrightMem]
    have hli : dyadicLeftHalfIndicator N l c k = 0 := by
      simp [dyadicLeftHalfIndicator, hleftMem]
    rw [dyadicHaarFromHalfIntervals, hri, hli]
    simp [dyadicHaarValue, hparent, hc]

/-- The geometric Haar sign identity on the finite dyadic grid. -/
theorem haarValue_eq_cellIndicator_mul_digit (N : ℕ) (l : Fin N) (c k : ℕ) :
    dyadicHaarValue N l c k =
      dyadicCellIndicator N l c k * dyadicDigit N l k := by
  simp [dyadicHaarValue, dyadicCellIndicator]

/-- A coefficient indexed by the containing level-`l` cell is constant on that cell. -/
theorem cellCoefficient_eq_of_same_cell (N : ℕ) (l : Fin N) (a : ℕ → ℝ)
    {k k' : ℕ} (h : dyadicCellIndex N l k = dyadicCellIndex N l k') :
    a (dyadicCellIndex N l k) = a (dyadicCellIndex N l k') := by
  rw [h]

/-- Multiplying by a cell-adapted coefficient preserves the Haar/digit factorization. -/
theorem adaptedHaarValue_eq_cellCoefficient_mul_digit
    (N : ℕ) (l : Fin N) (c k : ℕ) (a : ℕ → ℝ) :
    a (dyadicCellIndex N l k) * dyadicHaarValue N l c k =
      (a (dyadicCellIndex N l k) * dyadicCellIndicator N l c k) *
        dyadicDigit N l k := by
  rw [haarValue_eq_cellIndicator_mul_digit]
  simp only [mul_assoc]

/-- The supporting cell indicator is either zero or one, including its boundary convention. -/
theorem dyadicCellIndicator_nonneg (N : ℕ) (l : Fin N) (c k : ℕ) :
    0 ≤ dyadicCellIndicator N l c k := by
  unfold dyadicCellIndicator
  split <;> norm_num

/-- A grid point lies on exactly one of the two signed halves of its cell. -/
theorem dyadicDigit_abs (N : ℕ) (l : Fin N) (k : ℕ) : |dyadicDigit N l k| = 1 := by
  unfold dyadicDigit
  split <;> norm_num

/-- The normalized Haar function has unit magnitude on its cell and vanishes off it. -/
theorem dyadicHaar_abs_eq_indicator (N : ℕ) (l : Fin N) (c k : ℕ) :
    |dyadicHaarValue N l c k| = dyadicCellIndicator N l c k := by
  rw [haarValue_eq_cellIndicator_mul_digit, abs_mul]
  rw [abs_of_nonneg (dyadicCellIndicator_nonneg N l c k), dyadicDigit_abs]
  simp

end HaarQuarter
