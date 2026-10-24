import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
Finite index sets for the level-`n` tensor Haar layer and the corresponding
midpoint grid.  Shapes are weak compositions of `n` into `d` coordinates;
after a shape is chosen, its `i`th Haar interval is selected at depth `r i`.
This file is intentionally independent of the projection construction.
-/

namespace BrownianSharp

/-- Grade-`n` shapes on `d` coordinates, represented by the finite-support
version of a tuple of natural numbers. -/
abbrev Shape (d n : ℕ) :=
  {r : Fin d →₀ ℕ // r ∈ (Finset.univ : Finset (Fin d)).finsuppAntidiag n}

/-- A tensor Haar index consists of its coordinate depth profile and one
dyadic interval address at each coordinate depth. -/
abbrev LayerIndex (d n : ℕ) :=
  Σ r : Shape d n, (∀ i : Fin d, Fin (2 ^ r.1 i))

/-- The depth profile carried by a native layer index. -/
def layerIndexDepth {d n : ℕ} (a : LayerIndex d n) : Fin d → ℕ := a.1.1

/-- The tuple of integer dyadic addresses carried by a native layer index. -/
def layerIndexCell {d n : ℕ} (a : LayerIndex d n) : Fin d → ℕ :=
  fun i => (a.2 i).val

/-- Every coordinate address belongs to the interval range at its depth. -/
theorem layerIndexCell_lt {d n : ℕ} (a : LayerIndex d n) (i : Fin d) :
    layerIndexCell a i < 2 ^ layerIndexDepth a i :=
  (a.2 i).isLt

/-- The depth profile of an index has total grade `n`. -/
theorem layerIndexDepth_grade {d n : ℕ} (a : LayerIndex d n) :
    (a.1.1.sum fun _ k => k) = n :=
  (Finset.mem_finsuppAntidiag'.mp a.1.2).1

/-- The cardinality of the set of grade-`n` shapes is the weak-composition
number `binom(n+d-1,d-1)` (for positive dimension). -/
theorem shape_card (d n : ℕ) (hd : 0 < d) :
    Fintype.card (Shape d n) = Nat.choose (n + d - 1) (d - 1) := by
  classical
  let S : Finset (Fin d →₀ ℕ) :=
    (Finset.univ : Finset (Fin d)).finsuppAntidiag n
  have hcard : S.card = Nat.choose (d + n - 1) n := by
    rw [Finset.card_finsuppAntidiag_nat_eq_choose]
    simp [Fintype.card_fin]
  have htype : Fintype.card (Shape d n) = S.card := by
    exact Fintype.card_coe S
  have htop : d + n - 1 = n + d - 1 := by omega
  have hchoose : Nat.choose (n + d - 1) n =
      Nat.choose (n + d - 1) (d - 1) := by
    have hdle : d - 1 ≤ n + d - 1 := by omega
    calc
      Nat.choose (n + d - 1) n =
          Nat.choose (n + d - 1) (n + d - 1 - (d - 1)) := by
        congr 1
        omega
      _ = Nat.choose (n + d - 1) (d - 1) := Nat.choose_symm hdle
  rw [htype, hcard, htop, hchoose]

/-- The total number of tensor Haar indices in the grade-`n` layer. -/
theorem layerIndex_card (d n : ℕ) (hd : 0 < d) :
    Fintype.card (LayerIndex d n) =
      2 ^ n * Nat.choose (n + d - 1) (d - 1) := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_pi]
  have hfiber (r : Shape d n) :
      (∏ i : Fin d, Fintype.card (Fin (2 ^ r.1 i))) = 2 ^ n := by
    have hshape : (r.1.sum fun _ k => k) = n :=
      (Finset.mem_finsuppAntidiag'.mp r.2).1
    simp only [Fintype.card_fin]
    calc
      (∏ i : Fin d, 2 ^ r.1 i) = 2 ^ (∑ i : Fin d, r.1 i) := by
        rw [Finset.prod_pow_eq_pow_sum]
      _ = 2 ^ n := by
        have hshape' : (∑ i : Fin d, r.1 i) = n := by
          simpa [Finsupp.sum_fintype] using hshape
        rw [hshape']
  have hsum :
      (∑ r : Shape d n,
        ∏ i : Fin d, Fintype.card (Fin (2 ^ r.1 i))) =
      (Fintype.card (Shape d n) : ℕ) * 2 ^ n := by
    simp_rw [hfiber]
    simp
  rw [hsum, shape_card d n hd]
  ac_rfl

/-- All depth-`n+1` one-dimensional dyadic cells, indexed by their address. -/
abbrev MidpointGridCoordinate (n : ℕ) := Fin (2 ^ (n + 1))

/-- The full product midpoint grid for the dyadic partition into
`2^(n+1)` equal cells in every coordinate. -/
abbrev MidpointGridIndex (d n : ℕ) := Fin d → MidpointGridCoordinate n

/-- A cube anchor is a point in the closed unit cube. -/
def CubeAnchor (d : ℕ) := {x : Fin d → ℝ // ∀ i, 0 ≤ x i ∧ x i ≤ 1}

/-- The center of the dyadic interval named by an address at depth `n+1`. -/
noncomputable def midpointGridCoordinate (n : ℕ)
    (j : MidpointGridCoordinate n) : ℝ :=
  ((j.val : ℝ) + (1 / 2 : ℝ)) / (2 : ℝ) ^ (n + 1)

/-- A midpoint grid coordinate lies strictly inside the unit interval. -/
theorem midpointGridCoordinate_mem_Ioo (n : ℕ)
    (j : MidpointGridCoordinate n) :
    0 < midpointGridCoordinate n j ∧ midpointGridCoordinate n j < 1 := by
  have hden : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  have hjlt : j.val < 2 ^ (n + 1) := j.isLt
  have hnum0 : (0 : ℝ) < (j.val : ℝ) + (1 / 2 : ℝ) := by positivity
  have hnum1 : (j.val : ℝ) + (1 / 2 : ℝ) < (2 : ℝ) ^ (n + 1) := by
    have : ((j.val + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
      exact_mod_cast Nat.succ_le_of_lt hjlt
    norm_num at *
    linarith
  constructor
  · exact div_pos hnum0 hden
  · exact (div_lt_one hden).2 hnum1

/-- The coordinatewise midpoint anchor associated with a product grid index. -/
noncomputable def midpointGridAnchor {d n : ℕ}
    (j : MidpointGridIndex d n) : CubeAnchor d := by
  refine ⟨fun i => midpointGridCoordinate n (j i), ?_⟩
  intro i
  have hden : (0 : ℝ) < (2 : ℝ) ^ (n + 1) := by positivity
  have hjlt : (j i).val < 2 ^ (n + 1) := (j i).isLt
  have hnum0 : (0 : ℝ) ≤ (j i).val + (1 / 2 : ℝ) := by positivity
  have hnum1 : (j i).val + (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by
    have : ((j i).val : ℝ) + 1 ≤ (2 : ℝ) ^ (n + 1) := by
      exact_mod_cast Nat.succ_le_of_lt hjlt
    linarith
  constructor
  · exact div_nonneg hnum0 (le_of_lt hden)
  · exact (div_le_one hden).2 hnum1

@[simp] theorem midpointGridAnchor_apply {d n : ℕ}
    (j : MidpointGridIndex d n) (i : Fin d) :
    (midpointGridAnchor j).1 i = midpointGridCoordinate n (j i) := rfl

end BrownianSharp
