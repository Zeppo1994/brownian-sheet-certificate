import BrownianSharp.DyadicDigitBridge
import BrownianSharp.QueryEnergy
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

/-- A point of the depth-`N` product grid, one depth-`N` cell per axis. -/
abbrev ProductGridPoint (ι : Type*) (N : ℕ) := ι → Fin (2 ^ N)

/-- A product shape assigns a dyadic level to each axis. -/
abbrev ProductGridProfile (ι : Type*) (N : ℕ) := ι → Fin N

/-- The product rectangles of shape `profile`. -/
abbrev ProductGridCell {ι : Type*} {N : ℕ} (profile : ProductGridProfile ι N) :=
  ∀ a, Fin (2 ^ (profile a).val)

/-- The within-cell coordinate at each axis of a product rectangle. -/
abbrev ProductGridTail {ι : Type*} {N : ℕ}
    (profile : ProductGridProfile ι N) :=
  ∀ a, Fin (2 ^ (N - (profile a).val))

/-- The unique product cell of the specified shape containing a grid point. -/
def productGridCellIndex {ι : Type*} {N : ℕ}
    (profile : ProductGridProfile ι N) (x : ProductGridPoint ι N) :
    ProductGridCell profile := fun a =>
  ⟨dyadicCellIndex N (profile a) (x a).val,
    dyadicCellIndex_lt N (profile a) (x a).isLt⟩

/-- Exact number of product rectangles of a prescribed dyadic shape. -/
theorem productGridCell_card {ι : Type*} {N : ℕ} [Fintype ι] [DecidableEq ι]
    (profile : ProductGridProfile ι N) :
    Fintype.card (ProductGridCell profile) = ∏ a, 2 ^ (profile a).val := by
  classical
  simpa [ProductGridCell] using
    (Fintype.card_pi (α := fun a : ι => Fin (2 ^ (profile a).val)))

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

/-- The product grid splits coordinatewise into its containing rectangle and
the residual position inside that rectangle. -/
def productGridSplitEquiv {ι : Type*} {N : ℕ}
    (profile : ProductGridProfile ι N) :
    ProductGridPoint ι N ≃ ProductGridCell profile × ProductGridTail profile where
  toFun x :=
    (fun a => (dyadicGridSplitEquiv N (profile a) (x a)).1,
      fun a => (dyadicGridSplitEquiv N (profile a) (x a)).2)
  invFun p := fun a =>
    (dyadicGridSplitEquiv N (profile a)).symm (p.1 a, p.2 a)
  left_inv x := by
    funext a
    exact (dyadicGridSplitEquiv N (profile a)).symm_apply_apply (x a)
  right_inv p := by
    apply Prod.ext
    · funext a
      exact congrArg Prod.fst
        ((dyadicGridSplitEquiv N (profile a)).apply_symm_apply (p.1 a, p.2 a))
    · funext a
      exact congrArg Prod.snd
        ((dyadicGridSplitEquiv N (profile a)).apply_symm_apply (p.1 a, p.2 a))

/-- The product split's first coordinate is precisely `productGridCellIndex`. -/
theorem productGridSplitEquiv_fst {ι : Type*} {N : ℕ}
    (profile : ProductGridProfile ι N) (x : ProductGridPoint ι N) :
    (productGridSplitEquiv profile x).1 = productGridCellIndex profile x := by
  funext a
  apply Fin.ext
  exact dyadicGridSplitEquiv_fst N (profile a) (x a)

/-- The residual coordinates enumerate every grid point in a fixed product
rectangle exactly once. -/
def productGridFiberEquiv {ι : Type*} {N : ℕ} [Fintype ι] [DecidableEq ι]
    (profile : ProductGridProfile ι N) (cell : ProductGridCell profile) :
    {x : ProductGridPoint ι N // productGridCellIndex profile x = cell} ≃
      ProductGridTail profile where
  toFun x := (productGridSplitEquiv profile x.1).2
  invFun tail := ⟨(productGridSplitEquiv profile).symm (cell, tail), by
    have h := productGridSplitEquiv_fst profile
      ((productGridSplitEquiv profile).symm (cell, tail))
    simpa using h.symm⟩
  left_inv x := by
    apply Subtype.ext
    have hfirst : (productGridSplitEquiv profile x.1).1 = cell := by
      simpa [productGridSplitEquiv_fst] using x.2
    have hpair : (cell, (productGridSplitEquiv profile x.1).2) =
        productGridSplitEquiv profile x.1 := by
      apply Prod.ext
      · exact hfirst.symm
      · rfl
    change (productGridSplitEquiv profile).symm
      (cell, (productGridSplitEquiv profile x.1).2) = x.1
    rw [hpair]
    exact (productGridSplitEquiv profile).symm_apply_apply x.1
  right_inv tail := by simp

/-- A product rectangle contains exactly the product of its one-axis numbers
of depth-`N` grid points. -/
theorem productGridFiber_card {ι : Type*} {N : ℕ} [Fintype ι] [DecidableEq ι]
    (profile : ProductGridProfile ι N) (cell : ProductGridCell profile) :
    Fintype.card {x : ProductGridPoint ι N // productGridCellIndex profile x = cell} =
      ∏ a, 2 ^ (N - (profile a).val) := by
  classical
  calc
    _ = Fintype.card (ProductGridTail profile) :=
      Fintype.card_congr (productGridFiberEquiv profile cell)
    _ = ∏ a, 2 ^ (N - (profile a).val) := by
      simpa [ProductGridTail] using
        (Fintype.card_pi (α := fun a : ι => Fin (2 ^ (N - (profile a).val))))

/-- Summing any cell function over the depth-`N` grid repeats each cell's
contribution by the exact number of grid points it contains. -/
theorem productGrid_cellFunction_sum {ι : Type*} {N : ℕ}
    [Fintype ι] [DecidableEq ι] (profile : ProductGridProfile ι N)
    (f : ProductGridCell profile → ℝ) :
    (∑ x : ProductGridPoint ι N, f (productGridCellIndex profile x)) =
      (∏ a, 2 ^ (N - (profile a).val)) *
        ∑ cell : ProductGridCell profile, f cell := by
  classical
  let tailCount : ℝ := ∏ a, 2 ^ (N - (profile a).val)
  calc
    _ = ∑ point : ProductGridCell profile × ProductGridTail profile,
        f point.1 := by
          apply Fintype.sum_equiv (productGridSplitEquiv profile)
          intro x
          rw [productGridSplitEquiv_fst]
    _ = ∑ cell : ProductGridCell profile,
        ∑ tail : ProductGridTail profile, f cell :=
          Fintype.sum_prod_type _
    _ = tailCount * ∑ cell : ProductGridCell profile, f cell := by
          simp [tailCount, Finset.sum_const, nsmul_eq_mul, mul_comm]
          rw [← Finset.sum_mul, mul_comm]

/-- The absolute `p`-moment sum is the previous identity specialized to the
cell coefficient function. -/
theorem productGrid_cellMoment_sum {ι : Type*} {N : ℕ}
    [Fintype ι] [DecidableEq ι] (profile : ProductGridProfile ι N)
    (coefficient : ProductGridCell profile → ℝ) (p : ℕ) :
    (∑ x : ProductGridPoint ι N,
      abs (coefficient (productGridCellIndex profile x)) ^ p) =
      (∏ a, 2 ^ (N - (profile a).val)) *
        ∑ cell : ProductGridCell profile, abs (coefficient cell) ^ p := by
  exact productGrid_cellFunction_sum profile (fun cell => abs (coefficient cell) ^ p)

/-- Uniform averaging over grid points pushes forward to uniform averaging over
the product cells of the given profile. -/
theorem productGrid_uniform_mean_cellIndex {ι : Type*} {N : ℕ}
    [Fintype ι] [DecidableEq ι] (profile : ProductGridProfile ι N)
    (f : ProductGridCell profile → ℝ) :
    mean (uniformLaw (ProductGridPoint ι N))
        (fun x => f (productGridCellIndex profile x)) =
      mean (uniformLaw (ProductGridCell profile)) f := by
  classical
  letI : Nonempty (ProductGridPoint ι N) :=
    ⟨fun _ => ⟨0, Nat.pow_pos (by decide)⟩⟩
  letI : Nonempty (ProductGridCell profile) :=
    ⟨fun a => ⟨0, Nat.pow_pos (by decide)⟩⟩
  letI : Nonempty (ProductGridTail profile) :=
    ⟨fun a => ⟨0, Nat.pow_pos (by decide)⟩⟩
  calc
    _ = mean (uniformLaw (ProductGridCell profile × ProductGridTail profile))
          (fun point => f point.1) := by
      simpa [productGridSplitEquiv_fst] using
        (uniform_mean_equiv (productGridSplitEquiv profile)
          (fun point : ProductGridCell profile × ProductGridTail profile => f point.1))
    _ = mean (uniformLaw (ProductGridTail profile × ProductGridCell profile))
          (fun point => f point.2) := by
      exact uniform_mean_equiv (Equiv.prodComm (ProductGridCell profile)
        (ProductGridTail profile)) (fun point : ProductGridTail profile ×
          ProductGridCell profile => f point.2)
    _ = mean (uniformLaw (ProductGridCell profile)) f :=
      uniform_mean_product_snd f

/-- In particular, the exact normalized real-`p` moment of a coefficient
selected by its containing product cell is the uniform cell moment. -/
theorem productGrid_uniform_realMoment {ι : Type*} {N : ℕ}
    [Fintype ι] [DecidableEq ι] (profile : ProductGridProfile ι N)
    (coefficient : ProductGridCell profile → ℝ) (p : ℝ) :
    mean (uniformLaw (ProductGridPoint ι N))
        (fun x => abs (coefficient (productGridCellIndex profile x)) ^ p) =
      mean (uniformLaw (ProductGridCell profile))
        (fun cell => abs (coefficient cell) ^ p) :=
  productGrid_uniform_mean_cellIndex profile (fun cell => abs (coefficient cell) ^ p)

/-- Indicator of a product rectangle in the product grid. -/
noncomputable def productGridCellIndicator {ι : Type*} {N : ℕ}
    (profile : ProductGridProfile ι N) (cell : ProductGridCell profile)
    (x : ProductGridPoint ι N) : ℝ := by
  classical
  exact if productGridCellIndex profile x = cell then 1 else 0

/-- The tensor product of the next binary digits at the shape levels. -/
def productGridDigit {ι : Type*} {N : ℕ} [Fintype ι] [DecidableEq ι]
    (profile : ProductGridProfile ι N) (x : ProductGridPoint ι N) : ℝ :=
  ∏ a, dyadicDigit N (profile a) (x a).val

/-- The `L∞` normalized product Haar function for a product cell. -/
def productGridHaarValue {ι : Type*} {N : ℕ} [Fintype ι] [DecidableEq ι]
    (profile : ProductGridProfile ι N) (cell : ProductGridCell profile)
    (x : ProductGridPoint ι N) : ℝ :=
  ∏ a, dyadicHaarValue N (profile a) (cell a).val (x a).val

/-- A product rectangle indicator is the product of its one-axis indicators. -/
theorem productGridCellIndicator_eq_prod {ι : Type*} {N : ℕ} [Fintype ι]
    [DecidableEq ι]
    (profile : ProductGridProfile ι N) (cell : ProductGridCell profile)
    (x : ProductGridPoint ι N) :
    productGridCellIndicator profile cell x =
      ∏ a, dyadicCellIndicator N (profile a) (cell a).val (x a).val := by
  classical
  unfold productGridCellIndicator productGridCellIndex
  by_cases h : (fun a =>
      (⟨dyadicCellIndex N (profile a) (x a).val,
        dyadicCellIndex_lt N (profile a) (x a).isLt⟩ : Fin (2 ^ (profile a).val))) = cell
  · have hcoord (a : ι) : dyadicCellIndex N (profile a) (x a).val = (cell a).val := by
      have := congrFun h a
      exact congrArg Fin.val this
    rw [if_pos h]
    simp [dyadicCellIndicator, hcoord]
  · have hne : ∃ a, dyadicCellIndex N (profile a) (x a).val ≠ (cell a).val := by
      by_contra hn
      push_neg at hn
      apply h
      funext a
      apply Fin.ext
      exact hn a
    obtain ⟨a, ha⟩ := hne
    have hzero : dyadicCellIndicator N (profile a) (cell a).val (x a).val = 0 := by
      simp [dyadicCellIndicator, ha]
    have hp : (∏ b, dyadicCellIndicator N (profile b) (cell b).val (x b).val) = 0 :=
      Finset.prod_eq_zero (s := Finset.univ)
        (f := fun b => dyadicCellIndicator N (profile b) (cell b).val (x b).val)
        (Finset.mem_univ a) hzero
    rw [if_neg h]
    exact hp.symm

/-- Exact tensor Haar identity: the product Haar is its rectangle indicator
times the product of the next digits. -/
theorem productGridHaarValue_eq_cellIndicator_mul_digit {ι : Type*} {N : ℕ}
    [Fintype ι] [DecidableEq ι] (profile : ProductGridProfile ι N)
    (cell : ProductGridCell profile) (x : ProductGridPoint ι N) :
    productGridHaarValue profile cell x =
      productGridCellIndicator profile cell x * productGridDigit profile x := by
  rw [productGridHaarValue, productGridDigit,
    productGridCellIndicator_eq_prod]
  simp_rw [haarValue_eq_cellIndicator_mul_digit]
  rw [Finset.prod_mul_distrib]

/-- Product cells form a disjoint partition of the depth-`N` product grid. -/
theorem productGridCellIndicator_sum_eq_one {ι : Type*} {N : ℕ}
    [Fintype ι] [DecidableEq ι] (profile : ProductGridProfile ι N)
    (x : ProductGridPoint ι N) :
    (∑ cell : ProductGridCell profile, productGridCellIndicator profile cell x) = 1 := by
  classical
  let cell₀ := productGridCellIndex profile x
  have hterms (cell : ProductGridCell profile) :
    productGridCellIndicator profile cell x = if cell = cell₀ then 1 else 0 := by
    unfold productGridCellIndicator
    by_cases h : productGridCellIndex profile x = cell
    · simp only [if_pos h, cell₀, if_pos h.symm]
    · have hne : cell ≠ productGridCellIndex profile x := fun hc => h hc.symm
      simp only [if_neg h, cell₀, if_neg hne]
  calc
    _ = ∑ cell : ProductGridCell profile, (if cell = cell₀ then (1 : ℝ) else 0) :=
      Finset.sum_congr rfl (fun cell _ => hterms cell)
    _ = 1 := by simp

/-- The sum of all same-shape Haar terms with cell coefficients factors through
the coefficient on the unique cell containing the point. -/
theorem productGrid_shapeBlock_eq_coefficient_mul_digit {ι : Type*} {N : ℕ}
    [Fintype ι] [DecidableEq ι] (profile : ProductGridProfile ι N)
    (coefficient : ProductGridCell profile → ℝ) (x : ProductGridPoint ι N) :
    (∑ cell : ProductGridCell profile,
      coefficient cell * productGridHaarValue profile cell x) =
      coefficient (productGridCellIndex profile x) * productGridDigit profile x := by
  classical
  let cell₀ := productGridCellIndex profile x
  have hterms (cell : ProductGridCell profile) :
      coefficient cell * productGridHaarValue profile cell x =
        if cell = cell₀ then coefficient cell₀ * productGridDigit profile x else 0 := by
    rw [productGridHaarValue_eq_cellIndicator_mul_digit]
    unfold productGridCellIndicator
    by_cases h : productGridCellIndex profile x = cell
    · simp only [if_pos h, cell₀, if_pos h.symm]
      rw [h]
      simp
    · have hne : cell ≠ productGridCellIndex profile x := fun hc : cell =
        productGridCellIndex profile x => h hc.symm
      simp only [if_neg h, cell₀, if_neg hne]
      simp
  calc
    _ = ∑ cell : ProductGridCell profile,
        (if cell = cell₀ then coefficient cell₀ * productGridDigit profile x else 0) :=
      Finset.sum_congr rfl (fun cell _ => hterms cell)
    _ = coefficient cell₀ * productGridDigit profile x := by simp

end HaarQuarter
