import BrownianSharp.AlignmentPaperContinuumGoodRegion
import BrownianSharp.DyadicRealCells
import BrownianSharp.CovarianceBound
import Mathlib.MeasureTheory.Measure.WithDensity

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

/-! Support-level bridge from the actual continuous tensor atoms to the
dyadic rectangle cells used in the paper's pair-hull decomposition. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperContinuumHulls

open AlignmentPaperContinuumGoodRegion

/-- The real dyadic rectangle associated with one tensor shape and address. -/
def realDyadicBox {d n : ℕ} (a : LayerIndex d n) : Set (Fin d → ℝ) :=
  {x | ∀ i : Fin d,
    x i ∈ HaarQuarter.realDyadicCell (layerIndexDepth a i)
      (layerIndexCell a i)}

/-- Pairs in opposite children of one depth-`k` dyadic interval. -/
def oneDyadicOppositeHalfPair (k c : ℕ) : Set (ℝ × ℝ) :=
  (HaarQuarter.realDyadicLeftHalf k c ×ˢ
      HaarQuarter.realDyadicRightHalf k c) ∪
    (HaarQuarter.realDyadicRightHalf k c ×ˢ
      HaarQuarter.realDyadicLeftHalf k c)

/-- All pairs that first separate at depth `k` inside some depth-`k` parent. -/
def oneDyadicOppositeHalfShell (k : ℕ) : Set (ℝ × ℝ) :=
  ⋃ c ∈ Finset.range (2 ^ k), oneDyadicOppositeHalfPair k c

/-- Pairs in one common cell at the terminal resolution. -/
def oneDyadicSameDepthCellShell (N : ℕ) : Set (ℝ × ℝ) :=
  ⋃ c ∈ Finset.range (2 ^ N),
    HaarQuarter.realDyadicCell N c ×ˢ HaarQuarter.realDyadicCell N c

/-- Product of coordinatewise uniform Lebesgue measures on the pair square. -/
def unitIntervalPairMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).prod
    (volume.restrict (Set.Icc (0 : ℝ) 1))

/-- Tensor product of the pair-square measures, in coordinate-pair order. -/
def coordinatePairLebesgue (d : ℕ) : Measure (Fin d → ℝ × ℝ) :=
  Measure.pi (fun _ : Fin d => unitIntervalPairMeasure)

/-- Rearranging two cube points into coordinate pairs preserves the actual
product Lebesgue measure. This connects the coordinatewise hull calculation
below to the spatial pair integral on `[0,1]^d × [0,1]^d`. -/
theorem measurePreserving_cubePairEquiv_coordinatePairLebesgue (d : ℕ) :
    MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d)).symm
      ((AlignmentPaperContinuumGoodRegion.cubeLebesgue d).prod
        (AlignmentPaperContinuumGoodRegion.cubeLebesgue d))
      (coordinatePairLebesgue d) := by
  let μ : Fin d → Measure ℝ := fun _ =>
    volume.restrict (Set.Icc (0 : ℝ) 1)
  have hbase : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d))
      (Measure.pi fun i => (μ i).prod (μ i))
      ((Measure.pi fun i => μ i).prod (Measure.pi fun i => μ i)) := by
    exact MeasureTheory.measurePreserving_arrowProdEquivProdArrow
      ℝ ℝ (Fin d) μ μ
  simpa [coordinatePairLebesgue, unitIntervalPairMeasure, μ,
    AlignmentPaperContinuumGoodRegion.cubeLebesgue_eq_pi] using hbase.symm

/-- Coordinatewise first-separation shell for a prescribed dyadic depth vector. -/
def tensorOppositeHullShell {d : ℕ} (u : Fin d → ℕ) :
    Set (Fin d → ℝ × ℝ) :=
  Set.univ.pi (fun i => oneDyadicOppositeHalfShell (u i))

private theorem realDyadicHalves_subset_parent (k c : ℕ) :
    HaarQuarter.realDyadicLeftHalf k c ⊆ HaarQuarter.realDyadicCell k c ∧
    HaarQuarter.realDyadicRightHalf k c ⊆ HaarQuarter.realDyadicCell k c := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
    rw [pow_succ]
    ring
  constructor
  · intro x hx
    simp only [HaarQuarter.realDyadicLeftHalf, HaarQuarter.realDyadicCell,
      Set.mem_Ico] at hx ⊢
    rcases hx with ⟨hl, hu⟩
    constructor
    · rw [div_le_iff₀ hp]
      have hh := hl
      rw [hpow, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ k)] at hh
      push_cast at hh ⊢
      nlinarith
    · rw [lt_div_iff₀ hp]
      have hh := hu
      rw [hpow] at hh
      have hh' : x * (2 * (2 : ℝ) ^ k) < ((2 * c + 1 : ℕ) : ℝ) :=
        (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ k)).mp hh
      push_cast at hh' ⊢
      nlinarith
  · intro x hx
    simp only [HaarQuarter.realDyadicRightHalf, HaarQuarter.realDyadicCell, Set.mem_Ico] at hx ⊢
    rcases hx with ⟨hl, hu⟩
    constructor
    · rw [div_le_iff₀ hp]
      have hh := hl
      rw [hpow, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ k)] at hh
      push_cast at hh ⊢
      nlinarith [show 0 ≤ (c : ℝ) by positivity]
    · rw [lt_div_iff₀ hp]
      have hh := hu
      rw [hpow] at hh
      have hh' : x * (2 * (2 : ℝ) ^ k) < ((2 * c + 2 : ℕ) : ℝ) :=
        (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ k)).mp hh
      push_cast at hh' ⊢
      nlinarith

/-- The two half-open child cells partition a depth-`k` parent cell. -/
private theorem realDyadicCell_eq_union_halves (k c : ℕ) :
    HaarQuarter.realDyadicCell k c =
      HaarQuarter.realDyadicLeftHalf k c ∪
        HaarQuarter.realDyadicRightHalf k c := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
    rw [pow_succ]
    ring
  have hlo : (c : ℝ) / (2 : ℝ) ^ k =
      (2 * c : ℕ) / (2 : ℝ) ^ (k + 1) := by
    rw [hpow]
    push_cast
    field_simp <;> ring
  have hhi : ((c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ k =
      ((2 * c + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) := by
    rw [hpow]
    push_cast
    field_simp <;> ring
  have hleftbound : ((2 * c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) ≤
      ((2 * c + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith
  have hrightbound : (2 * c : ℕ) / (2 : ℝ) ^ (k + 1) ≤
      ((2 * c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    push_cast
    nlinarith
  ext x
  simp only [HaarQuarter.realDyadicCell, HaarQuarter.realDyadicLeftHalf,
    HaarQuarter.realDyadicRightHalf, Set.mem_Ico]
  rw [hlo, hhi]
  constructor
  · rintro ⟨hl, hu⟩
    by_cases hmid : x < ((2 * c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1)
    · exact Or.inl ⟨hl, hmid⟩
    · exact Or.inr ⟨le_of_not_gt hmid, hu⟩
  · rintro (⟨hl, hu⟩ | ⟨hl, hu⟩)
    · exact ⟨hl, lt_of_lt_of_le hu hleftbound⟩
    · exact ⟨le_trans hrightbound hl, hu⟩

private theorem realDyadicLeftHalf_eq_child (k c : ℕ) :
    HaarQuarter.realDyadicLeftHalf k c =
      HaarQuarter.realDyadicCell (k + 1) (2 * c) := by
  ext x
  simp [HaarQuarter.realDyadicLeftHalf, HaarQuarter.realDyadicCell,
    Set.mem_Ico]

private theorem realDyadicRightHalf_eq_child (k c : ℕ) :
    HaarQuarter.realDyadicRightHalf k c =
      HaarQuarter.realDyadicCell (k + 1) (2 * c + 1) := by
  ext x
  simp only [HaarQuarter.realDyadicRightHalf, HaarQuarter.realDyadicCell,
    Set.mem_Ico]

private theorem dyadicCell_address_lt_of_mem_unitInterval
    {k c : ℕ} {x : ℝ} (hx1 : x < 1)
    (hc : x ∈ HaarQuarter.realDyadicCell k c) : c < 2 ^ k := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  simp only [HaarQuarter.realDyadicCell, Set.mem_Ico] at hc
  have hlow : (c : ℝ) ≤ x * (2 : ℝ) ^ k := (div_le_iff₀ hp).mp hc.1
  have hupper : x * (2 : ℝ) ^ k < (2 : ℝ) ^ k := by
    have h := mul_lt_mul_of_pos_right hx1 hp
    nlinarith
  have hcast : (c : ℝ) < (2 ^ k : ℕ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact lt_of_le_of_lt hlow hupper
  exact_mod_cast hcast

private theorem realDyadicCells_disjoint_of_ne {k c c' : ℕ} (hcc : c ≠ c') :
    Disjoint (HaarQuarter.realDyadicCell k c)
      (HaarQuarter.realDyadicCell k c') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp [HaarQuarter.realDyadicCell, Set.mem_Ico] at hx hx'
  have hp : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hlow : (c : ℝ) ≤ x * (2 : ℝ) ^ k := (div_le_iff₀ hp).mp hx.1
  have hupp : x * (2 : ℝ) ^ k < (c' : ℝ) + 1 := (lt_div_iff₀ hp).mp hx'.2
  have hlow' : (c' : ℝ) ≤ x * (2 : ℝ) ^ k := (div_le_iff₀ hp).mp hx'.1
  have hupp' : x * (2 : ℝ) ^ k < (c : ℝ) + 1 := (lt_div_iff₀ hp).mp hx.2
  have hceq : c = c' := by
    by_contra hne
    have hlt : c < c' ∨ c' < c := Nat.lt_or_gt_of_ne hne
    rcases hlt with hlt | hlt
    · have hreal : (c' : ℝ) < (c : ℝ) + 1 := by linarith
      have hnat : c' < c + 1 := by exact_mod_cast hreal
      omega
    · have hreal : (c : ℝ) < (c' : ℝ) + 1 := by linarith
      have hnat : c < c' + 1 := by exact_mod_cast hreal
      omega
  exact hcc hceq

private theorem oneDyadicOppositeHalfPair_subset_parent (k c : ℕ) :
    oneDyadicOppositeHalfPair k c ⊆
      HaarQuarter.realDyadicCell k c ×ˢ HaarQuarter.realDyadicCell k c := by
  intro p hp
  rcases hp with hp | hp
  · exact ⟨(realDyadicHalves_subset_parent k c).1 hp.1,
      (realDyadicHalves_subset_parent k c).2 hp.2⟩
  · exact ⟨(realDyadicHalves_subset_parent k c).2 hp.1,
      (realDyadicHalves_subset_parent k c).1 hp.2⟩

/-- Distinct depth-`k` parent cells give disjoint opposite-half pair shells. -/
private theorem oneDyadicOppositeHalfPair_disjoint {k c c' : ℕ}
    (hcc : c ≠ c') :
    Disjoint (oneDyadicOppositeHalfPair k c)
      (oneDyadicOppositeHalfPair k c') := by
  rw [Set.disjoint_left]
  intro p hp hp'
  have hparent := realDyadicCells_disjoint_of_ne (k := k) hcc
  exact (Set.disjoint_left.mp hparent)
    (oneDyadicOppositeHalfPair_subset_parent k c hp).1
    (oneDyadicOppositeHalfPair_subset_parent k c' hp').1

/-- A depth-`k` opposite-half pair cannot lie together in any strictly finer
dyadic cell. The proof uses the aligned integer boundary at scale `k+1`. -/
private theorem no_common_deeper_dyadic_cell_of_opposite_halves
    {k c l m : ℕ} {x y : ℝ}
    (hkl : k < l)
    (hx : x ∈ HaarQuarter.realDyadicLeftHalf k c)
    (hy : y ∈ HaarQuarter.realDyadicRightHalf k c)
    (hc : x ∈ HaarQuarter.realDyadicCell l m)
    (hc' : y ∈ HaarQuarter.realDyadicCell l m) : False := by
  have hk1l : k + 1 ≤ l := by omega
  let q := l - (k + 1)
  have hl : l = (k + 1) + q := by
    dsimp [q]
    omega
  have hpow : (2 : ℝ) ^ l = (2 : ℝ) ^ (k + 1) * (2 : ℝ) ^ q := by
    rw [hl, pow_add]
  have hden0 : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
  have hden : (0 : ℝ) < (2 : ℝ) ^ l := by positivity
  simp only [HaarQuarter.realDyadicLeftHalf, Set.mem_Ico] at hx
  simp only [HaarQuarter.realDyadicRightHalf, Set.mem_Ico] at hy
  push_cast at hx hy
  simp only [HaarQuarter.realDyadicCell, Set.mem_Ico] at hc hc'
  have hxscale : x * (2 : ℝ) ^ (k + 1) < (2 * c + 1 : ℝ) :=
    (lt_div_iff₀ hden0).mp hx.2
  have hyscale : (2 * c + 1 : ℝ) ≤ y * (2 : ℝ) ^ (k + 1) :=
    (div_le_iff₀ hden0).mp hy.1
  have hxlarge : x * (2 : ℝ) ^ l <
      (((2 * c + 1) * 2 ^ q : ℕ) : ℝ) := by
    rw [hpow]
    have h := mul_lt_mul_of_pos_right hxscale
      (by positivity : 0 < (2 : ℝ) ^ q)
    push_cast at h ⊢
    nlinarith
  have hylarge : (((2 * c + 1) * 2 ^ q : ℕ) : ℝ) ≤
      y * (2 : ℝ) ^ l := by
    rw [hpow]
    have h := mul_le_mul_of_nonneg_right hyscale
      (by positivity : 0 ≤ (2 : ℝ) ^ q)
    push_cast at h ⊢
    nlinarith
  have hmlow : (m : ℝ) ≤ x * (2 : ℝ) ^ l :=
    (div_le_iff₀ hden).mp hc.1
  have hmyhigh : y * (2 : ℝ) ^ l < (m : ℝ) + 1 := by
    have h := (lt_div_iff₀ hden).mp hc'.2
    push_cast at h ⊢
    nlinarith
  have hmb : (m : ℝ) < (((2 * c + 1) * 2 ^ q : ℕ) : ℝ) := by linarith
  have hbm : (((2 * c + 1) * 2 ^ q : ℕ) : ℝ) < (m : ℝ) + 1 := by linarith
  have hmb' : m < (2 * c + 1) * 2 ^ q := by exact_mod_cast hmb
  have hbm' : (2 * c + 1) * 2 ^ q < m + 1 := by exact_mod_cast hbm
  omega

private theorem no_common_deeper_dyadic_cell_of_pair
    {k c l m : ℕ} {x y : ℝ}
    (hkl : k < l)
    (hp : (x, y) ∈ oneDyadicOppositeHalfPair k c)
    (hx : x ∈ HaarQuarter.realDyadicCell l m)
    (hy : y ∈ HaarQuarter.realDyadicCell l m) : False := by
  rcases hp with hp | hp
  · exact no_common_deeper_dyadic_cell_of_opposite_halves hkl hp.1 hp.2 hx hy
  · exact no_common_deeper_dyadic_cell_of_opposite_halves hkl hp.2 hp.1 hy hx

/-- Finite set of dyadic levels at which a pair lies in one common cell. -/
def oneDyadicCommonDepthSet (N : ℕ) (x y : ℝ) : Finset ℕ :=
  (by
    classical
    exact (Finset.range (N + 1)).filter fun k =>
      ∃ c, x ∈ HaarQuarter.realDyadicCell k c ∧
        y ∈ HaarQuarter.realDyadicCell k c)

/-- Largest common dyadic cell depth up to `N`; zero is the convention when
the pair has no common cell in that range. -/
def oneDyadicCommonDepthMax (N : ℕ) (x y : ℝ) : ℕ :=
  (oneDyadicCommonDepthSet N x y).sup id

/-- Finite one-dimensional pair partition: on `[0,1)²`, either the pair first
separates into opposite children at some level below `N`, or both points lie
in the same depth-`N` cell. This is the exact truncated hull decomposition. -/
theorem oneDyadicOppositeShell_or_sameDepthCell
    {N : ℕ} {x y : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    (∃ k < N, (x, y) ∈ oneDyadicOppositeHalfShell k) ∨
      (∃ c < 2 ^ N, x ∈ HaarQuarter.realDyadicCell N c ∧
        y ∈ HaarQuarter.realDyadicCell N c) := by
  classical
  let k := oneDyadicCommonDepthMax N x y
  have hzero : 0 ∈ oneDyadicCommonDepthSet N x y := by
    rw [oneDyadicCommonDepthSet, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, 0, ?_⟩
    simp only [HaarQuarter.realDyadicCell, Set.mem_Ico]
    exact ⟨⟨by linarith [hx.1], by linarith [hx.2]⟩,
      ⟨by linarith [hy.1], by linarith [hy.2]⟩⟩
  have hnonempty : (oneDyadicCommonDepthSet N x y).Nonempty := ⟨0, hzero⟩
  have hmaxmem : k ∈ oneDyadicCommonDepthSet N x y := by
    have hsup : (oneDyadicCommonDepthSet N x y).sup (fun j : ℕ => j) ∈
        id '' (↑(oneDyadicCommonDepthSet N x y) : Set ℕ) :=
      Finset.sup_mem_of_nonempty hnonempty
    rcases hsup with ⟨j, hj, hjeq⟩
    have hjeq' : j = k := by
      have hfun : (fun j : ℕ => j) = (id : ℕ → ℕ) := rfl
      have hsupEq : (oneDyadicCommonDepthSet N x y).sup
          (fun j : ℕ => j) =
          (oneDyadicCommonDepthSet N x y).sup (id : ℕ → ℕ) :=
        congrArg (fun f : ℕ → ℕ => (oneDyadicCommonDepthSet N x y).sup f) hfun
      simpa [k, oneDyadicCommonDepthMax] using hjeq.trans hsupEq
    simpa [hjeq'] using hj
  rw [oneDyadicCommonDepthSet, Finset.mem_filter, Finset.mem_range] at hmaxmem
  rcases hmaxmem with ⟨hkN, ⟨c, hxc, hyc⟩⟩
  by_cases hkeq : k = N
  · right
    rw [hkeq] at hxc hyc
    refine ⟨c, ?_, hxc, hyc⟩
    exact dyadicCell_address_lt_of_mem_unitInterval hx.2 hxc
  · have hklt : k < N := by omega
    have hxs : x ∈ HaarQuarter.realDyadicLeftHalf k c ∨
        x ∈ HaarQuarter.realDyadicRightHalf k c := by
      have h := hxc
      rw [realDyadicCell_eq_union_halves] at h
      exact h
    have hys : y ∈ HaarQuarter.realDyadicLeftHalf k c ∨
        y ∈ HaarQuarter.realDyadicRightHalf k c := by
      have h := hyc
      rw [realDyadicCell_eq_union_halves] at h
      exact h
    rcases hxs with hxL | hxR
    · rcases hys with hyL | hyR
      · have hdeeper : k + 1 ∈ oneDyadicCommonDepthSet N x y := by
          rw [oneDyadicCommonDepthSet, Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ?_⟩
          exact ⟨2 * c,
            by simpa [realDyadicLeftHalf_eq_child] using hxL,
            by simpa [realDyadicLeftHalf_eq_child] using hyL⟩
        have hle : k + 1 ≤ k := by
          have := Finset.le_sup
            (s := oneDyadicCommonDepthSet N x y) (f := id) hdeeper
          simpa [k, oneDyadicCommonDepthMax] using this
        omega

      · left
        refine ⟨k, hklt, ?_⟩
        have hc : c < 2 ^ k :=
          dyadicCell_address_lt_of_mem_unitInterval hx.2 hxc
        change (x, y) ∈ ⋃ j ∈ Finset.range (2 ^ k),
          oneDyadicOppositeHalfPair k j
        simp only [Set.mem_iUnion]
        exact ⟨c, Finset.mem_range.mpr hc, Or.inl ⟨hxL, hyR⟩⟩
    · rcases hys with hyL | hyR
      · left
        refine ⟨k, hklt, ?_⟩
        have hc : c < 2 ^ k :=
          dyadicCell_address_lt_of_mem_unitInterval hx.2 hxc
        change (x, y) ∈ ⋃ j ∈ Finset.range (2 ^ k),
          oneDyadicOppositeHalfPair k j
        simp only [Set.mem_iUnion]
        exact ⟨c, Finset.mem_range.mpr hc, Or.inr ⟨hxR, hyL⟩⟩
      · have hdeeper : k + 1 ∈ oneDyadicCommonDepthSet N x y := by
          rw [oneDyadicCommonDepthSet, Finset.mem_filter, Finset.mem_range]
          refine ⟨by omega, ?_⟩
          exact ⟨2 * c + 1,
            by simpa [realDyadicRightHalf_eq_child] using hxR,
            by simpa [realDyadicRightHalf_eq_child] using hyR⟩
        have hle : k + 1 ≤ k := by
          have := Finset.le_sup
            (s := oneDyadicCommonDepthSet N x y) (f := id) hdeeper
          simpa [k, oneDyadicCommonDepthMax] using this
        omega

/-- Coordinatewise tensor version of the finite hull partition: either every
coordinate pair has a first-separation profile below `N`, or at least one
coordinate lies in the terminal same-cell residual. -/
theorem tensorOppositeShell_or_coordinateResidual
    {d N : ℕ} (x y : Fin d → ℝ)
    (hx : ∀ i, x i ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) 1) :
    (∃ u : Fin d → ℕ, (∀ i, u i < N) ∧
      (fun i => (x i, y i)) ∈ tensorOppositeHullShell u) ∨
    (∃ i : Fin d, ∃ c < 2 ^ N,
      x i ∈ HaarQuarter.realDyadicCell N c ∧
      y i ∈ HaarQuarter.realDyadicCell N c) := by
  classical
  by_cases hres : ∃ i : Fin d, ∃ c < 2 ^ N,
      x i ∈ HaarQuarter.realDyadicCell N c ∧
      y i ∈ HaarQuarter.realDyadicCell N c
  · exact Or.inr hres
  · left
    have hsplit (i : Fin d) :
        ∃ k < N, (x i, y i) ∈ oneDyadicOppositeHalfShell k := by
      rcases oneDyadicOppositeShell_or_sameDepthCell (hx i) (hy i) with h | h
      · exact h
      · rcases h with ⟨c, hc, hxi, hyi⟩
        exact (hres ⟨i, c, hc, hxi, hyi⟩).elim
    let u : Fin d → ℕ := fun i => Classical.choose (hsplit i)
    have hu (i : Fin d) : u i < N ∧
        (x i, y i) ∈ oneDyadicOppositeHalfShell (u i) := by
      dsimp [u]
      exact Classical.choose_spec (hsplit i)
    refine ⟨u, (fun i => (hu i).1), ?_⟩
    simp only [tensorOppositeHullShell, Set.mem_pi, Set.mem_univ, true_implies]
    intro i
    exact (hu i).2
private theorem realDyadicLeftHalf_volume (k c : ℕ) :
    volume (HaarQuarter.realDyadicLeftHalf k c) =
      ENNReal.ofReal (((2 : ℝ) ^ (k + 1))⁻¹) := by
  rw [HaarQuarter.realDyadicLeftHalf, Real.volume_Ico]
  have hnum : ((2 * c + 1 : ℕ) : ℝ) - (2 * c : ℕ) = 1 := by norm_num
  have hspan : ((2 * c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) -
      ((2 * c : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) =
      ((2 : ℝ) ^ (k + 1))⁻¹ := by
    rw [div_sub_div_same, hnum]
    ring
  rw [hspan]

private theorem realDyadicRightHalf_volume (k c : ℕ) :
    volume (HaarQuarter.realDyadicRightHalf k c) =
      ENNReal.ofReal (((2 : ℝ) ^ (k + 1))⁻¹) := by
  rw [HaarQuarter.realDyadicRightHalf, Real.volume_Ico]
  have hnum : ((2 * c + 2 : ℕ) : ℝ) - (2 * c + 1 : ℕ) = 1 := by norm_num
  have hspan : ((2 * c + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) -
      ((2 * c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (k + 1) =
      ((2 : ℝ) ^ (k + 1))⁻¹ := by
    rw [div_sub_div_same, hnum]
    ring
  rw [hspan]

/-- Exact one-dimensional volume of the two opposite-half orientations for
one parent cell: `2 · 2^(-2(k+1)) = 2^(-2k-1)`. -/
theorem oneDyadicOppositeHalfPair_measure (k c : ℕ) :
    (volume.prod volume) (oneDyadicOppositeHalfPair k c) =
      ENNReal.ofReal
        (2 * (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2) := by
  let L := HaarQuarter.realDyadicLeftHalf k c
  let R := HaarQuarter.realDyadicRightHalf k c
  have hdisj : Disjoint (L ×ˢ R) (R ×ˢ L) := by
    rw [Set.disjoint_left]
    rintro ⟨x, y⟩ ⟨hxL, hyR⟩ ⟨hxR, hyL⟩
    have hLR : Disjoint L R := by
      rw [Set.disjoint_left]
      intro z hzL hzR
      simp [L, R, HaarQuarter.realDyadicLeftHalf,
        HaarQuarter.realDyadicRightHalf, Set.mem_Ico] at hzL hzR
      rcases hzL with ⟨_, hleft⟩
      rcases hzR with ⟨hright, _⟩
      linarith
    exact (Set.disjoint_left.mp hLR) hxL hxR
  have hmeasL : MeasurableSet L := by
    dsimp [L, HaarQuarter.realDyadicLeftHalf]
    measurability
  have hmeasR : MeasurableSet R := by
    dsimp [R, HaarQuarter.realDyadicRightHalf]
    measurability
  have hmeasure :
      (volume.prod volume) ((L ×ˢ R) ∪ (R ×ˢ L)) =
        (volume L * volume R) + (volume R * volume L) := by
    rw [MeasureTheory.measure_union hdisj (hmeasR.prod hmeasL),
      MeasureTheory.Measure.prod_prod,
      MeasureTheory.Measure.prod_prod]
  rw [show oneDyadicOppositeHalfPair k c = (L ×ˢ R) ∪ (R ×ˢ L) by rfl,
    hmeasure, realDyadicLeftHalf_volume, realDyadicRightHalf_volume]
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (((2 : ℝ) ^ (k + 1))⁻¹)),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1 <;> ring

/-- Summing over the `2^k` parent cells gives the one-coordinate shell mass.
This is the continuum version of the pair-hull factor used by the paper. -/
theorem oneDyadicOppositeHalfShell_measure (k : ℕ) :
    (volume.prod volume) (oneDyadicOppositeHalfShell k) =
      (2 ^ k : ℕ) • ENNReal.ofReal
        (2 * (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2) := by
  have hpairwise : Set.PairwiseDisjoint (↑(Finset.range (2 ^ k)))
      (fun c => oneDyadicOppositeHalfPair k c) := by
    intro c hc c' hc' hne
    exact oneDyadicOppositeHalfPair_disjoint hne
  have hmeas : ∀ c ∈ Finset.range (2 ^ k),
      MeasurableSet (oneDyadicOppositeHalfPair k c) := by
    intro c hc
    unfold oneDyadicOppositeHalfPair
    apply MeasurableSet.union
    · exact (measurableSet_Ico.prod measurableSet_Ico)
    · exact (measurableSet_Ico.prod measurableSet_Ico)
  rw [oneDyadicOppositeHalfShell,
    MeasureTheory.measure_biUnion_finset hpairwise hmeas]
  simp_rw [oneDyadicOppositeHalfPair_measure]
  rw [Finset.sum_const, Finset.card_range]

private theorem realDyadicCell_measure (N c : ℕ) :
    volume (HaarQuarter.realDyadicCell N c) =
      ENNReal.ofReal (((2 : ℝ) ^ N)⁻¹) := by
  rw [HaarQuarter.realDyadicCell, Real.volume_Ico]
  have hspan : ((c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N -
      (c : ℝ) / (2 : ℝ) ^ N = ((2 : ℝ) ^ N)⁻¹ := by
    rw [div_sub_div_same]
    push_cast
    ring
  rw [hspan]

private theorem realDyadicCell_subset_unitIcc {N c : ℕ} (hc : c < 2 ^ N) :
    HaarQuarter.realDyadicCell N c ⊆ Set.Icc (0 : ℝ) 1 := by
  intro x hx
  simp only [HaarQuarter.realDyadicCell, Set.mem_Ico] at hx
  constructor
  · exact le_trans (by positivity : (0 : ℝ) ≤ (c : ℝ) / (2 : ℝ) ^ N) hx.1
  · have hp : (0 : ℝ) < (2 : ℝ) ^ N := by positivity
    have hnat : c + 1 ≤ 2 ^ N := Nat.succ_le_iff.mpr hc
    have hu : ((c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ N ≤ 1 := by
      apply (div_le_iff₀ hp).2
      have hcast : ((c + 1 : ℕ) : ℝ) ≤ (2 ^ N : ℝ) := by exact_mod_cast hnat
      nlinarith
    exact le_of_lt (lt_of_lt_of_le hx.2 hu)

private theorem realDyadicHalves_subset_unitIcc {k c : ℕ} (hc : c < 2 ^ k) :
    HaarQuarter.realDyadicLeftHalf k c ⊆ Set.Icc (0 : ℝ) 1 ∧
    HaarQuarter.realDyadicRightHalf k c ⊆ Set.Icc (0 : ℝ) 1 := by
  have hparent := realDyadicCell_subset_unitIcc hc
  exact ⟨(realDyadicHalves_subset_parent k c).1.trans hparent,
    (realDyadicHalves_subset_parent k c).2.trans hparent⟩

/-- The same terminal-cell residual mass for the coordinate-pair probability
measure on `[0,1)²`; restriction does not change any cell's mass. -/
theorem oneDyadicSameDepthCellShell_probability_measure (N : ℕ) :
    unitIntervalPairMeasure (oneDyadicSameDepthCellShell N) =
      (2 ^ N : ℕ) • ENNReal.ofReal (((2 : ℝ) ^ N)⁻¹ ^ 2) := by
  have hpairwise : Set.PairwiseDisjoint (↑(Finset.range (2 ^ N)))
      (fun c => HaarQuarter.realDyadicCell N c ×ˢ
        HaarQuarter.realDyadicCell N c) := by
    intro c hc c' hc' hne
    change Disjoint (HaarQuarter.realDyadicCell N c ×ˢ
      HaarQuarter.realDyadicCell N c)
      (HaarQuarter.realDyadicCell N c' ×ˢ HaarQuarter.realDyadicCell N c')
    rw [Set.disjoint_left]
    intro p hp hp'
    exact (Set.disjoint_left.mp
      (realDyadicCells_disjoint_of_ne (k := N) hne)) hp.1 hp'.1
  have hmeas : ∀ c ∈ Finset.range (2 ^ N),
      MeasurableSet (HaarQuarter.realDyadicCell N c ×ˢ
        HaarQuarter.realDyadicCell N c) := by
    intro c hc
    exact measurableSet_Ico.prod measurableSet_Ico
  rw [oneDyadicSameDepthCellShell,
    MeasureTheory.measure_biUnion_finset hpairwise hmeas]
  simp_rw [unitIntervalPairMeasure, MeasureTheory.Measure.prod_prod]
  have hrestricted (c : ℕ) (hc : c < 2 ^ N) :
      (volume.restrict (Set.Icc (0 : ℝ) 1))
          (HaarQuarter.realDyadicCell N c) =
        volume (HaarQuarter.realDyadicCell N c) := by
    rw [Measure.restrict_apply' measurableSet_Icc]
    rw [Set.inter_eq_left.mpr (realDyadicCell_subset_unitIcc hc)]
  have hsum :
      (∑ c ∈ Finset.range (2 ^ N),
        (volume.restrict (Set.Icc (0 : ℝ) 1))
            (HaarQuarter.realDyadicCell N c) *
          (volume.restrict (Set.Icc (0 : ℝ) 1))
            (HaarQuarter.realDyadicCell N c)) =
      (∑ c ∈ Finset.range (2 ^ N),
        volume (HaarQuarter.realDyadicCell N c) *
          volume (HaarQuarter.realDyadicCell N c)) := by
    apply Finset.sum_congr rfl
    intro c hc
    rw [hrestricted c (Finset.mem_range.mp hc)]
  rw [hsum]
  simp_rw [realDyadicCell_measure]
  rw [Finset.sum_const, Finset.card_range]
  congr 1
  rw [← ENNReal.ofReal_mul
    (by positivity : 0 ≤ (((2 : ℝ) ^ N)⁻¹))]
  congr 1 <;> ring

/-- The coordinate-pair probability shell has the same exact mass as the
unrestricted Lebesgue shell, since every contributing child interval is in
the unit interval. -/
theorem oneDyadicOppositeHalfShell_probability_measure (k : ℕ) :
    unitIntervalPairMeasure (oneDyadicOppositeHalfShell k) =
      (2 ^ k : ℕ) • ENNReal.ofReal
        (2 * (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2) := by
  have hpairwise : Set.PairwiseDisjoint (↑(Finset.range (2 ^ k)))
      (fun c => oneDyadicOppositeHalfPair k c) := by
    intro c hc c' hc' hne
    exact oneDyadicOppositeHalfPair_disjoint hne
  have hmeas : ∀ c ∈ Finset.range (2 ^ k),
      MeasurableSet (oneDyadicOppositeHalfPair k c) := by
    intro c hc
    unfold oneDyadicOppositeHalfPair
    exact MeasurableSet.union (measurableSet_Ico.prod measurableSet_Ico)
      (measurableSet_Ico.prod measurableSet_Ico)
  have hpair : ∀ j < 2 ^ k,
      unitIntervalPairMeasure (oneDyadicOppositeHalfPair k j) =
        (volume.prod volume) (oneDyadicOppositeHalfPair k j) := by
    intro j hj
    let L := HaarQuarter.realDyadicLeftHalf k j
    let R := HaarQuarter.realDyadicRightHalf k j
    have hparentDisj' : Disjoint
        (HaarQuarter.realDyadicCell (k + 1) (2 * j))
        (HaarQuarter.realDyadicCell (k + 1) (2 * j + 1)) :=
      realDyadicCells_disjoint_of_ne (k := k + 1) (c := 2 * j)
        (c' := 2 * j + 1) (by omega)
    have hLR' : Disjoint L R := by
      dsimp [L, R]
      rw [realDyadicLeftHalf_eq_child, realDyadicRightHalf_eq_child]
      exact hparentDisj'
    have hdisj : Disjoint (L ×ˢ R) (R ×ˢ L) := by
      rw [Set.disjoint_left]
      rintro ⟨x, y⟩ ⟨hxL, hyR⟩ ⟨hxR, hyL⟩
      exact (Set.disjoint_left.mp hLR') hxL hxR
    have hmeasL : MeasurableSet L := by
      dsimp [L, HaarQuarter.realDyadicLeftHalf]
      measurability
    have hmeasR : MeasurableSet R := by
      dsimp [R, HaarQuarter.realDyadicRightHalf]
      measurability
    have hL : (volume.restrict (Set.Icc (0 : ℝ) 1)) L = volume L := by
      rw [Measure.restrict_apply' measurableSet_Icc]
      rw [Set.inter_eq_left.mpr ((realDyadicHalves_subset_unitIcc hj).1)]
    have hR : (volume.restrict (Set.Icc (0 : ℝ) 1)) R = volume R := by
      rw [Measure.restrict_apply' measurableSet_Icc]
      rw [Set.inter_eq_left.mpr ((realDyadicHalves_subset_unitIcc hj).2)]
    calc
      unitIntervalPairMeasure (oneDyadicOppositeHalfPair k j) =
          ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod
            (volume.restrict (Set.Icc (0 : ℝ) 1))) ((L ×ˢ R) ∪ (R ×ˢ L)) := by
              rfl
      _ = ((volume.restrict (Set.Icc (0 : ℝ) 1)) L *
            (volume.restrict (Set.Icc (0 : ℝ) 1)) R) +
          ((volume.restrict (Set.Icc (0 : ℝ) 1)) R *
            (volume.restrict (Set.Icc (0 : ℝ) 1)) L) := by
              rw [MeasureTheory.measure_union hdisj (hmeasR.prod hmeasL),
                MeasureTheory.Measure.prod_prod,
                MeasureTheory.Measure.prod_prod]
      _ = volume L * volume R + volume R * volume L := by rw [hL, hR]
      _ = (volume.prod volume) ((L ×ˢ R) ∪ (R ×ˢ L)) := by
            rw [MeasureTheory.measure_union hdisj (hmeasR.prod hmeasL),
              MeasureTheory.Measure.prod_prod,
              MeasureTheory.Measure.prod_prod]
      _ = (volume.prod volume) (oneDyadicOppositeHalfPair k j) := rfl
  calc
    unitIntervalPairMeasure (oneDyadicOppositeHalfShell k) =
        ∑ j ∈ Finset.range (2 ^ k),
          unitIntervalPairMeasure (oneDyadicOppositeHalfPair k j) := by
            rw [oneDyadicOppositeHalfShell,
              MeasureTheory.measure_biUnion_finset hpairwise hmeas]
    _ = ∑ j ∈ Finset.range (2 ^ k),
          (volume.prod volume) (oneDyadicOppositeHalfPair k j) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hpair j (Finset.mem_range.mp hj)
    _ = (volume.prod volume) (oneDyadicOppositeHalfShell k) := by
            symm
            rw [oneDyadicOppositeHalfShell,
              MeasureTheory.measure_biUnion_finset hpairwise hmeas]
    _ = (2 ^ k : ℕ) • ENNReal.ofReal
          (2 * (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2) :=
            oneDyadicOppositeHalfShell_measure k

private theorem oneDyadicOppositeHalfShell_mass_closed (k : ℕ) :
    (2 ^ k : ℕ) • ENNReal.ofReal
      (2 * (((2 : ℝ) ^ (k + 1))⁻¹) ^ 2) =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ (k + 1)) := by
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  push_cast
  have hpow : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
    rw [pow_succ]
    ring
  have hinv : (1 / 2 : ℝ) ^ (k + 1) = ((2 : ℝ) ^ (k + 1))⁻¹ := by
    rw [one_div_pow, pow_succ]
    field_simp
  rw [hpow, hinv]
  field_simp
  <;> ring

/-- Pairs with a common depth-`N` dyadic cell in at least one coordinate;
this is the residual set in the finite tensor hull partition. -/
def tensorCoordinateResidual {d : ℕ} (N : ℕ) : Set (Fin d → ℝ × ℝ) :=
  {p | ∃ i : Fin d, p i ∈ oneDyadicSameDepthCellShell N}

private theorem coordinateSameDepthCylinder_measure {d : ℕ} (N : ℕ)
    (i : Fin d) :
    coordinatePairLebesgue d
      {p | p i ∈ oneDyadicSameDepthCellShell N} =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
  let R := oneDyadicSameDepthCellShell N
  have hset : {p : Fin d → ℝ × ℝ | p i ∈ R} =
      Set.univ.pi (fun j : Fin d => if j = i then R else Set.univ) := by
    ext p
    simp [R]
  haveI : IsProbabilityMeasure unitIntervalPairMeasure := by
    refine ⟨?_⟩
    unfold unitIntervalPairMeasure
    rw [show (Set.univ : Set (ℝ × ℝ)) = Set.univ ×ˢ Set.univ by
      ext p
      simp, MeasureTheory.Measure.prod_prod]
    simp [Real.volume_Icc]
  haveI : IsFiniteMeasure unitIntervalPairMeasure := by
    unfold unitIntervalPairMeasure
    infer_instance
  rw [hset, coordinatePairLebesgue, MeasureTheory.Measure.pi_pi]
  calc
    (∏ j : Fin d, unitIntervalPairMeasure (if j = i then R else Set.univ)) =
        unitIntervalPairMeasure R := by
      rw [Finset.prod_eq_single i]
      · simp
      · intro j hj hji
        simp [hji]
      · simp
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
      rw [oneDyadicSameDepthCellShell_probability_measure]
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      field_simp
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, inv_pow]
      field_simp

/-- Finite type of coordinatewise depth profiles below a truncation level. -/
def BoundedHullProfile (d N : ℕ) :=
  {u : Fin d → ℕ // ∀ i, u i < N}

noncomputable def boundedHullProfileEquiv (d N : ℕ) :
    BoundedHullProfile d N ≃ (Fin d → Fin N) where
  toFun u := fun i => ⟨u.1 i, u.2 i⟩
  invFun v := ⟨fun i => (v i).val, fun i => (v i).isLt⟩
  left_inv u := by
    apply Subtype.ext
    rfl
  right_inv v := by
    funext i
    apply Fin.ext
    rfl

noncomputable instance boundedHullProfileFintype (d N : ℕ) :
    Fintype (BoundedHullProfile d N) :=
  Fintype.ofEquiv (Fin d → Fin N) (boundedHullProfileEquiv d N).symm

/-- Actual cube pairs admit a finite first-separation profile below level N,
unless some coordinate remains in a common depth-N cell. -/
theorem spatialPair_firstSeparation_or_residual {d N : ℕ}
    (p : (Fin d → ℝ) × (Fin d → ℝ))
    (hx : ∀ i, p.1 i ∈ Set.Ico (0 : ℝ) 1)
    (hy : ∀ i, p.2 i ∈ Set.Ico (0 : ℝ) 1) :
    (∃ u : BoundedHullProfile d N,
      (fun i => (p.1 i, p.2 i)) ∈ tensorOppositeHullShell u.1) ∨
      p ∈ {q : (Fin d → ℝ) × (Fin d → ℝ) |
        (fun i => (q.1 i, q.2 i)) ∈ tensorCoordinateResidual N} := by
  rcases tensorOppositeShell_or_coordinateResidual p.1 p.2 hx hy with h | h
  · rcases h with ⟨u, huN, huShell⟩
    exact Or.inl ⟨⟨u, huN⟩, huShell⟩
  · right
    rcases h with ⟨i, c, hc, hxi, hyi⟩
    apply Set.mem_setOf.mpr
    simp only [tensorCoordinateResidual, Set.mem_setOf_eq]
    refine ⟨i, ?_⟩
    change (p.1 i, p.2 i) ∈ oneDyadicSameDepthCellShell N
    simp only [oneDyadicSameDepthCellShell, Set.mem_iUnion]
    exact ⟨c, Finset.mem_range.mpr hc, hxi, hyi⟩

/-- The terminal same-cell residual in the tensor partition has mass at most
`d·2^-N`, so it vanishes as the dyadic truncation is refined. -/
theorem tensorCoordinateResidual_measure_le {d : ℕ} (N : ℕ) :
    coordinatePairLebesgue d (tensorCoordinateResidual N) ≤
      (d : ENNReal) * ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
  classical
  have hle : tensorCoordinateResidual N ⊆
      ⋃ i : Fin d, {p : Fin d → ℝ × ℝ |
        p i ∈ oneDyadicSameDepthCellShell N} := by
    intro p hp
    exact Set.mem_iUnion.mpr hp
  calc
    coordinatePairLebesgue d (tensorCoordinateResidual N) ≤
        coordinatePairLebesgue d
          (⋃ i : Fin d, {p : Fin d → ℝ × ℝ |
            p i ∈ oneDyadicSameDepthCellShell N}) := measure_mono hle
    _ ≤ ∑' i : Fin d, coordinatePairLebesgue d
          {p : Fin d → ℝ × ℝ | p i ∈ oneDyadicSameDepthCellShell N} :=
        MeasureTheory.measure_iUnion_le
          (fun i : Fin d => {p : Fin d → ℝ × ℝ |
            p i ∈ oneDyadicSameDepthCellShell N})
    _ = (d : ENNReal) * ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
      simp_rw [coordinateSameDepthCylinder_measure]
      simp [tsum_fintype, Fintype.card_fin, nsmul_eq_mul]

/-- Exact tensor profile volume: every coordinate has its own one-dimensional
first-separation scale, and the product law factors over coordinates. -/
theorem tensorOppositeHullShell_measure {d : ℕ} (u : Fin d → ℕ) :
    coordinatePairLebesgue d (tensorOppositeHullShell u) =
      ∏ i : Fin d,
        ((2 ^ (u i) : ℕ) • ENNReal.ofReal
          (2 * (((2 : ℝ) ^ (u i + 1))⁻¹) ^ 2)) := by
  haveI : IsFiniteMeasure unitIntervalPairMeasure := by
    unfold unitIntervalPairMeasure
    infer_instance
  unfold coordinatePairLebesgue tensorOppositeHullShell
  rw [MeasureTheory.Measure.pi_pi]
  simp_rw [oneDyadicOppositeHalfShell_probability_measure]

/-- Closed form of the continuum hull-shell volume. For a depth profile
`u`, each coordinate contributes the factor `2^(-(u_i+1))`. -/
theorem tensorOppositeHullShell_measure_eq {d : ℕ} (u : Fin d → ℕ) :
    coordinatePairLebesgue d (tensorOppositeHullShell u) =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ ((∑ i : Fin d, u i) + d)) := by
  rw [tensorOppositeHullShell_measure]
  have hone (i : Fin d) :
      (2 ^ (u i) : ℕ) • ENNReal.ofReal
        (2 * (((2 : ℝ) ^ (u i + 1))⁻¹) ^ 2) =
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (u i + 1)) :=
    oneDyadicOppositeHalfShell_mass_closed (u i)
  simp_rw [hone]
  rw [← ENNReal.ofReal_prod_of_nonneg (s := Finset.univ)
    (f := fun i : Fin d => (1 / 2 : ℝ) ^ (u i + 1)) (by
      intro i hi
      positivity)]
  congr 1
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  simp [Finset.sum_add_distrib]

/-- Finite type of continuum first-separation profiles of total grade `m`. -/
def ContinuumHullProfile (d m : ℕ) :=
  {u : Fin d → ℕ // (∑ i : Fin d, u i) = m}

/-- Continuum profiles are exactly the weak-composition shapes. -/
noncomputable def continuumHullProfileEquivShape (d m : ℕ) :
    ContinuumHullProfile d m ≃ Shape d m where
  toFun u := by
    refine ⟨Finsupp.equivFunOnFinite.symm u.1, ?_⟩
    rw [Finset.mem_finsuppAntidiag']
    constructor
    · simpa [Finsupp.sum_fintype] using u.2
    · simp
  invFun r := ⟨Finsupp.equivFunOnFinite r.1, by
      simpa [Finsupp.sum_fintype] using
        (Finset.mem_finsuppAntidiag'.mp r.2).1⟩
  left_inv u := by
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.apply_symm_apply u.1
  right_inv r := by
    apply Subtype.ext
    exact Finsupp.equivFunOnFinite.symm_apply_apply r.1

noncomputable instance continuumHullProfileFintype (d m : ℕ) :
    Fintype (ContinuumHullProfile d m) :=
  Fintype.ofEquiv (Shape d m) (continuumHullProfileEquivShape d m).symm

theorem continuumHullProfile_card (d m : ℕ) (hd : 0 < d) :
    Fintype.card (ContinuumHullProfile d m) =
      Nat.choose (m + d - 1) (d - 1) := by
  rw [Fintype.card_congr (continuumHullProfileEquivShape d m), shape_card d m hd]

/-- Pullback of a coordinate-pair first-separation shell to two spatial cube
points. -/
def spatialPairHullShell {d : ℕ} (u : Fin d → ℕ) :
    Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {p | (fun i => (p.1 i, p.2 i)) ∈ tensorOppositeHullShell u}

private theorem oneDyadicOppositeHalfShell_measurable (k : ℕ) :
    MeasurableSet (oneDyadicOppositeHalfShell k) := by
  unfold oneDyadicOppositeHalfShell oneDyadicOppositeHalfPair
  refine MeasurableSet.iUnion ?_
  intro c
  refine MeasurableSet.iUnion ?_
  intro hc
  exact MeasurableSet.union
    (measurableSet_Ico.prod measurableSet_Ico)
    (measurableSet_Ico.prod measurableSet_Ico)

theorem tensorOppositeHullShell_measurable {d : ℕ} (u : Fin d → ℕ) :
    MeasurableSet (tensorOppositeHullShell u) := by
  unfold tensorOppositeHullShell
  exact MeasurableSet.pi (Set.to_countable _) (fun i hi =>
    oneDyadicOppositeHalfShell_measurable (u i))

theorem spatialPairHullShell_measurable {d : ℕ} (u : Fin d → ℕ) :
    MeasurableSet (spatialPairHullShell u) := by
  unfold spatialPairHullShell
  exact (tensorOppositeHullShell_measurable u).preimage
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d)).symm.measurable

/-- The literal pair-cube measure of each pulled-back first-separation shell
is its coordinate-pair shell mass. -/
theorem spatialPairHullShell_measure {d : ℕ} (u : Fin d → ℕ) :
    ((AlignmentPaperContinuumGoodRegion.cubeLebesgue d).prod
      (AlignmentPaperContinuumGoodRegion.cubeLebesgue d)) (spatialPairHullShell u) =
      coordinatePairLebesgue d (tensorOppositeHullShell u) := by
  let e := (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d)).symm
  have hMP := measurePreserving_cubePairEquiv_coordinatePairLebesgue d
  have hs : MeasurableSet (tensorOppositeHullShell u) :=
    tensorOppositeHullShell_measurable u
  have hpre : e ⁻¹' tensorOppositeHullShell u = spatialPairHullShell u := by
    ext p
    rfl
  calc
    _ = ((AlignmentPaperContinuumGoodRegion.cubeLebesgue d).prod
        (AlignmentPaperContinuumGoodRegion.cubeLebesgue d))
        (e ⁻¹' tensorOppositeHullShell u) := by rw [hpre]
    _ = Measure.map e
        ((AlignmentPaperContinuumGoodRegion.cubeLebesgue d).prod
          (AlignmentPaperContinuumGoodRegion.cubeLebesgue d))
        (tensorOppositeHullShell u) := by
          rw [Measure.map_apply e.measurable hs]
    _ = coordinatePairLebesgue d (tensorOppositeHullShell u) := by
          rw [hMP.map_eq]

end BrownianSharp.AlignmentPaperContinuumHulls
