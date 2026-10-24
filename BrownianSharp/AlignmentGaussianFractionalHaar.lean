import BrownianSharp.AlignmentFractionalDyadicProjection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Algebra.Order.Field.GeomSum

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianFractionalHaar

open BrownianSharp.AlignmentFractionalDyadicProjection
open BrownianSharp.AlignmentFractionalL2

abbrev SourceL2 := BrownianSharp.AlignmentFractionalL2.UnitL2

theorem sourceDyadicCellIndicator_inner_self {n : ℕ} (j : Fin (2^n)) :
    inner ℝ (sourceDyadicCellIndicator n j) (sourceDyadicCellIndicator n j) =
      (1 : ℝ) / (2 : ℝ)^n := by
  unfold sourceDyadicCellIndicator
  rw [MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
    (μ := volume.restrict (Set.Icc (0:ℝ) 1))
    (s := sourceDyadicCell n j) (t := sourceDyadicCell n j)
    (by simp [sourceDyadicCell]) (by simp [sourceDyadicCell])]
  have hsub : sourceDyadicCell n j ⊆ Set.Icc (0:ℝ) 1 := by
    intro x hx
    constructor
    · have hj : 0 ≤ sourceDyadicLeft n j := by
        unfold sourceDyadicLeft
        positivity
      exact le_trans hj hx.1
    · have hright : sourceDyadicRight n j ≤ 1 := by
        unfold sourceDyadicRight
        apply (div_le_one (by positivity)).2
        have hj := j.isLt
        exact_mod_cast Nat.succ_le_of_lt hj
      exact le_trans hx.2.le hright
  rw [Set.inter_self, Measure.real_def]
  dsimp [sourceDyadicCell]
  rw [Measure.restrict_apply measurableSet_Ico]
  have hsub' : Set.Ico (sourceDyadicLeft n j) (sourceDyadicRight n j) ⊆
      Set.Icc (0:ℝ) 1 := by simpa [sourceDyadicCell] using hsub
  rw [Set.inter_eq_left.mpr hsub', Real.volume_Ico]
  unfold sourceDyadicLeft sourceDyadicRight
  have hd : (0:ℝ) < (2:ℝ)^n := by positivity
  have hcast : ((j.val+1:ℕ):ℝ) = (j.val:ℝ)+1 := by norm_num
  rw [hcast]
  have hdiff : ((j.val:ℝ)+1) / (2:ℝ)^n - (j.val:ℝ) / (2:ℝ)^n =
      1 / (2:ℝ)^n := by field_simp <;> ring
  rw [hdiff, ENNReal.toReal_ofReal (by positivity : 0 ≤ 1 / (2:ℝ)^n)]

def sourceDyadicLeftChild {r : ℕ} (j : Fin (2^r)) : Fin (2^(r+1)) :=
  ⟨2*j.val, by rw [pow_succ]; have hj := j.isLt; omega⟩

def sourceDyadicRightChild {r : ℕ} (j : Fin (2^r)) : Fin (2^(r+1)) :=
  ⟨2*j.val+1, by rw [pow_succ]; have hj := j.isLt; omega⟩

theorem sourceDyadic_leftChild_left_eq {r : ℕ} (j : Fin (2^r)) :
    sourceDyadicLeft (r+1) (sourceDyadicLeftChild j) = sourceDyadicLeft r j := by
  unfold sourceDyadicLeft sourceDyadicLeftChild
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [pow_succ]
  field_simp

theorem sourceDyadic_leftChild_right_eq_rightChild_left {r : ℕ}
    (j : Fin (2^r)) :
    sourceDyadicRight (r+1) (sourceDyadicLeftChild j) =
      sourceDyadicLeft (r+1) (sourceDyadicRightChild j) := by
  unfold sourceDyadicRight sourceDyadicLeft sourceDyadicLeftChild
    sourceDyadicRightChild
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]

theorem sourceDyadic_rightChild_right_eq {r : ℕ} (j : Fin (2^r)) :
    sourceDyadicRight (r+1) (sourceDyadicRightChild j) = sourceDyadicRight r j := by
  unfold sourceDyadicRight sourceDyadicRightChild
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat]
  rw [pow_succ]
  push_cast
  field_simp
  <;> ring

theorem sourceDyadic_leftChild_subset_parent {r : ℕ} (j : Fin (2^r)) :
    sourceDyadicCell (r+1) (sourceDyadicLeftChild j) ⊆ sourceDyadicCell r j := by
  intro x hx
  change sourceDyadicLeft (r+1) (sourceDyadicLeftChild j) ≤ x ∧
    x < sourceDyadicRight (r+1) (sourceDyadicLeftChild j) at hx
  change sourceDyadicLeft r j ≤ x ∧ x < sourceDyadicRight r j
  constructor
  · have hx' := hx
    rw [sourceDyadic_leftChild_left_eq] at hx'
    exact hx'.1
  · have hright : sourceDyadicRight (r+1) (sourceDyadicLeftChild j) ≤
        sourceDyadicRight r j := by
      simp only [sourceDyadicRight, sourceDyadicLeft, sourceDyadicLeftChild,
        Fin.val_mk, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      have hd : (0:ℝ)<(2:ℝ)^(r+1) := by positivity
      rw [pow_succ]
      field_simp
      push_cast
      have := j.isLt
      nlinarith
    exact lt_of_lt_of_le hx.2 hright

theorem sourceDyadic_rightChild_subset_parent {r : ℕ} (j : Fin (2^r)) :
    sourceDyadicCell (r+1) (sourceDyadicRightChild j) ⊆ sourceDyadicCell r j := by
  intro x hx
  change sourceDyadicLeft (r+1) (sourceDyadicRightChild j) ≤ x ∧
    x < sourceDyadicRight (r+1) (sourceDyadicRightChild j) at hx
  change sourceDyadicLeft r j ≤ x ∧ x < sourceDyadicRight r j
  constructor
  · have hleft : sourceDyadicLeft r j ≤
        sourceDyadicLeft (r+1) (sourceDyadicRightChild j) := by
      simp only [sourceDyadicLeft, sourceDyadicRightChild, Fin.val_mk,
        Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      have hd : (0:ℝ)<(2:ℝ)^(r+1) := by positivity
      rw [pow_succ]
      field_simp
      push_cast
      nlinarith
    exact le_trans hleft hx.1
  · have hx' := hx
    rw [sourceDyadic_rightChild_right_eq] at hx'
    exact hx'.2

theorem sourceDyadic_leftChild_lt_rightChild {r : ℕ} (j : Fin (2^r)) :
    sourceDyadicLeftChild j < sourceDyadicRightChild j := by
  apply Fin.lt_iff_val_lt_val.mpr
  simp [sourceDyadicLeftChild, sourceDyadicRightChild]

theorem sourceDyadic_leftChild_ne_rightChild {r : ℕ} (j : Fin (2^r)) :
    sourceDyadicLeftChild j ≠ sourceDyadicRightChild j :=
  ne_of_lt (sourceDyadic_leftChild_lt_rightChild j)

theorem sourceDyadicLeftChild_injective {r : ℕ} :
    Function.Injective (sourceDyadicLeftChild (r := r)) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  dsimp [sourceDyadicLeftChild] at hval
  omega

theorem sourceDyadicRightChild_injective {r : ℕ} :
    Function.Injective (sourceDyadicRightChild (r := r)) := by
  intro i j hij
  apply Fin.ext
  have hval := congrArg Fin.val hij
  dsimp [sourceDyadicRightChild] at hval
  omega

def sourceDyadicHaarMother (r : ℕ) (j : Fin (2^r)) : SourceL2 :=
  (Real.sqrt 2 ^ r) •
    (sourceDyadicCellIndicator (r+1) (sourceDyadicLeftChild j) -
      sourceDyadicCellIndicator (r+1) (sourceDyadicRightChild j))

theorem sourceDyadicHaarMother_orthonormal (r : ℕ) :
    Orthonormal ℝ (sourceDyadicHaarMother r) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  unfold sourceDyadicHaarMother
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial, inner_sub_left, inner_sub_right]
  by_cases hij : i = j
  · subst j
    have hdisj := sourceDyadicCellIndicator_orthogonal
      (sourceDyadic_leftChild_ne_rightChild i)
    have hn := sourceDyadicCellIndicator_inner_self (n := r+1)
      (sourceDyadicLeftChild i)
    have hr := sourceDyadicCellIndicator_inner_self (n := r+1)
      (sourceDyadicRightChild i)
    have hdisj' : inner ℝ
        (sourceDyadicCellIndicator (r+1) (sourceDyadicRightChild i))
        (sourceDyadicCellIndicator (r+1) (sourceDyadicLeftChild i)) = 0 := by
      rw [real_inner_comm]
      exact hdisj
    have hscale : (Real.sqrt 2 ^ r)^2 = (2:ℝ)^r := by
      calc
        (Real.sqrt 2 ^ r)^2 = Real.sqrt 2 ^ (r*2) := by rw [← pow_mul]
        _ = Real.sqrt 2 ^ (2*r) := by congr 1 <;> omega
        _ = (Real.sqrt 2 ^ 2)^r := by rw [pow_mul]
        _ = (2:ℝ)^r := by rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    simp only [hdisj, hdisj', hn, hr]
    rw [← mul_assoc, ← pow_two, hscale]
    norm_num [one_div, pow_succ]
    field_simp
    <;> ring
  · have hll : sourceDyadicLeftChild i ≠ sourceDyadicLeftChild j := by
      intro h
      exact hij (sourceDyadicLeftChild_injective h)
    have hrr : sourceDyadicRightChild i ≠ sourceDyadicRightChild j := by
      intro h
      exact hij (sourceDyadicRightChild_injective h)
    have hlr : sourceDyadicLeftChild i ≠ sourceDyadicRightChild j := by
      intro h
      have := congrArg Fin.val h
      dsimp [sourceDyadicLeftChild, sourceDyadicRightChild] at this
      omega
    have hrl : sourceDyadicRightChild i ≠ sourceDyadicLeftChild j := by
      intro h
      have := congrArg Fin.val h
      dsimp [sourceDyadicLeftChild, sourceDyadicRightChild] at this
      omega
    rw [sourceDyadicCellIndicator_orthogonal hll,
      sourceDyadicCellIndicator_orthogonal hlr,
      sourceDyadicCellIndicator_orthogonal hrl,
      sourceDyadicCellIndicator_orthogonal hrr]
    simp [hij]

theorem sourceDyadicCellIndicator_inner_eq_inter {n m : ℕ}
    (i : Fin (2^n)) (j : Fin (2^m)) :
    inner ℝ (sourceDyadicCellIndicator n i) (sourceDyadicCellIndicator m j) =
      (volume.restrict (Set.Icc (0:ℝ) 1)).real
        (sourceDyadicCell n i ∩ sourceDyadicCell m j) := by
  unfold sourceDyadicCellIndicator
  rw [MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
    (μ := volume.restrict (Set.Icc (0:ℝ) 1))
    (s := sourceDyadicCell n i) (t := sourceDyadicCell m j)
    (by simp [sourceDyadicCell]) (by simp [sourceDyadicCell])]

theorem sourceDyadicCellIndicator_parent_child_inner {r : ℕ}
    (j : Fin (2^r)) (left : Bool) :
    inner ℝ (sourceDyadicCellIndicator r j)
        (sourceDyadicCellIndicator (r+1)
          (if left then sourceDyadicLeftChild j else sourceDyadicRightChild j)) =
      1 / (2:ℝ)^(r+1) := by
  have hsub : sourceDyadicCell (r+1)
        (if left then sourceDyadicLeftChild j else sourceDyadicRightChild j) ⊆
      sourceDyadicCell r j := by
    cases left
    · simpa using sourceDyadic_rightChild_subset_parent j
    · simpa using sourceDyadic_leftChild_subset_parent j
  have hintersection : sourceDyadicCell r j ∩
      sourceDyadicCell (r+1)
        (if left then sourceDyadicLeftChild j else sourceDyadicRightChild j) =
      sourceDyadicCell (r+1)
        (if left then sourceDyadicLeftChild j else sourceDyadicRightChild j) :=
    Set.inter_eq_right.mpr hsub
  rw [sourceDyadicCellIndicator_inner_eq_inter, hintersection]
  calc
    (volume.restrict (Set.Icc (0:ℝ) 1)).real
        (sourceDyadicCell (r+1)
          (if left then sourceDyadicLeftChild j else sourceDyadicRightChild j))
        = inner ℝ
          (sourceDyadicCellIndicator (r+1)
            (if left then sourceDyadicLeftChild j else sourceDyadicRightChild j))
          (sourceDyadicCellIndicator (r+1)
            (if left then sourceDyadicLeftChild j else sourceDyadicRightChild j)) := by
              symm
              rw [sourceDyadicCellIndicator_inner_eq_inter]
              simp
    _ = 1 / (2:ℝ)^(r+1) := sourceDyadicCellIndicator_inner_self _

theorem sourceDyadicHaarMother_inner_parent {r : ℕ}
    (j k : Fin (2^r)) :
    inner ℝ (sourceDyadicHaarMother r j) (sourceDyadicCellIndicator r k) = 0 := by
  unfold sourceDyadicHaarMother
  rw [inner_smul_left, inner_sub_left]
  by_cases hjk : j = k
  · subst k
    have hleft := sourceDyadicCellIndicator_parent_child_inner j true
    have hright := sourceDyadicCellIndicator_parent_child_inner j false
    have hleft' : inner ℝ (sourceDyadicCellIndicator (r+1) (sourceDyadicLeftChild j))
        (sourceDyadicCellIndicator r j) = 1/(2:ℝ)^(r+1) := by
      rw [real_inner_comm]
      exact hleft
    have hright' : inner ℝ (sourceDyadicCellIndicator (r+1) (sourceDyadicRightChild j))
        (sourceDyadicCellIndicator r j) = 1/(2:ℝ)^(r+1) := by
      rw [real_inner_comm]
      exact hright
    rw [hleft', hright']
    ring
  · have hdisj : Disjoint (sourceDyadicCell r k) (sourceDyadicCell r j) :=
      sourceDyadicCells_disjoint (Ne.symm hjk)
    have hleftdisj : Disjoint (sourceDyadicCell r k)
        (sourceDyadicCell (r+1) (sourceDyadicLeftChild j)) := by
      exact Disjoint.mono_right (sourceDyadic_leftChild_subset_parent j) hdisj
    have hrightdisj : Disjoint (sourceDyadicCell r k)
        (sourceDyadicCell (r+1) (sourceDyadicRightChild j)) := by
      exact Disjoint.mono_right (sourceDyadic_rightChild_subset_parent j) hdisj
    have hzeroLeft := sourceDyadicCellIndicator_inner_eq_inter k
      (sourceDyadicLeftChild j)
    have hzeroRight := sourceDyadicCellIndicator_inner_eq_inter k
      (sourceDyadicRightChild j)
    have hleftempty := Set.disjoint_iff_inter_eq_empty.mp hleftdisj
    have hrightempty := Set.disjoint_iff_inter_eq_empty.mp hrightdisj
    rw [real_inner_comm, hzeroLeft, real_inner_comm, hzeroRight,
      hleftempty, hrightempty]
    simp

theorem sourceDyadicCellAverage_inner_mother {r : ℕ} (j : Fin (2^r))
    (f : ℝ → ℝ) :
    inner ℝ (sourceDyadicCellAverageApproximation r f)
      (sourceDyadicHaarMother r j) = 0 := by
  rw [real_inner_comm]
  unfold sourceDyadicCellAverageApproximation
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [inner_smul_right, sourceDyadicHaarMother_inner_parent]
  simp

/-- All normalized Haar-mother coefficients at one dyadic level are controlled
by the actual L² error of the cell-average approximation at the parent level.
This is the Hilbert-space Bessel bridge from cell oscillations to wavelet
energy, with no assumed Haar-tail estimate. -/
theorem sourceDyadicHaarMother_level_energy_le_cellAverage_error
    (r : ℕ) (f : SourceL2) :
    (∑ j : Fin (2^r),
      (inner ℝ (sourceDyadicHaarMother r j) f)^2) ≤
      ‖f-sourceDyadicCellAverageApproximation r
        (fun x => f x)‖^2 := by
  classical
  let e : Fin (2^r) → SourceL2 := fun j => sourceDyadicHaarMother r j
  let y : SourceL2 := f-sourceDyadicCellAverageApproximation r (fun x => f x)
  have horth : Orthonormal ℝ e := sourceDyadicHaarMother_orthonormal r
  have hB := horth.sum_inner_products_le y (s := Finset.univ)
  have hcoef : ∀ j : Fin (2^r), inner ℝ (e j) f = inner ℝ (e j) y := by
    intro j
    have hzero : inner ℝ (e j)
        (sourceDyadicCellAverageApproximation r (fun x => f x)) = 0 := by
      rw [real_inner_comm]
      exact sourceDyadicCellAverage_inner_mother j (fun x => f x)
    simp only [y, inner_sub_right, hzero, sub_zero]
  have hsum : (∑ j : Fin (2^r), (inner ℝ (e j) f)^2) =
      ∑ j : Fin (2^r), ‖inner ℝ (e j) y‖^2 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [hcoef j, Real.norm_eq_abs, sq_abs]
  calc
    (∑ j : Fin (2^r), (inner ℝ (e j) f)^2) =
        ∑ j : Fin (2^r), ‖inner ℝ (e j) y‖^2 := hsum
    _ ≤ ‖y‖^2 := by simpa [Real.norm_eq_abs, sq_abs] using hB
    _ = ‖f-sourceDyadicCellAverageApproximation r
        (fun x => f x)‖^2 := rfl

/-- Finite aggregate version: the energy in every Haar mother band from depth
`n` through `M-1` is bounded by the sum of the literal cell-average residuals
at those same depths. A separate scalar kernel estimate can now be summed
geometrically without any completeness assumption on the Haar family. -/
theorem sourceDyadicHaarMother_tail_energy_le_cellAverage_errors
    (n M : ℕ) (f : SourceL2) :
    (∑ r ∈ Finset.Ico n M,
      ∑ j : Fin (2^r), (inner ℝ (sourceDyadicHaarMother r j) f)^2) ≤
      ∑ r ∈ Finset.Ico n M,
        ‖f-sourceDyadicCellAverageApproximation r (fun x => f x)‖^2 := by
  apply Finset.sum_le_sum
  intro r hr
  exact sourceDyadicHaarMother_level_energy_le_cellAverage_error r f

/-- The cellwise squared residual of the actual causal-kernel L² vector is
integrable. This supplies the integrability side condition in the literal
cell-average residual identity, rather than assuming it. -/
theorem causalKernelVector_cell_residual_integrable
    {α t : ℝ} (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n : ℕ) (j : Fin (2^n)) :
    Integrable
      ((sourceDyadicCell n j).indicator
        (fun v => ((kernelVector α t hα ht0 ht1) v -
          average (volume.restrict (sourceDyadicCell n j))
            (fun x => (kernelVector α t hα ht0 ht1) x))^2))
      (volume.restrict (Set.Icc (0:ℝ) 1)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  let c : ℝ := average (volume.restrict (sourceDyadicCell n j))
    (fun x => (kernelVector α t hα ht0 ht1) x)
  have hf : MemLp (fun u : ℝ => (kernelVector α t hα ht0 ht1) u) 2 μ := by
    exact Lp.memLp (kernelVector α t hα ht0 ht1)
  have hc : MemLp (fun _ : ℝ => c) 2 μ := by
    dsimp [μ]
    exact memLp_const c
  have hdiff : MemLp
      (fun u : ℝ => (kernelVector α t hα ht0 ht1) u - c) 2 μ := by
    exact hf.sub hc
  have hsq := hdiff.integrable_sq
  have hlocal : Integrable
      ((sourceDyadicCell n j).indicator
        (fun v => ((kernelVector α t hα ht0 ht1) v - c)^2)) μ := by
    apply (integrable_indicator_iff measurableSet_Ico).2
    exact hsq.mono_measure Measure.restrict_le_self
  simpa [μ, c] using hlocal

/-- The actual causal-kernel feature's dyadic cell-average residual is exactly
the scalar interval-error sum from the fractional kernel analysis. The L²
representative is connected to the literal causal kernel by its proved
almost-everywhere realization, and all local integrability obligations are
discharged from its `Lp 2` membership. -/
theorem causalKernelVector_cellAverage_error_norm_sq
    {α t : ℝ} (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n : ℕ) :
    ‖kernelVector α t hα ht0 ht1 -
      sourceDyadicCellAverageApproximation n
        (fun x => (kernelVector α t hα ht0 ht1) x)‖^2 =
      ∑ j : Fin (2^n),
        causalKernelCellError α t (1/(2:ℝ)^n) j := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  let f : SourceL2 := kernelVector α t hα ht0 ht1
  let h : ℝ := 1/(2:ℝ)^n
  have hleft (j : Fin (2^n)) : sourceDyadicLeft n j = (j.val:ℝ)*h := by
    dsimp [sourceDyadicLeft, h]
    ring
  have hright (j : Fin (2^n)) : sourceDyadicRight n j =
      ((j.val+1:ℕ):ℝ)*h := by
    have hc : ((j.val+1:ℕ):ℝ) = (j.val:ℝ)+1 := by norm_num
    rw [hc]
    dsimp [sourceDyadicRight, h]
    push_cast
    ring_nf
  have hsubset (j : Fin (2^n)) : sourceDyadicCell n j ⊆ Set.Icc (0:ℝ) 1 := by
    intro u hu
    constructor
    · have hj : 0 ≤ sourceDyadicLeft n j := by
        unfold sourceDyadicLeft
        positivity
      exact le_trans hj hu.1
    · have hright' : sourceDyadicRight n j ≤ 1 := by
        unfold sourceDyadicRight
        apply (div_le_one (by positivity : (0:ℝ) < (2:ℝ)^n)).2
        have hj := j.isLt
        exact_mod_cast Nat.succ_le_of_lt hj
      exact le_trans hu.2.le hright'
  have hae : (kernelVector α t hα ht0 ht1 : ℝ → ℝ) =ᵐ[μ]
      (fun u => causalKernel α t u) := by
    exact MemLp.coeFn_toLp (causalKernel_memLp_unit hα ht0 ht1)
  have hresidual := sourceDyadicCellAverageApproximation_error_norm_sq n f
    (fun j => causalKernelVector_cell_residual_integrable hα ht0 ht1 n j)
  rw [hresidual]
  apply Finset.sum_congr rfl
  intro j hj
  have hmeasure : μ.restrict (sourceDyadicCell n j) =
      volume.restrict (sourceDyadicCell n j) := by
    change (volume.restrict (Set.Icc (0:ℝ) 1)).restrict
        (Set.Ico (sourceDyadicLeft n j) (sourceDyadicRight n j)) =
      volume.restrict (Set.Ico (sourceDyadicLeft n j) (sourceDyadicRight n j))
    rw [Measure.restrict_restrict measurableSet_Ico]
    congr 1
    exact Set.inter_eq_left.mpr (by simpa [sourceDyadicCell] using hsubset j)
  have haeCell : (fun u => f u) =ᵐ[
      volume.restrict (sourceDyadicCell n j)] (fun u => causalKernel α t u) := by
    have h' : (fun u => f u) =ᵐ[
        μ.restrict (sourceDyadicCell n j)] (fun u => causalKernel α t u) := by
      apply (ae_restrict_iff' measurableSet_Ico).2
      filter_upwards [hae] with u hu
      exact fun _ => hu
    simpa [hmeasure] using h'
  have havg : average (volume.restrict (sourceDyadicCell n j))
      (fun u => f u) =
      average (volume.restrict (sourceDyadicCell n j)) (causalKernel α t) := by
    exact average_congr haeCell
  have hintegral :
      (∫ u, (sourceDyadicCell n j).indicator
        (fun v => (f v - average (volume.restrict (sourceDyadicCell n j))
          (fun x => f x))^2) u ∂μ) =
      ∫ u, (sourceDyadicCell n j).indicator
        (fun v => (causalKernel α t v - average
          (volume.restrict (sourceDyadicCell n j)) (causalKernel α t))^2) u ∂μ := by
    apply integral_congr_ae
    filter_upwards [hae] with u hu
    by_cases hmem : u ∈ sourceDyadicCell n j
    · simpa [f, Set.indicator, hmem, hu, havg]
    · simp [Set.indicator, hmem]
  rw [hintegral]
  have hinterval := sourceDyadicCell_indicator_integral_eq_interval
    (a := sourceDyadicLeft n j) (b := sourceDyadicRight n j)
    (by
      rw [hleft, hright]
      have hc : ((j.val+1:ℕ):ℝ) = (j.val:ℝ)+1 := by norm_num
      have hj : (j.val:ℝ) < ((j.val+1:ℕ):ℝ) := by rw [hc]; linarith
      have hh : 0 < h := by dsimp [h]; positivity
      exact (mul_le_mul_of_nonneg_right hj.le hh.le))
    (by simpa [sourceDyadicCell] using hsubset j)
    (causalKernel α t)
  have hcell : sourceDyadicCell n j = Set.Ico
      (sourceDyadicLeft n j) (sourceDyadicRight n j) := rfl
  rw [hcell, hinterval]
  unfold causalKernelCellError
  rw [hleft, hright]

/-- Actual level-r Haar coefficients of the causal RL kernel are controlled
by the explicit finite sum of scalar cell oscillation integrals. -/
theorem causalKernelVector_haar_level_energy_le_cell_errors
    {α t : ℝ} (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n : ℕ) :
    (∑ j : Fin (2^n),
      (inner ℝ (sourceDyadicHaarMother n j)
        (kernelVector α t hα ht0 ht1))^2) ≤
      ∑ j : Fin (2^n),
        causalKernelCellError α t (1/(2:ℝ)^n) j := by
  calc
    (∑ j : Fin (2^n),
        (inner ℝ (sourceDyadicHaarMother n j)
          (kernelVector α t hα ht0 ht1))^2) ≤
        ‖kernelVector α t hα ht0 ht1 -
          sourceDyadicCellAverageApproximation n
            (fun x => (kernelVector α t hα ht0 ht1) x)‖^2 :=
      sourceDyadicHaarMother_level_energy_le_cellAverage_error n
        (kernelVector α t hα ht0 ht1)
    _ = ∑ j : Fin (2^n),
        causalKernelCellError α t (1/(2:ℝ)^n) j :=
      causalKernelVector_cellAverage_error_norm_sq hα ht0 ht1 n

/-- Uniform sharp scalar-order estimate for the actual normalized Haar band
of the causal Riemann--Liouville feature. The dyadic grid error theorem is
applied to a complete partition, and the preceding L² bridge identifies it
with genuine Haar coefficient energy. -/
theorem causalKernelVector_haar_level_energy_le_rate
    {α t : ℝ} (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) :
    (∑ j : Fin (2^n),
      (inner ℝ (sourceDyadicHaarMother n j)
        (kernelVector α t hα ht0 ht1))^2) ≤
      ((Real.Gamma α)⁻¹)^2 * (2 + 2^(2*α-1)/(2*α-1)) *
        (1/(2:ℝ)^n)^(min (2*α-1) 1) := by
  let h : ℝ := 1/(2:ℝ)^n
  have hh : 0 < h := by dsimp [h]; positivity
  have hM : 2 ≤ 2^n := by
    cases n with
    | zero => omega
    | succ n =>
        simpa [pow_succ] using
          (Nat.mul_le_mul_left 2 (Nat.one_le_two_pow (n := n)))
  have hgrid : ((2^n:ℕ):ℝ)*h = 1 := by
    rw [Nat.cast_pow, Nat.cast_ofNat]
    dsimp [h]
    field_simp
  have herror := causalKernel_dyadic_unit_cell_error_sum_le_rate
    hα ht0 ht1 hh hM hgrid
  have herror' :
      (∑ j : Fin (2^n),
        causalKernelCellError α t (1/(2:ℝ)^n) j) ≤
        ((Real.Gamma α)⁻¹)^2 *
          (2 + 2^(2*α-1)/(2*α-1)) *
          (1/(2:ℝ)^n)^(min (2*α-1) 1) := by
    simpa [h, Fin.sum_univ_eq_sum_range] using herror
  calc
    (∑ j : Fin (2^n),
        (inner ℝ (sourceDyadicHaarMother n j)
          (kernelVector α t hα ht0 ht1))^2) ≤
        ∑ j : Fin (2^n),
          causalKernelCellError α t (1/(2:ℝ)^n) j :=
      causalKernelVector_haar_level_energy_le_cell_errors hα ht0 ht1 n
    _ ≤ ((Real.Gamma α)⁻¹)^2 *
        (2 + 2^(2*α-1)/(2*α-1)) *
        (1/(2:ℝ)^n)^(min (2*α-1) 1) := herror'

/-- Every finite tail of actual causal-kernel Haar coefficients is bounded by
the corresponding finite sum of scalar dyadic cell errors. -/
theorem causalKernelVector_haar_tail_energy_le_cell_errors
    {α t : ℝ} (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n M : ℕ) :
    (∑ r ∈ Finset.Ico n M,
      ∑ j : Fin (2^r),
        (inner ℝ (sourceDyadicHaarMother r j)
          (kernelVector α t hα ht0 ht1))^2) ≤
      ∑ r ∈ Finset.Ico n M,
        ∑ j : Fin (2^r),
          causalKernelCellError α t (1/(2:ℝ)^r) j := by
  apply Finset.sum_le_sum
  intro r hr
  exact causalKernelVector_haar_level_energy_le_cell_errors hα ht0 ht1 r

/-- If the scalar cell-error bands obey a geometric rate, then the actual
finite Haar coefficient tail inherits the corresponding geometric bound. -/
theorem causalKernelVector_haar_tail_energy_le_geometric
    {α t C q : ℝ} (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n M : ℕ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (herr : ∀ r ∈ Finset.Ico n M,
      (∑ j : Fin (2^r),
        causalKernelCellError α t (1/(2:ℝ)^r) j) ≤ C*q^r) :
    (∑ r ∈ Finset.Ico n M,
      ∑ j : Fin (2^r),
        (inner ℝ (sourceDyadicHaarMother r j)
          (kernelVector α t hα ht0 ht1))^2) ≤ C*q^n/(1-q) := by
  calc
    (∑ r ∈ Finset.Ico n M,
        ∑ j : Fin (2^r),
          (inner ℝ (sourceDyadicHaarMother r j)
            (kernelVector α t hα ht0 ht1))^2) ≤
        ∑ r ∈ Finset.Ico n M,
          ∑ j : Fin (2^r),
            causalKernelCellError α t (1/(2:ℝ)^r) j :=
      causalKernelVector_haar_tail_energy_le_cell_errors hα ht0 ht1 n M
    _ ≤ ∑ r ∈ Finset.Ico n M, C*q^r := by
      apply Finset.sum_le_sum
      intro r hr
      exact herr r hr
    _ = C * (∑ r ∈ Finset.Ico n M, q^r) := by rw [Finset.mul_sum]
    _ ≤ C*q^n/(1-q) := by
      calc
        C * (∑ r ∈ Finset.Ico n M, q^r) ≤ C*(q^n/(1-q)) :=
          mul_le_mul_of_nonneg_left
            (geom_sum_Ico_le_of_lt_one hq0 hq1) hC
        _ = C*q^n/(1-q) := by
          field_simp [ne_of_gt (sub_pos.mpr hq1)]

end BrownianSharp.AlignmentGaussianFractionalHaar
