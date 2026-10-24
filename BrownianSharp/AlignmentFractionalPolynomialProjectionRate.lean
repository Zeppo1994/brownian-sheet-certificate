import BrownianSharp.AlignmentFractionalPolynomialApproximation
import BrownianSharp.AlignmentFractionalPolynomialTaylorWitness
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Actual scalar-source projection residuals for dyadic piecewise-polynomial
spaces. The candidate is the causal-kernel Taylor polynomial on every cell
strictly left of the singularity and zero on the remaining cells. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentFractionalPolynomialProjectionRate

open BrownianSharp.AlignmentFractionalPolynomialApproximation
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalPolynomialWitness
open BrownianSharp.AlignmentFractionalPolynomialTaylorWitness
open BrownianSharp.AlignmentFractionalDyadicProjection
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalKernel

abbrev SourceL2 := AlignmentFractionalL2.UnitL2

/-- The source-space vector obtained by putting the order-`q` Taylor model on
the first `N` cells and zero on the remaining cells. -/
def causalKernelTaylorGridVector (α t : ℝ) (q n N : ℕ) : SourceL2 :=
  ∑ j : Fin (2^n),
    if j.val < N then
      cellTaylorVector q n j (fun z : ℝ => z^(α-1))
        (Set.Icc (t-sourceDyadicRight n j) (t-sourceDyadicLeft n j))
        (t-sourceDyadicRight n j) t (Real.Gamma α)⁻¹
    else 0

theorem causalKernelTaylorGridVector_mem (α t : ℝ) (q n N : ℕ) :
    causalKernelTaylorGridVector α t q n N ∈ piecewisePolynomials q n := by
  classical
  unfold causalKernelTaylorGridVector
  apply Submodule.sum_mem
  intro j hj
  by_cases hjN : j.val < N
  · simp [hjN]
    exact cellTaylorVector_mem q n j _ _ _ _ _
  · simp [hjN]

/-- Scalar representative of the Taylor grid vector. -/
def causalKernelTaylorGridFunction (α t : ℝ) (q n N : ℕ) (u : ℝ) : ℝ :=
  ∑ j : Fin (2^n),
    if j.val < N then
      (sourceDyadicCell n j).indicator
        (fun v => causalKernelCellTaylorApprox α t
          (sourceDyadicLeft n j) (sourceDyadicRight n j) q v) u
    else 0

theorem causalKernelTaylorGridVector_coeFn_ae
    (α t : ℝ) (q n N : ℕ) (hq : 0 < q) :
    (causalKernelTaylorGridVector α t q n N : ℝ → ℝ) =ᵐ[
      volume.restrict (Set.Icc (0:ℝ) 1)] causalKernelTaylorGridFunction α t q n N := by
  classical
  change (↑(∑ j : Fin (2^n),
    if j.val < N then
      cellTaylorVector q n j (fun z : ℝ => z^(α-1))
        (Set.Icc (t-sourceDyadicRight n j) (t-sourceDyadicLeft n j))
        (t-sourceDyadicRight n j) t (Real.Gamma α)⁻¹
    else 0) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
      causalKernelTaylorGridFunction α t q n N
  have hs := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin (2^n)))
    (fun j : Fin (2^n) =>
      if j.val < N then
        cellTaylorVector q n j (fun z : ℝ => z^(α-1))
          (Set.Icc (t-sourceDyadicRight n j) (t-sourceDyadicLeft n j))
          (t-sourceDyadicRight n j) t (Real.Gamma α)⁻¹
      else 0)
  have ht : ∀ᵐ u ∂volume.restrict (Set.Icc (0:ℝ) 1),
      ∀ j : Fin (2^n),
        (if j.val < N then
          (if j.val < N then
            cellTaylorVector q n j (fun z : ℝ => z^(α-1))
              (Set.Icc (t-sourceDyadicRight n j) (t-sourceDyadicLeft n j))
              (t-sourceDyadicRight n j) t (Real.Gamma α)⁻¹ else 0) u
        else 0) =
          (if j.val < N then
            (sourceDyadicCell n j).indicator
              (fun v => causalKernelCellTaylorApprox α t
                (sourceDyadicLeft n j) (sourceDyadicRight n j) q v) u
          else 0) := by
    rw [ae_all_iff]
    intro j
    by_cases hj : j.val < N
    · filter_upwards [cellTaylorVector_coeFn q n j hq
        (fun z : ℝ => z^(α-1))
        (Set.Icc (t-sourceDyadicRight n j) (t-sourceDyadicLeft n j))
        (t-sourceDyadicRight n j) t (Real.Gamma α)⁻¹] with u hu
      simpa [hj, causalKernelCellTaylorApprox] using hu
    · simp [hj]
  have hz : ∀ᵐ u ∂volume.restrict (Set.Icc (0:ℝ) 1),
      ∀ j : Fin (2^n), (((0:SourceL2) : ℝ → ℝ) u = 0) := by
    rw [ae_all_iff]
    intro j
    exact Lp.coeFn_zero ℝ 2 (volume.restrict (Set.Icc (0:ℝ) 1))
  filter_upwards [hs, ht, hz] with u hs ht hz
  rw [hs]
  simp only [causalKernelTaylorGridFunction]
  refine Finset.sum_congr rfl ?_
  intro j hj
  by_cases hjN : j.val < N
  · simpa [hjN] using ht j
  · simpa [hjN] using hz j

private theorem sourceL2_norm_sq (f : SourceL2) :
    ‖f‖^2 = ∫ u, (f u)^2 ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext u
  simp [pow_two]

def causalKernelUnitVector (α t : ℝ) (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : SourceL2 :=
  (causalKernel_memLp_unit hα ht0 ht1).toLp (causalKernel α t)

def causalKernelTaylorCellResidual (α t : ℝ) (q n N : ℕ)
    (j : Fin (2^n)) (u : ℝ) : ℝ :=
  if j.val < N then
    causalKernel α t u - causalKernelCellTaylorApprox α t
      (sourceDyadicLeft n j) (sourceDyadicRight n j) q u
  else causalKernel α t u

theorem causalKernelTaylorGridFunction_eq_cell_candidate
    (α t : ℝ) (q n N : ℕ) (j : Fin (2^n)) {u : ℝ}
    (hu : u ∈ sourceDyadicCell n j) :
    causalKernelTaylorGridFunction α t q n N u =
      if j.val < N then causalKernelCellTaylorApprox α t
        (sourceDyadicLeft n j) (sourceDyadicRight n j) q u else 0 := by
  classical
  unfold causalKernelTaylorGridFunction
  rw [Finset.sum_eq_single j]
  · simp [hu]
  · intro i hi hij
    have hnot : u ∉ sourceDyadicCell n i := by
      intro hmem
      exact (Set.disjoint_left.mp
        (sourceDyadicCells_disjoint hij)) hmem hu
    simp [hnot]
  · simp

theorem causalKernelTaylorResidual_partition_ae
    (α t : ℝ) (q n N : ℕ) :
    (fun u =>
      (causalKernel α t u - causalKernelTaylorGridFunction α t q n N u)^2) =ᵐ[
        volume.restrict (Set.Icc (0:ℝ) 1)]
      (fun u => ∑ j : Fin (2^n), (sourceDyadicCell n j).indicator
        (fun v => causalKernelTaylorCellResidual α t q n N j v ^ 2) u) := by
  classical
  filter_upwards [ae_restrict_mem measurableSet_Icc,
    Measure.ae_ne (volume.restrict (Set.Icc (0:ℝ) 1)) 1] with u hu hne
  have hu1 : u < 1 := lt_of_le_of_ne hu.2 hne
  obtain ⟨j, hj⟩ := sourceDyadicCell_cover hu.1 hu1
  have hres : causalKernel α t u - causalKernelTaylorGridFunction α t q n N u =
      causalKernelTaylorCellResidual α t q n N j u := by
    rw [causalKernelTaylorGridFunction_eq_cell_candidate α t q n N j hj]
    by_cases hjN : j.val < N <;>
      simp [causalKernelTaylorCellResidual, hjN]
  rw [hres]
  rw [Finset.sum_eq_single j]
  · simp [hj, causalKernelTaylorCellResidual]
  · intro i hi hij
    have hnot : u ∉ sourceDyadicCell n i := by
      intro hmem
      exact (Set.disjoint_left.mp
        (sourceDyadicCells_disjoint hij)) hmem hj
    simp [hnot]
  · simp

theorem sourceDyadicCell_indicator_integral_eq_interval
    {a b : ℝ} (hab : a ≤ b) (hsubset : Set.Ico a b ⊆ Set.Icc (0:ℝ) 1)
    (f : ℝ → ℝ) :
    (∫ u, (Set.Ico a b).indicator f u
      ∂(volume.restrict (Set.Icc (0:ℝ) 1))) = ∫ u in a..b, f u := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  have hrestrict : μ.restrict (Set.Ico a b) = volume.restrict (Set.Ico a b) := by
    dsimp [μ]
    rw [Measure.restrict_restrict measurableSet_Ico]
    rw [Set.inter_eq_left.mpr hsubset]
  have hcell : volume.restrict (Set.Ico a b) = volume.restrict (Set.Ioc a b) :=
    Measure.restrict_congr_set Ico_ae_eq_Ioc
  rw [integral_indicator measurableSet_Ico]
  change (∫ u, f u ∂(μ.restrict (Set.Ico a b))) = _
  rw [hrestrict, hcell, intervalIntegral.integral_of_le hab]

theorem causalKernelTaylorGridVector_error_norm_sq_eq
    (α t : ℝ) (q n N : ℕ) (hq : 0 < q) (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖causalKernelUnitVector α t hα ht0 ht1 -
        causalKernelTaylorGridVector α t q n N‖^2 =
      ∑ j : Fin (2^n),
        ∫ u, (sourceDyadicCell n j).indicator
          (fun v => causalKernelTaylorCellResidual α t q n N j v ^ 2) u
          ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
  classical
  let K := causalKernelUnitVector α t hα ht0 ht1
  let A := causalKernelTaylorGridVector α t q n N
  let D := K-A
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  have hK : (K : ℝ → ℝ) =ᵐ[μ] causalKernel α t :=
    MemLp.coeFn_toLp (causalKernel_memLp_unit hα ht0 ht1)
  have hA := causalKernelTaylorGridVector_coeFn_ae α t q n N hq
  have hD : (D : ℝ → ℝ) =ᵐ[μ]
      (fun u => causalKernel α t u - causalKernelTaylorGridFunction α t q n N u) := by
    filter_upwards [Lp.coeFn_sub K A, hK, hA] with u hsub hku hau
    change ((K-A : SourceL2) : ℝ → ℝ) u = _
    rw [hsub, Pi.sub_apply, hku, hau]
  have hnorm := sourceL2_norm_sq D
  have hnorm' : ‖D‖^2 = ∫ u,
      (causalKernel α t u - causalKernelTaylorGridFunction α t q n N u)^2 ∂μ := by
    rw [hnorm]
    apply integral_congr_ae
    filter_upwards [hD] with u hu
    rw [hu]
  have hpart := causalKernelTaylorResidual_partition_ae α t q n N
  have hglobal : Integrable (fun u => ((D : ℝ → ℝ) u)^2) μ :=
    (Lp.memLp D).integrable_sq
  have hlocalAE (j : Fin (2^n)) :
      (fun u => (sourceDyadicCell n j).indicator
        (fun v => causalKernelTaylorCellResidual α t q n N j v ^ 2) u) =ᵐ[μ]
      (fun u => (sourceDyadicCell n j).indicator
        (fun v => ((D : ℝ → ℝ) v)^2) u) := by
    filter_upwards [hD, ae_restrict_mem measurableSet_Icc] with u hdu hu
    by_cases hcell : u ∈ sourceDyadicCell n j
    · have happrox := causalKernelTaylorGridFunction_eq_cell_candidate
        α t q n N j hcell
      simp only [Set.indicator_of_mem hcell]
      rw [hdu, happrox]
      by_cases hjN : j.val < N <;>
        simp [causalKernelTaylorCellResidual, hjN]
    · simp [hcell]
  have hlocalInt (j : Fin (2^n)) : Integrable
      (fun u => (sourceDyadicCell n j).indicator
        (fun v => causalKernelTaylorCellResidual α t q n N j v ^ 2) u) μ := by
    have hi := hglobal.indicator (show MeasurableSet (sourceDyadicCell n j) by
      exact measurableSet_Ico)
    exact hi.congr (hlocalAE j).symm
  have hsumInt := integral_finsetSum Finset.univ
    (fun j hj => hlocalInt j)
  rw [hnorm', integral_congr_ae hpart, hsumInt]

theorem sourceDyadicCell_subset_unit (n : ℕ) (j : Fin (2^n)) :
    sourceDyadicCell n j ⊆ Set.Icc (0:ℝ) 1 := by
  intro x hx
  have hden : 0 < (2:ℝ)^n := by positivity
  constructor
  · have hj0 : 0 ≤ (j.val:ℝ) := Nat.cast_nonneg _
    have hleft : 0 ≤ (j.val:ℝ)/(2:ℝ)^n := div_nonneg hj0 hden.le
    exact le_trans hleft hx.1
  · have hjright : ((j.val+1:ℕ):ℝ) ≤ (2:ℝ)^n := by
      have hjnat : j.val+1 ≤ 2^n := Nat.succ_le_of_lt j.isLt
      exact_mod_cast hjnat
    have hright : ((j.val+1:ℕ):ℝ)/(2:ℝ)^n ≤ 1 :=
      (div_le_iff₀ hden).2 (by nlinarith)
    exact le_trans hx.2.le hright

theorem sourceDyadicLeft_eq_mul_invGrid {n : ℕ} (j : Fin (2^n)) :
    sourceDyadicLeft n j = (j.val:ℝ) * ((2:ℝ)^n)⁻¹ := by
  simp [sourceDyadicLeft, div_eq_mul_inv]

theorem sourceDyadicRight_eq_succ_mul_invGrid {n : ℕ} (j : Fin (2^n)) :
    sourceDyadicRight n j = ((j.val+1:ℕ):ℝ) * ((2:ℝ)^n)⁻¹ := by
  simp [sourceDyadicRight, div_eq_mul_inv]

theorem causalKernel_intervalIntegral_sq_eq_zero_of_left
    {α t a b : ℝ} (hab : a ≤ b) (hta : t ≤ a) :
    (∫ u in a..b, (causalKernel α t u)^2) = 0 := by
  have hzero : Set.EqOn (fun u => (causalKernel α t u)^2)
      (fun _ => (0:ℝ)) (Set.uIcc a b) := by
    intro u hu
    have huI : u∈Set.Icc a b := by simpa [Set.uIcc_of_le hab] using hu
    have huab : a≤u := huI.1
    simp [causalKernel, le_trans hta huab]
  rw [intervalIntegral.integral_congr hzero]
  simp

/-- Explicit-grid projection estimate: the actual `L²` residual of the
degree-`q-1` piecewise polynomial projection is bounded by the Taylor
candidate error, whenever `N` isolates the singularity in its two adjacent
cells. -/
theorem causalKernel_polynomialProjection_residual_sq_le_explicit_rate
    {α t h : ℝ} {n q N : ℕ} (hq : 0 < q)
    (hα : 1/2 < α) (horder : α-1+1/2 < q)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hh : 0 < h)
    (hgrid : ((2^n:ℕ):ℝ)*h=1) (hN : N+2≤2^n)
    (hfar : ((N+1:ℕ):ℝ)*h≤t) (hnear : t≤((N+2:ℕ):ℝ)*h) :
    ‖causalKernelUnitVector α t hα ht0 ht1 -
      polynomialProjection q n (causalKernelUnitVector α t hα ht0 ht1)‖^2 ≤
      (((|(Real.Gamma α)⁻¹| *
          |(descPochhammer ℝ q).eval (α-1)| /
            (Nat.factorial (q-1):ℝ))^2 *
          (∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*(α-1-q))) +
        ((Real.Gamma α)⁻¹)^2 * (2^(2*α-1)/(2*α-1))) *
        h^(2*α-1)) := by
  classical
  let K := causalKernelUnitVector α t hα ht0 ht1
  let A := causalKernelTaylorGridVector α t q n N
  let Creg : ℝ :=
    ((|(Real.Gamma α)⁻¹| *
      |(descPochhammer ℝ q).eval (α-1)| /
        (Nat.factorial (q-1):ℝ))^2 *
      (∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*(α-1-q))))
  let Csing : ℝ := ((Real.Gamma α)⁻¹)^2 * (2^(2*α-1)/(2*α-1))
  have hN2 : N+2≤2^n := hN
  have hcast : ((2^n:ℕ):ℝ)=(2:ℝ)^n := by norm_num [Nat.cast_pow]
  have hInv : h=((2:ℝ)^n)⁻¹ := by
    rw [hcast] at hgrid
    have hden : (2:ℝ)^n≠0 := by positivity
    field_simp at hgrid ⊢
    nlinarith [hgrid]
  let E : Fin (2^n) → ℝ := fun j =>
    ∫ u, (sourceDyadicCell n j).indicator
      (fun v => causalKernelTaylorCellResidual α t q n N j v ^ 2) u
      ∂(volume.restrict (Set.Icc (0:ℝ) 1))
  have hleft (j : Fin (2^n)) : sourceDyadicLeft n j=(j.val:ℝ)*h := by
    rw [sourceDyadicLeft_eq_mul_invGrid, hInv]
  have hright (j : Fin (2^n)) : sourceDyadicRight n j=((j.val+1:ℕ):ℝ)*h := by
    rw [sourceDyadicRight_eq_succ_mul_invGrid, hInv]
  have hcellInt (j : Fin (2^n)) : E j =
      ∫ u in ((j.val:ℝ)*h)..(((j.val+1:ℕ):ℝ)*h),
        (causalKernelTaylorCellResidual α t q n N j u)^2 := by
    have hcell := sourceDyadicCell_indicator_integral_eq_interval
      (show sourceDyadicLeft n j≤sourceDyadicRight n j by
        unfold sourceDyadicLeft sourceDyadicRight
        apply (div_le_div_iff_of_pos_right (by positivity : 0<(2:ℝ)^n)).2
        exact_mod_cast Nat.le_succ j.val)
      (sourceDyadicCell_subset_unit n j)
      (fun v => causalKernelTaylorCellResidual α t q n N j v ^ 2)
    simpa [E, sourceDyadicCell, hleft j, hright j] using hcell
  have htail : ∀ j : Fin (2^n), N+2≤j.val → E j=0 := by
    intro j hj
    rw [hcellInt j]
    have hjcast : ((N+2:ℕ):ℝ)≤(j.val:ℝ) := by exact_mod_cast hj
    have htleft : t≤(j.val:ℝ)*h := by
      calc
        t≤((N+2:ℕ):ℝ)*h := hnear
        _≤(j.val:ℝ)*h := mul_le_mul_of_nonneg_right hjcast hh.le
    have hrightj : (j.val:ℝ)*h≤((j.val:ℝ)+1)*h := by
      nlinarith [hh]
    have hzero := causalKernel_intervalIntegral_sq_eq_zero_of_left
      (α:=α) (a:=(j.val:ℝ)*h) (b:=((j.val:ℝ)+1)*h) hrightj htleft
    have hcast'' : ((j.val+1:ℕ):ℝ)=(j.val:ℝ)+1 := by norm_num
    have hzero' :
        ∫ u in ((j.val:ℝ)*h)..(((j.val+1:ℕ):ℝ)*h),
          (causalKernel α t u)^2=0 := by simpa [hcast''] using hzero
    unfold causalKernelTaylorCellResidual
    have hnot : ¬ j.val<N := by omega
    simp [hnot, hcast'', hzero]
  have hsplit : (∑ j : Fin (2^n), E j) =
      (∑ j ∈ Finset.range N,
        ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
          (causalKernel α t u - causalKernelCellTaylorApprox α t
            ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h) q u)^2) +
       (∫ u in ((N:ℝ)*h)..(((N+1:ℕ):ℝ)*h), (causalKernel α t u)^2) +
       (∫ u in (((N+1:ℕ):ℝ)*h)..(((N+2:ℕ):ℝ)*h), (causalKernel α t u)^2) := by
    let eNat : ℕ → ℝ := fun j => if hj:j<2^n then E ⟨j,hj⟩ else 0
    have hsumFin : (∑ j : Fin (2^n), E j) = ∑ j ∈ Finset.range (2^n), eNat j := by
      calc
        (∑ j : Fin (2^n), E j) = ∑ j : Fin (2^n), eNat j.val := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [eNat]
        _ = ∑ j ∈ Finset.range (2^n), eNat j := Fin.sum_univ_eq_sum_range eNat (2^n)
    have htailSum : (∑ j ∈ Finset.Ico (N+2) (2^n), eNat j)=0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hjlt : j<2^n := (Finset.mem_Ico.mp hj).2
      have hjN : N+2≤j := (Finset.mem_Ico.mp hj).1
      simp [eNat, hjlt, htail ⟨j,hjlt⟩ hjN]
    rw [hsumFin, ← Finset.sum_range_add_sum_Ico eNat hN, htailSum,
      Finset.sum_range_succ, Finset.sum_range_succ]
    have hregular : ∑ j ∈ Finset.range N, eNat j =
        ∑ j ∈ Finset.range N,
          ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
            (causalKernel α t u - causalKernelCellTaylorApprox α t
              ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h) q u)^2 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < 2^n := by
        have hjN : j < N := Finset.mem_range.mp hj
        omega
      have he : eNat j = E ⟨j,hjlt⟩ := by simp [eNat, hjlt]
      rw [he, hcellInt]
      simp [causalKernelTaylorCellResidual, hleft ⟨j,hjlt⟩,
        hright ⟨j,hjlt⟩, Finset.mem_range.mp hj]
    have hNlt : N < 2^n := by omega
    have hN1lt : N+1 < 2^n := by omega
    have heN : eNat N = E ⟨N, hNlt⟩ := by simp [eNat, hNlt]
    have heN1 : eNat (N+1) = E ⟨N+1, hN1lt⟩ := by simp [eNat, hN1lt]
    rw [hregular, heN, heN1, hcellInt ⟨N, by omega⟩, hcellInt ⟨N+1, by omega⟩]
    simp [causalKernelTaylorCellResidual, show ¬ N<N by omega,
      show ¬ N+1<N by omega, add_assoc]
  have hnormeq := causalKernelTaylorGridVector_error_norm_sq_eq α t q n N hq hα ht0 ht1
  have hmem : A∈piecewisePolynomials q n := by
    exact causalKernelTaylorGridVector_mem α t q n N
  have hmin := polynomialProjection_residual_le q n K A hmem
  have hminsq : ‖K-polynomialProjection q n K‖^2≤‖K-A‖^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmin)
      (add_nonneg (norm_nonneg (K-polynomialProjection q n K)) (norm_nonneg (K-A)))]
  have hcalculus := causalKernel_full_grid_taylor_candidate_error_sum_le_rate
    hα hq horder hh hgrid hN hfar hnear
  have hcoef : 0≤Creg := by dsimp [Creg]; positivity
  have hsing : 0≤Csing := by
    dsimp [Csing]
    apply mul_nonneg (sq_nonneg _)
    apply div_nonneg (by positivity)
    linarith
  have hcandidate : ‖K-A‖^2 ≤ (Creg+Csing)*h^(2*α-1) := by
    rw [hnormeq, hsplit]
    simpa [Creg,Csing] using hcalculus
  calc
    ‖K-polynomialProjection q n K‖^2≤‖K-A‖^2 := hminsq
    _≤(Creg+Csing)*h^(2*α-1) := hcandidate
    _ = _ := by rfl

/-- Uniform dyadic version of the polynomial projection estimate. The cut is
chosen from the cell containing the singularity; when the singularity lies in
the first cell, its entire kernel energy is already of the required scale. -/
theorem causalKernel_polynomialProjection_residual_sq_le_dyadic_rate
    {α : ℝ} {q : ℕ} (hq : 0 < q) (hα : 1/2 < α)
    (horder : α-1+1/2 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ t : ℝ, (ht0 : 0 ≤ t) →
      (ht1 : t ≤ 1) →
      ‖causalKernelUnitVector α t hα ht0 ht1 -
        polynomialProjection q n
          (causalKernelUnitVector α t hα ht0 ht1)‖^2 ≤
        C * (1/(2:ℝ)^n)^(2*α-1) := by
  let Creg : ℝ :=
    ((|(Real.Gamma α)⁻¹| * |(descPochhammer ℝ q).eval (α-1)| /
      (Nat.factorial (q-1):ℝ))^2 *
      (∑' k : ℕ, ((k+1:ℕ):ℝ)^(2*(α-1-q))))
  let Csing : ℝ := ((Real.Gamma α)⁻¹)^2 * (2^(2*α-1)/(2*α-1))
  have hCreg0 : 0≤Creg := by dsimp [Creg]; positivity
  have hCsing0 : 0≤Csing := by
    dsimp [Csing]
    apply mul_nonneg (sq_nonneg _)
    apply div_nonneg (by positivity)
    linarith
  refine ⟨Creg+Csing+1, by linarith, ?_⟩
  intro n hn t ht0 ht1
  let M : ℕ := 2^n
  let h : ℝ := 1/(2:ℝ)^n
  have hM : M = 2^n := rfl
  have hcast : (M:ℝ)=(2:ℝ)^n := by dsimp [M]; norm_num [Nat.cast_pow]
  have hpos : 0<h := by dsimp [h]; positivity
  have hgrid : (M:ℝ)*h=1 := by dsimp [h]; rw [hcast]; field_simp
  have hNbase : 2 ≤ M := by
    dsimp [M]
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
    calc 2 = 2^1 := by norm_num
         _ ≤ 2^(k+1) := by gcongr
  have htarget : 0≤(1/(2:ℝ)^n)^(2*α-1) := by positivity
  by_cases hsmall : t≤h
  · let K := causalKernelUnitVector α t hα ht0 ht1
    have hzeroMem : (0:SourceL2) ∈ piecewisePolynomials q n :=
      (piecewisePolynomials q n).zero_mem
    have hmin := polynomialProjection_residual_le q n K 0 hzeroMem
    have hmin' : ‖K-polynomialProjection q n K‖≤‖K‖ := by simpa using hmin
    have hminsq : ‖K-polynomialProjection q n K‖^2≤‖K‖^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hmin')
        (add_nonneg (norm_nonneg (K-polynomialProjection q n K)) (norm_nonneg K))]
    have hnorm := sourceL2_norm_sq K
    have hKae : (K : ℝ→ℝ)=ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)] causalKernel α t :=
      MemLp.coeFn_toLp (causalKernel_memLp_unit hα ht0 ht1)
    have hnormK : ‖K‖^2 = ∫ u, (causalKernel α t u)^2
        ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
      rw [hnorm]
      apply integral_congr_ae
      filter_upwards [hKae] with u hu
      rw [hu]
    have hunit : (∫ u, (causalKernel α t u)^2
        ∂(volume.restrict (Set.Icc (0:ℝ) 1))) =
        ∫ u in (0:ℝ)..1, (causalKernel α t u)^2 := by
      rw [intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num)]
      rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    have hbase : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume 0 1 :=
      causalKernel_sq_intervalIntegrable_unit hα ht0 ht1
    have hbase0 : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume 0 t := by
      apply hbase.mono_set
      rw [Set.uIcc_of_le ht0, Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      exact Set.Icc_subset_Icc le_rfl ht1
    have hbase1 : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume t 1 := by
      apply hbase.mono_set
      rw [Set.uIcc_of_le ht1, Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
      exact Set.Icc_subset_Icc ht0 le_rfl
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      hbase0 hbase1
    have hfirst := causalKernel_singular_cell_energy hα (by norm_num : (0:ℝ)≤0)
      ht0 (le_rfl : t≤t) ht1
    have htail := causalKernel_intervalIntegral_sq_eq_zero_of_left
      (α:=α) (a:=t) (b:=1) ht1 le_rfl
    have henergy : ‖K‖^2 = ((Real.Gamma α)⁻¹)^2 *
        (t^(2*α-1)/(2*α-1)) := by
      rw [hnormK, hunit, ← hsplit, hfirst, htail]
      ring_nf
    have hpow : t^(2*α-1)≤h^(2*α-1) := by
      apply Real.rpow_le_rpow ht0 hsmall
      linarith
    have hheq : h^(2*α-1)=(1/(2:ℝ)^n)^(2*α-1) := by rfl
    calc
      ‖K-polynomialProjection q n K‖^2≤‖K‖^2 := hminsq
      _=((Real.Gamma α)⁻¹)^2*(t^(2*α-1)/(2*α-1)) := henergy
      _≤Csing*h^(2*α-1) := by
        dsimp [Csing]
        have hp : 0<2*α-1 := by linarith
        have htwo : 1≤(2:ℝ)^(2*α-1) := by
          exact Real.one_le_rpow (by norm_num) (by linarith)
        have hcoef : 0≤((Real.Gamma α)⁻¹)^2 := sq_nonneg _
        calc
          _ ≤ ((Real.Gamma α)⁻¹)^2*(h^(2*α-1)/(2*α-1)) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hpow hp.le) hcoef
          _ ≤ ((Real.Gamma α)⁻¹)^2*((2:ℝ)^(2*α-1)*(h^(2*α-1)/(2*α-1))) := by
            apply mul_le_mul_of_nonneg_left _ hcoef
            exact le_mul_of_one_le_left (by positivity) htwo
          _ = Csing*h^(2*α-1) := by dsimp [Csing]; ring
      _≤(Creg+Csing+1)*(1/(2:ℝ)^n)^(2*α-1) := by
        rw [hheq]
        nlinarith [mul_nonneg htarget (by linarith : 0≤Creg+1)]
  · have hlarge : h<t := lt_of_not_ge hsmall
    by_cases htone : t=1
    · subst t
      let N := M-2
      have hNm : N+2≤M := by dsimp [N]; omega
      have hfar : ((N+1:ℕ):ℝ)*h≤1 := by
        dsimp [N]
        have hcastM : (M:ℝ)*h=1 := hgrid
        have hm : ((M-1:ℕ):ℝ)≤M := by exact_mod_cast (Nat.sub_le M 1)
        calc ((M-2+1:ℕ):ℝ)*h ≤ (M:ℝ)*h := by
                apply mul_le_mul_of_nonneg_right _ hpos.le
                exact_mod_cast (by omega : M-2+1≤M)
             _=1 := hgrid
      have hnear : (1:ℝ)≤((N+2:ℕ):ℝ)*h := by
        dsimp [N]
        have hcastM' : ((M-2+2:ℕ):ℝ)=(M:ℝ) := by congr 1 <;> omega
        rw [hcastM']
        linarith [hgrid]
      have hex := causalKernel_polynomialProjection_residual_sq_le_explicit_rate
        hq hα horder (by norm_num) (by norm_num) hpos hgrid hNm hfar hnear
      have hpow : h^(2*α-1)=(1/(2:ℝ)^n)^(2*α-1) := by rfl
      rw [hpow] at hex
      dsimp [Creg,Csing]
      nlinarith [hex, hCreg0, hCsing0, htarget]
    · have htlt : t<1 := lt_of_le_of_ne ht1 htone
      obtain ⟨j,hj⟩ := sourceDyadicCell_cover ht0 htlt
      have hjl : sourceDyadicLeft n j≤t := hj.1
      have hjr : t<sourceDyadicRight n j := hj.2
      have hleft : sourceDyadicLeft n j=(j.val:ℝ)*h := by
        rw [sourceDyadicLeft_eq_mul_invGrid]
        rw [show h=((2:ℝ)^n)⁻¹ by dsimp [h]; field_simp]
      have hright : sourceDyadicRight n j=((j.val+1:ℕ):ℝ)*h := by
        rw [sourceDyadicRight_eq_succ_mul_invGrid]
        rw [show h=((2:ℝ)^n)⁻¹ by dsimp [h]; field_simp]
      have hjpos : 1≤j.val := by
        by_contra hhj
        have hjzero : j.val=0 := by omega
        rw [hleft, hjzero] at hjl
        rw [hright, hjzero] at hjr
        norm_num at hjr
        linarith
      let N := j.val-1
      have hN : N+2≤M := by
        dsimp [N,M]
        have hjlt : j.val<2^n := j.isLt
        omega
      have hfar : ((N+1:ℕ):ℝ)*h≤t := by
        have hN1 : N+1=j.val := by dsimp [N]; omega
        rw [hN1, ← hleft]
        exact hjl
      have hnear : t≤((N+2:ℕ):ℝ)*h := by
        have hN2 : N+2=j.val+1 := by dsimp [N]; omega
        have hle : t≤sourceDyadicRight n j := le_of_lt hjr
        rw [hright] at hle
        rw [hN2]
        exact hle
      have hex := causalKernel_polynomialProjection_residual_sq_le_explicit_rate
        hq hα horder ht0 ht1 hpos hgrid hN hfar hnear
      have hpow : h^(2*α-1)=(1/(2:ℝ)^n)^(2*α-1) := by rfl
      rw [hpow] at hex
      dsimp [Creg,Csing]
      nlinarith [hex, hCreg0, hCsing0, htarget]

/-- Every order above one half admits a finite degree for the sharp dyadic
source-projection residual rate. -/
theorem exists_degree_causalKernel_polynomialProjection_dyadic_rate
    {α : ℝ} (hα : 1/2 < α) :
    ∃ q : ℕ, ∃ C : ℝ, 0<q ∧ 0<C ∧
      ∀ n : ℕ, 1≤n → ∀ t : ℝ, (ht0 : 0≤t) → (ht1 : t≤1) →
        ‖causalKernelUnitVector α t hα ht0 ht1 -
          polynomialProjection q n (causalKernelUnitVector α t hα ht0 ht1)‖^2 ≤
          C*(1/(2:ℝ)^n)^(2*α-1) := by
  obtain ⟨q,hq⟩ := exists_nat_gt (α+1)
  have hqreal : (0:ℝ)<(q:ℝ) := by linarith
  have hqpos : 0<q := by exact_mod_cast hqreal
  have horder : α-1+1/2<(q:ℝ) := by linarith
  obtain ⟨C,hC,hbound⟩ :=
    causalKernel_polynomialProjection_residual_sq_le_dyadic_rate hqpos hα horder
  exact ⟨q,C,hqpos,hC,hbound⟩

end BrownianSharp.AlignmentFractionalPolynomialProjectionRate
