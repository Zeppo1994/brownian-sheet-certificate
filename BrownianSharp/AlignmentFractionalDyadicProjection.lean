import BrownianSharp.AlignmentFractionalHolder
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-! A quantitative cellwise approximation estimate for the scalar RL kernel.

The local estimate below is the elementary variance bound behind projection
onto dyadic piecewise constants. For monotone nonnegative functions, the
cellwise oscillation telescopes after squaring, while the singular first cell
is controlled by its exact power integral.
-/

noncomputable section
open MeasureTheory
open BrownianSharp.AlignmentFractionalKernel
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalHolder
open BrownianSharp.AlignmentFractionalL2

namespace BrownianSharp.AlignmentFractionalDyadicProjection

abbrev SourceL2 := AlignmentFractionalL2.UnitL2

/-- Left endpoint of a dyadic source cell. -/
def sourceDyadicLeft (n : ℕ) (j : Fin (2^n)) : ℝ :=
  (j.val : ℝ) / (2:ℝ)^n

/-- Right endpoint of a dyadic source cell. -/
def sourceDyadicRight (n : ℕ) (j : Fin (2^n)) : ℝ :=
  ((j.val+1 : ℕ) : ℝ) / (2:ℝ)^n

/-- The half-open dyadic cells partitioning the unit source interval. -/
def sourceDyadicCell (n : ℕ) (j : Fin (2^n)) : Set ℝ :=
  Set.Ico (sourceDyadicLeft n j) (sourceDyadicRight n j)

/-- The L² indicator of one dyadic source cell. -/
noncomputable def sourceDyadicCellIndicator (n : ℕ) (j : Fin (2^n)) : SourceL2 :=
  MeasureTheory.indicatorConstLp (μ := volume.restrict (Set.Icc (0:ℝ) 1))
    (s := sourceDyadicCell n j) 2 (measurableSet_Ico)
    (by exact measure_ne_top _ _) (1:ℝ)

theorem sourceDyadicCellIndicator_coeFn (n : ℕ) (j : Fin (2^n)) :
    (sourceDyadicCellIndicator n j : ℝ → ℝ) =ᵐ[
      volume.restrict (Set.Icc (0:ℝ) 1)]
        (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) := by
  unfold sourceDyadicCellIndicator
  exact indicatorConstLp_coeFn

theorem sourceDyadicCells_disjoint {n : ℕ} {i j : Fin (2^n)} (hij : i ≠ j) :
    Disjoint (sourceDyadicCell n i) (sourceDyadicCell n j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne (fun heq => hij (Fin.ext heq)) with hlt | hlt
  · have hstep : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hlt
    have hcast : ((i.val+1:ℕ):ℝ) ≤ (j.val:ℝ) := by exact_mod_cast hstep
    have hden : 0 < (2:ℝ)^n := by positivity
    have hend : sourceDyadicRight n i ≤ sourceDyadicLeft n j := by
      unfold sourceDyadicRight sourceDyadicLeft
      exact (div_le_div_iff_of_pos_right hden).2 hcast
    have hxilt : x < sourceDyadicRight n i := hxi.2
    have hxjle : sourceDyadicLeft n j ≤ x := hxj.1
    linarith
  · have hstep : j.val + 1 ≤ i.val := Nat.succ_le_of_lt hlt
    have hcast : ((j.val+1:ℕ):ℝ) ≤ (i.val:ℝ) := by exact_mod_cast hstep
    have hden : 0 < (2:ℝ)^n := by positivity
    have hend : sourceDyadicRight n j ≤ sourceDyadicLeft n i := by
      unfold sourceDyadicRight sourceDyadicLeft
      exact (div_le_div_iff_of_pos_right hden).2 hcast
    have hxjlt : x < sourceDyadicRight n j := hxj.2
    have hxile : sourceDyadicLeft n i ≤ x := hxi.1
    linarith

theorem sourceDyadicCell_cover {n : ℕ} {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∃ j : Fin (2^n), x ∈ sourceDyadicCell n j := by
  let M : ℝ := (2:ℝ)^n
  let q : ℕ := Nat.floor (x*M)
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hMcast : ((2^n:ℕ):ℝ) = M := by
    dsimp [M]
    norm_num [Nat.cast_pow]
  have hfloorle : (q:ℝ) ≤ x*M := by
    exact Nat.floor_le (mul_nonneg hx0 hMpos.le)
  have hltfloor : x*M < (q:ℝ)+1 := by
    exact Nat.lt_floor_add_one (x*M)
  have hqMreal : (q:ℝ) < (2^n:ℕ) := by
    rw [hMcast]
    calc
      (q:ℝ) ≤ x*M := hfloorle
      _ < M := by nlinarith [mul_lt_mul_of_pos_right hx1 hMpos]
  have hqM : q < 2^n := by exact_mod_cast hqMreal
  refine ⟨⟨q,hqM⟩, ?_⟩
  unfold sourceDyadicCell sourceDyadicLeft sourceDyadicRight
  dsimp
  constructor
  · apply (div_le_iff₀ hMpos).2
    exact hfloorle
  · apply (lt_div_iff₀ hMpos).2
    have hcast : ((q+1:ℕ):ℝ) = (q:ℝ)+1 := by norm_num
    rw [hcast]
    exact hltfloor

theorem sourceDyadicCell_indicator_sum_eq_one_ae (n : ℕ) :
    ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1),
      (∑ j : Fin (2^n), (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) x) = 1 := by
  let μ := volume.restrict (Set.Icc (0:ℝ) 1)
  filter_upwards [ae_restrict_mem measurableSet_Icc, Measure.ae_ne μ 1] with x hx hne
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hne
  obtain ⟨j, hj⟩ := sourceDyadicCell_cover hx.1 hxlt
  have hsum : (∑ i : Fin (2^n), (sourceDyadicCell n i).indicator
      (fun _ => (1:ℝ)) x) =
      (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) x := by
    rw [Finset.sum_eq_single j]
    · intro i hi hij
      have hnot : x ∉ sourceDyadicCell n i := by
        intro hxi
        have hdisj := sourceDyadicCells_disjoint hij
        exact (Set.disjoint_left.mp hdisj) hxi hj
      simp [hnot]
    · simp [hj]
  rw [hsum]
  simp [Set.indicator, hj]

theorem sourceDyadicCellIndicator_orthogonal {n : ℕ} {i j : Fin (2^n)}
    (hij : i ≠ j) : inner ℝ (sourceDyadicCellIndicator n i)
      (sourceDyadicCellIndicator n j) = 0 := by
  unfold sourceDyadicCellIndicator
  rw [MeasureTheory.L2.real_inner_indicatorConstLp_one_indicatorConstLp_one
    (μ := volume.restrict (Set.Icc (0:ℝ) 1))
    (s := sourceDyadicCell n i) (t := sourceDyadicCell n j)
    (by simp [sourceDyadicCell]) (by simp [sourceDyadicCell])]
  have hdisj := sourceDyadicCells_disjoint hij
  have hempty : sourceDyadicCell n i ∩ sourceDyadicCell n j = ∅ := Set.disjoint_iff_inter_eq_empty.mp hdisj
  simp [hempty]

/-- Piecewise constants on the depth-`n` dyadic source partition. -/
def sourceDyadicPiecewiseConstants (n : ℕ) : Submodule ℝ SourceL2 :=
  Submodule.span ℝ (Set.range (sourceDyadicCellIndicator n))

instance sourceDyadicPiecewiseConstants_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (sourceDyadicPiecewiseConstants n) := by
  unfold sourceDyadicPiecewiseConstants
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

/-- Orthogonal projection in the actual source Hilbert space onto dyadic
piecewise constants. -/
noncomputable def sourceDyadicOrthogonalProjection (n : ℕ) :
    SourceL2 →L[ℝ] SourceL2 :=
  (sourceDyadicPiecewiseConstants n).starProjection

/-- The literal finite piecewise-constant candidate whose value on each
dyadic source cell is the cell average of `f`. -/
noncomputable def sourceDyadicCellAverageApproximation (n : ℕ) (f : ℝ → ℝ) : SourceL2 :=
  ∑ j : Fin (2^n),
    average (volume.restrict (sourceDyadicCell n j)) f • sourceDyadicCellIndicator n j

theorem sourceDyadicCellAverageApproximation_coeFn_ae
    (n : ℕ) (f : ℝ → ℝ) :
    (sourceDyadicCellAverageApproximation n f : ℝ → ℝ) =ᵐ[
      volume.restrict (Set.Icc (0:ℝ) 1)]
      (fun x => ∑ j : Fin (2^n),
        average (volume.restrict (sourceDyadicCell n j)) f *
          (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) x) := by
  have hsum : (sourceDyadicCellAverageApproximation n f : ℝ → ℝ) =ᵐ[
      volume.restrict (Set.Icc (0:ℝ) 1)]
      (fun x => ∑ j : Fin (2^n),
        (average (volume.restrict (sourceDyadicCell n j)) f •
          sourceDyadicCellIndicator n j) x) := by
    simpa [sourceDyadicCellAverageApproximation] using
      (Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin (2^n)))
        (fun j => average (volume.restrict (sourceDyadicCell n j)) f •
          sourceDyadicCellIndicator n j))
  have hterms : ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1),
      ∀ j : Fin (2^n),
        (average (volume.restrict (sourceDyadicCell n j)) f •
          sourceDyadicCellIndicator n j) x =
        average (volume.restrict (sourceDyadicCell n j)) f *
          (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) x := by
    rw [ae_all_iff]
    intro j
    have hs := Lp.coeFn_smul
      (average (volume.restrict (sourceDyadicCell n j)) f)
      (sourceDyadicCellIndicator n j)
    have hi := sourceDyadicCellIndicator_coeFn n j
    filter_upwards [hs, hi] with x hsx hix
    calc
      ((average (volume.restrict (sourceDyadicCell n j)) f) •
          sourceDyadicCellIndicator n j) x =
          average (volume.restrict (sourceDyadicCell n j)) f *
            (sourceDyadicCellIndicator n j) x := by simpa [smul_eq_mul] using hsx
      _ = average (volume.restrict (sourceDyadicCell n j)) f *
            (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) x := by rw [hix]
  filter_upwards [hsum, hterms] with x hx htx
  rw [hx]
  congr 1
  funext j
  exact htx j

theorem sourceDyadicCellAverageSum_value {n : ℕ} {f : ℝ → ℝ} {x : ℝ}
    {j : Fin (2^n)} (hj : x ∈ sourceDyadicCell n j) :
    (∑ i : Fin (2^n),
      average (volume.restrict (sourceDyadicCell n i)) f *
        (sourceDyadicCell n i).indicator (fun _ => (1:ℝ)) x) =
      average (volume.restrict (sourceDyadicCell n j)) f := by
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro i hi hij
    have hnot : x ∉ sourceDyadicCell n i := by
      intro hxi
      have hdisj := sourceDyadicCells_disjoint hij
      exact (Set.disjoint_left.mp hdisj) hxi hj
    simp [hnot]
  · simp

theorem sourceDyadicCellAverage_residual_sq_partition_ae
    (n : ℕ) (f : ℝ → ℝ) :
    (fun x => (f x - ∑ j : Fin (2^n),
      average (volume.restrict (sourceDyadicCell n j)) f *
        (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) x)^2) =ᵐ[
      volume.restrict (Set.Icc (0:ℝ) 1)]
    (fun x => ∑ j : Fin (2^n),
      (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) x *
        (f x - average (volume.restrict (sourceDyadicCell n j)) f)^2) := by
  let μ := volume.restrict (Set.Icc (0:ℝ) 1)
  filter_upwards [ae_restrict_mem measurableSet_Icc, Measure.ae_ne μ 1] with x hx hne
  have hxlt : x < 1 := lt_of_le_of_ne hx.2 hne
  obtain ⟨j, hj⟩ := sourceDyadicCell_cover hx.1 hxlt
  have hmean := sourceDyadicCellAverageSum_value (f := f) hj
  have hres : (∑ i : Fin (2^n),
      (sourceDyadicCell n i).indicator (fun _ => (1:ℝ)) x *
        (f x - average (volume.restrict (sourceDyadicCell n i)) f)^2) =
      (f x - average (volume.restrict (sourceDyadicCell n j)) f)^2 := by
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i hi hij
      have hnot : x ∉ sourceDyadicCell n i := by
        intro hxi
        have hdisj := sourceDyadicCells_disjoint hij
        exact (Set.disjoint_left.mp hdisj) hxi hj
      simp [hnot]
    · simp
  rw [hres, hmean]

/-- The Hilbert norm on the unit-interval source is the integral of the
pointwise squared representative. -/
private theorem sourceL2_norm_sq (f : SourceL2) :
    ‖f‖^2 = ∫ u, (f u)^2 ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext u
  simp [pow_two]

/-- The literal cell-average residual norm is the sum of the scalar local
residual integrals, provided those local residuals are integrable. -/
theorem sourceDyadicCellAverageApproximation_error_norm_sq
    (n : ℕ) (f : SourceL2)
    (hlocal : ∀ j : Fin (2^n),
      Integrable (fun u => (sourceDyadicCell n j).indicator
        (fun v => (f v -
          average (volume.restrict (sourceDyadicCell n j)) (fun x => f x))^2) u)
        (volume.restrict (Set.Icc (0:ℝ) 1))) :
    ‖f-sourceDyadicCellAverageApproximation n (fun x => f x)‖^2 =
      ∑ j : Fin (2^n),
        ∫ u, (sourceDyadicCell n j).indicator
          (fun v => (f v -
            average (volume.restrict (sourceDyadicCell n j)) (fun x => f x))^2) u
          ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  let c : (Fin (2^n)) → ℝ := fun j =>
    average (volume.restrict (sourceDyadicCell n j)) (fun x => f x)
  have happrox := sourceDyadicCellAverageApproximation_coeFn_ae n (fun x => f x)
  have hpart := sourceDyadicCellAverage_residual_sq_partition_ae n (fun x => f x)
  have hres : (fun u => (f u -
      sourceDyadicCellAverageApproximation n (fun x => f x) u)^2) =ᵐ[μ]
      (fun u => (f u - ∑ j : Fin (2^n),
        c j * (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) u)^2) := by
    filter_upwards [happrox] with u hu
    rw [hu]
  have hnorm := sourceL2_norm_sq
    (f-sourceDyadicCellAverageApproximation n (fun x => f x))
  have hsub : (↑(f-sourceDyadicCellAverageApproximation n
      (fun x => f x)) : ℝ → ℝ) =ᵐ[μ]
      ((↑f : ℝ → ℝ) -
        (↑(sourceDyadicCellAverageApproximation n (fun x => f x)) : ℝ → ℝ)) := by
    simpa [μ] using (Lp.coeFn_sub f
      (sourceDyadicCellAverageApproximation n (fun x => f x)))
  have hnorm' : ‖f-sourceDyadicCellAverageApproximation n (fun x => f x)‖^2 =
      ∫ u, (f u-sourceDyadicCellAverageApproximation n (fun x => f x) u)^2 ∂μ := by
    rw [hnorm]
    exact integral_congr_ae (hsub.mono fun u hu => congrArg (fun x : ℝ => x^2) hu)
  rw [hnorm']
  have hpartition := integral_congr_ae hpart
  have hpartition' :
      ∫ u, (f u - ∑ j : Fin (2^n),
        c j * (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) u)^2 ∂μ =
      ∫ u, ∑ j : Fin (2^n),
        (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) u *
          (f u-c j)^2 ∂μ := by
    simpa [μ,c] using hpartition
  have hresint :
      ∫ u, (f u-sourceDyadicCellAverageApproximation n (fun x => f x) u)^2 ∂μ =
      ∫ u, (f u - ∑ j : Fin (2^n),
        c j * (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) u)^2 ∂μ :=
    integral_congr_ae hres
  rw [hresint, hpartition']
  have hsumrep :
      (fun u => ∑ j : Fin (2^n),
        (sourceDyadicCell n j).indicator (fun _ => (1:ℝ)) u * (f u-c j)^2) =ᵐ[μ]
      (fun u => ∑ j : Fin (2^n), (sourceDyadicCell n j).indicator
        (fun v => (f v-c j)^2) u) := by
    filter_upwards with u
    congr 1
    funext j
    simp [Set.indicator]
  rw [integral_congr_ae hsumrep]
  rw [integral_finsetSum Finset.univ (fun j hj => hlocal j)]

/-- A dyadic cell's indicator integral in the restricted unit source equals
the ordinary interval integral on that cell; endpoint conventions do not
change the average or the integral. -/
theorem sourceDyadicCell_indicator_integral_eq_interval
    {a b : ℝ} (hab : a ≤ b) (hsubset : Set.Ico a b ⊆ Set.Icc (0:ℝ) 1)
    (f : ℝ → ℝ) :
    (∫ u, (Set.Ico a b).indicator
      (fun v => (f v-average (volume.restrict (Set.Ico a b)) f)^2) u
      ∂(volume.restrict (Set.Icc (0:ℝ) 1))) =
    ∫ u in a..b,
      (f u-average (volume.restrict (Set.Ioc a b)) f)^2 := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  have hrestrict : μ.restrict (Set.Ico a b) = volume.restrict (Set.Ico a b) := by
    dsimp [μ]
    rw [Measure.restrict_restrict measurableSet_Ico]
    rw [Set.inter_eq_left.mpr hsubset]
  have hcell : volume.restrict (Set.Ico a b) = volume.restrict (Set.Ioc a b) := by
    exact Measure.restrict_congr_set Ico_ae_eq_Ioc
  have havg : average (volume.restrict (Set.Ico a b)) f =
      average (volume.restrict (Set.Ioc a b)) f := by
    rw [average_eq, average_eq, hcell]
  rw [integral_indicator measurableSet_Ico]
  change (∫ u, (f u-average (volume.restrict (Set.Ico a b)) f)^2
      ∂(μ.restrict (Set.Ico a b))) = _
  rw [hrestrict, hcell, intervalIntegral.integral_of_le hab]

theorem sourceDyadicCellAverageApproximation_mem (n : ℕ) (f : ℝ → ℝ) :
    sourceDyadicCellAverageApproximation n f ∈ sourceDyadicPiecewiseConstants n := by
  rw [sourceDyadicPiecewiseConstants]
  unfold sourceDyadicCellAverageApproximation
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨j, rfl⟩

/-- The orthogonal projection minimizes source-L² error among all dyadic
piecewise constants. -/
theorem sourceDyadicOrthogonalProjection_minimal (n : ℕ) (f y : SourceL2)
    (hy : y ∈ sourceDyadicPiecewiseConstants n) :
    ‖f - sourceDyadicOrthogonalProjection n f‖ ≤ ‖f-y‖ := by
  rw [sourceDyadicOrthogonalProjection,
    Submodule.starProjection_minimal (U := sourceDyadicPiecewiseConstants n) f]
  have hbdd : BddBelow (Set.range (fun x : sourceDyadicPiecewiseConstants n => ‖f-x‖)) :=
    ⟨0, Set.forall_mem_range.mpr (fun x => norm_nonneg (f-x))⟩
  exact ciInf_le hbdd ⟨y, hy⟩

/-- The orthogonal dyadic source projection is at least as good as the literal
cell-average candidate. -/
theorem sourceDyadicOrthogonalProjection_le_cellAverageApproximation
    (n : ℕ) (f : SourceL2) :
    ‖f-sourceDyadicOrthogonalProjection n f‖ ≤
      ‖f-sourceDyadicCellAverageApproximation n (fun x => f x)‖ := by
  exact sourceDyadicOrthogonalProjection_minimal n f
    (sourceDyadicCellAverageApproximation n (fun x => f x))
    (sourceDyadicCellAverageApproximation_mem n (fun x => f x))

/-- The causal Γ kernel is nonnegative. -/
theorem causalKernel_nonneg {α t u : ℝ} (hα : 1/2 < α) :
    0 ≤ causalKernel α t u := by
  unfold causalKernel
  split
  · rename_i hu
    have htu : 0 < t-u := by linarith
    unfold kernel
    positivity
  · positivity

/-- Ordinary interval integrability of the actual causal kernel on `[0,1]`. -/
theorem causalKernel_intervalIntegrable_unit {α t : ℝ}
    (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IntervalIntegrable (causalKernel α t) volume 0 1 := by
  have hbase : IntervalIntegrable (fun u : ℝ => kernel α (t-u)) volume 0 t := by
    have hk := kernel_intervalIntegrable hα (t := t)
    have hc := hk.comp_sub_left t
    simpa using hc.symm
  have hleft : IntervalIntegrable (causalKernel α t) volume 0 t := by
    have heq : Set.EqOn (causalKernel α t) (fun u => kernel α (t-u)) (Set.uIoo 0 t) := by
      intro u hu
      have hut : u < t := by
        have : u ∈ Set.Ioo (0:ℝ) t := by
          simpa [Set.uIoo_of_le ht0] using hu
        exact this.2
      simp [causalKernel, hut]
    exact (intervalIntegrable_congr_uIoo heq).mpr hbase
  have hright : IntervalIntegrable (causalKernel α t) volume t 1 := by
    have heq : Set.EqOn (causalKernel α t) (fun _ => (0:ℝ)) (Set.uIoo t 1) := by
      intro u hu
      have hut : t < u := by
        have : u ∈ Set.Ioo t (1:ℝ) := by
          simpa [Set.uIoo_of_le ht1] using hu
        exact this.1
      simp [causalKernel, le_of_lt hut]
    have hz : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume t 1 :=
      continuous_const.intervalIntegrable t 1
    exact (intervalIntegrable_congr_uIoo heq).mpr hz
  exact hleft.trans hright

/-- Square integrability of the actual causal kernel on `[0,1]`. -/
theorem causalKernel_sq_intervalIntegrable_unit {α t : ℝ}
    (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IntervalIntegrable (fun u => (causalKernel α t u)^2) volume 0 1 := by
  have hbase : IntervalIntegrable (fun u : ℝ => (kernel α (t-u))^2) volume 0 t := by
    have hk := kernel_sq_intervalIntegrable hα ht0
    have hc := hk.comp_sub_left t
    simpa using hc.symm
  have hleft : IntervalIntegrable (fun u : ℝ => (causalKernel α t u)^2) volume 0 t := by
    have heq : Set.EqOn (fun u : ℝ => (causalKernel α t u)^2)
        (fun u => (kernel α (t-u))^2) (Set.uIoo 0 t) := by
      intro u hu
      have hut : u < t := by
        have : u ∈ Set.Ioo (0:ℝ) t := by
          simpa [Set.uIoo_of_le ht0] using hu
        exact this.2
      simp [causalKernel, hut]
    exact (intervalIntegrable_congr_uIoo heq).mpr hbase
  have hright : IntervalIntegrable (fun u : ℝ => (causalKernel α t u)^2) volume t 1 := by
    have heq : Set.EqOn (fun u : ℝ => (causalKernel α t u)^2)
        (fun _ => (0:ℝ)) (Set.uIoo t 1) := by
      intro u hu
      have hut : t < u := by
        have : u ∈ Set.Ioo t (1:ℝ) := by
          simpa [Set.uIoo_of_le ht1] using hu
        exact this.1
      simp [causalKernel, le_of_lt hut]
    have hz : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume t 1 :=
      continuous_const.intervalIntegrable t 1
    exact (intervalIntegrable_congr_uIoo heq).mpr hz
  exact hleft.trans hright

/-- Restriction of the unit source integrability facts to any cell. -/
theorem causalKernel_intervalIntegrable_cell {α t a b : ℝ}
    (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (causalKernel α t) volume a b := by
  have hglobal := causalKernel_intervalIntegrable_unit hα ht0 ht1
  apply hglobal.mono_set
  rw [Set.uIcc_of_le hab, Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  exact Set.Icc_subset_Icc ha hb

/-- The squared-kernel restriction to any source cell. -/
theorem causalKernel_sq_intervalIntegrable_cell {α t a b : ℝ}
    (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (fun u => (causalKernel α t u)^2) volume a b := by
  have hglobal := causalKernel_sq_intervalIntegrable_unit hα ht0 ht1
  apply hglobal.mono_set
  rw [Set.uIcc_of_le hab, Set.uIcc_of_le (show (0:ℝ) ≤ 1 by norm_num)]
  exact Set.Icc_subset_Icc ha hb

/-- Below order one, the causal kernel grows monotonically toward its
integrable singularity. -/
theorem causalKernel_monoOn_of_order_le_one {α t a b : ℝ}
    (hα : 1/2 < α) (hα1 : α ≤ 1) (hbt : b < t) :
    MonotoneOn (causalKernel α t) (Set.Icc a b) := by
  intro u hu v hv huv
  have hut : u < t := lt_of_le_of_lt hu.2 hbt
  have hvt : v < t := lt_of_le_of_lt hv.2 hbt
  simp only [causalKernel, if_pos hut, if_pos hvt]
  unfold kernel
  have hbase : 0 < t-v := by linarith
  have hpow : (t-u)^(α-1) ≤ (t-v)^(α-1) := by
    exact Real.rpow_le_rpow_of_nonpos hbase (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Above order one, the causal kernel decreases as its source coordinate
approaches the endpoint. -/
theorem causalKernel_antitoneOn_of_order_ge_one {α t a b : ℝ}
    (hα : 1/2 < α) (hα1 : 1 ≤ α) (hbt : b < t) :
    AntitoneOn (causalKernel α t) (Set.Icc a b) := by
  intro u hu v hv huv
  have hut : u < t := lt_of_le_of_lt hu.2 hbt
  have hvt : v < t := lt_of_le_of_lt hv.2 hbt
  simp only [causalKernel, if_pos hut, if_pos hvt]
  unfold kernel
  have hbase : 0 < t-v := by linarith [hv.2]
  have hpow : (t-v)^(α-1) ≤ (t-u)^(α-1) := by
    exact Real.rpow_le_rpow hbase.le (by linarith) (by linarith)
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

/-- Away from its moving singularity, the literal causal kernel is continuous
on a source interval. -/
theorem causalKernel_continuousOn_of_right_lt {α t a b : ℝ}
    (hbt : b < t) : ContinuousOn (causalKernel α t) (Set.Icc a b) := by
  have harg : ∀ x ∈ Set.Icc a b, (t-x) ≠ 0 ∨ 0 ≤ α-1 := by
    intro x hx
    left
    apply ne_of_gt
    linarith [hx.2, hbt]
  have hpow : ContinuousOn (fun x : ℝ => (t-x)^(α-1)) (Set.Icc a b) :=
    (continuousOn_const.sub continuousOn_id).rpow_const harg
  have hker : ContinuousOn (fun x : ℝ => kernel α (t-x)) (Set.Icc a b) := by
    unfold kernel
    exact hpow.const_mul _
  apply hker.congr
  intro x hx
  have hxt : x < t := lt_of_le_of_lt hx.2 hbt
  simp [causalKernel, hxt]

/-- The average of a function taking values in `[lo,hi]` also lies in that
interval. -/
theorem average_mem_Icc {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsFiniteMeasure μ] [NeZero μ] {f : X → ℝ} {lo hi : ℝ}
    (hf : Integrable f μ)
    (hlo : ∀ᵐ x ∂μ, lo ≤ f x) (hhi : ∀ᵐ x ∂μ, f x ≤ hi) :
    lo ≤ average μ f ∧ average μ f ≤ hi := by
  have hlow : 0 ≤ᵐ[μ] fun x => f x - lo := hlo.mono fun x hx => by
    dsimp
    linarith
  have hhigh : 0 ≤ᵐ[μ] fun x => hi - f x := hhi.mono fun x hx => by
    dsimp
    linarith
  have hlowAvg := average_nonneg_of_ae hlow
  have hhighAvg := average_nonneg_of_ae hhigh
  have hconst : Integrable (fun _ : X => lo) μ := integrable_const _
  have hconstHi : Integrable (fun _ : X => hi) μ := integrable_const _
  have hlowEq : average μ (fun x => f x - lo) = average μ f - lo := by
    change average μ (f - fun _ : X => lo) = _
    rw [average_sub hf hconst, average_const]
  have hhighEq : average μ (fun x => hi - f x) = hi - average μ f := by
    change average μ ((fun _ : X => hi) - f) = _
    rw [average_sub hconstHi hf, average_const]
  rw [hlowEq] at hlowAvg
  rw [hhighEq] at hhighAvg
  exact ⟨by linarith, by linarith⟩

/-- The exact cell-average projection is contractive on the squared integral;
this is the singular-cell estimate used when a dyadic cell contains `t`. -/
theorem integral_sq_sub_average_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] [NeZero μ] {f : X → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => (f x)^2) μ) :
    (∫ x, (f x - average μ f)^2 ∂μ) ≤ ∫ x, (f x)^2 ∂μ := by
  let m := average μ f
  have hmean : (μ.real Set.univ) * m = ∫ x, f x ∂μ := by
    have h := integral_average μ f
    rw [integral_const] at h
    simpa [m, smul_eq_mul] using h
  have hlin : Integrable (fun x => (2*m)*f x) μ := hf.const_mul (2*m)
  have hc : Integrable (fun _ : X => m^2) μ := integrable_const _
  have hexp : (∫ x, (f x-m)^2 ∂μ) =
      (∫ x, (f x)^2 ∂μ) - m^2 * (μ.real Set.univ) := by
    calc
      (∫ x, (f x-m)^2 ∂μ) =
          ∫ x, ((f x)^2 - (2*m)*f x + m^2) ∂μ := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (∫ x, (f x)^2 ∂μ) - 2*m*(∫ x, f x ∂μ) +
          ∫ x, (m^2:ℝ) ∂μ := by
            have hadd := integral_add (hf2.sub hlin) hc
            have hsub' := integral_sub hf2 hlin
            have hmul : (∫ x, (2*m)*f x ∂μ) = (2*m)*(∫ x, f x ∂μ) :=
              integral_const_mul (μ := μ) (2*m) f
            calc
              (∫ x, (f x)^2 - 2*m*f x + m^2 ∂μ) =
                  ∫ x, ((f x)^2 - (2*m)*f x) + m^2 ∂μ := by
                    apply integral_congr_ae
                    filter_upwards with x
                    ring
              _ = (∫ x, (f x)^2 - (2*m)*f x ∂μ) +
                  (∫ x, m^2 ∂μ) := hadd
              _ = ((∫ x, (f x)^2 ∂μ) - (∫ x, (2*m)*f x ∂μ)) +
                  (∫ x, m^2 ∂μ) := by rw [hsub']
              _ = (∫ x, (f x)^2 ∂μ) - 2*m*(∫ x, f x ∂μ) +
                  (∫ x, m^2 ∂μ) := by rw [hmul]
      _ = (∫ x, (f x)^2 ∂μ) - m^2 * (μ.real Set.univ) := by
            have hconstInt : (∫ x, (m^2:ℝ) ∂μ) = (μ.real Set.univ)*m^2 := by
              rw [integral_const]
              simp only [smul_eq_mul]
            rw [hconstInt, ← hmean]
            ring
  rw [show (∫ x, (f x-average μ f)^2 ∂μ) =
      (∫ x, (f x-m)^2 ∂μ) by rfl, hexp]
  have hmnonneg : 0 ≤ m^2 * (μ.real Set.univ) :=
    mul_nonneg (sq_nonneg m) (ENNReal.toReal_nonneg)
  linarith

/-- Interval form of the exact cell-average contraction. This applies without
monotonicity, hence is the estimate for the unique dyadic cell meeting the
moving RL singularity. -/
theorem interval_integral_sq_sub_average_le {a b : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hf : IntervalIntegrable f volume a b)
    (hf2 : IntervalIntegrable (fun x => (f x)^2) volume a b) :
    (∫ x in a..b, (f x - average (volume.restrict (Set.Ioc a b)) f)^2) ≤
      ∫ x in a..b, (f x)^2 := by
  let μ := volume.restrict (Set.Ioc a b)
  have hμfin : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hμnz : μ ≠ 0 := by
    apply (Measure.measure_univ_ne_zero).mp
    simpa [μ, Real.volume_Ioc] using hab
  haveI : NeZero μ := ⟨hμnz⟩
  have hfμ : Integrable f μ := by
    dsimp [μ]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hf
  have hf2μ : Integrable (fun x => (f x)^2) μ := by
    dsimp [μ]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hf2
  have hv := integral_sq_sub_average_le hfμ hf2μ
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le]
  simpa [μ] using hv

/-- A function whose values and approximation constant lie in a fixed
nonnegative interval has pointwise squared error bounded by the squared
oscillation of that interval. -/
theorem sq_error_le_sq_oscillation {f : ℝ → ℝ} {x c lo hi : ℝ}
    (hlo0 : 0 ≤ lo) (hlo : lo ≤ f x) (hhi : f x ≤ hi)
    (hc0 : lo ≤ c) (hchi : c ≤ hi) :
    (f x - c)^2 ≤ hi^2 - lo^2 := by
  have hosc : 0 ≤ hi - lo := by linarith
  have hdiff1 : f x - c ≤ hi - lo := by linarith
  have hdiff2 : -(hi - lo) ≤ f x - c := by linarith
  have hsq : (f x - c)^2 ≤ (hi-lo)^2 := by nlinarith
  have hpow := sq_sub_le_sq_sub_of_nonneg_order hlo0 (by linarith : lo ≤ hi)
  nlinarith

/-- The cellwise squared approximation error is controlled by the variation
of the squared endpoint values. -/
theorem interval_sq_error_le_sq_endpoint_variation
    {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hlo0 : 0 ≤ f a) (hmonoLo : ∀ x ∈ Set.Icc a b, f a ≤ f x)
    (hmonoHi : ∀ x ∈ Set.Icc a b, f x ≤ f b)
    (hcLo : f a ≤ c) (hcHi : c ≤ f b)
    (hf : IntervalIntegrable (fun x => (f x-c)^2) volume a b) :
    (∫ x in a..b, (f x-c)^2) ≤ (b-a) * (f b^2-f a^2) := by
  have hvar : 0 ≤ f b^2-f a^2 := by nlinarith [hmonoLo b ⟨hab, le_rfl⟩]
  have hconst : IntervalIntegrable (fun _ : ℝ => f b^2-f a^2) volume a b :=
    intervalIntegrable_const
  calc
    (∫ x in a..b, (f x-c)^2) ≤ ∫ x in a..b, (f b^2-f a^2) :=
      intervalIntegral.integral_mono_on hab hf hconst (fun x hx =>
        sq_error_le_sq_oscillation hlo0
          (hmonoLo x hx)
          (hmonoHi x hx) hcLo hcHi)
    _ = (b-a) * (f b^2-f a^2) := by rw [intervalIntegral.integral_const]; ring_nf

/-- The reverse-monotone form of the endpoint-variation estimate. -/
theorem interval_sq_error_le_sq_endpoint_variation_antitone
    {f : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hhi0 : 0 ≤ f b) (hmonoHi : ∀ x ∈ Set.Icc a b, f x ≤ f a)
    (hmonoLo : ∀ x ∈ Set.Icc a b, f b ≤ f x)
    (hcLo : f b ≤ c) (hcHi : c ≤ f a)
    (hf : IntervalIntegrable (fun x => (f x-c)^2) volume a b) :
    (∫ x in a..b, (f x-c)^2) ≤ (b-a) * (f a^2-f b^2) := by
  have hvar : 0 ≤ f a^2-f b^2 := by nlinarith [hmonoHi a ⟨le_rfl, hab⟩]
  have hconst : IntervalIntegrable (fun _ : ℝ => f a^2-f b^2) volume a b :=
    intervalIntegrable_const
  calc
    (∫ x in a..b, (f x-c)^2) ≤ ∫ x in a..b, (f a^2-f b^2) :=
      intervalIntegral.integral_mono_on hab hf hconst (fun x hx =>
        sq_error_le_sq_oscillation hhi0
          (hmonoLo x hx)
          (hmonoHi x hx) hcLo hcHi)
    _ = (b-a) * (f a^2-f b^2) := by rw [intervalIntegral.integral_const]; ring_nf

/-- On a monotone cell, the exact orthogonal cell-average coefficient lies
between the endpoint values, so its squared projection residual obeys the
same endpoint-variation estimate. -/
theorem interval_average_sq_error_le_endpoint_variation
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hlo0 : 0 ≤ f a)
    (hmonoLo : ∀ x ∈ Set.Icc a b, f a ≤ f x)
    (hmonoHi : ∀ x ∈ Set.Icc a b, f x ≤ f b)
    (hf : IntervalIntegrable f volume a b)
    (hfsq : IntervalIntegrable (fun x => (f x -
      average (volume.restrict (Set.Ioc a b)) f)^2) volume a b) :
    (∫ x in a..b, (f x - average (volume.restrict (Set.Ioc a b)) f)^2) ≤
      (b-a) * (f b^2-f a^2) := by
  let μ := volume.restrict (Set.Ioc a b)
  have hμfin : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hμnz : μ ≠ 0 := by
    apply (Measure.measure_univ_ne_zero).mp
    simpa [μ, Real.volume_Ioc] using hab
  haveI : NeZero μ := ⟨hμnz⟩
  have hfμ : Integrable f μ := by
    dsimp [μ]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hf
  have hloAE : ∀ᵐ x ∂μ, f a ≤ f x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hmonoLo x (Set.Ioc_subset_Icc_self hx)
  have hhiAE : ∀ᵐ x ∂μ, f x ≤ f b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hmonoHi x (Set.Ioc_subset_Icc_self hx)
  have havg := average_mem_Icc hfμ hloAE hhiAE
  exact interval_sq_error_le_sq_endpoint_variation hab.le hlo0 hmonoLo hmonoHi
    havg.1 havg.2 hfsq

/-- Cell-average error on a decreasing nonnegative cell. -/
theorem interval_average_sq_error_le_endpoint_variation_antitone
    {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hhi0 : 0 ≤ f b)
    (hmonoHi : ∀ x ∈ Set.Icc a b, f x ≤ f a)
    (hmonoLo : ∀ x ∈ Set.Icc a b, f b ≤ f x)
    (hf : IntervalIntegrable f volume a b)
    (hfsq : IntervalIntegrable (fun x => (f x -
      average (volume.restrict (Set.Ioc a b)) f)^2) volume a b) :
    (∫ x in a..b, (f x - average (volume.restrict (Set.Ioc a b)) f)^2) ≤
      (b-a) * (f a^2-f b^2) := by
  let μ := volume.restrict (Set.Ioc a b)
  have hμfin : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hμnz : μ ≠ 0 := by
    apply (Measure.measure_univ_ne_zero).mp
    simpa [μ, Real.volume_Ioc] using hab
  haveI : NeZero μ := ⟨hμnz⟩
  have hfμ : Integrable f μ := by
    dsimp [μ]
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mp hf
  have hloAE : ∀ᵐ x ∂μ, f b ≤ f x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hmonoLo x (Set.Ioc_subset_Icc_self hx)
  have hhiAE : ∀ᵐ x ∂μ, f x ≤ f a := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact hmonoHi x (Set.Ioc_subset_Icc_self hx)
  have havg := average_mem_Icc hfμ hloAE hhiAE
  exact interval_sq_error_le_sq_endpoint_variation_antitone hab.le hhi0
    hmonoHi hmonoLo havg.1 havg.2 hfsq

/-- Actual cell-average estimate for the RL kernel on any cell wholly before
the causal boundary. The one cell containing `t` is deliberately separate. -/
theorem causalKernel_cell_average_error {α t a b : ℝ}
    (hα : 1/2 < α) (hab : a < b) (hbt : b < t) :
    (∫ x in a..b,
        (causalKernel α t x -
          average (volume.restrict (Set.Ioc a b)) (causalKernel α t))^2) ≤
      (b-a) * (max ((causalKernel α t a)^2 - (causalKernel α t b)^2)
        ((causalKernel α t b)^2 - (causalKernel α t a)^2)) := by
  have hcont := causalKernel_continuousOn_of_right_lt (α := α) (t := t) (a := a) (b := b) hbt
  have hf : IntervalIntegrable (causalKernel α t) volume a b := by
    exact hcont.intervalIntegrable_of_Icc hab.le
  have hrescont : ContinuousOn
      (fun x => (causalKernel α t x -
        average (volume.restrict (Set.Ioc a b)) (causalKernel α t))^2)
      (Set.Icc a b) := by
    exact (hcont.sub continuousOn_const).pow 2
  have hfsq : IntervalIntegrable (fun x =>
      (causalKernel α t x -
        average (volume.restrict (Set.Ioc a b)) (causalKernel α t))^2)
      volume a b := by
    exact hrescont.intervalIntegrable_of_Icc hab.le
  by_cases hα1 : α ≤ 1
  · have hmono := causalKernel_monoOn_of_order_le_one (a := a) (b := b) hα hα1 hbt
    have hloc := interval_average_sq_error_le_endpoint_variation hab
      (causalKernel_nonneg hα)
      (fun x hx => hmono ⟨le_rfl, hab.le⟩ hx hx.1)
      (fun x hx => hmono hx ⟨hab.le, le_rfl⟩ hx.2) hf hfsq
    calc
      _ ≤ (b-a) * ((causalKernel α t b)^2 - (causalKernel α t a)^2) := hloc
      _ ≤ (b-a) * max ((causalKernel α t a)^2-(causalKernel α t b)^2)
            ((causalKernel α t b)^2-(causalKernel α t a)^2) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact le_max_right _ _
  · have hα1' : 1 ≤ α := le_of_not_ge hα1
    have hmono := causalKernel_antitoneOn_of_order_ge_one (a := a) (b := b) hα hα1' hbt
    have hloc := interval_average_sq_error_le_endpoint_variation_antitone hab
      (causalKernel_nonneg hα)
      (fun x hx => hmono ⟨le_rfl, hab.le⟩ hx hx.1)
      (fun x hx => hmono hx ⟨hab.le, le_rfl⟩ hx.2) hf hfsq
    calc
      _ ≤ (b-a) * ((causalKernel α t a)^2 - (causalKernel α t b)^2) := hloc
      _ ≤ (b-a) * max ((causalKernel α t a)^2-(causalKernel α t b)^2)
            ((causalKernel α t b)^2-(causalKernel α t a)^2) := by
          apply mul_le_mul_of_nonneg_left _ (by linarith)
          exact le_max_left _ _

/-- Exact squared energy of the causal kernel on a cell whose left endpoint
is before the singularity and whose right endpoint is after it. -/
theorem causalKernel_singular_cell_energy {α t a b : ℝ}
    (hα : 1/2 < α) (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b)
    (hb : b ≤ 1) :
    (∫ u in a..b, (causalKernel α t u)^2) =
      ((Real.Gamma α)⁻¹)^2 *
        ((t-a)^(2*α-1)/(2*α-1)) := by
  have ht0 : 0 ≤ t := le_trans ha hat
  have hkernel : IntervalIntegrable (fun u : ℝ => (kernel α (t-u))^2)
      volume 0 t := by
    have hbase := kernel_sq_intervalIntegrable hα ht0
    have hcomp := hbase.comp_sub_left t
    simpa using hcomp.symm
  have hkernelSub : IntervalIntegrable (fun u : ℝ => (kernel α (t-u))^2)
      volume a t := by
    apply hkernel.mono_set
    rw [Set.uIcc_of_le hat]
    rw [Set.uIcc_of_le ht0]
    exact Set.Icc_subset_Icc ha (le_rfl)
  have hcausalLeft : IntervalIntegrable (fun u : ℝ => (causalKernel α t u)^2)
      volume a t := by
    have heq : Set.EqOn (fun u : ℝ => (causalKernel α t u)^2)
        (fun u => (kernel α (t-u))^2) (Set.uIoo a t) := by
      intro u hu
      have hut : u < t := by
        have : u ∈ Set.Ioo a t := by
          simpa [Set.uIoo_of_le hat] using hu
        exact this.2
      simp [causalKernel, hut]
    exact (intervalIntegrable_congr_uIoo heq).mpr hkernelSub
  have hzero : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume t b :=
    continuous_const.intervalIntegrable t b
  have hcausalRight : IntervalIntegrable (fun u : ℝ => (causalKernel α t u)^2)
      volume t b := by
    have heq : Set.EqOn (fun u : ℝ => (causalKernel α t u)^2)
        (fun _ => (0:ℝ)) (Set.uIoo t b) := by
      intro u hu
      have hut : t < u := by
        have : u ∈ Set.Ioo t b := by
          simpa [Set.uIoo_of_le htb] using hu
        exact this.1
      simp [causalKernel, le_of_lt hut]
    exact (intervalIntegrable_congr_uIoo heq).mpr hzero
  have hrightZero : (∫ u in t..b, (causalKernel α t u)^2) = 0 := by
    have heq : Set.EqOn (fun u : ℝ => (causalKernel α t u)^2)
        (fun _ => (0:ℝ)) (Set.uIoo t b) := by
      intro u hu
      have hut : t < u := by
        have : u ∈ Set.Ioo t b := by simpa [Set.uIoo_of_le htb] using hu
        exact this.1
      simp [causalKernel, le_of_lt hut]
    calc
      (∫ u in t..b, (causalKernel α t u)^2) =
          ∫ u in t..b, (0:ℝ) := intervalIntegral.integral_congr_uIoo heq
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals hcausalLeft hcausalRight
  have heqLeft :
      (∫ u in a..t, (causalKernel α t u)^2) =
        ∫ u in a..t, (kernel α (t-u))^2 := by
    apply intervalIntegral.integral_congr_uIoo
    intro u hu
    have hut : u < t := by
      have : u ∈ Set.Ioo a t := by simpa [Set.uIoo_of_le hat] using hu
      exact this.2
    simp [causalKernel, hut]
  have hshift :
      (∫ u in a..t, (kernel α (t-u))^2) =
        ∫ v in (0:ℝ)..(t-a), (kernel α ((t-a)-v))^2 := by
    have hcomp := intervalIntegral.integral_comp_add_right
      (a := (0:ℝ)) (b := t-a)
      (f := fun u : ℝ => (kernel α (t-u))^2) a
    have hcomp' :
        (∫ v in (0:ℝ)..(t-a), (kernel α (t-(v+a)))^2) =
          ∫ u in a..t, (kernel α (t-u))^2 := by
      simpa [sub_add_cancel] using hcomp
    calc
      (∫ u in a..t, (kernel α (t-u))^2) =
          ∫ v in (0:ℝ)..(t-a), (kernel α (t-(v+a)))^2 := hcomp'.symm
      _ = ∫ v in (0:ℝ)..(t-a), (kernel α ((t-a)-v))^2 := by
        apply intervalIntegral.integral_congr
        intro v hv
        congr 2 <;> ring
  have hbase : 0 ≤ t-a := sub_nonneg.mpr hat
  calc
    (∫ u in a..b, (causalKernel α t u)^2) =
        (∫ u in a..t, (causalKernel α t u)^2) +
          ∫ u in t..b, (causalKernel α t u)^2 := hadd.symm
    _ = ∫ u in a..t, (kernel α (t-u))^2 := by rw [hrightZero, add_zero, heqLeft]
    _ = ∫ v in (0:ℝ)..(t-a), (kernel α ((t-a)-v))^2 := hshift
    _ = ((Real.Gamma α)⁻¹)^2 * ((t-a)^(2*α-1)/(2*α-1)) :=
      kernel_sq_integral hα hbase

/-- The exact cell-average residual on the singular cell has the expected
`(cell width)^(2α−1)` energy scale. -/
theorem causalKernel_singular_cell_average_error {α t a b : ℝ}
    (hα : 1/2 < α) (hab : a < b) (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b)
    (hb : b ≤ 1)
    (hf : IntervalIntegrable (causalKernel α t) volume a b)
    (hf2 : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume a b) :
    (∫ u in a..b, (causalKernel α t u -
      average (volume.restrict (Set.Ioc a b)) (causalKernel α t))^2) ≤
      ((Real.Gamma α)⁻¹)^2 *
        ((b-a)^(2*α-1)/(2*α-1)) := by
  have henergy := causalKernel_singular_cell_energy hα ha hat htb hb
  have hvar := interval_integral_sq_sub_average_le hab hf hf2
  have hp : 0 < 2*α-1 := by linarith
  have hwidth : 0 ≤ b-a := by linarith
  have hdist : t-a ≤ b-a := by linarith
  have hpow : (t-a)^(2*α-1) ≤ (b-a)^(2*α-1) :=
    Real.rpow_le_rpow (by linarith) hdist hp.le
  have hden : 0 < 2*α-1 := hp
  have hgamma : 0 ≤ ((Real.Gamma α)⁻¹)^2 := sq_nonneg _
  calc
    _ ≤ ∫ u in a..b, (causalKernel α t u)^2 := hvar
    _ = ((Real.Gamma α)⁻¹)^2 * ((t-a)^(2*α-1)/(2*α-1)) := henergy
    _ ≤ ((Real.Gamma α)⁻¹)^2 * ((b-a)^(2*α-1)/(2*α-1)) := by
      apply mul_le_mul_of_nonneg_left _ hgamma
      exact div_le_div_of_nonneg_right hpow hden.le

/-- Telescoping form of the cellwise monotone estimate on an equally spaced
partition.  This is the regular-cell part of the dyadic kernel projection
bound; the one cell meeting the singularity must be estimated separately. -/
theorem sum_equal_cell_variation_eq {N : ℕ} {h : ℝ} {g : ℕ → ℝ} :
    (∑ j ∈ Finset.range N, h * (g (j+1) - g j)) = h * (g N - g 0) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ j ∈ Finset.range N, h * (g (j+1)-g j)) +
            h * (g (N+1)-g N) =
          h * (g N-g 0) + h * (g (N+1)-g N) := by rw [ih]
        _ = h * (g (N+1)-g 0) := by ring

/-- The decreasing analogue of `sum_equal_cell_variation_le`. -/
theorem sum_equal_cell_variation_eq_antitone {N : ℕ} {h : ℝ} {g : ℕ → ℝ} :
    (∑ j ∈ Finset.range N, h * (g j - g (j+1))) = h * (g 0 - g N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ j ∈ Finset.range N, h * (g j-g (j+1))) +
            h * (g N-g (N+1)) =
          h * (g 0-g N) + h * (g N-g (N+1)) := by rw [ih]
        _ = h * (g 0-g (N+1)) := by ring

/-- Assemble actual local cell-average estimates over an increasing equal
partition; the sum collapses to the endpoint variation. -/
theorem sum_equal_cell_average_errors_le {N : ℕ} {h : ℝ}
    {E g : ℕ → ℝ}
    (hcell : ∀ j ∈ Finset.range N, E j ≤ h * (g (j+1)-g j)) :
    (∑ j ∈ Finset.range N, E j) ≤ h * (g N-g 0) := by
  calc
    (∑ j ∈ Finset.range N, E j) ≤
        ∑ j ∈ Finset.range N, h*(g (j+1)-g j) :=
      Finset.sum_le_sum fun j hj => hcell j hj
    _ = h*(g N-g 0) := sum_equal_cell_variation_eq

/-- Decreasing equal partitions telescope in the opposite endpoint order. -/
theorem sum_equal_cell_average_errors_le_antitone {N : ℕ} {h : ℝ}
    {E g : ℕ → ℝ}
    (hcell : ∀ j ∈ Finset.range N, E j ≤ h * (g j-g (j+1))) :
    (∑ j ∈ Finset.range N, E j) ≤ h * (g 0-g N) := by
  calc
    (∑ j ∈ Finset.range N, E j) ≤
        ∑ j ∈ Finset.range N, h*(g j-g (j+1)) :=
      Finset.sum_le_sum fun j hj => hcell j hj
    _ = h*(g 0-g N) := sum_equal_cell_variation_eq_antitone

/-- Sum of the actual cell-average errors on a regular grid of cells lying
strictly before the causal boundary, for orders at most one. The singular
cell is excluded and handled by `causalKernel_singular_cell_average_error`. -/
theorem causalKernel_regular_grid_average_error_sum_le
    {α t h : ℝ} {N : ℕ} (hα : 1/2 < α) (hα1 : α ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hh : 0 < h)
    (hend : (N:ℝ)*h ≤ t)
    (hcell : ∀ j ∈ Finset.range N, ((j+1:ℕ):ℝ)*h < t) :
    (∑ j ∈ Finset.range N,
      ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
        (causalKernel α t u -
          average (volume.restrict
            (Set.Ioc ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h))) (causalKernel α t))^2) ≤
      h * ((causalKernel α t ((N:ℝ)*h))^2 - (causalKernel α t 0)^2) := by
  let E : ℕ → ℝ := fun j =>
    ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
      (causalKernel α t u -
        average (volume.restrict
          (Set.Ioc ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h))) (causalKernel α t))^2
  let g : ℕ → ℝ := fun j => (causalKernel α t ((j:ℝ)*h))^2
  have hcell' : ∀ j ∈ Finset.range N, E j ≤ h * (g (j+1)-g j) := by
    intro j hj
    have hjt : ((j+1:ℕ):ℝ)*h < t := hcell j hj
    have hjstep : (j:ℝ)*h < ((j+1:ℕ):ℝ)*h := by
      have hcast : ((j+1:ℕ):ℝ) = (j:ℝ)+1 := by norm_num
      rw [hcast]
      nlinarith
    have hlocal := causalKernel_cell_average_error hα hjstep hjt
    have hmono := causalKernel_monoOn_of_order_le_one
      (a := (j:ℝ)*h) (b := ((j+1:ℕ):ℝ)*h) hα hα1 hjt
    have hendpoint := hmono ⟨le_rfl, hjstep.le⟩ ⟨hjstep.le, le_rfl⟩ hjstep.le
    have hnon : 0 ≤ (causalKernel α t (((j+1:ℕ):ℝ)*h))^2 -
        (causalKernel α t ((j:ℝ)*h))^2 := by
      nlinarith [causalKernel_nonneg hα (t := t) (u := (j:ℝ)*h),
        causalKernel_nonneg hα (t := t) (u := ((j+1:ℕ):ℝ)*h)]
    have hmax : max ((causalKernel α t ((j:ℝ)*h))^2 -
        (causalKernel α t (((j+1:ℕ):ℝ)*h))^2)
        ((causalKernel α t (((j+1:ℕ):ℝ)*h))^2 -
          (causalKernel α t ((j:ℝ)*h))^2) =
        (causalKernel α t (((j+1:ℕ):ℝ)*h))^2 -
          (causalKernel α t ((j:ℝ)*h))^2 := max_eq_right (by nlinarith)
    have hlength : (((j+1:ℕ):ℝ)*h) - (j:ℝ)*h = h := by
      have hcast : ((j+1:ℕ):ℝ) = (j:ℝ)+1 := by norm_num
      rw [hcast]
      ring
    change E j ≤ h * (g (j+1)-g j)
    dsimp [E, g]
    rw [hmax] at hlocal
    rw [hlength] at hlocal
    exact hlocal
  have hsum := sum_equal_cell_average_errors_le hcell'
  simpa [E, g] using hsum

/-- The same assembled estimate for decreasing kernels, with endpoint
variation in the reverse order. -/
theorem causalKernel_regular_grid_average_error_sum_le_antitone
    {α t h : ℝ} {N : ℕ} (hα : 1/2 < α) (hα1 : 1 ≤ α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hh : 0 < h)
    (hend : (N:ℝ)*h ≤ t)
    (hcell : ∀ j ∈ Finset.range N, ((j+1:ℕ):ℝ)*h < t) :
    (∑ j ∈ Finset.range N,
      ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
        (causalKernel α t u -
          average (volume.restrict
            (Set.Ioc ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h))) (causalKernel α t))^2) ≤
      h * ((causalKernel α t 0)^2 - (causalKernel α t ((N:ℝ)*h))^2) := by
  let E : ℕ → ℝ := fun j =>
    ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
      (causalKernel α t u -
        average (volume.restrict
          (Set.Ioc ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h))) (causalKernel α t))^2
  let g : ℕ → ℝ := fun j => (causalKernel α t ((j:ℝ)*h))^2
  have hcell' : ∀ j ∈ Finset.range N, E j ≤ h * (g j-g (j+1)) := by
    intro j hj
    have hjt : ((j+1:ℕ):ℝ)*h < t := hcell j hj
    have hjstep : (j:ℝ)*h < ((j+1:ℕ):ℝ)*h := by
      have hcast : ((j+1:ℕ):ℝ) = (j:ℝ)+1 := by norm_num
      rw [hcast]
      nlinarith
    have hlocal := causalKernel_cell_average_error hα hjstep hjt
    have hmono := causalKernel_antitoneOn_of_order_ge_one
      (a := (j:ℝ)*h) (b := ((j+1:ℕ):ℝ)*h) hα hα1 hjt
    have hendpoint := hmono ⟨le_rfl, hjstep.le⟩ ⟨hjstep.le, le_rfl⟩ hjstep.le
    have hnon : 0 ≤ (causalKernel α t ((j:ℝ)*h))^2 -
        (causalKernel α t (((j+1:ℕ):ℝ)*h))^2 := by
      nlinarith [causalKernel_nonneg hα (t := t) (u := (j:ℝ)*h),
        causalKernel_nonneg hα (t := t) (u := ((j+1:ℕ):ℝ)*h)]
    have hmax : max ((causalKernel α t ((j:ℝ)*h))^2 -
        (causalKernel α t (((j+1:ℕ):ℝ)*h))^2)
        ((causalKernel α t (((j+1:ℕ):ℝ)*h))^2 -
          (causalKernel α t ((j:ℝ)*h))^2) =
        (causalKernel α t ((j:ℝ)*h))^2 -
          (causalKernel α t (((j+1:ℕ):ℝ)*h))^2 := max_eq_left (by linarith)
    have hlength : (((j+1:ℕ):ℝ)*h) - (j:ℝ)*h = h := by
      have hcast : ((j+1:ℕ):ℝ) = (j:ℝ)+1 := by norm_num
      rw [hcast]
      ring
    change E j ≤ h * (g j-g (j+1))
    dsimp [E, g]
    rw [hmax] at hlocal
    rw [hlength] at hlocal
    exact hlocal
  have hsum := sum_equal_cell_average_errors_le_antitone hcell'
  simpa [E, g] using hsum

/-- Uniform power bound for the regular-cell sum when the grid block stops at
least one full cell before the singularity. -/
theorem causalKernel_regular_grid_average_error_sum_le_power
    {α t h : ℝ} {N : ℕ} (hα : 1/2 < α) (hα1 : α ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hh : 0 < h)
    (hmargin : (N:ℝ)*h+h ≤ t) :
    (∑ j ∈ Finset.range N,
      ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
        (causalKernel α t u -
          average (volume.restrict
            (Set.Ioc ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h))) (causalKernel α t))^2) ≤
      ((Real.Gamma α)⁻¹)^2 * h^(2*α-1) := by
  have hh0 : 0 ≤ h := hh.le
  have htend : (N:ℝ)*h ≤ t := by linarith
  have hN0 : 0 ≤ (N:ℝ)*h := mul_nonneg (Nat.cast_nonneg _) hh.le
  have hcell : ∀ j ∈ Finset.range N, ((j+1:ℕ):ℝ)*h < t := by
    intro j hj
    have hjN : j+1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hjcast : ((j+1:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hjN
    have hgrid : ((j+1:ℕ):ℝ)*h ≤ (N:ℝ)*h :=
      mul_le_mul_of_nonneg_right hjcast hh0
    linarith
  have hsum := causalKernel_regular_grid_average_error_sum_le
    hα hα1 ht0 ht1 hh htend hcell
  have hgap : h ≤ t-(N:ℝ)*h := by linarith
  have hgap0 : 0 < t-(N:ℝ)*h := lt_of_lt_of_le hh hgap
  have hq : 2*α-2 ≤ 0 := by linarith
  have hpow := Real.rpow_le_rpow_of_nonpos hh hgap hq
  have hker : causalKernel α t ((N:ℝ)*h) =
      (Real.Gamma α)⁻¹ * (t-(N:ℝ)*h)^(α-1) := by
    have htlt : (N:ℝ)*h < t := by linarith
    simp [causalKernel, kernel, htlt, sub_sub_cancel]
  have hpowSq : ((t-(N:ℝ)*h)^(α-1))^2 = (t-(N:ℝ)*h)^(2*α-2) := by
    have hp : 0 < t-(N:ℝ)*h := hgap0
    calc
      ((t-(N:ℝ)*h)^(α-1))^2 =
          (t-(N:ℝ)*h)^(α-1) * (t-(N:ℝ)*h)^(α-1) := by rw [pow_two]
      _ = (t-(N:ℝ)*h)^((α-1)+(α-1)) := (Real.rpow_add hp _ _).symm
      _ = (t-(N:ℝ)*h)^(2*α-2) := by congr 1 <;> ring
  have hgamma : 0 ≤ ((Real.Gamma α)⁻¹)^2 := sq_nonneg _
  have hgnon : 0 ≤ (causalKernel α t 0)^2 := sq_nonneg _
  have hendpow : (causalKernel α t ((N:ℝ)*h))^2 ≤
      ((Real.Gamma α)⁻¹)^2 * h^(2*α-2) := by
    rw [hker, mul_pow, hpowSq]
    exact mul_le_mul_of_nonneg_left hpow hgamma
  calc
    _ ≤ h * ((causalKernel α t ((N:ℝ)*h))^2 - (causalKernel α t 0)^2) := hsum
    _ ≤ h * (causalKernel α t ((N:ℝ)*h))^2 := by
      apply mul_le_mul_of_nonneg_left _ hh0
      nlinarith
    _ ≤ h * (((Real.Gamma α)⁻¹)^2 * h^(2*α-2)) :=
      mul_le_mul_of_nonneg_left hendpow hh0
    _ = ((Real.Gamma α)⁻¹)^2 * h^(2*α-1) := by
      rw [show 2*α-1 = (2*α-2)+1 by ring, Real.rpow_add hh _ (1:ℝ)]
      simp [Real.rpow_one]
      ring

/-- Above order one the same regular-grid sum is Lipschitz-scale; the kernel
decreases from its finite value at the left endpoint. -/
theorem causalKernel_regular_grid_average_error_sum_le_ge_one
    {α t h : ℝ} {N : ℕ} (hα : 1/2 < α) (hα1 : 1 ≤ α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hh : 0 < h)
    (hmargin : (N:ℝ)*h+h ≤ t) :
    (∑ j ∈ Finset.range N,
      ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
        (causalKernel α t u -
          average (volume.restrict
            (Set.Ioc ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h))) (causalKernel α t))^2) ≤
      ((Real.Gamma α)⁻¹)^2 * h := by
  have hh0 : 0 ≤ h := hh.le
  have htend : (N:ℝ)*h ≤ t := by linarith
  have hN0 : 0 ≤ (N:ℝ)*h := mul_nonneg (Nat.cast_nonneg _) hh0
  have hcell : ∀ j ∈ Finset.range N, ((j+1:ℕ):ℝ)*h < t := by
    intro j hj
    have hjN : j+1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hjcast : ((j+1:ℕ):ℝ) ≤ (N:ℝ) := by exact_mod_cast hjN
    have hgrid : ((j+1:ℕ):ℝ)*h ≤ (N:ℝ)*h := mul_le_mul_of_nonneg_right hjcast hh0
    linarith
  have hsum := causalKernel_regular_grid_average_error_sum_le_antitone
    hα hα1 ht0 ht1 hh htend hcell
  have hgap : h ≤ t-(N:ℝ)*h := by linarith
  have hgap0 : 0 < t-(N:ℝ)*h := lt_of_lt_of_le hh hgap
  have hq : 2*α-2 ≥ 0 := by linarith
  have hker0 : causalKernel α t 0 =
      (Real.Gamma α)⁻¹ * t^(α-1) := by
    have htpos : 0 < t := by nlinarith [hN0]
    simp [causalKernel, kernel, htpos]
  have hpow : t^(2*α-2) ≤ 1 := by
    have hpow' : t^(2*α-2) ≤ (1:ℝ)^(2*α-2) :=
      Real.rpow_le_rpow ht0 ht1 hq
    simpa using hpow'
  have hsq : (t^(α-1))^2 = t^(2*α-2) := by
    have htpos : 0 < t := by nlinarith [hN0]
    calc
      (t^(α-1))^2 = t^(α-1) * t^(α-1) := by rw [pow_two]
      _ = t^((α-1)+(α-1)) := (Real.rpow_add htpos _ _).symm
      _ = t^(2*α-2) := by congr 1 <;> ring
  have hgamma : 0 ≤ ((Real.Gamma α)⁻¹)^2 := sq_nonneg _
  have hstart : 0 ≤ (causalKernel α t 0)^2 := sq_nonneg _
  have hend : (causalKernel α t 0)^2 ≤ ((Real.Gamma α)⁻¹)^2 := by
    rw [hker0, mul_pow, hsq]
    calc
      _ ≤ ((Real.Gamma α)⁻¹)^2 * 1 := mul_le_mul_of_nonneg_left hpow hgamma
      _ = _ := by ring
  calc
    _ ≤ h * ((causalKernel α t 0)^2 -
        (causalKernel α t ((N:ℝ)*h))^2) := hsum
    _ ≤ h * (causalKernel α t 0)^2 := by
      apply mul_le_mul_of_nonneg_left _ hh0
      nlinarith [sq_nonneg (causalKernel α t ((N:ℝ)*h))]
    _ ≤ h * ((Real.Gamma α)⁻¹)^2 := mul_le_mul_of_nonneg_left hend hh0
    _ = ((Real.Gamma α)⁻¹)^2*h := by ring

/-- The at-most-two cells bordering the causal singularity can be grouped
into one short interval. Their separate average residuals sum to at most the
exact kernel energy of that interval. -/
theorem causalKernel_two_cell_average_error_le_energy
    {α t a b c : ℝ} (hα : 1/2 < α) (hab : a < b) (hbc : b < c)
    (ha : 0 ≤ a) (hat : a ≤ t) (htc : t ≤ c) (hc : c ≤ 1)
    (hf1 : IntervalIntegrable (causalKernel α t) volume a b)
    (hf1sq : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume a b)
    (hf2 : IntervalIntegrable (causalKernel α t) volume b c)
    (hf2sq : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume b c) :
    (∫ u in a..b, (causalKernel α t u -
      average (volume.restrict (Set.Ioc a b)) (causalKernel α t))^2) +
    (∫ u in b..c, (causalKernel α t u -
      average (volume.restrict (Set.Ioc b c)) (causalKernel α t))^2) ≤
      ((Real.Gamma α)⁻¹)^2 * ((t-a)^(2*α-1)/(2*α-1)) := by
  have hvar1 := interval_integral_sq_sub_average_le hab hf1 hf1sq
  have hvar2 := interval_integral_sq_sub_average_le hbc hf2 hf2sq
  have hfadd := intervalIntegral.integral_add_adjacent_intervals hf1sq hf2sq
  have henergy := causalKernel_singular_cell_energy hα ha hat htc hc
  have hwhole :
      (∫ u in a..b, (causalKernel α t u)^2) +
        ∫ u in b..c, (causalKernel α t u)^2 =
          ((Real.Gamma α)⁻¹)^2 * ((t-a)^(2*α-1)/(2*α-1)) := by
    calc
      _ = ∫ u in a..c, (causalKernel α t u)^2 := hfadd
      _ = _ := henergy
  calc
    _ ≤ (∫ u in a..b, (causalKernel α t u)^2) +
        ∫ u in b..c, (causalKernel α t u)^2 := add_le_add hvar1 hvar2
    _ = _ := hwhole

/-- Power-scale version of `causalKernel_two_cell_average_error_le_energy`
when the combined boundary interval has width at most `Lh`. -/
theorem causalKernel_two_cell_average_error_le_power
    {α t a b c h L : ℝ} (hα : 1/2 < α) (hab : a < b) (hbc : b < c)
    (ha : 0 ≤ a) (hat : a ≤ t) (htc : t ≤ c) (hc : c ≤ 1)
    (hwidth0 : 0 ≤ c-a) (hwidth : c-a ≤ L*h) (hL : 0 ≤ L) (hh : 0 ≤ h)
    (hf1 : IntervalIntegrable (causalKernel α t) volume a b)
    (hf1sq : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume a b)
    (hf2 : IntervalIntegrable (causalKernel α t) volume b c)
    (hf2sq : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume b c) :
    (∫ u in a..b, (causalKernel α t u -
      average (volume.restrict (Set.Ioc a b)) (causalKernel α t))^2) +
    (∫ u in b..c, (causalKernel α t u -
      average (volume.restrict (Set.Ioc b c)) (causalKernel α t))^2) ≤
      ((Real.Gamma α)⁻¹)^2 * ((L*h)^(2*α-1)/(2*α-1)) := by
  have hbase := causalKernel_two_cell_average_error_le_energy
    hα hab hbc ha hat htc hc hf1 hf1sq hf2 hf2sq
  have hp : 0 < 2*α-1 := by linarith
  have htwidth0 : 0 ≤ t-a := sub_nonneg.mpr hat
  have htwidth : t-a ≤ L*h := le_trans (sub_le_sub_right htc a) hwidth
  have hpow := Real.rpow_le_rpow htwidth0 htwidth hp.le
  have hgamma : 0 ≤ ((Real.Gamma α)⁻¹)^2 := sq_nonneg _
  calc
    _ ≤ ((Real.Gamma α)⁻¹)^2 * ((t-a)^(2*α-1)/(2*α-1)) := hbase
    _ ≤ ((Real.Gamma α)⁻¹)^2 * ((L*h)^(2*α-1)/(2*α-1)) := by
      apply mul_le_mul_of_nonneg_left _ hgamma
      exact div_le_div_of_nonneg_right hpow hp.le

/-- The scalar squared error on one regular cell. -/
noncomputable def causalKernelCellError (α t h : ℝ) (j : ℕ) : ℝ :=
  ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
    (causalKernel α t u -
      average (volume.restrict
        (Set.Ioc ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h))) (causalKernel α t))^2

/-- Cells wholly to the right of the causal boundary have zero approximation
error, including when the boundary coincides with their left endpoint. -/
theorem causalKernelCellError_eq_zero_of_right
    {α t h : ℝ} {j N : ℕ} (hh : 0 < h)
    (ht : t ≤ ((N+2:ℕ):ℝ)*h) (hNj : N+2 ≤ j) :
    causalKernelCellError α t h j = 0 := by
  let a := (j:ℝ)*h
  let b := ((j+1:ℕ):ℝ)*h
  have hjcast : ((N+2:ℕ):ℝ) ≤ (j:ℝ) := by exact_mod_cast hNj
  have hleft : t ≤ a := by
    dsimp [a]
    calc
      t ≤ ((N+2:ℕ):ℝ)*h := ht
      _ ≤ (j:ℝ)*h := mul_le_mul_of_nonneg_right hjcast hh.le
  have hzero : causalKernel α t =ᵐ[volume.restrict (Set.Ioc a b)] (fun _ => (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    simp [causalKernel, le_trans hleft hu.1.le]
  have havg : average (volume.restrict (Set.Ioc a b)) (causalKernel α t) = 0 := by
    rw [average_congr hzero]
    simp [average_eq]
  unfold causalKernelCellError
  rw [havg]
  have hab : a ≤ b := by
    dsimp [a, b]
    have hcast : ((j+1:ℕ):ℝ) = (j:ℝ)+1 := by norm_num
    rw [hcast]
    nlinarith
  have hz' : Set.EqOn (fun u : ℝ => (causalKernel α t u - 0)^2)
      (fun _ => (0:ℝ)) (Set.Icc a b) := by
    intro u hu
    have huA : a ≤ u := hu.1
    have hut : t ≤ u := le_trans hleft huA
    simp [causalKernel, hut]
  have hz : Set.EqOn (fun u : ℝ => (causalKernel α t u - 0)^2)
      (fun _ => (0:ℝ)) (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using hz'
  rw [intervalIntegral.integral_congr hz]
  simp

/-- Cells starting at or after the causal boundary have zero projection
residual. -/
theorem causalKernelCellError_eq_zero_of_left
    {α t h : ℝ} {j : ℕ} (hh : 0 < h) (ht : t ≤ (j:ℝ)*h) :
    causalKernelCellError α t h j = 0 := by
  let a := (j:ℝ)*h
  let b := ((j+1:ℕ):ℝ)*h
  have hleft : t ≤ a := by simpa [a] using ht
  have hzero : causalKernel α t =ᵐ[volume.restrict (Set.Ioc a b)] (fun _ => (0:ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    simp [causalKernel, le_trans hleft hu.1.le]
  have havg : average (volume.restrict (Set.Ioc a b)) (causalKernel α t) = 0 := by
    rw [average_congr hzero]
    simp [average_eq]
  unfold causalKernelCellError
  rw [havg]
  have hab : a ≤ b := by
    dsimp [a,b]
    have hc : ((j+1:ℕ):ℝ) = (j:ℝ)+1 := by norm_num
    rw [hc]
    nlinarith [hh]
  have hz' : Set.EqOn (fun u : ℝ => (causalKernel α t u-0)^2)
      (fun _ => (0:ℝ)) (Set.Icc a b) := by
    intro u hu
    have hut : t ≤ u := le_trans hleft hu.1
    simp [causalKernel, hut]
  have hz : Set.EqOn (fun u : ℝ => (causalKernel α t u-0)^2)
      (fun _ => (0:ℝ)) (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using hz'
  rw [intervalIntegral.integral_congr hz]
  simp

/-- Full finite-grid assembly of the scalar cell-average residuals. The
regular cells telescope, the at-most-two cells around the moving singularity
are estimated by their exact energy, and every cell to the right vanishes. -/
theorem causalKernel_dyadic_cell_error_sum_le
    {α t h : ℝ} {N M : ℕ} (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hNM : N+2 ≤ M) (hgrid : (M:ℝ)*h = 1)
    (hleft : ((N+1:ℕ):ℝ)*h ≤ t)
    (hright : t ≤ ((N+2:ℕ):ℝ)*h) :
    (∑ j ∈ Finset.range M, causalKernelCellError α t h j) ≤
      ((Real.Gamma α)⁻¹)^2 *
        (h^(2*α-1) + ((2*h)^(2*α-1))/(2*α-1) + h) := by
  let E : ℕ → ℝ := causalKernelCellError α t h
  have hh0 : 0 ≤ h := hh.le
  have hM : (N+2:ℕ) ≤ M := hNM
  have hboundgrid : ((N+2:ℕ):ℝ)*h ≤ 1 := by
    calc
      ((N+2:ℕ):ℝ)*h ≤ (M:ℝ)*h := mul_le_mul_of_nonneg_right (by exact_mod_cast hM) hh0
      _ = 1 := hgrid
  have ha0 : 0 ≤ (N:ℝ)*h := mul_nonneg (Nat.cast_nonneg _) hh0
  have hab : (N:ℝ)*h ≤ ((N+1:ℕ):ℝ)*h := by
    have hc : ((N+1:ℕ):ℝ) = (N:ℝ)+1 := by norm_num
    rw [hc]
    nlinarith
  have hbc : ((N+1:ℕ):ℝ)*h ≤ ((N+2:ℕ):ℝ)*h := by
    have hc1 : ((N+1:ℕ):ℝ) = (N:ℝ)+1 := by norm_num
    have hc2 : ((N+2:ℕ):ℝ) = (N:ℝ)+2 := by norm_num
    rw [hc1, hc2]
    nlinarith
  have hca : (N:ℝ)*h ≤ ((N+2:ℕ):ℝ)*h := le_trans hab hbc
  have hleft' : ((N:ℝ)*h)+h ≤ t := by
    have hc : ((N+1:ℕ):ℝ) = (N:ℝ)+1 := by norm_num
    rw [hc] at hleft
    nlinarith
  have hends : ((N+2:ℕ):ℝ)*h ≤ 1 := hboundgrid
  have hcellA : 0 ≤ (N:ℝ)*h := ha0
  have hcellB : 0 ≤ ((N+1:ℕ):ℝ)*h := le_trans ha0 hab
  have hcellC : 0 ≤ ((N+2:ℕ):ℝ)*h := le_trans hcellB hbc
  have htail : ∑ j ∈ Finset.Ico (N+2) M, E j = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hjN : N+2 ≤ j := (Finset.mem_Ico.mp hj).1
    exact causalKernelCellError_eq_zero_of_right hh hright hjN
  have hsplit : (∑ j ∈ Finset.range M, E j) =
      ((∑ j ∈ Finset.range N, E j) + E N + E (N+1)) +
        ∑ j ∈ Finset.Ico (N+2) M, E j := by
    rw [← Finset.sum_range_add_sum_Ico E hNM,
      Finset.sum_range_succ, Finset.sum_range_succ]
  have hp : 0 < 2*α-1 := by linarith
  have hprefix : (∑ j ∈ Finset.range N, E j) ≤
      ((Real.Gamma α)⁻¹)^2 * (h^(2*α-1) + h) := by
    by_cases hα1 : α ≤ 1
    · have hregular := causalKernel_regular_grid_average_error_sum_le_power
        hα hα1 ht0 ht1 hh hleft'
      have hrewrite : (∑ j ∈ Finset.range N, E j) =
          (∑ j ∈ Finset.range N,
            ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
              (causalKernel α t u - average (volume.restrict
                (Set.Ioc ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h))) (causalKernel α t))^2) := by
        apply Finset.sum_congr rfl
        intro j hj
        rfl
      rw [hrewrite]
      nlinarith [hregular, mul_nonneg (sq_nonneg ((Real.Gamma α)⁻¹))
        (Real.rpow_nonneg hh0 (2*α-1))]
    · have hα1 : 1 ≤ α := le_of_not_ge hα1
      have hregular := causalKernel_regular_grid_average_error_sum_le_ge_one
        hα hα1 ht0 ht1 hh hleft'
      have hrewrite : (∑ j ∈ Finset.range N, E j) =
          (∑ j ∈ Finset.range N,
            ∫ u in ((j:ℝ)*h)..(((j+1:ℕ):ℝ)*h),
              (causalKernel α t u - average (volume.restrict
                (Set.Ioc ((j:ℝ)*h) (((j+1:ℕ):ℝ)*h))) (causalKernel α t))^2) := by
        apply Finset.sum_congr rfl
        intro j hj
        rfl
      rw [hrewrite]
      have hpow0 : 0 ≤ h^(2*α-1) := Real.rpow_nonneg hh0 _
      nlinarith [hregular, mul_nonneg (sq_nonneg ((Real.Gamma α)⁻¹)) hpow0]
  have hboundary : E N + E (N+1) ≤
      ((Real.Gamma α)⁻¹)^2 * ((2*h)^(2*α-1)/(2*α-1)) := by
    have hab' : (N:ℝ)*h < ((N+1:ℕ):ℝ)*h := by
      have hc : ((N+1:ℕ):ℝ) = (N:ℝ)+1 := by norm_num
      rw [hc]
      nlinarith
    have hbc' : ((N+1:ℕ):ℝ)*h < ((N+2:ℕ):ℝ)*h := by
      have hc1 : ((N+1:ℕ):ℝ) = (N:ℝ)+1 := by norm_num
      have hc2 : ((N+2:ℕ):ℝ) = (N:ℝ)+2 := by norm_num
      rw [hc1, hc2]
      nlinarith
    have hcellB1 : ((N+1:ℕ):ℝ)*h ≤ 1 := le_trans hbc hboundgrid
    have hf1 := causalKernel_intervalIntegrable_cell hα ht0 ht1 hcellA hab hcellB1
    have hf1sq := causalKernel_sq_intervalIntegrable_cell hα ht0 ht1 hcellA hab hcellB1
    have hf2 := causalKernel_intervalIntegrable_cell hα ht0 ht1 hcellB hbc'.le hends
    have hf2sq := causalKernel_sq_intervalIntegrable_cell hα ht0 ht1 hcellB hbc'.le hends
    have htwo := causalKernel_two_cell_average_error_le_power (L := (2:ℝ))
      hα hab' hbc' hcellA
      (by nlinarith [hleft]) hright hends (by positivity)
      (by have hc1 : ((N+1:ℕ):ℝ) = (N:ℝ)+1 := by norm_num
          have hc2 : ((N+2:ℕ):ℝ) = (N:ℝ)+2 := by norm_num
          calc
            ((N+2:ℕ):ℝ)*h - (N:ℝ)*h = 2*h := by rw [hc2]; ring
            _ ≤ 2*h := le_rfl)
      (by norm_num) hh0 hf1 hf1sq hf2 hf2sq
    have hrewrite1 : E N =
        ∫ u in ((N:ℝ)*h)..(((N+1:ℕ):ℝ)*h),
          (causalKernel α t u - average (volume.restrict
            (Set.Ioc ((N:ℝ)*h) (((N+1:ℕ):ℝ)*h))) (causalKernel α t))^2 := rfl
    have hrewrite2 : E (N+1) =
        ∫ u in (((N+1:ℕ):ℝ)*h)..(((N+2:ℕ):ℝ)*h),
          (causalKernel α t u - average (volume.restrict
            (Set.Ioc (((N+1:ℕ):ℝ)*h) (((N+2:ℕ):ℝ)*h))) (causalKernel α t))^2 := by
      rfl
    rw [hrewrite1, hrewrite2]
    have heq1 : (N:ℝ)*h+h = ((N+1:ℕ):ℝ)*h := by
      have hc : ((N+1:ℕ):ℝ) = (N:ℝ)+1 := by norm_num
      rw [hc]
      ring
    have heq2 : (N:ℝ)*h+2*h = ((N+2:ℕ):ℝ)*h := by
      have hc : ((N+2:ℕ):ℝ) = (N:ℝ)+2 := by norm_num
      rw [hc]
      ring
    exact htwo
  rw [hsplit, htail]
  calc
    (∑ j ∈ Finset.range N, E j) + E N + E (N+1) + 0 ≤
        ((Real.Gamma α)⁻¹)^2 * (h^(2*α-1) + h) +
          ((Real.Gamma α)⁻¹)^2 * ((2*h)^(2*α-1)/(2*α-1)) := by
            nlinarith [hprefix, hboundary]
    _ = ((Real.Gamma α)⁻¹)^2 *
        (h^(2*α-1) + ((2*h)^(2*α-1))/(2*α-1) + h) := by ring

/-- Rate form of the finite-grid estimate: the squared scalar projection
error decays like `h ^ min (2α-1) 1`, uniformly in the moving boundary. -/
theorem causalKernel_dyadic_cell_error_sum_le_rate
    {α t h : ℝ} {N M : ℕ} (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hNM : N+2 ≤ M) (hgrid : (M:ℝ)*h = 1)
    (hleft : ((N+1:ℕ):ℝ)*h ≤ t)
    (hright : t ≤ ((N+2:ℕ):ℝ)*h) :
    (∑ j ∈ Finset.range M, causalKernelCellError α t h j) ≤
      ((Real.Gamma α)⁻¹)^2 *
        (2 + 2^(2*α-1)/(2*α-1)) * h^(min (2*α-1) 1) := by
  have hbase := causalKernel_dyadic_cell_error_sum_le hα ht0 ht1 hh hh1
    hNM hgrid hleft hright
  let p := 2*α-1
  have hp : 0 < p := by dsimp [p]; linarith
  have hpow : 0 ≤ h^p := Real.rpow_nonneg hh.le p
  have hscaled : (2*h)^p = 2^p*h^p := by
    rw [Real.mul_rpow (by norm_num) hh.le]
  have hsmall : h^p ≤ h^(min p 1) := by
    by_cases hp1 : p ≤ 1
    · rw [min_eq_left hp1]
    · have hp1' : 1 ≤ p := le_of_not_ge hp1
      rw [min_eq_right hp1']
      exact Real.rpow_le_rpow_of_exponent_ge' hh.le hh1 (by norm_num) hp1'
  have hlin : h ≤ h^(min p 1) := by
    have hmin0 : 0 ≤ min p 1 := le_of_lt (lt_min hp (by norm_num))
    simpa [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge' hh.le hh1 hmin0 (min_le_right p 1))
  have hcombine : h^p + (2*h)^p/p + h ≤
      (2+2^p/p)*h^(min p 1) := by
    rw [hscaled]
    have hpdiv : 0 ≤ 2^p/p := div_nonneg (Real.rpow_nonneg (by norm_num) _) hp.le
    calc
      h^p + 2^p*h^p/p + h = h^p + (2^p/p)*h^p + h := by ring
      _ ≤ h^(min p 1) + (2^p/p)*h^(min p 1) + h^(min p 1) := by
        nlinarith [hsmall, hlin, mul_le_mul_of_nonneg_left hsmall hpdiv]
      _ = (2+2^p/p)*h^(min p 1) := by ring
  have hgamma : 0 ≤ ((Real.Gamma α)⁻¹)^2 := sq_nonneg _
  calc
    _ ≤ ((Real.Gamma α)⁻¹)^2 * (h^p + (2*h)^p/p + h) := by
      simpa [p, add_assoc, add_comm, add_left_comm] using hbase
    _ ≤ ((Real.Gamma α)⁻¹)^2 * ((2+2^p/p)*h^(min p 1)) :=
      mul_le_mul_of_nonneg_left hcombine hgamma
    _ = ((Real.Gamma α)⁻¹)^2 * (2+2^(2*α-1)/(2*α-1)) *
          h^(min (2*α-1) 1) := by
        dsimp [p]
        ring

/-- Uniform scalar projection-error rate on a complete dyadic partition of
the source interval. The floor choice isolates the cell containing the moving
causal boundary, including the endpoint and first-cell cases. -/
theorem causalKernel_dyadic_unit_cell_error_sum_le_rate
    {α t h : ℝ} {M : ℕ} (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hh : 0 < h) (hM : 2 ≤ M) (hgrid : (M:ℝ)*h = 1) :
    (∑ j ∈ Finset.range M, causalKernelCellError α t h j) ≤
      ((Real.Gamma α)⁻¹)^2 * (2 + 2^(2*α-1)/(2*α-1)) *
        h^(min (2*α-1) 1) := by
  have hh1 : h ≤ 1 := by
    have hMpos : 0 < (M:ℝ) := by positivity
    have hMle : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast (show 1 ≤ M by omega)
    have heq : h = 1/(M:ℝ) := by
      field_simp [ne_of_gt hMpos]
      nlinarith [hgrid]
    rw [heq, div_le_one hMpos]
    exact hMle
  have hh0 : 0 ≤ h := hh.le
  have hp : 0 < 2*α-1 := by linarith
  have hgamma : 0 ≤ ((Real.Gamma α)⁻¹)^2 := sq_nonneg _
  by_cases hsmall : t < h
  · have hMnat : 1 ≤ M := by omega
    have hMcast : (1:ℝ) ≤ (M:ℝ) := by exact_mod_cast hMnat
    have hMpos : (0:ℝ) < (M:ℝ) := by linarith
    have hgrid' : h = 1/(M:ℝ) := by
      field_simp [ne_of_gt hMpos]
      nlinarith [hgrid]
    have htbh : t ≤ h := le_of_lt hsmall
    have hf : IntervalIntegrable (causalKernel α t) volume 0 h := by
      have hunit := causalKernel_intervalIntegrable_unit hα ht0 ht1
      apply hunit.mono_set
      rw [Set.uIcc_of_le hh0, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      intro u hu
      exact ⟨hu.1, le_trans hu.2 hh1⟩
    have hf2 : IntervalIntegrable (fun u => (causalKernel α t u)^2) volume 0 h := by
      have hunit := causalKernel_sq_intervalIntegrable_unit hα ht0 ht1
      apply hunit.mono_set
      rw [Set.uIcc_of_le hh0, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      intro u hu
      exact ⟨hu.1, le_trans hu.2 hh1⟩
    have hE0 := causalKernel_singular_cell_average_error hα
      (by linarith) (by norm_num) ht0 htbh hh1 hf hf2
    have hterm0 : causalKernelCellError α t h 0 ≤
        ((Real.Gamma α)⁻¹)^2 * (h^(2*α-1)/(2*α-1)) := by
      simpa [causalKernelCellError] using hE0
    have htail : ∑ j ∈ Finset.Ico 1 M, causalKernelCellError α t h j = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Ico.mp hj).1
      have hjpos : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj1
      have hleft : h ≤ (j:ℝ)*h := by nlinarith
      exact causalKernelCellError_eq_zero_of_left hh (le_trans htbh hleft)
    have hsplit : (∑ j ∈ Finset.range M, causalKernelCellError α t h j) =
        causalKernelCellError α t h 0 +
          ∑ j ∈ Finset.Ico 1 M, causalKernelCellError α t h j := by
      rw [← Finset.sum_range_add_sum_Ico (causalKernelCellError α t h) hMnat,
        Finset.sum_range_succ]
      simp
    rw [hsplit, htail, add_zero]
    simp
    have hpow : h^(2*α-1) ≤ h^(min (2*α-1) 1) := by
      by_cases hp1 : 2*α-1 ≤ 1
      · rw [min_eq_left hp1]
      · rw [min_eq_right (le_of_not_ge hp1)]
        exact Real.rpow_le_rpow_of_exponent_ge' hh0 hh1 (by norm_num) (le_of_not_ge hp1)
    have hcoef : 1/(2*α-1) ≤ 2 + 2^(2*α-1)/(2*α-1) := by
      have h2 : (1:ℝ) ≤ 2^(2*α-1) := Real.one_le_rpow (by norm_num) hp.le
      have hdiv : 1/(2*α-1) ≤ 2^(2*α-1)/(2*α-1) :=
        div_le_div_of_nonneg_right h2 hp.le
      have hdiv0 : 0 ≤ 2^(2*α-1)/(2*α-1) := div_nonneg
        (Real.rpow_nonneg (by norm_num) _) hp.le
      linarith
    calc
      causalKernelCellError α t h 0 ≤
          ((Real.Gamma α)⁻¹)^2 * (h^(2*α-1)/(2*α-1) ) := hterm0
      _ ≤ ((Real.Gamma α)⁻¹)^2 *
          ((2 + 2^(2*α-1)/(2*α-1))*h^(min (2*α-1) 1)) := by
        apply mul_le_mul_of_nonneg_left _ hgamma
        have hpowdiv : h^(2*α-1)/(2*α-1) ≤
            h^(min (2*α-1) 1)/(2*α-1) :=
          div_le_div_of_nonneg_right hpow hp.le
        calc
          h^(2*α-1)/(2*α-1) ≤ h^(min (2*α-1) 1)/(2*α-1) := hpowdiv
          _ ≤ (2+2^(2*α-1)/(2*α-1))*h^(min (2*α-1) 1) := by
            have hx : 0 ≤ h^(min (2*α-1) 1) := Real.rpow_nonneg hh0 _
            have hc := mul_le_mul_of_nonneg_right hcoef hx
            calc
              h^(min (2*α-1) 1)/(2*α-1) =
                  (1/(2*α-1))*h^(min (2*α-1) 1) := by ring
              _ ≤ (2+2^(2*α-1)/(2*α-1))*h^(min (2*α-1) 1) := hc
      _ = _ := by ring
  · have hlarge : h ≤ t := le_of_not_gt hsmall
    let F : ℕ := Nat.floor (t/h)
    let q : ℕ := min F (M-1)
    let N : ℕ := q-1
    have hratio0 : 0 ≤ t/h := div_nonneg ht0 hh.le
    have hFle : (F:ℝ) ≤ t/h := Nat.floor_le hratio0
    have hFlt : t/h < (F:ℝ)+1 := Nat.lt_floor_add_one _
    have hqpos : 1 ≤ q := by
      have hFpos : 1 ≤ F := by
        by_contra hnot
        have hFzero : F = 0 := by omega
        have hratio : (1:ℝ) ≤ t/h := (le_div_iff₀ hh).2 (by nlinarith [hlarge])
        rw [hFzero] at hFlt
        linarith
      have hMpos : 1 ≤ M-1 := by omega
      dsimp [q]
      exact le_min hFpos hMpos
    have hqle : q ≤ M-1 := by dsimp [q]; exact min_le_right _ _
    have hNadd : N+1=q := by dsimp [N]; omega
    have hNadd2 : N+2=q+1 := by dsimp [N]; omega
    have hN2M : N+2 ≤ M := by rw [hNadd2]; omega
    have hqleF : q ≤ F := by dsimp [q]; exact min_le_left _ _
    have hleft : ((N+1:ℕ):ℝ)*h ≤ t := by
      rw [hNadd]
      by_cases hFcap : F ≤ M-1
      · have hqeq : q=F := min_eq_left hFcap
        rw [hqeq]
        have : (F:ℝ)*h ≤ t := (le_div_iff₀ hh).mp hFle
        exact this
      · have hqeq : q=M-1 := min_eq_right (le_of_not_ge hFcap)
        rw [hqeq]
        have hMF : M ≤ F := by omega
        have hratio : (M:ℝ) ≤ t/h := le_trans (by exact_mod_cast hMF) hFle
        have htimes : (M:ℝ)*h ≤ t := (le_div_iff₀ hh).mp hratio
        have hMreal : ((M-1:ℕ):ℝ) ≤ (M:ℝ) := by exact_mod_cast (Nat.sub_le M 1)
        calc
          ((M-1:ℕ):ℝ)*h ≤ (M:ℝ)*h := mul_le_mul_of_nonneg_right hMreal hh0
          _ ≤ t := htimes
    have hright : t ≤ ((N+2:ℕ):ℝ)*h := by
      rw [hNadd2]
      by_cases hFcap : F ≤ M-1
      · have hqeq : q=F := min_eq_left hFcap
        rw [hqeq]
        have hFlt' : t < ((F:ℝ)+1)*h := (div_lt_iff₀ hh).mp hFlt
        have hcast : ((F+1:ℕ):ℝ) = (F:ℝ)+1 := by norm_num
        rw [hcast]
        exact hFlt'.le
      · have hqeq : q=M-1 := min_eq_right (le_of_not_ge hFcap)
        rw [hqeq]
        have hcast : ((M-1+1:ℕ):ℝ) = (M:ℝ) := by
          congr 1
          omega
        rw [hcast]
        calc
          t ≤ 1 := ht1
          _ = (M:ℝ)*h := hgrid.symm
    exact causalKernel_dyadic_cell_error_sum_le_rate hα ht0 ht1 hh hh1
      hN2M hgrid hleft hright

end BrownianSharp.AlignmentFractionalDyadicProjection
