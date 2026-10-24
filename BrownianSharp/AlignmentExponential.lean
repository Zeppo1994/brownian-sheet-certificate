import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import BrownianSharp.GaussianRows
import BrownianSharp.Statistics
import BrownianSharp.GaussianGridStatistics
import BrownianSharp.GaussianSupport
import BrownianSharp.ActualConcentration
import BrownianSharp.NativeVarianceBound
import BrownianSharp.EventualRates
import BrownianSharp.GaussianEhrhardCertified
import BrownianSharp.NativeUniformConfinement
import BrownianSharp.SmoothVarianceBound
import BrownianSharp.SmoothGridConfinement
import BrownianSharp.SheetProductComparison
import BrownianSharp.AlignmentGaussianRates
import BrownianSharp.UniformSharpCertified

/-!
# Exponential-average shortcut for the Brownian alignment

This module proves a finite-dimensional log-cosh shortcut, including its
convexity, atomlessness, unboundedness, and a median/PV lower-tail theorem
conditional only on the standard set-level Gaussian Ehrhard inequality.
-/

open scoped BigOperators

open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology

namespace BrownianSharp.AlignmentExponential

/-- A finite exponential sum of linear functionals. -/
noncomputable def exponentialSum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ι → E →L[ℝ] ℝ) (x : E) : ℝ :=
  ∑ i, Real.exp (a i x)

/-- Exponential sums of linear functionals are convex. -/
theorem exponentialSum_convexOn {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ι → E →L[ℝ] ℝ) :
    ConvexOn ℝ Set.univ (exponentialSum a) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy u v hu hv huv
  dsimp [exponentialSum]
  calc
    (∑ i, Real.exp ((a i) (u • x + v • y))) ≤
        ∑ i, (u * Real.exp (a i x) + v * Real.exp (a i y)) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := convexOn_exp.2 (Set.mem_univ (a i x)) (Set.mem_univ (a i y)) hu hv huv
      simpa [map_add, map_smul, smul_eq_mul] using h
    _ = u * (∑ i, Real.exp (a i x)) + v * (∑ i, Real.exp (a i y)) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The log-sum-exp statistic. -/
noncomputable def logExponentialAverage {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ι → E →L[ℝ] ℝ) (x : E) : ℝ := Real.log (exponentialSum a x)

/-- Finite Holder inequality for two exponential sums. The proof normalizes
both families to sum to one and applies weighted AM--GM term by term. -/
theorem exponentialSum_holder {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ι → E →L[ℝ] ℝ) (x y : E) (u v : ℝ)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    exponentialSum a (u • x + v • y) ≤
      (exponentialSum a x) ^ u * (exponentialSum a y) ^ v := by
  classical
  let sx := exponentialSum a x
  let sy := exponentialSum a y
  have hsx : 0 < sx := by dsimp [sx, exponentialSum]; positivity
  have hsy : 0 < sy := by dsimp [sy, exponentialSum]; positivity
  have hterm (i : ι) :
      Real.exp (a i (u • x + v • y)) =
        sx ^ u * sy ^ v *
          ((Real.exp (a i x) / sx) ^ u * (Real.exp (a i y) / sy) ^ v) := by
    rw [show a i (u • x + v • y) = u * a i x + v * a i y by simp, Real.exp_add]
    rw [Real.rpow_def_of_pos hsx, Real.rpow_def_of_pos hsy,
      Real.rpow_def_of_pos (div_pos (Real.exp_pos _) hsx),
      Real.rpow_def_of_pos (div_pos (Real.exp_pos _) hsy)]
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) hsx.ne', Real.log_div (ne_of_gt (Real.exp_pos _)) hsy.ne',
      Real.log_exp, Real.log_exp]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring_nf
  calc
    exponentialSum a (u • x + v • y) =
        sx ^ u * sy ^ v * ∑ i, ((Real.exp (a i x) / sx) ^ u *
          (Real.exp (a i y) / sy) ^ v) := by
      change (∑ i, Real.exp (a i (u • x + v • y))) =
          sx ^ u * sy ^ v * ∑ i, ((Real.exp (a i x) / sx) ^ u *
            (Real.exp (a i y) / sy) ^ v)
      calc
        _ = ∑ i, (sx ^ u * sy ^ v * ((Real.exp (a i x) / sx) ^ u *
              (Real.exp (a i y) / sy) ^ v)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i
        _ = sx ^ u * sy ^ v * ∑ i, ((Real.exp (a i x) / sx) ^ u *
              (Real.exp (a i y) / sy) ^ v) := by rw [← Finset.mul_sum]
    _ ≤ sx ^ u * sy ^ v * ∑ i,
          (u * (Real.exp (a i x) / sx) + v * (Real.exp (a i y) / sy)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro i hi
      exact Real.geom_mean_le_arith_mean2_weighted hu hv
        (by positivity) (by positivity) huv
    _ = sx ^ u * sy ^ v := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hsumx : (∑ i, Real.exp (a i x) / sx) = 1 := by
        rw [← Finset.sum_div, show (∑ i, Real.exp (a i x)) = sx by rfl, div_self hsx.ne']
      have hsumy : (∑ i, Real.exp (a i y) / sy) = 1 := by
        rw [← Finset.sum_div, show (∑ i, Real.exp (a i y)) = sy by rfl, div_self hsy.ne']
      rw [hsumx, hsumy]
      simp [huv]

/-- Log-sum-exp of finitely many linear functionals is convex. -/
theorem logExponentialAverage_convexOn {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ι → E →L[ℝ] ℝ) :
    ConvexOn ℝ Set.univ (logExponentialAverage a) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy u v hu hv huv
  dsimp [logExponentialAverage]
  have hxpos : 0 < exponentialSum a x := by
    dsimp [exponentialSum]; positivity
  have hypos : 0 < exponentialSum a y := by
    dsimp [exponentialSum]; positivity
  have hzpos : 0 < exponentialSum a (u • x + v • y) := by
    dsimp [exponentialSum]; positivity
  have h := exponentialSum_holder a x y u v hu hv huv
  calc
    Real.log (exponentialSum a (u • x + v • y)) ≤
        Real.log ((exponentialSum a x) ^ u * (exponentialSum a y) ^ v) :=
      Real.log_le_log hzpos h
    _ = u * Real.log (exponentialSum a x) + v * Real.log (exponentialSum a y) := by
      rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hxpos _))
        (ne_of_gt (Real.rpow_pos_of_pos hypos _)),
        Real.log_rpow hxpos, Real.log_rpow hypos]

/-- Add a sign coordinate to turn a finite cosh sum into a finite exponential sum. -/
noncomputable def signedFunctional {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ι → E →L[ℝ] ℝ) : (ι × Bool) → E →L[ℝ] ℝ :=
  fun ib => if ib.2 then a ib.1 else -a ib.1

/-- Log of a finite average of cosh of linear functionals is convex. The
normalizing factor and any positive scalar multiplying the average contribute
only constants to the logarithm. -/
noncomputable def logCoshSum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ι → E →L[ℝ] ℝ) (x : E) : ℝ :=
  Real.log (∑ i, Real.cosh (a i x))

theorem logCoshSum_convexOn {ι E : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ι → E →L[ℝ] ℝ) :
    ConvexOn ℝ Set.univ (logCoshSum a) := by
  classical
  let b : (ι × Bool) → E →L[ℝ] ℝ := signedFunctional a
  have hb := logExponentialAverage_convexOn b
  have hsum (x : E) : exponentialSum b x =
      2 * (∑ i, Real.cosh (a i x)) := by
    dsimp [exponentialSum, b, signedFunctional]
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte]
    calc
      (∑ i, (Real.exp (a i x) + Real.exp (-(a i x)))) =
          ∑ i, 2 * Real.cosh (a i x) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.cosh_eq]
        ring
      _ = 2 * (∑ i, Real.cosh (a i x)) := by rw [← Finset.mul_sum]
  have hpos (x : E) : 0 < ∑ i, Real.cosh (a i x) := by
    apply Finset.sum_pos
    · intro i hi
      exact Real.cosh_pos _
    · exact Finset.univ_nonempty_iff.mpr ‹Nonempty ι›
  have heq (x : E) : logCoshSum a x = logExponentialAverage b x - Real.log 2 := by
    rw [logCoshSum, logExponentialAverage, hsum x, Real.log_mul (by norm_num) (ne_of_gt (hpos x))]
    ring
  have hconv : ConvexOn ℝ Set.univ (fun x => logExponentialAverage b x - Real.log 2) := by
    convert hb.add_const (-Real.log 2) using 1
  convert hconv using 1
  funext x
  exact heq x

/-- Continuous linear functional corresponding to one row of a finite matrix. -/
noncomputable def rowFunctional {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : ι → κ → ℝ) (i : ι) : (κ → ℝ) →L[ℝ] ℝ := by
  let R : (κ → ℝ) →L[ℝ] (ι → ℝ) :=
    ⟨BrownianSharp.rowEvaluation A,
      BrownianSharp.rowEvaluation A |>.continuous_of_finiteDimensional⟩
  exact (ContinuousLinearMap.proj i).comp R

/-- Log of the empirical cosh average; this is nonnegative, vanishes at zero,
and is convex for every real scale. -/
noncomputable def logMeanCosh {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : ι → κ → ℝ) (a : ℝ) (x : κ → ℝ) : ℝ :=
  Real.log ((∑ i, Real.cosh (a * BrownianSharp.rowEvaluation A x i)) /
    (Fintype.card ι : ℝ))

/-- Log of a finite average of cosh of linear row functionals is convex. -/
theorem logMeanCosh_convexOn {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (a : ℝ) :
    ConvexOn ℝ Set.univ (logMeanCosh A a) := by
  let L : ι → (κ → ℝ) →L[ℝ] ℝ := fun i => a • rowFunctional A i
  have h := logCoshSum_convexOn L
  have hpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  have hEq (x : κ → ℝ) : logMeanCosh A a x =
      logCoshSum L x - Real.log (Fintype.card ι : ℝ) := by
    dsimp [logMeanCosh, logCoshSum]
    have hrow (i : ι) : L i x = a * BrownianSharp.rowEvaluation A x i := by
      simp [L, rowFunctional, BrownianSharp.rowEvaluation]
    simp_rw [hrow]
    rw [Real.log_div (ne_of_gt (by positivity)) (ne_of_gt hpos)]
  have hconv : ConvexOn ℝ Set.univ
      (fun x => logCoshSum L x - Real.log (Fintype.card ι : ℝ)) := by
    convert h.add_const (-Real.log (Fintype.card ι : ℝ)) using 1
  convert hconv using 1
  funext x
  exact hEq x

/-- The empirical log-cosh statistic is continuous on coefficient space. -/
theorem logMeanCosh_continuous {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (a : ℝ) : Continuous (logMeanCosh A a) := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hNpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  have hsum : Continuous (fun x : κ → ℝ =>
      ∑ i, Real.cosh (a * BrownianSharp.rowEvaluation A x i)) := by
    apply continuous_finsetSum
    intro i hi
    have hlin : Continuous (rowFunctional A i) := (rowFunctional A i).continuous
    have hrow : Continuous (fun x : κ → ℝ =>
        a * BrownianSharp.rowEvaluation A x i) := by
      have hEq : (fun x : κ → ℝ => a * BrownianSharp.rowEvaluation A x i) =
          fun x => a * rowFunctional A i x := by
        funext x
        simp [rowFunctional, BrownianSharp.rowEvaluation]
      rw [hEq]
      exact continuous_const.mul hlin
    exact Real.continuous_cosh.comp hrow
  have hratio : Continuous (fun x : κ → ℝ =>
      (∑ i, Real.cosh (a * BrownianSharp.rowEvaluation A x i)) /
        (Fintype.card ι : ℝ)) := hsum.div_const _
  have hpos (x : κ → ℝ) : 0 <
      (∑ i, Real.cosh (a * BrownianSharp.rowEvaluation A x i)) /
        (Fintype.card ι : ℝ) := by
    apply div_pos
    · apply Finset.sum_pos
      · intro i hi
        exact Real.cosh_pos _
      · exact Finset.univ_nonempty_iff.mpr ‹Nonempty ι›
    · exact hNpos
  change Continuous (fun x : κ → ℝ => Real.log
    ((∑ i, Real.cosh (a * BrownianSharp.rowEvaluation A x i)) /
      (Fintype.card ι : ℝ)))
  exact hratio.log fun x => ne_of_gt (hpos x)

/-- The empirical log-cosh statistic is zero at the origin. -/
theorem logMeanCosh_zero {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (a : ℝ) : logMeanCosh A a 0 = 0 := by
  have hN : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  simp [logMeanCosh, BrownianSharp.rowEvaluation, Real.cosh_zero, hN]

/-- The empirical log-cosh statistic is nonnegative everywhere. -/
theorem logMeanCosh_nonneg {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (a : ℝ) (x : κ → ℝ) : 0 ≤ logMeanCosh A a x := by
  have hNpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  have hsum : (Fintype.card ι : ℝ) ≤
      ∑ i, Real.cosh (a * BrownianSharp.rowEvaluation A x i) := by
    calc
      (Fintype.card ι : ℝ) = ∑ i : ι, (1 : ℝ) := by simp
      _ ≤ ∑ i, Real.cosh (a * BrownianSharp.rowEvaluation A x i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact Real.one_le_cosh _
  apply Real.log_nonneg
  apply (one_le_div hNpos).2
  exact hsum

/-- Every strictly positive level of a convex function vanishing at the origin
is contained in the frontier of its weak sublevel set. The proof uses a nearby
outward dilation, whose value is forced above the level by convexity. -/
theorem convex_positive_level_subset_frontier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (hconvex : ConvexOn ℝ Set.univ f) (hzero : f 0 = 0)
    (r : ℝ) (hr : 0 < r) :
    {x | f x = r} ⊆ frontier {x | f x ≤ r} := by
  intro x hx
  have hxsub : x ∈ {y | f y ≤ r} := by simp [hx.le]
  rw [mem_frontier_iff_notMem_interior hxsub]
  intro hxint
  let c : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  have hc_tendsto : Tendsto c atTop (𝓝 1) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hrecip : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    simpa [c] using hconst.add hrecip
  have hscale_tendsto : Tendsto (fun n => c n • x) atTop (𝓝 x) := by
    have hconstx : Tendsto (fun _ : ℕ => x) atTop (𝓝 x) := tendsto_const_nhds
    have hpair : Tendsto (fun n => (c n, x)) atTop (𝓝 (1, x)) := by
      simpa only [nhds_prod_eq] using hc_tendsto.prodMk hconstx
    have h := (continuous_smul.tendsto (1, x)).comp hpair
    simpa [Function.comp_def] using h
  have hevent : ∀ᶠ n in atTop, c n • x ∈ interior {y | f y ≤ r} :=
    hscale_tendsto.eventually (isOpen_interior.mem_nhds hxint)
  obtain ⟨n, hn⟩ := hevent.exists
  have hcpos : 0 < c n := by
    dsimp [c]
    positivity
  have hcgt : 1 < c n := by
    dsimp [c]
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hrecip : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hcoeff1 : 0 ≤ (c n)⁻¹ := by positivity
  have hcoeff2 : 0 ≤ 1 - (c n)⁻¹ := by
    have hle : (c n)⁻¹ ≤ 1 := (inv_le_one₀ hcpos).2 (le_of_lt hcgt)
    linarith
  have hcoeffsum : (c n)⁻¹ + (1 - (c n)⁻¹) = 1 := by ring
  have hconv := hconvex.2 (Set.mem_univ (c n • x)) (Set.mem_univ (0 : E))
    hcoeff1 hcoeff2 hcoeffsum
  have harg : (c n)⁻¹ • (c n • x) + (1 - (c n)⁻¹) • (0 : E) = x := by
    simp [smul_smul, hcpos.ne']
  rw [harg] at hconv
  have hle : r ≤ f (c n • x) / c n := by
    have hconv' : f x ≤ (c n)⁻¹ * f (c n • x) := by
      simpa [hzero, smul_eq_mul] using hconv
    rw [hx] at hconv'
    simpa [div_eq_mul_inv, mul_comm] using hconv'
  have hscaled : c n * r ≤ f (c n • x) := by
    nlinarith [(le_div_iff₀ hcpos).mp hle]
  have hlarge : r < f (c n • x) := by nlinarith [hr, hcgt]
  have hnot : ¬ c n • x ∈ {y | f y ≤ r} := by
    simp only [Set.mem_setOf_eq]
    exact not_le_of_gt hlarge
  exact hnot (interior_subset hn)

/-- Positive levels of a continuous convex function vanishing at zero are
Gaussian-null in finite coefficient space, because they sit on a convex
frontier and the Gaussian law is absolutely continuous. -/
theorem convex_positive_level_measure_zero_of_ac
    {κ : Type*} [Fintype κ]
    (μ : MeasureTheory.Measure (κ → ℝ))
    (hac : μ ≪ (MeasureTheory.volume : MeasureTheory.Measure (κ → ℝ)))
    (f : (κ → ℝ) → ℝ) (hconvex : ConvexOn ℝ Set.univ f)
    (hzero : f 0 = 0) (r : ℝ) (hr : 0 < r) :
    μ {x | f x = r} = 0 := by
  apply hac
  apply measure_mono_null (convex_positive_level_subset_frontier f hconvex hzero r hr)
  have hsublevel : Convex ℝ {x : κ → ℝ | f x ≤ r} := by
    simpa using hconvex.convex_le r
  exact Convex.addHaar_frontier
    (μ := (MeasureTheory.volume : MeasureTheory.Measure (κ → ℝ))) hsublevel

/-- In particular, every strictly positive level of a finite log-cosh average
is null under any coefficient law absolutely continuous with respect to
Lebesgue measure. -/
theorem logMeanCosh_positive_level_measure_zero
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (μ : MeasureTheory.Measure (κ → ℝ))
    (hac : μ ≪ (MeasureTheory.volume : MeasureTheory.Measure (κ → ℝ)))
    (A : ι → κ → ℝ) (a r : ℝ) (hr : 0 < r) :
    μ {x | logMeanCosh A a x = r} = 0 := by
  exact convex_positive_level_measure_zero_of_ac μ hac (logMeanCosh A a)
    (logMeanCosh_convexOn A a) (logMeanCosh_zero A a) r hr

/-- With standard Gaussian row marginals, the zero level is null as soon as
the scale is nonzero: a zero log-average forces every row evaluation to vanish,
and one row already has a continuous Gaussian law. -/
theorem logMeanCosh_zero_level_measure_zero
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (hunit : ∀ i, ∑ k, A i k ^ 2 = 1)
    (a : ℝ) (ha : a ≠ 0) :
    productStandardGaussian κ {x | logMeanCosh A a x = 0} = 0 := by
  classical
  let μ := productStandardGaussian κ
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hNpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  have hN : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hNpos
  have hrowLaw := normalized_matrix_row_hasLaw A hunit i
  have hrowLaw' : HasLaw (fun x : κ → ℝ => BrownianSharp.rowEvaluation A x i)
      (gaussianReal 0 1) μ := by
    convert hrowLaw using 1 <;> funext x <;> simp [BrownianSharp.rowEvaluation]
  have hsingle : gaussianReal 0 1 ({0} : Set ℝ) = 0 := by
    apply (gaussianReal_absolutelyContinuous 0 (by norm_num : (1 : NNReal) ≠ 0))
    exact measure_singleton 0
  have hkernel : μ {x | BrownianSharp.rowEvaluation A x i = 0} = 0 := by
    calc
      μ {x | BrownianSharp.rowEvaluation A x i = 0} =
          (μ.map (fun x : κ → ℝ => BrownianSharp.rowEvaluation A x i)) {0} := by
            rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
            rfl
      _ = gaussianReal 0 1 ({0} : Set ℝ) := by rw [hrowLaw'.map_eq]
      _ = 0 := hsingle
  apply measure_mono_null ?_ hkernel
  intro x hx
  have hlog := hx
  dsimp [logMeanCosh] at hlog
  have hratioPos : 0 <
      (∑ j, Real.cosh (a * BrownianSharp.rowEvaluation A x j)) /
        (Fintype.card ι : ℝ) := by
    apply div_pos
    · apply Finset.sum_pos
      · intro j hj
        exact Real.cosh_pos _
      · exact Finset.univ_nonempty_iff.mpr (inferInstance : Nonempty ι)
    · exact hNpos
  have hratioOne :
      (∑ j, Real.cosh (a * BrownianSharp.rowEvaluation A x j)) /
        (Fintype.card ι : ℝ) = 1 :=
    Real.eq_one_of_pos_of_log_eq_zero hratioPos hlog
  let S : ℝ := ∑ j : ι, Real.cosh (a * BrownianSharp.rowEvaluation A x j)
  have hsumEq : S = (Fintype.card ι : ℝ) := by
    calc
      S = (S / (Fintype.card ι : ℝ)) * (Fintype.card ι : ℝ) := by
        field_simp [hN]
      _ = (Fintype.card ι : ℝ) := by
        rw [hratioOne]
        ring
  have hsumRaw :
      ∑ j : ι, Real.cosh (a * BrownianSharp.rowEvaluation A x j) =
        (Fintype.card ι : ℝ) := by
    simpa [S] using hsumEq
  have hsumZero :
      ∑ j, (Real.cosh (a * BrownianSharp.rowEvaluation A x j) - 1) = 0 := by
    rw [Finset.sum_sub_distrib, hsumRaw]
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have htermZero : Real.cosh (a * BrownianSharp.rowEvaluation A x i) - 1 = 0 := by
    have hle : Real.cosh (a * BrownianSharp.rowEvaluation A x i) - 1 ≤
        ∑ j : ι, (Real.cosh (a * BrownianSharp.rowEvaluation A x j) - 1) := by
      exact Finset.single_le_sum (f := fun j : ι =>
        Real.cosh (a * BrownianSharp.rowEvaluation A x j) - 1)
        (fun j hj => sub_nonneg.mpr
          (Real.one_le_cosh (a * BrownianSharp.rowEvaluation A x j)))
        (Finset.mem_univ i)
    have hnonneg := sub_nonneg.mpr (Real.one_le_cosh
      (a * BrownianSharp.rowEvaluation A x i))
    rw [hsumZero] at hle
    linarith
  have hargZero : a * BrownianSharp.rowEvaluation A x i = 0 := by
    by_contra hne
    have hlt : 1 < Real.cosh (a * BrownianSharp.rowEvaluation A x i) :=
      Real.one_lt_cosh.mpr hne
    linarith
  have hrowZero : BrownianSharp.rowEvaluation A x i = 0 :=
    (mul_eq_zero.mp hargZero).resolve_left ha
  exact hrowZero

/-- Every level of the finite log-mean-cosh statistic is atomless under
product standard Gaussian measure, provided the rows have unit variance and
the scale is nonzero. Positive levels use convex frontiers, the zero level
uses one nondegenerate row, and negative levels are empty. -/
theorem gaussian_logMeanCosh_all_levels_null
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (hunit : ∀ i, ∑ k, A i k ^ 2 = 1)
    (a : ℝ) (ha : a ≠ 0) (r : ℝ) :
    productStandardGaussian κ {x | logMeanCosh A a x = r} = 0 := by
  classical
  by_cases hr : 0 < r
  · exact logMeanCosh_positive_level_measure_zero
      (productStandardGaussian κ)
      (GaussianDensity.standardGaussian_absolutelyContinuous (ι := κ)) A a r hr
  · by_cases hr0 : r = 0
    · subst r
      exact logMeanCosh_zero_level_measure_zero A hunit a ha
    · have hrneg : r < 0 := by
        by_contra hnot
        have hnonneg : 0 ≤ r := le_of_not_gt hnot
        rcases lt_or_eq_of_le hnonneg with hpos | heq
        · exact (hr hpos).elim
        · exact hr0 heq.symm
      have hempty : {x : κ → ℝ | logMeanCosh A a x = r} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        have hnonneg := logMeanCosh_nonneg A a x
        linarith
      rw [hempty]
      simp

/-- The strict CDF of the Gaussian log-mean-cosh statistic lies in `(0,1)` at
every positive level once an unboundedness witness is supplied. The lower side
comes from continuity at the origin; the upper side comes from an open
superlevel set and full support of product Gaussian measure. -/
theorem gaussian_logMeanCosh_cdf_range
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (a : ℝ) (s : ℝ) (hs : 0 < s)
    (hhigh : ∃ x, s < logMeanCosh A a x) :
    0 < (productStandardGaussian κ).real {x | logMeanCosh A a x < s} ∧
      (productStandardGaussian κ).real {x | logMeanCosh A a x < s} < 1 := by
  classical
  let μ := productStandardGaussian κ
  let f := logMeanCosh A a
  let L : Set (κ → ℝ) := {x | f x < s}
  have hfcont : Continuous f := logMeanCosh_continuous A a
  have hLopen : IsOpen L := by
    simpa [L] using isOpen_lt hfcont continuous_const
  have hLne : L.Nonempty := by
    refine ⟨0, ?_⟩
    change logMeanCosh A a 0 < s
    rw [logMeanCosh_zero]
    exact hs
  have hLmass : 0 < μ L := GaussianDensity.standardGaussian_open_pos hLopen hLne
  have hLreal : 0 < μ.real L :=
    ENNReal.toReal_pos (ne_of_gt hLmass) (measure_ne_top μ L)
  obtain ⟨x, hx⟩ := hhigh
  let U : Set (κ → ℝ) := {y | s < f y}
  have hUopen : IsOpen U := by
    simpa [U] using isOpen_lt continuous_const hfcont
  have hUne : U.Nonempty := ⟨x, hx⟩
  have hUmass : 0 < μ U := GaussianDensity.standardGaussian_open_pos hUopen hUne
  have hUreal : 0 < μ.real U :=
    ENNReal.toReal_pos (ne_of_gt hUmass) (measure_ne_top μ U)
  have hUsubset : U ⊆ Lᶜ := by
    intro y hy
    change s < f y at hy
    change ¬ f y < s
    exact not_lt_of_ge hy.le
  have hcomp : 0 < μ.real Lᶜ := lt_of_lt_of_le hUreal
    (MeasureTheory.measureReal_mono hUsubset)
  have hsum : μ.real L + μ.real Lᶜ = 1 := by
    rw [MeasureTheory.measureReal_add_measureReal_compl hLopen.measurableSet]
    simp [μ]
  constructor
  · simpa [L] using hLreal
  · linarith

/-- Unit row norms make the empirical log-cosh statistic unbounded in every
nonzero scale: along any row's own coefficient vector, one cosh term grows
exponentially. -/
theorem gaussian_logMeanCosh_unbounded
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (hunit : ∀ i, ∑ k, A i k ^ 2 = 1)
    (a : ℝ) (ha : a ≠ 0) {s : ℝ} (hs : 0 < s) :
    ∃ x, s < logMeanCosh A a x := by
  classical
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  have hNpos : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  have hNge : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
    exact_mod_cast (Nat.succ_le_of_lt
      (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)))
  have htwoN : 1 < 2 * (Fintype.card ι : ℝ) := by nlinarith
  let z : ℝ := s + Real.log (2 * (Fintype.card ι : ℝ)) + 1
  have hzpos : 0 < z := by
    dsimp [z]
    have hlog : 0 < Real.log (2 * (Fintype.card ι : ℝ)) := Real.log_pos htwoN
    linarith
  let c : ℝ := z / |a|
  have hcpos : 0 < c := div_pos hzpos (abs_pos.mpr ha)
  let v : κ → ℝ := fun k => A i k
  let x : κ → ℝ := c • v
  have hrow : BrownianSharp.rowEvaluation A x i = c := by
    dsimp [x, v, BrownianSharp.rowEvaluation]
    calc
      (∑ k, A i k * (c * A i k)) = ∑ k, c * A i k ^ 2 := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = c * ∑ k, A i k ^ 2 := by rw [← Finset.mul_sum]
      _ = c := by rw [hunit i]; ring
  have habs : |a * c| = z := by
    rw [abs_mul, abs_of_pos hcpos]
    dsimp [c]
    field_simp [ha]
  have hcoshEq : Real.cosh (a * c) = Real.cosh z := by
    rw [← Real.cosh_abs, habs]
  have hcosh : Real.exp z / 2 ≤ Real.cosh (a * c) := by
    rw [hcoshEq, Real.cosh_eq]
    have hnonneg : 0 ≤ Real.exp (-z) := (Real.exp_pos _).le
    linarith
  have hsum : Real.cosh (a * c) ≤
      ∑ j : ι, Real.cosh (a * BrownianSharp.rowEvaluation A x j) := by
    have ht := Finset.single_le_sum (f := fun j : ι =>
      Real.cosh (a * BrownianSharp.rowEvaluation A x j))
      (fun j hj => (Real.cosh_pos _).le) (Finset.mem_univ i)
    simpa [hrow] using ht
  have hratio : Real.exp z / (2 * (Fintype.card ι : ℝ)) ≤
      (∑ j : ι, Real.cosh (a * BrownianSharp.rowEvaluation A x j)) /
        (Fintype.card ι : ℝ) := by
    have hfirst : Real.exp z / 2 ≤
        ∑ j : ι, Real.cosh (a * BrownianSharp.rowEvaluation A x j) := hcosh.trans hsum
    have hdiv := div_le_div_of_nonneg_right hfirst hNpos.le
    simpa [div_div, mul_assoc] using hdiv
  have hleftpos : 0 < Real.exp z / (2 * (Fintype.card ι : ℝ)) := by positivity
  have hlogle := Real.log_le_log hleftpos hratio
  have hlogleft : Real.log (Real.exp z / (2 * (Fintype.card ι : ℝ))) =
      z - Real.log (2 * (Fintype.card ι : ℝ)) := by
    rw [Real.log_div (ne_of_gt (Real.exp_pos _)) (by positivity), Real.log_exp]
  have hmain : s < logMeanCosh A a x := by
    dsimp [logMeanCosh]
    have hstrict : s < Real.log
        (Real.exp z / (2 * (Fintype.card ι : ℝ))) := by
      rw [hlogleft]
      dsimp [z]
      linarith
    exact lt_of_lt_of_le hstrict hlogle
  exact ⟨x, hmain⟩

/-- Unit row norms discharge the high-side premise of the Gaussian CDF range
theorem for every nonzero scale. -/
theorem gaussian_logMeanCosh_cdf_range_of_unit_rows
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (hunit : ∀ i, ∑ k, A i k ^ 2 = 1)
    (a : ℝ) (ha : a ≠ 0) (s : ℝ) (hs : 0 < s) :
    0 < (productStandardGaussian κ).real {x | logMeanCosh A a x < s} ∧
      (productStandardGaussian κ).real {x | logMeanCosh A a x < s} < 1 := by
  exact gaussian_logMeanCosh_cdf_range A a s hs
    (gaussian_logMeanCosh_unbounded A hunit a ha hs)

/-- The Gaussian log-mean-cosh statistic is square-integrable. Its pointwise
upper bound by the sum of absolute row coordinates reduces this to the
one-dimensional Gaussian second moment. -/
theorem gaussian_logMeanCosh_memLp_two
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (hunit : ∀ i, ∑ k, A i k ^ 2 = 1) (a : ℝ) :
    MemLp (logMeanCosh A a) 2 (productStandardGaussian κ) := by
  classical
  let μ := productStandardGaussian κ
  let Y : (κ → ℝ) → ℝ := fun x =>
    ∑ i : ι, |a * BrownianSharp.rowEvaluation A x i|
  have hterm : ∀ i : ι,
      MemLp (fun x : κ → ℝ => |a * BrownianSharp.rowEvaluation A x i|) 2 μ := by
    intro i
    have hrow := normalized_matrix_row_power_memLp_two A hunit i 1
    have hrow' : MemLp (fun x : κ → ℝ => BrownianSharp.rowEvaluation A x i) 2 μ := by
      convert hrow using 1 <;> simp [BrownianSharp.rowEvaluation]
    have hscaled := hrow'.const_mul a
    exact hscaled.norm
  have hY : MemLp Y 2 μ := by
    dsimp [Y]
    simpa using memLp_finsetSum (Finset.univ : Finset ι)
      (fun i _ => hterm i)
  have hbound (x : κ → ℝ) : logMeanCosh A a x ≤ Y x := by
    have htermBound (i : ι) : |a * BrownianSharp.rowEvaluation A x i| ≤ Y x :=
      Finset.single_le_sum (f := fun j : ι =>
        |a * BrownianSharp.rowEvaluation A x j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have hcosh (i : ι) :
        Real.cosh (a * BrownianSharp.rowEvaluation A x i) ≤ Real.exp (Y x) := by
      rw [Real.cosh_eq]
      have he1 := Real.exp_le_exp.mpr (le_abs_self (a * BrownianSharp.rowEvaluation A x i))
      have he2 := Real.exp_le_exp.mpr (le_abs_self (-(a * BrownianSharp.rowEvaluation A x i)))
      rw [abs_neg] at he2
      calc
        (Real.exp (a * BrownianSharp.rowEvaluation A x i) +
          Real.exp (-(a * BrownianSharp.rowEvaluation A x i))) / 2 ≤
          (Real.exp |a * BrownianSharp.rowEvaluation A x i| +
            Real.exp |a * BrownianSharp.rowEvaluation A x i|) / 2 := by
              exact div_le_div_of_nonneg_right (add_le_add he1 he2) (by norm_num)
        _ = Real.exp |a * BrownianSharp.rowEvaluation A x i| := by ring
        _ ≤ Real.exp (Y x) := Real.exp_le_exp.mpr (htermBound i)
    have hsum : (∑ i : ι, Real.cosh (a * BrownianSharp.rowEvaluation A x i)) ≤
        (Fintype.card ι : ℝ) * Real.exp (Y x) := by
      calc
        _ ≤ ∑ _i : ι, Real.exp (Y x) := Finset.sum_le_sum fun i _ => hcosh i
        _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
    have hN : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
    have havg : (∑ i : ι, Real.cosh (a * BrownianSharp.rowEvaluation A x i)) /
          (Fintype.card ι : ℝ) ≤ Real.exp (Y x) := (div_le_iff₀ hN).2 (by
      simpa [mul_comm] using hsum)
    have hpos : 0 < (∑ i : ι, Real.cosh (a * BrownianSharp.rowEvaluation A x i)) /
        (Fintype.card ι : ℝ) := by
      apply div_pos
      · apply Finset.sum_pos
        · intro i hi
          exact Real.cosh_pos _
        · exact Finset.univ_nonempty_iff.mpr (inferInstance : Nonempty ι)
      · exact hN
    dsimp [logMeanCosh]
    exact (Real.log_le_log hpos havg).trans_eq (Real.log_exp _)
  have hfmeas : AEStronglyMeasurable (logMeanCosh A a) μ :=
    (logMeanCosh_continuous A a).aestronglyMeasurable
  exact hY.mono' hfmeas (ae_of_all _ fun x => by
    have hnonneg : 0 ≤ logMeanCosh A a x := logMeanCosh_nonneg A a x
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hbound x)

/-- The mean of the Gaussian log-mean-cosh observable is strictly positive
when its scale is nonzero. -/
theorem gaussian_logMeanCosh_mean_pos
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (hunit : ∀ i, ∑ k, A i k ^ 2 = 1)
    (a : ℝ) (ha : a ≠ 0) :
    0 < (productStandardGaussian κ)[logMeanCosh A a] := by
  classical
  let μ := productStandardGaussian κ
  let X := logMeanCosh A a
  have hXlp := gaussian_logMeanCosh_memLp_two A hunit a
  have hXint : Integrable X μ := hXlp.integrable one_le_two
  have hnonneg : 0 ≤ᵐ[μ] X := ae_of_all _ (fun x => logMeanCosh_nonneg A a x)
  obtain ⟨x, hx⟩ := gaussian_logMeanCosh_unbounded A hunit a ha (by norm_num : 0 < (1 : ℝ))
  have hopen : IsOpen {y : κ → ℝ | 1 < X y} := by
    simpa [X] using isOpen_lt continuous_const (logMeanCosh_continuous A a)
  have hne : ({y : κ → ℝ | 1 < X y} : Set (κ → ℝ)).Nonempty := ⟨x, hx⟩
  have hmass : 0 < μ {y : κ → ℝ | 1 < X y} :=
    GaussianDensity.standardGaussian_open_pos hopen hne
  have hsub : {y : κ → ℝ | 1 < X y} ⊆ Function.support X := by
    intro y hy
    apply Function.mem_support.mpr
    intro hzero
    have hval : 1 < X y := by simpa [X] using hy
    rw [hzero] at hval
    norm_num at hval
  have hsupp : 0 < μ (Function.support X) := lt_of_lt_of_le hmass (measure_mono hsub)
  have hmean := (integral_pos_iff_support_of_nonneg_ae hnonneg hXint).2 hsupp
  exact hmean

/-- Actual median/PV lower-tail bound for the finite normalized cosh average.
All observable-specific hypotheses (convexity, nonnegativity, L²,
atomlessness, CDF range, and positive mean) are proved in this module. The
single remaining analytic premise is the set-level Gaussian Ehrhard
interpolation statement on coefficient space. -/
theorem gaussian_logMeanCosh_mean_lower_tail_of_ehrhard
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (hunit : ∀ i, ∑ k, A i k ^ 2 = 1)
    (p : ℝ) (hp : 0 < p)
    (hEhrhard : BrownianSharp.Concentration.GaussianEhrhard
      (κ → ℝ) (productStandardGaussian κ))
    (t : ℝ) (ht : 1 < t) :
    (productStandardGaussian κ).real
      {x | logMeanCosh A (Real.sqrt p) x -
        (productStandardGaussian κ)[logMeanCosh A (Real.sqrt p)] <
          -t * Real.sqrt (ProbabilityTheory.variance
            (logMeanCosh A (Real.sqrt p)) (productStandardGaussian κ))} ≤
      Real.exp (-Real.pi * (t - 1) ^ 2 / 1024) := by
  classical
  let μ := productStandardGaussian κ
  let X : (κ → ℝ) → ℝ := logMeanCosh A (Real.sqrt p)
  have ha : Real.sqrt p ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hconv : ConvexOn ℝ Set.univ X := by
    simpa [X] using logMeanCosh_convexOn A (Real.sqrt p)
  have hmeas : Measurable X := (logMeanCosh_continuous A (Real.sqrt p)).measurable
  have hAtom : ∀ r, μ {x | X x = r} = 0 := by
    intro r
    simpa [μ, X] using gaussian_logMeanCosh_all_levels_null A hunit
      (Real.sqrt p) ha r
  have hLp : MemLp X 2 μ := by
    simpa [μ, X] using gaussian_logMeanCosh_memLp_two A hunit (Real.sqrt p)
  have hmean : 0 < μ[X] := by
    simpa [μ, X] using gaussian_logMeanCosh_mean_pos A hunit
      (Real.sqrt p) ha
  let F : ℝ → ℝ := fun s => μ.real {x | X x < s}
  let G : ℝ → ℝ := BrownianSharp.Concentration.cdfGaussianQuantile F
  have hF : ∀ s, F s = μ.real {x | X x < s} := fun _ => rfl
  have hFRange : ∀ s, 0 < s → 0 < F s ∧ F s < 1 := by
    intro s hs
    simpa [F, μ, X] using gaussian_logMeanCosh_cdf_range_of_unit_rows
      A hunit (Real.sqrt p) ha s hs
  have hGconcave : ConcaveOn ℝ (Set.Ioi 0) G := by
    apply BrownianSharp.transformed_cdf_concave_of_set_ehrhard
      μ X hconv hmeas hAtom F G hF hFRange hEhrhard
    intro s
    rfl
  have hGrep : ∀ s, 0 < s → F s = BrownianSharp.Concentration.standardGaussianCDF (G s) := by
    intro s hs
    exact BrownianSharp.Concentration.cdfGaussianQuantile_representation F (hFRange s hs).1
      (hFRange s hs).2
  simpa [μ, X] using BrownianSharp.mean_lower_tail_of_transformed_cdf_concave_actual
    μ X hLp hmeas (fun x => logMeanCosh_nonneg A (Real.sqrt p) x)
    hmean hAtom F G hF hGconcave hGrep t ht

/-- Direct Paouris--Valettas form for the log-mean-cosh observable: its
median-centered lower tail is controlled at the positive-part scale itself.
This is the scale needed when the variance bound is transferred from the
normalized exponential average. The only analytic premise is set-level
Gaussian Ehrhard on coefficient space. -/
theorem gaussian_logMeanCosh_median_pospart_tail_of_ehrhard
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (hunit : ∀ i, ∑ k, A i k ^ 2 = 1)
    (p : ℝ) (hp : 0 < p)
    (hEhrhard : BrownianSharp.Concentration.GaussianEhrhard
      (κ → ℝ) (productStandardGaussian κ))
    (t : ℝ) (ht : 0 < t) :
    ∃ M : ℝ,
      (1 / 2 : ℝ) ≤ (productStandardGaussian κ).real
        {x | logMeanCosh A (Real.sqrt p) x ≤ M} ∧
      (1 / 2 : ℝ) ≤ (productStandardGaussian κ).real
        {x | M ≤ logMeanCosh A (Real.sqrt p) x} ∧
      (productStandardGaussian κ).real
        {x | logMeanCosh A (Real.sqrt p) x < M - t *
          (∫ x, max (logMeanCosh A (Real.sqrt p) x - M) 0
            ∂productStandardGaussian κ)} ≤
        Real.exp (-Real.pi * t ^ 2 / 512) := by
  classical
  let μ := productStandardGaussian κ
  let X : (κ → ℝ) → ℝ := logMeanCosh A (Real.sqrt p)
  have ha : Real.sqrt p ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hconv : ConvexOn ℝ Set.univ X := by
    simpa [X] using logMeanCosh_convexOn A (Real.sqrt p)
  have hmeas : Measurable X := (logMeanCosh_continuous A (Real.sqrt p)).measurable
  have hAtom : ∀ r, μ {x | X x = r} = 0 := by
    intro r
    simpa [μ, X] using gaussian_logMeanCosh_all_levels_null A hunit
      (Real.sqrt p) ha r
  have hLp : MemLp X 2 μ := by
    simpa [μ, X] using gaussian_logMeanCosh_memLp_two A hunit (Real.sqrt p)
  have hnonneg : ∀ x, 0 ≤ X x := by
    intro x
    exact logMeanCosh_nonneg A (Real.sqrt p) x
  let F : ℝ → ℝ := fun s => μ.real {x | X x < s}
  let G : ℝ → ℝ := BrownianSharp.Concentration.cdfGaussianQuantile F
  have hF : ∀ s, F s = μ.real {x | X x < s} := fun _ => rfl
  have hFRange : ∀ s, 0 < s → 0 < F s ∧ F s < 1 := by
    intro s hs
    simpa [F, μ, X] using gaussian_logMeanCosh_cdf_range_of_unit_rows
      A hunit (Real.sqrt p) ha s hs
  have hGconcave : ConcaveOn ℝ (Set.Ioi 0) G := by
    apply BrownianSharp.transformed_cdf_concave_of_set_ehrhard
      μ X hconv hmeas hAtom F G hF hFRange hEhrhard
    intro s
    rfl
  have hGrep : ∀ s, 0 < s → F s = BrownianSharp.Concentration.standardGaussianCDF (G s) := by
    intro s hs
    exact BrownianSharp.Concentration.cdfGaussianQuantile_representation F
      (hFRange s hs).1 (hFRange s hs).2
  obtain ⟨M, hMLt, hMGt⟩ :=
    BrownianSharp.Concentration.exists_two_sided_median_of_null_levels μ X hmeas hAtom
  have hMpos : 0 < M := by
    by_contra hnot
    have hMle : M ≤ 0 := le_of_not_gt hnot
    have hempty : {x | X x < M} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      linarith [hnonneg x]
    rw [hempty] at hMLt
    norm_num at hMLt
  have hFM : F M = 1 / 2 := by rw [hF]; exact hMLt
  have hGM : G M = 0 := by
    apply BrownianSharp.Concentration.standardGaussianCDF_strictMono.injective
    rw [← hGrep M hMpos, hFM,
      BrownianSharp.Concentration.standardGaussianCDF_zero]
  have hMLower : (1 / 2 : ℝ) ≤ μ.real {x | X x ≤ M} := by
    calc
      (1 / 2 : ℝ) = μ.real {x | X x < M} := hMLt.symm
      _ ≤ μ.real {x | X x ≤ M} := MeasureTheory.measureReal_mono
        (by intro x hx; change X x < M at hx; exact hx.le)
  have hMUpper : (1 / 2 : ℝ) ≤ μ.real {x | M ≤ X x} := by
    calc
      (1 / 2 : ℝ) = μ.real {x | M < X x} := hMGt.symm
      _ ≤ μ.real {x | M ≤ X x} := MeasureTheory.measureReal_mono
        (by intro x hx; change M < X x at hx; exact hx.le)
  have hEpos : 0 < ∫ x, max (X x - M) 0 ∂μ :=
    BrownianSharp.Concentration.pospart_integral_pos_of_positive_upper_median
      μ X hLp M (by
        have hnotzero : μ {x | M < X x} ≠ 0 := by
          intro hz
          have hreal : μ.real {x | M < X x} = 0 := by
            simp [Measure.real_def, hz]
          rw [hreal] at hMGt
          norm_num at hMGt
        exact ENNReal.toReal_pos hnotzero (measure_ne_top μ _))
  let Δ : ℝ := ∫ x, max (X x - M) 0 ∂μ
  have hΔ : 0 < Δ := by simpa [Δ] using hEpos
  have hδ : 0 < 4 * Δ := by positivity
  have hmy : M < M + 4 * Δ := by linarith
  have hweakInterval := BrownianSharp.Concentration.measure_median_interval_mass_ge_quarter_of_pospart
    μ X hLp hmeas M hMGt hEpos
  have hlevelpos : 0 < M + 4 * Δ := by linarith
  have hAtomY : μ.real {x | X x = M + 4 * Δ} = 0 := by
    have hzero := hAtom (M + 4 * Δ)
    simp [Measure.real_def, hzero]
  have hopenInterval := BrownianSharp.Concentration.measure_median_open_interval_mass_ge_quarter
    μ X hmeas M (M + 4 * Δ) hmy hweakInterval hAtomY
  have hrepY : F (M + 4 * Δ) =
      BrownianSharp.Concentration.standardGaussianCDF (G (M + 4 * Δ)) :=
    hGrep (M + 4 * Δ) hlevelpos
  have hquantile : Real.sqrt Real.pi / 4 ≤ G (M + 4 * Δ) :=
    BrownianSharp.Concentration.transformed_cdf_right_quantile_of_interval_mass
      μ X hmeas F G M (M + 4 * Δ) (Real.sqrt Real.pi / 4) hmy hF hrepY hMLt
      hopenInterval BrownianSharp.Concentration.standardGaussianCDF_strictMono
      BrownianSharp.Concentration.standardGaussianCDF_sqrt_pi_div_four_lt_three_quarters
  let q : ℝ := t / 4
  have hq : 0 < q := by dsimp [q]; linarith
  by_cases hthreshold : 0 < M - t * Δ
  · have hscale : M - q * (4 * Δ) = M - t * Δ := by
      dsimp [q]
      ring
    have hthreshold' : 0 < M - q * (4 * Δ) := by rw [hscale]; exact hthreshold
    have hFthreshold : F (M - q * (4 * Δ)) =
        μ.real {x | X x < M - q * (4 * Δ)} := hF _
    have hrepthreshold : F (M - q * (4 * Δ)) =
        (ProbabilityTheory.gaussianReal 0 1).real
          {z | z < G (M - q * (4 * Δ))} := by
      rw [hscale]
      exact hGrep (M - t * Δ) hthreshold
    have htail := BrownianSharp.Concentration.measure_median_lower_tail_le_of_transformed_cdf_concave
      μ X F G M (4 * Δ) (Real.sqrt Real.pi / 4) q hFthreshold hrepthreshold
      hGconcave hGM hquantile hthreshold' (by positivity)
      (by positivity) hq
    have hprob : μ.real {x | X x < M - t * Δ} ≤
        Real.exp (-Real.pi * t ^ 2 / 512) := by
      calc
        μ.real {x | X x < M - t * Δ} =
            μ.real {x | X x < M - q * (4 * Δ)} := by rw [hscale]
        _ ≤ Real.exp (-((Real.sqrt Real.pi / 4) * q) ^ 2 / 2) := htail
        _ = Real.exp (-Real.pi * t ^ 2 / 512) := by
          congr 1
          have hs : Real.sqrt Real.pi / 4 * q = Real.sqrt Real.pi * t / 16 := by
            dsimp [q]
            ring
          rw [hs, div_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
          norm_num
          ring
    refine ⟨M, ?_, ?_, ?_⟩
    · simpa [μ, X] using hMLower
    · simpa [μ, X] using hMUpper
    · simpa [μ, X, Δ] using hprob
  · have hlevel : M - t * Δ ≤ 0 := le_of_not_gt hthreshold
    have hempty : {x | X x < M - t * Δ} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hx
      linarith [hnonneg x]
    refine ⟨M, ?_, ?_, ?_⟩
    · simpa [μ, X] using hMLower
    · simpa [μ, X] using hMUpper
    · rw [hempty]
      simp
      positivity

/-- A global second-order envelope for the centered hyperbolic cosine. -/
theorem cosh_sub_one_le_sq_exp_abs (z : ℝ) :
    Real.cosh z - 1 ≤ z ^ 2 / 2 * Real.exp |z| := by
  have hcoshAbs : Real.cosh z ≤ Real.exp |z| := by
    rw [Real.cosh_eq]
    have h₁ : Real.exp z ≤ Real.exp |z| := Real.exp_le_exp.mpr (le_abs_self z)
    have h₂ : Real.exp (-z) ≤ Real.exp |z| := by
      apply Real.exp_le_exp.mpr
      simpa using (le_abs_self (-z))
    nlinarith
  by_cases hs : z ^ 2 ≤ 2
  · let w : ℝ := z ^ 2 / 2
    have hw0 : 0 ≤ w := by dsimp [w]; positivity
    have hwabs : w ≤ |z| := by
      dsimp [w]
      have hzabs : |z| ≤ 2 := by nlinarith [sq_abs z]
      have habs : 0 ≤ |z| := abs_nonneg z
      nlinarith [sq_abs z, mul_nonneg habs (sub_nonneg.mpr (show 2 - |z| ≥ 0 by linarith))]
    have hcosh : Real.cosh z ≤ Real.exp w := by
      simpa [w] using Real.cosh_le_exp_half_sq z
    have hExpSub : Real.exp w - 1 ≤ w * Real.exp w := by
      have h0 := Real.add_one_le_exp (-w)
      have h1 := mul_le_mul_of_nonneg_left h0 (Real.exp_pos w).le
      rw [Real.exp_neg] at h1
      field_simp [ne_of_gt (Real.exp_pos w)] at h1
      nlinarith
    have hExpAbs : Real.exp w ≤ Real.exp |z| := Real.exp_le_exp.mpr hwabs
    have hbound : w * Real.exp w ≤ w * Real.exp |z| :=
      mul_le_mul_of_nonneg_left hExpAbs hw0
    have hcalc : Real.cosh z - 1 ≤ w * Real.exp |z| := by
      calc
        Real.cosh z - 1 ≤ Real.exp w - 1 := by linarith
        _ ≤ w * Real.exp w := hExpSub
        _ ≤ w * Real.exp |z| := hbound
    simpa [w] using hcalc
  · have hz2 : 2 ≤ z ^ 2 := le_of_not_ge hs
    have hscaled : Real.exp |z| ≤ z ^ 2 / 2 * Real.exp |z| := by
      nlinarith [Real.exp_pos |z|]
    linarith [hcoshAbs]

/-- The scalar exponential moment of a Gaussian-law random variable, expressed
as an integral rather than through the mgf API. -/
theorem integral_exp_mul_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    {X : Ω → ℝ} {m : ℝ} {v : NNReal}
    (hX : ProbabilityTheory.HasLaw X (ProbabilityTheory.gaussianReal m v) P)
    (t : ℝ) :
    ∫ ω, Real.exp (t * X ω) ∂P =
      Real.exp (m * t + (v : ℝ) * t ^ 2 / 2) := by
  change ProbabilityTheory.mgf X P t = _
  rw [← ProbabilityTheory.mgf_id_map hX.aemeasurable, hX.map_eq,
    ProbabilityTheory.mgf_id_gaussianReal]

/-- The cosh moment of a centered Gaussian law follows by expanding cosh into
its two exponential terms and applying the exact Gaussian mgf twice. -/
theorem integral_cosh_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    {Z : Ω → ℝ} {q : NNReal}
    (hZ : ProbabilityTheory.HasLaw Z (ProbabilityTheory.gaussianReal 0 q) P)
    (a : ℝ) :
    ∫ ω, Real.cosh (a * Z ω) ∂P =
      Real.exp ((q : ℝ) * a ^ 2 / 2) := by
  have hpos : Integrable (fun ω => Real.exp (a * Z ω)) P := by
    exact hZ.integrable_comp (ProbabilityTheory.integrable_exp_mul_gaussianReal
      (μ := 0) (v := q) a)
  have hneg : Integrable (fun ω => Real.exp (-a * Z ω)) P := by
    exact hZ.integrable_comp (ProbabilityTheory.integrable_exp_mul_gaussianReal
      (μ := 0) (v := q) (-a))
  have hfun : (fun ω => Real.cosh (a * Z ω)) = fun ω =>
      (Real.exp (a * Z ω) + Real.exp (-a * Z ω)) / 2 := by
    funext ω
    rw [Real.cosh_eq]
    congr 1 <;> ring_nf
  rw [hfun, integral_div, integral_add hpos hneg,
    integral_exp_mul_of_hasLaw P hZ a, integral_exp_mul_of_hasLaw P hZ (-a)]
  simp

/-- A Gaussian hyperbolic cosine has a finite second moment. The square is
expanded into the two exponential moments at twice the argument. -/
theorem cosh_memLp_two_of_hasLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [IsProbabilityMeasure P]
    {Z : Ω → ℝ} {q : NNReal}
    (hZ : ProbabilityTheory.HasLaw Z (ProbabilityTheory.gaussianReal 0 q) P)
    (a : ℝ) : MemLp (fun ω => Real.cosh (a * Z ω)) 2 P := by
  have hmeas : AEStronglyMeasurable (fun ω => Real.cosh (a * Z ω)) P := by
    exact (Real.continuous_cosh.measurable.comp_aemeasurable
      (hZ.aemeasurable.const_mul a)).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  have hplus : Integrable (fun ω => Real.exp ((2 * a) * Z ω)) P :=
    hZ.integrable_comp (ProbabilityTheory.integrable_exp_mul_gaussianReal
      (μ := 0) (v := q) (2 * a))
  have hminus : Integrable (fun ω => Real.exp (-(2 * a) * Z ω)) P :=
    hZ.integrable_comp (ProbabilityTheory.integrable_exp_mul_gaussianReal
      (μ := 0) (v := q) (-(2 * a)))
  have hsq : (fun ω => Real.cosh (a * Z ω) ^ 2) = fun ω =>
      (Real.exp ((2 * a) * Z ω) + 2 + Real.exp (-(2 * a) * Z ω)) / 4 := by
    funext ω
    rw [Real.cosh_eq]
    calc
      ((Real.exp (a * Z ω) + Real.exp (-(a * Z ω))) / 2) ^ 2 =
          (Real.exp (a * Z ω) * Real.exp (a * Z ω) +
            2 * (Real.exp (a * Z ω) * Real.exp (-(a * Z ω))) +
            Real.exp (-(a * Z ω)) * Real.exp (-(a * Z ω))) / 4 := by ring_nf
      _ = (Real.exp (a * Z ω + a * Z ω) +
            2 * Real.exp (a * Z ω + -(a * Z ω)) +
            Real.exp (-(a * Z ω) + -(a * Z ω))) / 4 := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ = (Real.exp ((2 * a) * Z ω) + 2 +
            Real.exp (-(2 * a) * Z ω)) / 4 := by
        rw [show a * Z ω + -(a * Z ω) = 0 by ring, Real.exp_zero,
          show a * Z ω + a * Z ω = (2 * a) * Z ω by ring,
          show -(a * Z ω) + -(a * Z ω) = -(2 * a) * Z ω by ring]
        ring
  rw [hsq]
  exact ((hplus.add (integrable_const (2 : ℝ))).add hminus).div_const 4

/-- The product cosh moment of a correlated Gaussian pair. The laws of the sum
and difference are the two scalar Gaussian pushforwards; their variance values
are stated explicitly so callers can discharge them from the pair covariance. -/
theorem gaussianCoshProduct_of_sum_difference_laws
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    {X Y : Ω → ℝ} {qPlus qMinus : NNReal} {rho a : ℝ}
    (hPlus : HasLaw (fun ω => X ω + Y ω) (gaussianReal 0 qPlus) P)
    (hMinus : HasLaw (fun ω => X ω - Y ω) (gaussianReal 0 qMinus) P)
    (hqPlus : (qPlus : ℝ) = 2 + 2 * rho)
    (hqMinus : (qMinus : ℝ) = 2 - 2 * rho) :
    ∫ ω, Real.cosh (a * X ω) * Real.cosh (a * Y ω) ∂P =
      Real.exp (a ^ 2) * Real.cosh (a ^ 2 * rho) := by
  have hIntPlus : Integrable (fun ω => Real.cosh (a * (X ω + Y ω))) P := by
    have hbase : Integrable (fun z : ℝ => Real.cosh (a * z)) (gaussianReal 0 qPlus) := by
      have he1 := ProbabilityTheory.integrable_exp_mul_gaussianReal
        (μ := 0) (v := qPlus) a
      have he2 := ProbabilityTheory.integrable_exp_mul_gaussianReal
        (μ := 0) (v := qPlus) (-a)
      have hrew : (fun z : ℝ => Real.cosh (a * z)) =
          fun z => (Real.exp (a * z) + Real.exp (-a * z)) / 2 := by
        funext z
        rw [Real.cosh_eq]
        congr 1 <;> ring_nf
      rw [hrew]
      exact (he1.add he2).div_const 2
    exact hPlus.integrable_comp hbase
  have hIntMinus : Integrable (fun ω => Real.cosh (a * (X ω - Y ω))) P := by
    have hbase : Integrable (fun z : ℝ => Real.cosh (a * z)) (gaussianReal 0 qMinus) := by
      have he1 := ProbabilityTheory.integrable_exp_mul_gaussianReal
        (μ := 0) (v := qMinus) a
      have he2 := ProbabilityTheory.integrable_exp_mul_gaussianReal
        (μ := 0) (v := qMinus) (-a)
      have hrew : (fun z : ℝ => Real.cosh (a * z)) =
          fun z => (Real.exp (a * z) + Real.exp (-a * z)) / 2 := by
        funext z
        rw [Real.cosh_eq]
        congr 1 <;> ring_nf
      rw [hrew]
      exact (he1.add he2).div_const 2
    exact hMinus.integrable_comp hbase
  have hpoint : (fun ω => Real.cosh (a * X ω) * Real.cosh (a * Y ω)) =
      fun ω => (Real.cosh (a * (X ω + Y ω)) +
        Real.cosh (a * (X ω - Y ω))) / 2 := by
    funext ω
    have hsum : Real.cosh (a * X ω + a * Y ω) +
        Real.cosh (a * X ω - a * Y ω) =
          2 * (Real.cosh (a * X ω) * Real.cosh (a * Y ω)) := by
      rw [Real.cosh_add, Real.cosh_sub]
      ring
    have hlin1 : a * (X ω + Y ω) = a * X ω + a * Y ω := by ring
    have hlin2 : a * (X ω - Y ω) = a * X ω - a * Y ω := by ring
    rw [hlin1, hlin2]
    nlinarith [hsum]
  rw [hpoint, integral_div, integral_add hIntPlus hIntMinus,
    integral_cosh_of_hasLaw P hPlus a, integral_cosh_of_hasLaw P hMinus a]
  rw [hqPlus, hqMinus, Real.cosh_eq]
  field_simp
  rw [mul_add, ← Real.exp_add, ← Real.exp_add]
  congr 1 <;> ring_nf

/-- Gaussian row cosh covariance, with the sum and difference laws proved from
the independent standard coordinates. This is the finite-row form of the
manuscript identity `e⁻ᵖ Cov(cosh(√p X), cosh(√p Y)) = cosh(p ρ) - 1`. -/
theorem gaussianRows_coshProduct_mgf
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : MeasureTheory.Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ) (hG : ∀ i, Measurable (G i))
    (hLaw : ∀ i, P.map (G i) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (c d : ι → ℝ)
    (hc : ∑ i, c i ^ 2 = 1) (hd : ∑ i, d i ^ 2 = 1)
    (rho : ℝ) (hcd : ∑ i, c i * d i = rho) (hrho : |rho| ≤ 1)
    (a : ℝ) :
    ∫ ω, Real.cosh (a * GaussianRows.row G c ω) *
      Real.cosh (a * GaussianRows.row G d ω) ∂P =
      Real.exp (a ^ 2) * Real.cosh (a ^ 2 * rho) := by
  classical
  let cplus : ι → ℝ := fun i => c i + d i
  let cminus : ι → ℝ := fun i => c i - d i
  let rplus : ℝ := 2 + 2 * rho
  let rminus : ℝ := 2 - 2 * rho
  have hplusvar : ∑ i, cplus i ^ 2 = rplus := by
    dsimp [cplus, rplus]
    have hterm : ∀ i, (c i + d i) ^ 2 = c i ^ 2 + 2 * (c i * d i) + d i ^ 2 := by
      intro i; ring
    rw [show (∑ i, (c i + d i) ^ 2) =
        ∑ i, (c i ^ 2 + 2 * (c i * d i) + d i ^ 2) by
          apply Finset.sum_congr rfl; intro i hi; exact hterm i]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hc, hd, hcd]
    ring
  have hminusvar : ∑ i, cminus i ^ 2 = rminus := by
    dsimp [cminus, rminus]
    have hterm : ∀ i, (c i - d i) ^ 2 = c i ^ 2 - 2 * (c i * d i) + d i ^ 2 := by
      intro i; ring
    rw [show (∑ i, (c i - d i) ^ 2) =
        ∑ i, (c i ^ 2 - 2 * (c i * d i) + d i ^ 2) by
          apply Finset.sum_congr rfl; intro i hi; exact hterm i]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hc, hd, hcd]
    ring
  have hrplus : 0 ≤ rplus := by dsimp [rplus]; have := abs_le.mp hrho; linarith
  have hrminus : 0 ≤ rminus := by dsimp [rminus]; have := abs_le.mp hrho; linarith
  have hplusmap : P.map (GaussianRows.row G cplus) = gaussianReal 0 rplus.toNNReal := by
    rw [GaussianRows.row_law G hG hLaw hIndep cplus, hplusvar]
  have hminusmap : P.map (GaussianRows.row G cminus) = gaussianReal 0 rminus.toNNReal := by
    rw [GaussianRows.row_law G hG hLaw hIndep cminus, hminusvar]
  have hplusmeas : Measurable (GaussianRows.row G cplus) := by
    change Measurable (fun ω => ∑ i, cplus i * G i ω)
    exact Finset.measurable_fun_sum _ (fun i hi => measurable_const.mul (hG i))
  have hminusmeas : Measurable (GaussianRows.row G cminus) := by
    change Measurable (fun ω => ∑ i, cminus i * G i ω)
    exact Finset.measurable_fun_sum _ (fun i hi => measurable_const.mul (hG i))
  have hPlus : HasLaw (fun ω => GaussianRows.row G c ω + GaussianRows.row G d ω)
      (gaussianReal 0 rplus.toNNReal) P := by
    have hrow : (fun ω => GaussianRows.row G c ω + GaussianRows.row G d ω) =
        GaussianRows.row G cplus := by
      funext ω
      change (∑ i, c i * G i ω) + (∑ i, d i * G i ω) =
        ∑ i, (c i + d i) * G i ω
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hrow]
    exact ⟨hplusmeas.aemeasurable, hplusmap⟩
  have hMinus : HasLaw (fun ω => GaussianRows.row G c ω - GaussianRows.row G d ω)
      (gaussianReal 0 rminus.toNNReal) P := by
    have hrow : (fun ω => GaussianRows.row G c ω - GaussianRows.row G d ω) =
        GaussianRows.row G cminus := by
      funext ω
      change (∑ i, c i * G i ω) - (∑ i, d i * G i ω) =
        ∑ i, (c i - d i) * G i ω
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hrow]
    exact ⟨hminusmeas.aemeasurable, hminusmap⟩
  have hqplus : (rplus.toNNReal : ℝ) = 2 + 2 * rho := by
    simpa [rplus, max_eq_left hrplus] using Real.coe_toNNReal rplus hrplus
  have hqminus : (rminus.toNNReal : ℝ) = 2 - 2 * rho := by
    simpa [rminus, max_eq_left hrminus] using Real.coe_toNNReal rminus hrminus
  exact gaussianCoshProduct_of_sum_difference_laws P hPlus hMinus hqplus hqminus

/-- The normalized cosh-product covariance factor for standard finite Gaussian
rows is exactly `cosh(a²ρ) - 1`, with no moment approximation. -/
theorem gaussianRows_normalizedCoshCovariance
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : MeasureTheory.Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ) (hG : ∀ i, Measurable (G i))
    (hLaw : ∀ i, P.map (G i) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (c d : ι → ℝ)
    (hc : ∑ i, c i ^ 2 = 1) (hd : ∑ i, d i ^ 2 = 1)
    (rho : ℝ) (hcd : ∑ i, c i * d i = rho) (hrho : |rho| ≤ 1)
    (a : ℝ) :
    (∫ ω, Real.exp (-a ^ 2) * Real.cosh (a * GaussianRows.row G c ω) *
      Real.cosh (a * GaussianRows.row G d ω) ∂P) - 1 = Real.cosh (a ^ 2 * rho) - 1 := by
  have hassoc : (fun ω => Real.exp (-a ^ 2) *
      Real.cosh (a * GaussianRows.row G c ω) *
      Real.cosh (a * GaussianRows.row G d ω)) =
      fun ω => Real.exp (-a ^ 2) *
        (Real.cosh (a * GaussianRows.row G c ω) *
          Real.cosh (a * GaussianRows.row G d ω)) := by
    funext ω
    ring
  rw [hassoc, integral_const_mul, gaussianRows_coshProduct_mgf G hG hLaw hIndep c d
    hc hd rho hcd hrho a]
  rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- A covariance-form version of the exact row identity. The one-row cosh
means are evaluated as well, so the expression is the centered covariance. -/
theorem gaussianRows_coshCovariance
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : MeasureTheory.Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ) (hG : ∀ i, Measurable (G i))
    (hLaw : ∀ i, P.map (G i) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (c d : ι → ℝ)
    (hc : ∑ i, c i ^ 2 = 1) (hd : ∑ i, d i ^ 2 = 1)
    (rho : ℝ) (hcd : ∑ i, c i * d i = rho) (hrho : |rho| ≤ 1)
    (a : ℝ) :
    Real.exp (-a ^ 2) * ((∫ ω, Real.cosh (a * GaussianRows.row G c ω) *
      Real.cosh (a * GaussianRows.row G d ω) ∂P) -
      (∫ ω, Real.cosh (a * GaussianRows.row G c ω) ∂P) *
      (∫ ω, Real.cosh (a * GaussianRows.row G d ω) ∂P)) =
        Real.cosh (a ^ 2 * rho) - 1 := by
  have hcm : Measurable (GaussianRows.row G c) := by
    change Measurable (fun ω => ∑ i, c i * G i ω)
    exact Finset.measurable_fun_sum _ (fun i hi => measurable_const.mul (hG i))
  have hdm : Measurable (GaussianRows.row G d) := by
    change Measurable (fun ω => ∑ i, d i * G i ω)
    exact Finset.measurable_fun_sum _ (fun i hi => measurable_const.mul (hG i))
  have hclaw : HasLaw (GaussianRows.row G c) (gaussianReal 0 1) P := by
    refine ⟨hcm.aemeasurable, ?_⟩
    rw [GaussianRows.row_law G hG hLaw hIndep c, hc]
    norm_num
  have hdlaw : HasLaw (GaussianRows.row G d) (gaussianReal 0 1) P := by
    refine ⟨hdm.aemeasurable, ?_⟩
    rw [GaussianRows.row_law G hG hLaw hIndep d, hd]
    norm_num
  have hmeanprod :
      (∫ ω, Real.cosh (a * GaussianRows.row G c ω) ∂P) *
      (∫ ω, Real.cosh (a * GaussianRows.row G d ω) ∂P) = Real.exp (a ^ 2) := by
    rw [integral_cosh_of_hasLaw P hclaw a, integral_cosh_of_hasLaw P hdlaw a]
    rw [← Real.exp_add]
    congr 1
    norm_num
  rw [gaussianRows_coshProduct_mgf G hG hLaw hIndep c d hc hd rho hcd hrho a,
    hmeanprod]
  have hinner : Real.exp (a ^ 2) * Real.cosh (a ^ 2 * rho) - Real.exp (a ^ 2) =
      Real.exp (a ^ 2) * (Real.cosh (a ^ 2 * rho) - 1) := by
    rw [mul_sub, mul_one]
  rw [hinner, ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- The manuscript's pointwise Gaussian cosh covariance envelope, now in the
finite-row setting: `cosh(pρ) - 1 ≤ p²ρ² exp(p|ρ|)/2`. -/
theorem gaussianRows_coshCovariance_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : MeasureTheory.Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ) (hG : ∀ i, Measurable (G i))
    (hLaw : ∀ i, P.map (G i) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (c d : ι → ℝ)
    (hc : ∑ i, c i ^ 2 = 1) (hd : ∑ i, d i ^ 2 = 1)
    (rho : ℝ) (hcd : ∑ i, c i * d i = rho) (hrho : |rho| ≤ 1)
    (p : ℝ) (hp : 0 ≤ p) :
    Real.exp (-p) * ((∫ ω, Real.cosh (Real.sqrt p * GaussianRows.row G c ω) *
      Real.cosh (Real.sqrt p * GaussianRows.row G d ω) ∂P) -
      (∫ ω, Real.cosh (Real.sqrt p * GaussianRows.row G c ω) ∂P) *
      (∫ ω, Real.cosh (Real.sqrt p * GaussianRows.row G d ω) ∂P)) ≤
        p ^ 2 * rho ^ 2 / 2 * Real.exp (p * |rho|) := by
  have hsqrt : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
  calc
    Real.exp (-p) * ((∫ ω, Real.cosh (Real.sqrt p * GaussianRows.row G c ω) *
        Real.cosh (Real.sqrt p * GaussianRows.row G d ω) ∂P) -
        (∫ ω, Real.cosh (Real.sqrt p * GaussianRows.row G c ω) ∂P) *
        (∫ ω, Real.cosh (Real.sqrt p * GaussianRows.row G d ω) ∂P)) =
      Real.exp (-(Real.sqrt p) ^ 2) * ((∫ ω, Real.cosh (Real.sqrt p * GaussianRows.row G c ω) *
        Real.cosh (Real.sqrt p * GaussianRows.row G d ω) ∂P) -
        (∫ ω, Real.cosh (Real.sqrt p * GaussianRows.row G c ω) ∂P) *
        (∫ ω, Real.cosh (Real.sqrt p * GaussianRows.row G d ω) ∂P)) := by rw [hsqrt]
    _ = Real.cosh ((Real.sqrt p) ^ 2 * rho) - 1 :=
      gaussianRows_coshCovariance G hG hLaw hIndep c d hc hd rho hcd hrho (Real.sqrt p)
    _ ≤ p ^ 2 * rho ^ 2 / 2 * Real.exp (p * |rho|) := by
      have hcosh := cosh_sub_one_le_sq_exp_abs ((Real.sqrt p) ^ 2 * rho)
      simpa [hsqrt, abs_mul, abs_of_nonneg hp, mul_pow, mul_comm, mul_left_comm,
        mul_assoc] using hcosh

/-- A finite-sum variance transport rule: pairwise covariance bounds add after
centering, and a scalar prefactor contributes its square. -/
theorem variance_const_mul_finite_sum_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ι → Ω → ℝ) (c : ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (B : ι → ι → ℝ)
    (hB : ∀ i j, c ^ 2 * cov[X i, X j; P] ≤ B i j) :
    variance (fun ω => c * ∑ i, X i ω) P ≤ ∑ i, ∑ j, B i j := by
  have hsum : MemLp (fun ω => ∑ i, X i ω) 2 P := by
    convert (memLp_finsetSum' Finset.univ (fun i hi => hX i) :
      MemLp (∑ i ∈ Finset.univ, X i) 2 P) using 1
    ext ω
    simp
  rw [variance_const_mul, ← covariance_self hsum.aemeasurable,
    covariance_fun_sum_fun_sum hX hX]
  calc
    c ^ 2 * (∑ i, ∑ j, cov[X i, X j; P]) =
        ∑ i, ∑ j, c ^ 2 * cov[X i, X j; P] := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ ≤ ∑ i, ∑ j, B i j := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hB i j

/-- Finite version of the manuscript's normalized exponential average, using
hyperbolic cosines to encode the two exponential signs at once. -/
noncomputable def normalizedCoshAverage {ι Ω : Type*} [Fintype ι]
    (p : ℝ) (X : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  (Real.exp (-p / 2) / (Fintype.card ι : ℝ)) *
    ∑ i, Real.cosh (Real.sqrt p * X i ω)

/-- Identification of the manuscript's normalized exponential average with
the exponential of the convex log-mean-cosh observable. -/
theorem normalizedCoshAverage_eq_exp_logMeanCosh
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (p : ℝ) (hp : 0 ≤ p) (x : κ → ℝ) :
    normalizedCoshAverage p (fun i x => BrownianSharp.rowEvaluation A x i) x =
      Real.exp (logMeanCosh A (Real.sqrt p) x - p / 2) := by
  have hN : 0 < (Fintype.card ι : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
  have havg : 0 < (∑ i : ι,
      Real.cosh (Real.sqrt p * BrownianSharp.rowEvaluation A x i)) /
        (Fintype.card ι : ℝ) := by
    apply div_pos
    · apply Finset.sum_pos
      · intro i hi
        exact Real.cosh_pos _
      · exact Finset.univ_nonempty_iff.mpr (inferInstance : Nonempty ι)
    · exact hN
  dsimp [normalizedCoshAverage, logMeanCosh]
  rw [Real.exp_sub, Real.exp_log havg]
  have hExp : Real.exp (-p / 2) = (Real.exp (p / 2))⁻¹ := by
    rw [show -p / 2 = -(p / 2) by ring, Real.exp_neg]
  rw [hExp]
  field_simp [ne_of_gt hN, ne_of_gt (Real.exp_pos (p / 2))]

/-- Standard Gaussian row laws make every cosh summand square-integrable. -/
theorem gaussianRows_cosh_memLp_two
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype κ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G : κ → Ω → ℝ) (hG : ∀ k, Measurable (G k))
    (hLaw : ∀ k, P.map (G k) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (A : ι → κ → ℝ)
    (hunit : ∀ i, ∑ k, A i k ^ 2 = 1) (p : ℝ) (hp : 0 ≤ p) (i : ι) :
    MemLp (fun ω => Real.cosh (Real.sqrt p * GaussianRows.row G (A i) ω)) 2 P := by
  have hrow : HasLaw (GaussianRows.row G (A i)) (gaussianReal 0 1) P := by
    refine ⟨(GaussianRows.row_gaussian G hG hLaw hIndep (A i)).aemeasurable, ?_⟩
    rw [GaussianRows.row_law G hG hLaw hIndep, hunit i]
    norm_num
  exact cosh_memLp_two_of_hasLaw P hrow (Real.sqrt p)

/-- The normalized finite cosh average has mean exactly one when every row is
standard Gaussian. -/
theorem gaussianRows_normalizedCoshAverage_mean
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] [Fintype κ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G : κ → Ω → ℝ) (hG : ∀ k, Measurable (G k))
    (hLaw : ∀ k, P.map (G k) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (A : ι → κ → ℝ)
    (hunit : ∀ i, ∑ k, A i k ^ 2 = 1) (p : ℝ) (hp : 0 ≤ p) :
    ∫ ω, normalizedCoshAverage p (fun i => GaussianRows.row G (A i)) ω ∂P = 1 := by
  classical
  have hrow (i : ι) : HasLaw (GaussianRows.row G (A i)) (gaussianReal 0 1) P := by
    refine ⟨(GaussianRows.row_gaussian G hG hLaw hIndep (A i)).aemeasurable, ?_⟩
    rw [GaussianRows.row_law G hG hLaw hIndep, hunit i]
    norm_num
  have hLp (i : ι) : MemLp
      (fun ω => Real.cosh (Real.sqrt p * GaussianRows.row G (A i) ω)) 2 P :=
    cosh_memLp_two_of_hasLaw P (hrow i) (Real.sqrt p)
  have hInt (i : ι) : Integrable
      (fun ω => Real.cosh (Real.sqrt p * GaussianRows.row G (A i) ω)) P :=
    (hLp i).integrable (by norm_num)
  have hmeanCosh (i : ι) :
      ∫ ω, Real.cosh (Real.sqrt p * GaussianRows.row G (A i) ω) ∂P =
        Real.exp (p / 2) := by
    rw [integral_cosh_of_hasLaw P (hrow i) (Real.sqrt p)]
    simp [Real.sq_sqrt hp]
  dsimp [normalizedCoshAverage]
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [hmeanCosh]
    have hterm : Real.exp (-p / 2) * Real.exp (p / 2) = 1 := by
      rw [← Real.exp_add]
      rw [show -p / 2 + p / 2 = 0 by ring, Real.exp_zero]
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp [hn]
    simpa only [show -(p / 2) = -p / 2 by ring] using hterm
  · intro i hi
    exact hInt i

/-- Pairwise Gaussian cosh covariance bounds aggregate directly into a variance
bound for the normalized average. The overlap matrix may contain arbitrary
signed correlations, each controlled by its absolute value. -/
theorem gaussianRows_normalizedCoshAverage_variance_le
    {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι] [Fintype κ]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (G : κ → Ω → ℝ) (hG : ∀ k, Measurable (G k))
    (hLaw : ∀ k, P.map (G k) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (A : ι → κ → ℝ)
    (hunit : ∀ i, ∑ k, A i k ^ 2 = 1)
    (rho : ι → ι → ℝ)
    (hdot : ∀ i j, ∑ k, A i k * A j k = rho i j)
    (hrho : ∀ i j, |rho i j| ≤ 1) (p : ℝ) (hp : 0 ≤ p) :
    ProbabilityTheory.variance
      (normalizedCoshAverage p (fun i => GaussianRows.row G (A i))) P ≤
      (p ^ 2 / 2 / (Fintype.card ι : ℝ) ^ 2) *
        ∑ i, ∑ j, rho i j ^ 2 * Real.exp (p * |rho i j|) := by
  classical
  let X : ι → Ω → ℝ := fun i ω =>
    Real.cosh (Real.sqrt p * GaussianRows.row G (A i) ω)
  let c : ℝ := Real.exp (-p / 2) / (Fintype.card ι : ℝ)
  let B : ι → ι → ℝ := fun i j =>
    (p ^ 2 * rho i j ^ 2 / 2 * Real.exp (p * |rho i j|)) /
      (Fintype.card ι : ℝ) ^ 2
  have hLp (i : ι) : MemLp (X i) 2 P := by
    exact gaussianRows_cosh_memLp_two P G hG hLaw hIndep A hunit p hp i
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hc2 : c ^ 2 = Real.exp (-p) / (Fintype.card ι : ℝ) ^ 2 := by
    dsimp [c]
    rw [div_pow, pow_two, ← Real.exp_add]
    congr 1 <;> ring
  have hB (i j : ι) : c ^ 2 * cov[X i, X j; P] ≤ B i j := by
    have hpair := gaussianRows_coshCovariance_bound G hG hLaw hIndep
      (A i) (A j) (hunit i) (hunit j) (rho i j) (hdot i j) (hrho i j) p hp
    have hcov : Real.exp (-p) * cov[X i, X j; P] ≤
        p ^ 2 * rho i j ^ 2 / 2 * Real.exp (p * |rho i j|) := by
      simpa [X, covariance_eq_sub (hLp i) (hLp j)] using hpair
    calc
      c ^ 2 * cov[X i, X j; P] =
          ((Fintype.card ι : ℝ) ^ 2)⁻¹ *
            (Real.exp (-p) * cov[X i, X j; P]) := by
              rw [hc2]
              ring
      _ ≤ ((Fintype.card ι : ℝ) ^ 2)⁻¹ *
            (p ^ 2 * rho i j ^ 2 / 2 * Real.exp (p * |rho i j|)) := by
              apply mul_le_mul_of_nonneg_left hcov
              positivity
      _ = B i j := by
            dsimp [B]
            ring
  have hvar := variance_const_mul_finite_sum_le P X c hLp B hB
  have heq : normalizedCoshAverage p (fun i => GaussianRows.row G (A i)) =
      fun ω => c * ∑ i, X i ω := by
    funext ω
    simp [normalizedCoshAverage, X, c, div_eq_mul_inv, mul_assoc]
  rw [heq]
  calc
    ProbabilityTheory.variance
        (normalizedCoshAverage p (fun i => GaussianRows.row G (A i))) P ≤
        ∑ i, ∑ j, B i j := hvar
    _ = (p ^ 2 / 2 / (Fintype.card ι : ℝ) ^ 2) *
          ∑ i, ∑ j, rho i j ^ 2 * Real.exp (p * |rho i j|) := by
        simp only [B]
        have hterm (i j : ι) :
            p ^ 2 * rho i j ^ 2 / 2 * Real.exp (p * |rho i j|) /
                (Fintype.card ι : ℝ) ^ 2 =
              (p ^ 2 / 2 / (Fintype.card ι : ℝ) ^ 2) *
                (rho i j ^ 2 * Real.exp (p * |rho i j|)) := by
          field_simp [hcard]
        calc
          (∑ i, ∑ j, p ^ 2 * rho i j ^ 2 / 2 *
                Real.exp (p * |rho i j|) / (Fintype.card ι : ℝ) ^ 2) =
              ∑ i, ∑ j, (p ^ 2 / 2 / (Fintype.card ι : ℝ) ^ 2) *
                (rho i j ^ 2 * Real.exp (p * |rho i j|)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm i j
          _ = (p ^ 2 / 2 / (Fintype.card ι : ℝ) ^ 2) *
                ∑ i, ∑ j, rho i j ^ 2 * Real.exp (p * |rho i j|) := by
            calc
              _ = ∑ i, (p ^ 2 / 2 / (Fintype.card ι : ℝ) ^ 2) *
                    ∑ j, rho i j ^ 2 * Real.exp (p * |rho i j|) := by
                apply Finset.sum_congr rfl
                intro i hi
                rw [← Finset.mul_sum Finset.univ
                  (fun j => rho i j ^ 2 * Real.exp (p * |rho i j|))
                  (p ^ 2 / 2 / (Fintype.card ι : ℝ) ^ 2)]
              _ = (p ^ 2 / 2 / (Fintype.card ι : ℝ) ^ 2) *
                    ∑ i, ∑ j, rho i j ^ 2 * Real.exp (p * |rho i j|) := by
                rw [← Finset.mul_sum Finset.univ
                  (fun i => ∑ j, rho i j ^ 2 * Real.exp (p * |rho i j|))
                  (p ^ 2 / 2 / (Fintype.card ι : ℝ) ^ 2)]

/-- Manuscript-style covariance-sum variance bound for finite unit rows under
an actual product standard Gaussian vector. Correlation information is kept
explicit as `rho` and `hrho`, so overlap estimates can be supplied by the
application without hiding any probabilistic step. -/
theorem productGaussian_normalizedCoshAverage_variance_le
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (hunit : ∀ i, ∑ k, A i k ^ 2 = 1)
    (rho : ι → ι → ℝ)
    (hdot : ∀ i j, ∑ k, A i k * A j k = rho i j)
    (hrho : ∀ i j, |rho i j| ≤ 1) (p : ℝ) (hp : 0 ≤ p) :
    ProbabilityTheory.variance
      (normalizedCoshAverage p (fun i x => BrownianSharp.rowEvaluation A x i))
      (productStandardGaussian κ) ≤
      (p ^ 2 / 2 / (Fintype.card ι : ℝ) ^ 2) *
        ∑ i, ∑ j, rho i j ^ 2 * Real.exp (p * |rho i j|) := by
  let G : κ → (κ → ℝ) → ℝ := fun k x => x k
  have hG : ∀ k, Measurable (G k) := fun k => measurable_pi_apply k
  have hLaw : ∀ k, (productStandardGaussian κ).map (G k) = gaussianReal 0 1 := by
    intro k
    exact productStandardGaussian_coordinate_law k
  have hIndep : iIndepFun G (productStandardGaussian κ) :=
    productStandardGaussian_coordinates_independent κ
  have hbound := gaussianRows_normalizedCoshAverage_variance_le
    (productStandardGaussian κ) G hG hLaw hIndep A hunit rho hdot hrho p hp
  have heq : (fun x : κ → ℝ => normalizedCoshAverage p
      (fun i => GaussianRows.row G (A i)) x) =
      (fun x => normalizedCoshAverage p
        (fun i z => BrownianSharp.rowEvaluation A z i) x) := by
    funext x
    congr 1
  have hbound' : ProbabilityTheory.variance
      (fun x : κ → ℝ => normalizedCoshAverage p
        (fun i => GaussianRows.row G (A i)) x)
      (productStandardGaussian κ) ≤
      (p ^ 2 / 2 / (Fintype.card ι : ℝ) ^ 2) *
        ∑ i, ∑ j, rho i j ^ 2 * Real.exp (p * |rho i j|) := hbound
  rw [heq] at hbound'
  exact hbound'

/-- When the normalized cosh average has variance at most `1/4`, its median is
at least `1/2`, and the positive-part scale of its logarithm is at most four
standard deviations of the average. This is the quantitative bridge from the
manuscript's covariance bound to the median PV scale. -/
theorem gaussian_logMeanCosh_median_scale_control
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (hunit : ∀ i, ∑ k, A i k ^ 2 = 1)
    (p : ℝ) (hp : 0 < p)
    (hEhrhard : BrownianSharp.Concentration.GaussianEhrhard
      (κ → ℝ) (productStandardGaussian κ))
    (t : ℝ) (ht : 0 < t)
    (hsmall : Real.sqrt (ProbabilityTheory.variance
      (normalizedCoshAverage p (fun i x => BrownianSharp.rowEvaluation A x i))
      (productStandardGaussian κ)) ≤ 1 / 2) :
    ∃ M : ℝ,
      (1 / 2 : ℝ) ≤ (productStandardGaussian κ).real
        {x | logMeanCosh A (Real.sqrt p) x ≤ M} ∧
      (1 / 2 : ℝ) ≤ (productStandardGaussian κ).real
        {x | M ≤ logMeanCosh A (Real.sqrt p) x} ∧
      (1 / 2 : ℝ) ≤ Real.exp (M - p / 2) ∧
      (∫ x, max (logMeanCosh A (Real.sqrt p) x - M) 0
        ∂productStandardGaussian κ) ≤
        4 * Real.sqrt (ProbabilityTheory.variance
          (normalizedCoshAverage p (fun i x => BrownianSharp.rowEvaluation A x i))
          (productStandardGaussian κ)) ∧
      (productStandardGaussian κ).real
        {x | logMeanCosh A (Real.sqrt p) x < M - t *
          (∫ x, max (logMeanCosh A (Real.sqrt p) x - M) 0
            ∂productStandardGaussian κ)} ≤
        Real.exp (-Real.pi * t ^ 2 / 512) := by
  classical
  let μ := productStandardGaussian κ
  let X : (κ → ℝ) → ℝ := logMeanCosh A (Real.sqrt p)
  let U : (κ → ℝ) → ℝ := normalizedCoshAverage p
    (fun i x => BrownianSharp.rowEvaluation A x i)
  let σ : ℝ := Real.sqrt (ProbabilityTheory.variance U μ)
  have ha : Real.sqrt p ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hp)
  have hMed := gaussian_logMeanCosh_median_pospart_tail_of_ehrhard
    A hunit p hp hEhrhard t ht
  obtain ⟨M, hMLowerX, hMUpperX, htail⟩ := hMed
  have hσ : σ ≤ 1 / 2 := by simpa [σ, U, μ] using hsmall
  let G : κ → (κ → ℝ) → ℝ := fun k x => x k
  have hG : ∀ k, Measurable (G k) := fun k => measurable_pi_apply k
  have hLaw : ∀ k, μ.map (G k) = gaussianReal 0 1 := by
    intro k
    exact productStandardGaussian_coordinate_law k
  have hIndep : iIndepFun G μ := productStandardGaussian_coordinates_independent κ
  have hUMeanRow := gaussianRows_normalizedCoshAverage_mean μ G hG hLaw hIndep
    A hunit p hp.le
  have hRowEq : normalizedCoshAverage p (fun i => GaussianRows.row G (A i)) = U := by
    funext x
    congr 1
  have hUMean : μ[U] = 1 := by
    rw [hRowEq] at hUMeanRow
    simpa [U] using hUMeanRow
  have hTermLp (i : ι) : MemLp
      (fun x : κ → ℝ => Real.cosh (Real.sqrt p * GaussianRows.row G (A i) x)) 2 μ :=
    gaussianRows_cosh_memLp_two μ G hG hLaw hIndep A hunit p hp.le i
  have hSumLp : MemLp (fun x : κ → ℝ =>
      ∑ i : ι, Real.cosh (Real.sqrt p * GaussianRows.row G (A i) x)) 2 μ := by
    simpa using memLp_finsetSum (Finset.univ : Finset ι)
      (fun i _ => hTermLp i)
  have hULp : MemLp U 2 μ := by
    have hrowEq : U = normalizedCoshAverage p
        (fun i => GaussianRows.row G (A i)) := by
      funext x
      simp [U, normalizedCoshAverage, GaussianRows.row, G,
        BrownianSharp.rowEvaluation]
    rw [hrowEq]
    have hconst := hSumLp.const_mul
      (Real.exp (-p / 2) / (Fintype.card ι : ℝ))
    have heq : normalizedCoshAverage p (fun i => GaussianRows.row G (A i)) =
        fun x => (Real.exp (-p / 2) / (Fintype.card ι : ℝ)) *
          ∑ i, Real.cosh (Real.sqrt p * GaussianRows.row G (A i) x) := by
      funext x
      rfl
    rw [heq]
    exact hconst
  let Z : ℝ := Real.exp (M - p / 2)
  have hUexp (x : κ → ℝ) : U x = Real.exp (X x - p / 2) := by
    simpa [U, X, μ] using normalizedCoshAverage_eq_exp_logMeanCosh A p hp.le x
  have hZpos : 0 < Z := Real.exp_pos _
  have hmedianLowerU : (1 / 2 : ℝ) ≤ μ.real {x | U x ≤ Z} := by
    rw [show {x | U x ≤ Z} = {x | X x ≤ M} by
      ext x
      change U x ≤ Z ↔ X x ≤ M
      rw [hUexp x]
      simp only [Z]
      rw [Real.exp_le_exp]
      constructor <;> intro h <;> linarith]
    exact hMLowerX
  have hmedianUpperU : (1 / 2 : ℝ) ≤ μ.real {x | Z ≤ U x} := by
    rw [show {x | Z ≤ U x} = {x | M ≤ X x} by
      ext x
      change Z ≤ U x ↔ M ≤ X x
      rw [hUexp x]
      simp only [Z]
      rw [Real.exp_le_exp]
      constructor <;> intro h <;> linarith]
    exact hMUpperX
  have hZlower : 1 - σ ≤ Z := by
    have h := BrownianSharp.Concentration.mean_sub_median_le_sqrt_variance
      μ U hULp Z hmedianLowerU
    rw [hUMean] at h
    linarith
  have hZge : 1 / 2 ≤ Z := by linarith
  have hYlogLp : MemLp (fun x : κ → ℝ => X x - M) 2 μ := by
    have h := gaussian_logMeanCosh_memLp_two A hunit (Real.sqrt p)
    convert h.sub (memLp_const M) using 1 <;> ext x <;> simp [X]
  have hYlogInt : Integrable (fun x : κ → ℝ => max (X x - M) 0) μ :=
    hYlogLp.pos_part.integrable one_le_two
  have hYUlp : MemLp (fun x : κ → ℝ => U x - Z) 2 μ := hULp.sub (memLp_const Z)
  have hYUposInt : Integrable (fun x : κ → ℝ => max (U x - Z) 0) μ :=
    hYUlp.pos_part.integrable one_le_two
  have hpoint (x : κ → ℝ) : max (X x - M) 0 ≤ 2 * max (U x - Z) 0 := by
    by_cases hx : X x ≤ M
    · rw [max_eq_right (sub_nonpos.mpr hx)]
      positivity
    · have hx' : M < X x := lt_of_not_ge hx
      have hgap : 0 ≤ U x - Z := by
        rw [hUexp x]
        simp only [Z]
        apply sub_nonneg.mpr
        exact Real.exp_le_exp.mpr (by linarith)
      rw [max_eq_left (sub_nonneg.mpr hx'.le), max_eq_left hgap]
      have hratio : U x / Z = Real.exp (X x - M) := by
        change U x / Real.exp (M - p / 2) = Real.exp (X x - M)
        rw [hUexp x, ← Real.exp_sub]
        congr 1
        ring
      have hUpos : 0 < U x := by rw [hUexp x]; positivity
      have hratioPos : 0 < U x / Z := div_pos hUpos hZpos
      have hlog : Real.log (U x / Z) ≤ U x / Z - 1 :=
        Real.log_le_sub_one_of_pos hratioPos
      have hquot : U x / Z - 1 = (U x - Z) / Z := by
        field_simp [ne_of_gt hZpos]
        <;> ring
      rw [hquot, hratio, Real.log_exp] at hlog
      have hden : (U x - Z) / Z ≤ 2 * (U x - Z) := by
        apply (div_le_iff₀ hZpos).2
        have hgap : 0 ≤ U x - Z := by
          rw [hUexp x]
          simp only [Z]
          exact sub_nonneg.mpr (Real.exp_le_exp.mpr (by linarith))
        have hfactor : 0 ≤ Z - 1 / 2 := by linarith
        nlinarith [mul_nonneg hgap hfactor]
      exact hlog.trans hden
  have hscale : (∫ x, max (X x - M) 0 ∂μ) ≤
      4 * σ := by
    calc
      (∫ x, max (X x - M) 0 ∂μ) ≤
          ∫ x, 2 * max (U x - Z) 0 ∂μ :=
        integral_mono_ae hYlogInt (hYUposInt.const_mul 2) (ae_of_all _ hpoint)
      _ = 2 * ∫ x, max (U x - Z) 0 ∂μ := by rw [integral_const_mul]
      _ ≤ 2 * (Real.sqrt 2 * σ) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        have h := BrownianSharp.Concentration.median_pospart_expectation_le_sqrt_two_mul_sqrt_variance
          μ U hULp Z hmedianLowerU hmedianUpperU
        simpa [σ] using h
      _ ≤ 4 * σ := by
        have hσnonneg : 0 ≤ σ := by dsimp [σ]; positivity
        have hsqrt2 : Real.sqrt 2 ≤ 2 := by
          nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
        nlinarith
  refine ⟨M, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [μ, X] using hMLowerX
  · simpa [μ, X] using hMUpperX
  · simpa [Z] using hZge
  · simpa [μ, X, σ, U] using hscale
  · simpa [μ, X] using htail

/-- The sharp median-scale implication used in the manuscript: if the
normalized cosh average has variance small enough that its median is at least
`1/2` and the PV scale times `t` is at most `p/8`, then its lower event at
`exp(-p/4)` has the Gaussian-order tail. Pairwise-correlation estimates feed
the two displayed variance-scale hypotheses through
`productGaussian_normalizedCoshAverage_variance_le`. -/
theorem productGaussian_normalizedCoshAverage_lower_tail_of_ehrhard
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (hunit : ∀ i, ∑ k, A i k ^ 2 = 1)
    (p : ℝ) (hp : 0 < p)
    (hEhrhard : BrownianSharp.Concentration.GaussianEhrhard
      (κ → ℝ) (productStandardGaussian κ))
    (t : ℝ) (ht : 0 < t)
    (hlarge : 8 * Real.log 2 < p)
    (hsmall : Real.sqrt (ProbabilityTheory.variance
      (normalizedCoshAverage p (fun i x => BrownianSharp.rowEvaluation A x i))
      (productStandardGaussian κ)) ≤ 1 / 2)
    (hscale : 4 * t * Real.sqrt (ProbabilityTheory.variance
      (normalizedCoshAverage p (fun i x => BrownianSharp.rowEvaluation A x i))
      (productStandardGaussian κ)) ≤ p / 8) :
    (productStandardGaussian κ).real
      {x | normalizedCoshAverage p
        (fun i z => BrownianSharp.rowEvaluation A z i) x ≤ Real.exp (-p / 4)} ≤
      Real.exp (-Real.pi * t ^ 2 / 512) := by
  classical
  let μ := productStandardGaussian κ
  let X : (κ → ℝ) → ℝ := logMeanCosh A (Real.sqrt p)
  let U : (κ → ℝ) → ℝ := normalizedCoshAverage p
    (fun i x => BrownianSharp.rowEvaluation A x i)
  let σ : ℝ := Real.sqrt (ProbabilityTheory.variance U μ)
  have hcontrol := gaussian_logMeanCosh_median_scale_control A hunit p hp hEhrhard
    t ht (by simpa [U, μ] using hsmall)
  obtain ⟨M, hMLower, hMUpper, hZhalf, hDelta, htail⟩ := hcontrol
  have hDeltaT : t * (∫ x, max (X x - M) 0 ∂μ) ≤ p / 8 := by
    calc
      t * (∫ x, max (X x - M) 0 ∂μ) ≤ t * (4 * σ) :=
        mul_le_mul_of_nonneg_left (by simpa [μ, X] using hDelta) ht.le
      _ = 4 * t * σ := by ring
      _ ≤ p / 8 := by simpa [σ, U, μ] using hscale
  have hexpLog2 : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num : 0 < (2 : ℝ))
  have hexpNegLog2 : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, hexpLog2]
    norm_num
  have hMbound : p / 2 - Real.log 2 ≤ M := by
    have hExpLe : Real.exp (-Real.log 2) ≤ Real.exp (M - p / 2) := by
      rw [hexpNegLog2]
      exact hZhalf
    have hlogle : -Real.log 2 ≤ M - p / 2 := (Real.exp_le_exp).mp hExpLe
    linarith
  have hthreshold : p / 4 < M - t * (∫ x, max (X x - M) 0 ∂μ) := by
    have hbase : p / 4 < p / 2 - Real.log 2 - p / 8 := by nlinarith
    linarith
  have hUexp (x : κ → ℝ) : U x = Real.exp (X x - p / 2) := by
    simpa [U, X, μ] using normalizedCoshAverage_eq_exp_logMeanCosh A p hp.le x
  have hsubset : {x : κ → ℝ | U x ≤ Real.exp (-p / 4)} ⊆
      {x | X x < M - t * (∫ y, max (X y - M) 0 ∂μ)} := by
    intro x hx
    have hx' : Real.exp (X x - p / 2) ≤ Real.exp (-p / 4) := by
      simpa [hUexp x] using hx
    have hXle : X x ≤ p / 4 := by
      rw [Real.exp_le_exp] at hx'
      linarith
    exact lt_of_le_of_lt hXle hthreshold
  have htail' := MeasureTheory.measureReal_mono hsubset
    (measure_ne_top μ {x | X x < M - t * (∫ y, max (X y - M) 0 ∂μ)})
  calc
    μ.real {x | U x ≤ Real.exp (-p / 4)} ≤
        μ.real {x | X x < M - t * (∫ y, max (X y - M) 0 ∂μ)} := htail'
    _ ≤ Real.exp (-Real.pi * t ^ 2 / 512) := by simpa [μ, X] using htail

/-- The finite log-cosh shortcut on the actual native good grid inherits the
proved common-prefix shell variance bound. The cosh parameter is twice `r`,
so the Gaussian covariance kernel is exactly half the native shell kernel. -/
theorem nativeGoodGrid_normalizedCoshAverage_variance_le
    {d n r : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    (hr : (r : ℝ) ≤ nativeMomentSlope d * ((n : ℝ) + 1)) :
    ProbabilityTheory.variance
      (normalizedCoshAverage (2 * (r : ℝ))
        (fun i x => BrownianSharp.rowEvaluation (nativeGoodMatrix d n) x i))
      (productStandardGaussian (LayerIndex d n)) ≤
        nativeVarianceConstant d * (r : ℝ) ^ 2 / nativeDimension d n := by
  letI := nativeGoodGrid_nonempty (d := d) (n := n) (by omega : 0 < d)
  let A := nativeGoodMatrix d n
  have hunit : ∀ i : NativeGoodGrid d n, ∑ k, A i k ^ 2 = 1 := by
    intro i
    exact nativeGoodMatrix_unit_rows (by omega : 0 < d) i
  let rho : NativeGoodGrid d n → NativeGoodGrid d n → ℝ :=
    fun i j => nativeRowCorrelation i.val j.val
  have hdot : ∀ i j, ∑ k, A i k * A j k = rho i j := by
    intro i j
    exact nativeStandardMatrix_dot _ i j
  have hrho : ∀ i j, |rho i j| ≤ 1 := by
    intro i j
    rw [abs_of_nonneg (nativeRowCorrelation_nonneg _ _)]
    exact nativeRowCorrelation_le_one _ _
  have hvar := productGaussian_normalizedCoshAverage_variance_le
    (A := A) hunit rho hdot hrho (2 * (r : ℝ)) (by positivity)
  have hcard : (Fintype.card (NativeGoodGrid d n) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (NativeGoodGrid d n) ≠ 0)
  have hsum :
      ((2 * (r : ℝ)) ^ 2 / 2 / (Fintype.card (NativeGoodGrid d n) : ℝ) ^ 2) *
        ∑ i, ∑ j, rho i j ^ 2 * Real.exp (2 * (r : ℝ) * |rho i j|) =
      ((Fintype.card (NativeGoodGrid d n) : ℝ)⁻¹ ^ 2) *
        (∑ i, ∑ j, highPowerPairKernel r (rho i j)) / 2 := by
    have hterm (i j : NativeGoodGrid d n) :
        (2 * (r : ℝ)) ^ 2 / 2 *
            (rho i j ^ 2 * Real.exp (2 * (r : ℝ) * |rho i j|)) =
          highPowerPairKernel r (rho i j) / 2 := by
      unfold highPowerPairKernel
      push_cast
      ring
    have hsumKernel :
        (∑ i, ∑ j, (2 * (r : ℝ)) ^ 2 / 2 *
            (rho i j ^ 2 * Real.exp (2 * (r : ℝ) * |rho i j|))) =
          (∑ i, ∑ j, highPowerPairKernel r (rho i j)) / 2 := by
      calc
        _ = ∑ i, ∑ j, highPowerPairKernel r (rho i j) / 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hterm i j
        _ = _ := by simp_rw [Finset.sum_div]
    calc
      _ = ((Fintype.card (NativeGoodGrid d n) : ℝ)⁻¹ ^ 2) *
          (((2 * (r : ℝ)) ^ 2 / 2) *
            (∑ i, ∑ j, rho i j ^ 2 * Real.exp (2 * (r : ℝ) * |rho i j|))) := by
          rw [div_eq_mul_inv, inv_pow]
          ring
      _ = ((Fintype.card (NativeGoodGrid d n) : ℝ)⁻¹ ^ 2) *
          (∑ i, ∑ j, (2 * (r : ℝ)) ^ 2 / 2 *
            (rho i j ^ 2 * Real.exp (2 * (r : ℝ) * |rho i j|))) := by
          congr 1
          simp_rw [← Finset.mul_sum]
      _ = ((Fintype.card (NativeGoodGrid d n) : ℝ)⁻¹ ^ 2) *
          ((∑ i, ∑ j, highPowerPairKernel r (rho i j)) / 2) := by rw [hsumKernel]
      _ = _ := by ring
  have hkernel := nativeGoodPairKernel_average_bound hd hn hr
  have havg : 0 ≤ ((Fintype.card (NativeGoodGrid d n) : ℝ)⁻¹ ^ 2) *
      (∑ i, ∑ j, highPowerPairKernel r (rho i j)) := by
    apply mul_nonneg (sq_nonneg _)
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    unfold highPowerPairKernel
    positivity
  have hhalf :
      ((Fintype.card (NativeGoodGrid d n) : ℝ)⁻¹ ^ 2) *
        (∑ i, ∑ j, highPowerPairKernel r (rho i j)) / 2 ≤
      nativeVarianceConstant d * (r : ℝ) ^ 2 / nativeDimension d n := by
    nlinarith [hkernel, havg]
  exact hvar.trans (by rw [hsum]; exact hhalf)

/-- The analogous actual smooth good-grid cosh statistic inherits the
smooth-row common-prefix shell variance estimate. -/
theorem smoothGoodGrid_normalizedCoshAverage_variance_le
    {d n r : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    (hr : (r : ℝ) ≤ smoothMomentSlope d * ((n : ℝ) + 1)) :
    ProbabilityTheory.variance
      (normalizedCoshAverage (2 * (r : ℝ))
        (fun i x => BrownianSharp.rowEvaluation (smoothGoodMatrix d n) x i))
      (productStandardGaussian (LayerIndex d n)) ≤
        smoothVarianceConstant d * (r : ℝ) ^ 2 / nativeDimension d n := by
  letI := smoothGoodGrid_nonempty (d := d) (n := n) (by omega : 0 < d)
  let A := smoothGoodMatrix d n
  let rho : SmoothGoodGrid d n → SmoothGoodGrid d n → ℝ :=
    fun i j => smoothRowCorrelation i.1 j.1
  have hunit : ∀ i : SmoothGoodGrid d n, ∑ k, A i k ^ 2 = 1 := by
    intro i
    exact smoothGoodMatrix_unit_rows (by omega : 0 < d) i
  have hdot : ∀ i j, ∑ k, A i k * A j k = rho i j := by
    intro i j
    exact smoothStandardMatrix_dot (fun q : SmoothGoodGrid d n => q.1) i j
  have hrho : ∀ i j, |rho i j| ≤ 1 := by
    intro i j
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun k : LayerIndex d n => A i k) (fun k => A j k)
    rw [hunit i, hunit j] at hcs
    have hsq : rho i j ^ 2 ≤ 1 := by
      simpa [hdot i j] using hcs
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (rho i j + 1), sq_nonneg (rho i j - 1)]
  have hvar := productGaussian_normalizedCoshAverage_variance_le
    (A := A) hunit rho hdot hrho (2 * (r : ℝ)) (by positivity)
  have hcard : (Fintype.card (SmoothGoodGrid d n) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (SmoothGoodGrid d n) ≠ 0)
  have hterm (i j : SmoothGoodGrid d n) :
      (2 * (r : ℝ)) ^ 2 / 2 *
          (rho i j ^ 2 * Real.exp (2 * (r : ℝ) * |rho i j|)) =
        highPowerPairKernel r (rho i j) / 2 := by
    unfold highPowerPairKernel
    push_cast
    ring
  have hsumKernel :
      (∑ i, ∑ j, (2 * (r : ℝ)) ^ 2 / 2 *
          (rho i j ^ 2 * Real.exp (2 * (r : ℝ) * |rho i j|))) =
        (∑ i, ∑ j, highPowerPairKernel r (rho i j)) / 2 := by
    calc
      _ = ∑ i, ∑ j, highPowerPairKernel r (rho i j) / 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hterm i j
      _ = _ := by simp_rw [Finset.sum_div]
  have hsum :
      ((2 * (r : ℝ)) ^ 2 / 2 / (Fintype.card (SmoothGoodGrid d n) : ℝ) ^ 2) *
        ∑ i, ∑ j, rho i j ^ 2 * Real.exp (2 * (r : ℝ) * |rho i j|) =
      ((Fintype.card (SmoothGoodGrid d n) : ℝ)⁻¹ ^ 2) *
        (∑ i, ∑ j, highPowerPairKernel r (rho i j)) / 2 := by
    calc
      _ = ((Fintype.card (SmoothGoodGrid d n) : ℝ)⁻¹ ^ 2) *
          (((2 * (r : ℝ)) ^ 2 / 2) *
            (∑ i, ∑ j, rho i j ^ 2 * Real.exp (2 * (r : ℝ) * |rho i j|))) := by
          rw [div_eq_mul_inv, inv_pow]
          ring
      _ = ((Fintype.card (SmoothGoodGrid d n) : ℝ)⁻¹ ^ 2) *
          (∑ i, ∑ j, (2 * (r : ℝ)) ^ 2 / 2 *
            (rho i j ^ 2 * Real.exp (2 * (r : ℝ) * |rho i j|))) := by
          congr 1
          simp_rw [← Finset.mul_sum]
      _ = ((Fintype.card (SmoothGoodGrid d n) : ℝ)⁻¹ ^ 2) *
          ((∑ i, ∑ j, highPowerPairKernel r (rho i j)) / 2) := by rw [hsumKernel]
      _ = _ := by ring
  have hkernel := smoothGoodPairKernel_average_bound hd hn hr
  have havg : 0 ≤ ((Fintype.card (SmoothGoodGrid d n) : ℝ)⁻¹ ^ 2) *
      (∑ i, ∑ j, highPowerPairKernel r (rho i j)) := by
    apply mul_nonneg (sq_nonneg _)
    apply Finset.sum_nonneg
    intro i hi
    apply Finset.sum_nonneg
    intro j hj
    unfold highPowerPairKernel
    positivity
  have hhalf :
      ((Fintype.card (SmoothGoodGrid d n) : ℝ)⁻¹ ^ 2) *
        (∑ i, ∑ j, highPowerPairKernel r (rho i j)) / 2 ≤
      smoothVarianceConstant d * (r : ℝ) ^ 2 / nativeDimension d n := by
    nlinarith [hkernel, havg]
  exact hvar.trans (by rw [hsum]; exact hhalf)

/-- The actual finite native-grid log-cosh statistic satisfies uniform
exponential confinement at its manuscript scale. The only remaining analytic
premise is the set-level Gaussian Ehrhard inequality already isolated by the
certificate's concentration bridge. -/
theorem eventually_nativeGoodGrid_logMeanCosh_confinement_of_ehrhard
    {d : ℕ} (hd : 2 ≤ d)
    (hEhrhard : ∀ n : ℕ, BrownianSharp.Concentration.GaussianEhrhard
      (LayerIndex d n → ℝ) (productStandardGaussian (LayerIndex d n))) :
    ∃ N : ℕ, ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, N ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        {x | normalizedCoshAverage
          (2 * (gradeEvenPower (nativeMomentSlope d) n : ℝ))
          (fun i z => BrownianSharp.rowEvaluation (nativeGoodMatrix d n) z i) x ≤
            Real.exp (-(gradeEvenPower (nativeMomentSlope d) n : ℝ) / 2)} ≤
        Real.exp (-b * nativeDimension d n) := by
  let κ := nativeMomentSlope d
  let C := nativeVarianceConstant d
  let r (n : ℕ) := gradeEvenPower κ n
  let b := Real.pi / (512 * (16 * Real.sqrt C) ^ 2)
  have hκ : 0 < κ := nativeMomentSlope_pos d
  have hκone : κ ≤ 1 := nativeMomentSlope_le_one d
  have hC : 0 < C := nativeVarianceConstant_pos d
  have hc : 0 < 1 / (16 * Real.sqrt C) := by positivity
  have hlargeRate : ∃ Nlarge : ℕ, ∀ n : ℕ, Nlarge ≤ n →
      8 * Real.log 2 < κ * (n : ℝ) := by
    refine ⟨Nat.ceil ((8 * Real.log 2 + 1) / κ), ?_⟩
    intro n hn
    have hceil := Nat.le_ceil ((8 * Real.log 2 + 1) / κ)
    have hnreal : (Nat.ceil ((8 * Real.log 2 + 1) / κ) : ℝ) ≤ n := by exact_mod_cast hn
    have hdiv : (8 * Real.log 2 + 1) / κ ≤ (n : ℝ) := hceil.trans hnreal
    have hmul : 8 * Real.log 2 + 1 ≤ κ * (n : ℝ) := by
      have hmul' := (div_le_iff₀ hκ).mp hdiv
      nlinarith [hmul']
    linarith
  obtain ⟨Nvar, hvarSmall⟩ := eventually_evenPower_variance_small
    (d := d) (by omega : 0 < d) hκ hκone hC
  obtain ⟨Npower, hpower⟩ := eventually_gradeEvenPower_bounds hκ
  obtain ⟨Nlarge, hlarge⟩ := hlargeRate
  refine ⟨max Nvar (max Npower Nlarge), b, ?_, ?_⟩
  · dsimp [b]
    positivity
  · intro n hn
    have hnvar : Nvar ≤ n := by omega
    have hnpower : Npower ≤ n := by omega
    have hnlarge : Nlarge ≤ n := by omega
    have hbounds := hpower n hnpower
    have hrupper : (r n : ℝ) ≤ κ * ((n : ℝ) + 1) := by simpa [r] using hbounds.1
    have hrlower : κ * ((n : ℝ) + 1) / 2 ≤ (r n : ℝ) := by simpa [r] using hbounds.2.1
    have hrpos : 0 < (r n : ℝ) := by
      have hkn : 0 < κ * ((n : ℝ) + 1) := mul_pos hκ (by positivity)
      exact lt_of_lt_of_le (div_pos hkn (by norm_num : (0 : ℝ) < 2)) hrlower
    have hnpos : 0 < n := by
      have hnreal : 0 < (n : ℝ) := by
        have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hlargeN := hlarge n hnlarge
        have hkprod : 0 < κ * (n : ℝ) := by
          exact lt_trans (mul_pos (by norm_num : (0 : ℝ) < 8)
            (Real.log_pos (by norm_num))) hlargeN
        rcases mul_pos_iff.mp hkprod with ⟨_, hnreal⟩ | ⟨hκneg, _⟩
        · exact hnreal
        · exact False.elim ((not_lt_of_ge hκ.le) hκneg)
      exact_mod_cast hnreal
    have hDpos : 0 < nativeDimension d n := by
      unfold nativeDimension hyperbolicCount
      have hc' : 0 < Nat.choose (n + d - 1) (d - 1) := Nat.choose_pos (by omega)
      positivity
    letI := nativeGoodGrid_nonempty (d := d) (n := n) (by omega : 0 < d)
    have hCsmall : C * (r n : ℝ) ^ 2 / nativeDimension d n ≤ 1 / 16 := by
      simpa [C, r] using hvarSmall n hnvar
    let U : (LayerIndex d n → ℝ) → ℝ := normalizedCoshAverage
      (2 * (r n : ℝ)) (fun i z => BrownianSharp.rowEvaluation (nativeGoodMatrix d n) z i)
    have hUvar : ProbabilityTheory.variance U
        (productStandardGaussian (LayerIndex d n)) ≤ C * (r n : ℝ) ^ 2 / nativeDimension d n := by
      simpa [U, C, r] using nativeGoodGrid_normalizedCoshAverage_variance_le
        (d := d) (n := n) (r := r n) hd hnpos hrupper
    have hsmall : Real.sqrt (ProbabilityTheory.variance U
        (productStandardGaussian (LayerIndex d n)) : ℝ) ≤ 1 / 2 := by
      calc
        _ ≤ Real.sqrt (1 / 16) := Real.sqrt_le_sqrt (hUvar.trans hCsmall)
        _ ≤ 1 / 2 := by norm_num
    let t := (1 / (16 * Real.sqrt C)) * Real.sqrt (nativeDimension d n)
    have ht : 0 < t := by
      dsimp [t]
      positivity
    have hroot : Real.sqrt (ProbabilityTheory.variance U
        (productStandardGaussian (LayerIndex d n))) ≤
        Real.sqrt C * (r n : ℝ) / Real.sqrt (nativeDimension d n) := by
      have hbound : C * (r n : ℝ) ^ 2 / nativeDimension d n ≤
          (Real.sqrt C * (r n : ℝ) / Real.sqrt (nativeDimension d n)) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hC.le, Real.sq_sqrt hDpos.le]
      calc
        _ ≤ Real.sqrt (C * (r n : ℝ) ^ 2 / nativeDimension d n) :=
          Real.sqrt_le_sqrt hUvar
        _ ≤ _ := by
          calc
            _ ≤ Real.sqrt ((Real.sqrt C * (r n : ℝ) /
                Real.sqrt (nativeDimension d n)) ^ 2) := Real.sqrt_le_sqrt hbound
            _ = Real.sqrt C * (r n : ℝ) / Real.sqrt (nativeDimension d n) := by
                rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    have hscale : 4 * t * Real.sqrt (ProbabilityTheory.variance U
        (productStandardGaussian (LayerIndex d n))) ≤ (2 * (r n : ℝ)) / 8 := by
      dsimp [t]
      calc
        _ ≤ 4 * ((1 / (16 * Real.sqrt C)) * Real.sqrt (nativeDimension d n)) *
            (Real.sqrt C * (r n : ℝ) / Real.sqrt (nativeDimension d n)) := by
              apply mul_le_mul_of_nonneg_left hroot
              positivity
        _ = (2 * (r n : ℝ)) / 8 := by
              field_simp [ne_of_gt hC, ne_of_gt hDpos]
              ring
    have hlarge : 8 * Real.log 2 < 2 * (r n : ℝ) := by
      have := hlarge n hnlarge
      linarith [hrlower]
    have htail := productGaussian_normalizedCoshAverage_lower_tail_of_ehrhard
      (A := nativeGoodMatrix d n) (nativeGoodMatrix_unit_rows (by omega : 0 < d))
      (2 * (r n : ℝ)) (by positivity) (hEhrhard n)
      t ht hlarge hsmall hscale
    have hexponent : -Real.pi * t ^ 2 / 512 = -b * nativeDimension d n := by
      dsimp [t, b]
      rw [mul_pow, Real.sq_sqrt hDpos.le]
      field_simp [ne_of_gt hC]
    have hthreshold : Real.exp (-(2 * (r n : ℝ)) / 4) =
        Real.exp (-(r n : ℝ) / 2) := by congr 1 <;> ring
    rw [hthreshold, hexponent] at htail
    simpa [U, r, κ, b] using htail

/-- Unconditional form: finite-product Ehrhard is instantiated from the
certificate's regularized Gaussian heat-flow proof. -/
theorem eventually_nativeGoodGrid_logMeanCosh_confinement
    {d : ℕ} (hd : 2 ≤ d) :
    ∃ N : ℕ, ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, N ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        {x | normalizedCoshAverage
          (2 * (gradeEvenPower (nativeMomentSlope d) n : ℝ))
          (fun i z => BrownianSharp.rowEvaluation (nativeGoodMatrix d n) z i) x ≤
            Real.exp (-(gradeEvenPower (nativeMomentSlope d) n : ℝ) / 2)} ≤
        Real.exp (-b * nativeDimension d n) := by
  apply eventually_nativeGoodGrid_logMeanCosh_confinement_of_ehrhard hd
  intro n
  exact finiteProductGaussianEhrhard_certified (κ := LayerIndex d n)

/-- The standard Gaussian even-moment root is at most `sqrt p`; this upper
bound complements the lower estimate used in the manuscript radius choice. -/
theorem standardGaussianMoment_evenOrder_root_upper {p : ℕ}
    (hp : 2 ≤ p) (heven : Even p) :
    standardGaussianMoment p ^ (1 / (p : ℝ)) ≤ Real.sqrt (p : ℝ) := by
  obtain ⟨k, hk⟩ := heven
  have hpk : p = 2 * k := by omega
  have hM : 0 < standardGaussianMoment p := by
    rw [hpk]
    exact standardGaussianMoment_even_pos k
  have hmoment : standardGaussianMoment p ≤ (Real.sqrt (p : ℝ)) ^ p := by
    rw [hpk, standardGaussianMoment]
    simpa [hpk] using standardGaussian_evenMoment_le_sqrt_power k
  have hpow := Real.rpow_le_rpow hM.le hmoment (by positivity : 0 ≤ (1 / (p : ℝ)))
  have hroot : ((Real.sqrt (p : ℝ)) ^ p) ^ (1 / (p : ℝ)) = Real.sqrt (p : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : 0 ≤ Real.sqrt (p : ℝ))]
    have hpne : (p : ℝ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
    have hexp : (p : ℝ) * (1 / (p : ℝ)) = 1 := by field_simp
    rw [hexp, Real.rpow_one]
  calc
    _ ≤ (Real.sqrt (p : ℝ) ^ p) ^ (1 / (p : ℝ)) := hpow
    _ = Real.sqrt (p : ℝ) := hroot

/-- If all unit-Gaussian row arguments are at most `p/4`, the normalized
cosh average is at most `exp(-p/4)`. This is the deterministic bridge from
uniform row confinement to the exponential-average statistic. -/
theorem normalizedCoshAverage_le_exp_neg_quarter_of_row_bound
    {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (p : ℝ) (hp : 0 < p) (x : κ → ℝ)
    (hrow : ∀ i, |Real.sqrt p * BrownianSharp.rowEvaluation A x i| ≤ p / 4) :
    normalizedCoshAverage p (fun i z => BrownianSharp.rowEvaluation A z i) x ≤
      Real.exp (-p / 4) := by
  have hN : 0 < (Fintype.card ι : ℝ) := by positivity
  have hsum :
      (∑ i, Real.cosh (Real.sqrt p * BrownianSharp.rowEvaluation A x i)) ≤
        (Fintype.card ι : ℝ) * Real.exp (p / 4) := by
    calc
      _ ≤ ∑ _i : ι, Real.exp (p / 4) := by
        apply Finset.sum_le_sum
        intro i hi
        have habs := hrow i
        let z := Real.sqrt p * BrownianSharp.rowEvaluation A x i
        have hcosh : Real.cosh (Real.sqrt p * BrownianSharp.rowEvaluation A x i) ≤
            Real.exp |Real.sqrt p * BrownianSharp.rowEvaluation A x i| := by
          rw [Real.cosh_eq]
          have h1 : Real.exp z ≤ Real.exp |z| := Real.exp_le_exp.mpr (le_abs_self z)
          have h2 : Real.exp (-z) ≤ Real.exp |z| := Real.exp_le_exp.mpr (neg_le_abs z)
          simpa [z] using (by nlinarith : (Real.exp z + Real.exp (-z)) / 2 ≤ Real.exp |z|)
        exact hcosh.trans (Real.exp_le_exp.mpr habs)
      _ = _ := by simp
  unfold normalizedCoshAverage
  calc
    _ ≤ (Real.exp (-p / 2) / (Fintype.card ι : ℝ)) *
        ((Fintype.card ι : ℝ) * Real.exp (p / 4)) :=
      mul_le_mul_of_nonneg_left hsum (div_nonneg (Real.exp_nonneg _) hN.le)
    _ = Real.exp (-p / 4) := by
      field_simp [hN.ne']
      rw [← Real.exp_add]
      congr 1 <;> ring

/-- The manuscript's native uniform row event implies the small normalized
cosh-average event at any even moment scale satisfying the displayed radius
comparison. -/
theorem nativeGoodUniformEvent_subset_normalizedCoshAverage
    {d n p : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    (hp : 2 ≤ p) (heven : Even p)
    (hκ : 0 < nativeMomentSlope d)
    (hpLower : nativeMomentSlope d * (n : ℝ) ≤ 2 * (p : ℝ)) :
    nativeGoodUniformEvent d n
      (sharpRadius d (nativeRadiusConstant d (1 / 2) (nativeMomentSlope d)) n) ⊆
    {x | normalizedCoshAverage (p : ℝ)
      (fun i z => BrownianSharp.rowEvaluation (nativeGoodMatrix d n) z i) x ≤
        Real.exp (-(p : ℝ) / 4)} := by
  have hM : 0 < standardGaussianMoment p := by
    obtain ⟨k, hk⟩ := heven
    rw [show p = 2 * k by omega]
    exact standardGaussianMoment_even_pos k
  have hmomentInv : Real.sqrt (p : ℝ) / 2 ≤
      standardGaussianMoment p ^ ((p : ℝ)⁻¹) :=
    standardGaussianMoment_evenOrder_root_lower heven hp
  have hmoment' : Real.sqrt (p : ℝ) / 2 ≤
      standardGaussianMoment p ^ (1 / (p : ℝ)) := by
    simpa [one_div] using hmomentInv
  have hmoment : (1 / 2 : ℝ) * Real.sqrt (p : ℝ) ≤
      standardGaussianMoment p ^ (1 / (p : ℝ)) := by
    nlinarith [hmoment']
  have hthreshold := native_sharpRadius_standardized_threshold hd hn hp
    (c := 1 / 2) (κ := nativeMomentSlope d) (by norm_num) hκ hpLower hmoment
  have hrootUpper := standardGaussianMoment_evenOrder_root_upper hp heven
  have hv₀ : 0 < nativeVarianceMeanLowerBound d n / 2 :=
    half_pos (nativeVarianceMeanLowerBound_pos (by omega))
  letI := nativeGoodGrid_nonempty (d := d) (n := n) (by omega : 0 < d)
  intro x hx
  apply normalizedCoshAverage_le_exp_neg_quarter_of_row_bound
    (A := nativeGoodMatrix d n) (p : ℝ) (by positivity) x
  intro q
  have hrow := nativeStandardMatrix_bound_of_native_bound
    (fun q : NativeGoodGrid d n => q.1) hv₀ (fun q => q.property)
    (sharpRadius_pos hd (nativeRadiusConstant_pos d (by norm_num) hκ) hn).le
    x (fun q => hx q) q
  have hroweval : |BrownianSharp.rowEvaluation (nativeGoodMatrix d n) x q| ≤
      sharpRadius d (nativeRadiusConstant d (1 / 2) (nativeMomentSlope d)) n /
        Real.sqrt (nativeVarianceMeanLowerBound d n / 2) := by
    simpa [nativeGoodMatrix, BrownianSharp.rowEvaluation] using hrow
  have hscaled : Real.sqrt (p : ℝ) *
      (sharpRadius d (nativeRadiusConstant d (1 / 2) (nativeMomentSlope d)) n /
        Real.sqrt (nativeVarianceMeanLowerBound d n / 2)) ≤ (p : ℝ) / 4 := by
    calc
      _ ≤ Real.sqrt (p : ℝ) *
          ((1 / 4 : ℝ) * standardGaussianMoment p ^ (1 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hthreshold (Real.sqrt_nonneg _)
      _ ≤ (p : ℝ) / 4 := by
        have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ p)
        nlinarith [hrootUpper, Real.sqrt_nonneg (p : ℝ)]
  have habs : |Real.sqrt (p : ℝ) *
      BrownianSharp.rowEvaluation (nativeGoodMatrix d n) x q| ≤ (p : ℝ) / 4 := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left hroweval (Real.sqrt_nonneg _)).trans hscaled
  exact habs

/-- The native uniform grid event has the manuscript's exponential small-ball
bound.  This is the event-level consequence of its inclusion in the
normalized-cosh lower tail proved above. -/
theorem eventually_nativeGoodUniform_confinement_of_exponential_average
    {d : ℕ} (hd : 2 ≤ d) :
    ∃ N : ℕ, 2 * d ≤ N ∧ ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, N ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        (nativeGoodUniformEvent d n
          (sharpRadius d (nativeRadiusConstant d (1 / 2) (nativeMomentSlope d)) n)) ≤
        Real.exp (-b * nativeDimension d n) := by
  obtain ⟨Nc, b, hb, hcosh⟩ := eventually_nativeGoodGrid_logMeanCosh_confinement hd
  obtain ⟨Np, hpow⟩ := eventually_gradeEvenPower_bounds (nativeMomentSlope_pos d)
  let N := max (2 * d) (max Nc Np)
  refine ⟨N, le_max_left _ _, b, hb, ?_⟩
  intro n hn
  have hnC : Nc ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnP : Np ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnD : 2 * d ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := by omega
  obtain ⟨hpUpper, hpLower, hp2⟩ := hpow n hnP
  let p := 2 * gradeEvenPower (nativeMomentSlope d) n
  have heven : Even p := by
    dsimp [p]
    exact even_two_mul _
  have hp2' : 2 ≤ p := by dsimp [p]; omega
  have hpLower' : nativeMomentSlope d * (n : ℝ) ≤ 2 * (p : ℝ) := by
    have hnle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hnle (nativeMomentSlope_pos d).le
    have hpl : nativeMomentSlope d * ((n : ℝ) + 1) ≤
        2 * (gradeEvenPower (nativeMomentSlope d) n : ℝ) := by
      simpa [mul_comm] using
        (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hpLower
    have hgrade : 0 ≤ (gradeEvenPower (nativeMomentSlope d) n : ℝ) := by
      exact_mod_cast (Nat.zero_le _)
    calc
      nativeMomentSlope d * (n : ℝ) ≤ nativeMomentSlope d * ((n : ℝ) + 1) := hmul
      _ ≤ 2 * (gradeEvenPower (nativeMomentSlope d) n : ℝ) := hpl
      _ ≤ 2 * (p : ℝ) := by
        dsimp [p]
        push_cast
        nlinarith [hgrade]
  letI := nativeGoodGrid_nonempty (d := d) (n := n) (by omega : 0 < d)
  have hsub := nativeGoodUniformEvent_subset_normalizedCoshAverage hd hnpos hp2' heven
    (nativeMomentSlope_pos d) hpLower'
  have htail := hcosh n hnC
  have hpcast : (p : ℝ) = 2 * (gradeEvenPower (nativeMomentSlope d) n : ℝ) := by
    simp [p]
  have hthreshold : Real.exp (-(p : ℝ) / 4) =
      Real.exp (-(gradeEvenPower (nativeMomentSlope d) n : ℝ) / 2) := by
    rw [hpcast]
    congr 1 <;> ring
  have hthreshold' : Real.exp (-(2 * (gradeEvenPower (nativeMomentSlope d) n : ℝ)) / 4) =
      Real.exp (-(gradeEvenPower (nativeMomentSlope d) n : ℝ) / 2) := by
    have h := hthreshold
    rw [hpcast] at h
    exact h
  have hset :
      {x | normalizedCoshAverage (p : ℝ)
          (fun i z => BrownianSharp.rowEvaluation (nativeGoodMatrix d n) z i) x ≤
        Real.exp (-(p : ℝ) / 4)} =
      {x | normalizedCoshAverage
          (2 * (gradeEvenPower (nativeMomentSlope d) n : ℝ))
          (fun i z => BrownianSharp.rowEvaluation (nativeGoodMatrix d n) z i) x ≤
        Real.exp (-(gradeEvenPower (nativeMomentSlope d) n : ℝ) / 2)} := by
    ext x
    simp only [Set.mem_setOf_eq, hpcast, hthreshold']
  calc
    _ ≤ (productStandardGaussian (LayerIndex d n)).real
        {x | normalizedCoshAverage (p : ℝ)
          (fun i z => BrownianSharp.rowEvaluation (nativeGoodMatrix d n) z i) x ≤
          Real.exp (-(p : ℝ) / 4)} := measureReal_mono hsub (measure_ne_top _ _)
    _ = (productStandardGaussian (LayerIndex d n)).real
        {x | normalizedCoshAverage
          (2 * (gradeEvenPower (nativeMomentSlope d) n : ℝ))
          (fun i z => BrownianSharp.rowEvaluation (nativeGoodMatrix d n) z i) x ≤
          Real.exp (-(gradeEvenPower (nativeMomentSlope d) n : ℝ) / 2)} := by rw [hset]
    _ ≤ Real.exp (-b * nativeDimension d n) := htail

/-- The coefficient-grid shortcut transfers to the original continuous
Brownian sheet through the certificate's exact product-Gaussian comparison. -/
theorem originalSheet_sharpRadius_bound_of_exponential_average
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (B : HaarQuarter.BrownianSheetOnCube d Ω P) (hd : 2 ≤ d) :
    ∃ N : ℕ, 2 * d ≤ N ∧ ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, N ≤ n →
      P.real {ω | ‖B.path ω‖ ≤
        sharpRadius d (nativeRadiusConstant d (1 / 2) (nativeMomentSlope d)) n} ≤
        Real.exp (-b * nativeDimension d n) := by
  obtain ⟨N, hN, b, hb, hbound⟩ :=
    eventually_nativeGoodUniform_confinement_of_exponential_average hd
  refine ⟨N, hN, b, hb, ?_⟩
  intro n hn
  have hnpos : 0 < n := by have := hN.trans hn; omega
  let ε := sharpRadius d (nativeRadiusConstant d (1 / 2) (nativeMomentSlope d)) n
  have hε : 0 ≤ ε := by
    dsimp [ε]
    exact (sharpRadius_pos hd
      (nativeRadiusConstant_pos d (by norm_num) (nativeMomentSlope_pos d)) hnpos).le
  have hcomp := original_sheet_product_native_comparison (n := n) (by omega : 0 < d)
    B (fun q : NativeGoodGrid d n => q.1) hε
  have hcompReal := ENNReal.toReal_mono (measure_ne_top _ _) hcomp
  have hset : {x | ∀ q : NativeGoodGrid d n,
      |∑ a, nativeLayerRowCoefficient q.1 a * x a| ≤ ε} =
      nativeGoodUniformEvent d n ε := by
    rfl
  change P.real {ω | ‖B.path ω‖ ≤ ε} ≤ _ at hcompReal
  rw [hset] at hcompReal
  exact hcompReal.trans (hbound n hn)

/-- Dimension-uniform discrete-scale Brownian-sheet estimate obtained from
the exponential-average route. The scale constants come from the new native
cosh proof and are independent of the sheet realization. -/
theorem uniformDiscreteSheetBound_of_exponentialAverage :
    ∀ d : ℕ, 2 ≤ d → ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, 2 * d ≤ N ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : HaarQuarter.BrownianSheetOnCube d Ω P) (n : ℕ), N ≤ n →
        P.real {ω | ‖B.path ω‖ ≤ sharpRadius d a n} ≤
          Real.exp (-b * nativeDimension d n) := by
  intro d hd
  obtain ⟨N, hN, b, hb, hbound⟩ :=
    eventually_nativeGoodUniform_confinement_of_exponential_average hd
  let a := nativeRadiusConstant d (1 / 2) (nativeMomentSlope d)
  refine ⟨a, b, ?_, hb, N, hN, ?_⟩
  · dsimp [a]
    exact nativeRadiusConstant_pos d (by norm_num) (nativeMomentSlope_pos d)
  · intro Ω _ P _ B n hn
    have hnpos : 0 < n := by have := hN.trans hn; omega
    let ε := sharpRadius d a n
    have hε : 0 ≤ ε := by
      dsimp [ε, a]
      exact (sharpRadius_pos hd
        (nativeRadiusConstant_pos d (by norm_num) (nativeMomentSlope_pos d)) hnpos).le
    have hcomp := original_sheet_product_native_comparison (n := n) (by omega : 0 < d)
      B (fun q : NativeGoodGrid d n => q.1) hε
    have hcompReal := ENNReal.toReal_mono (measure_ne_top _ _) hcomp
    have hset : {x | ∀ q : NativeGoodGrid d n,
        |∑ k, nativeLayerRowCoefficient q.1 k * x k| ≤ ε} =
        nativeGoodUniformEvent d n ε := rfl
    change P.real {ω | ‖B.path ω‖ ≤ ε} ≤ _ at hcompReal
    rw [hset] at hcompReal
    simpa [ε, a] using hcompReal.trans (hbound n hn)

/-- The literal old uniform sharp logarithmic statement, now discharged via
the finite normalized-cosh statistic, certified Gaussian Ehrhard, and the
existing discrete-scale interpolation closure. -/
theorem uniformSharpLog_of_exponentialAverage :
    BrownianSharp.UniformSharpLogStatement :=
  BrownianSharp.uniformSharpLog_of_uniformDiscreteSheetBound
    uniformDiscreteSheetBound_of_exponentialAverage

/-- Probability-form counterpart of the same new proof chain. -/
theorem uniformSharpProbability_of_exponentialAverage :
    BrownianSharp.UniformSharpProbabilityStatement :=
  BrownianSharp.uniformSharp_statements_iff.mpr
    uniformSharpLog_of_exponentialAverage

/-- Eventual concentration of the actual smooth good-grid exponential
average, obtained from the proved smooth common-prefix covariance sum. -/
theorem eventually_smoothGoodGrid_logMeanCosh_confinement_of_ehrhard
    {d : ℕ} (hd : 2 ≤ d)
    (hEhrhard : ∀ n : ℕ, BrownianSharp.Concentration.GaussianEhrhard
      (LayerIndex d n → ℝ) (productStandardGaussian (LayerIndex d n))) :
    ∃ N : ℕ, ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, N ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        {x | normalizedCoshAverage
          (2 * (gradeEvenPower (smoothMomentSlope d) n : ℝ))
          (fun i z => BrownianSharp.rowEvaluation (smoothGoodMatrix d n) z i) x ≤
            Real.exp (-(gradeEvenPower (smoothMomentSlope d) n : ℝ) / 2)} ≤
        Real.exp (-b * nativeDimension d n) := by
  let κ := smoothMomentSlope d
  let C := smoothVarianceConstant d
  let r (n : ℕ) := gradeEvenPower κ n
  let b := Real.pi / (512 * (16 * Real.sqrt C) ^ 2)
  have hκ : 0 < κ := smoothMomentSlope_pos d
  have hκone : κ ≤ 1 := min_le_left _ _
  have hC : 0 < C := smoothVarianceConstant_pos d
  have hlargeRate : ∃ Nlarge : ℕ, ∀ n : ℕ, Nlarge ≤ n →
      8 * Real.log 2 < κ * (n : ℝ) := by
    refine ⟨Nat.ceil ((8 * Real.log 2 + 1) / κ), ?_⟩
    intro n hn
    have hceil := Nat.le_ceil ((8 * Real.log 2 + 1) / κ)
    have hnreal : (Nat.ceil ((8 * Real.log 2 + 1) / κ) : ℝ) ≤ n := by exact_mod_cast hn
    have hdiv : (8 * Real.log 2 + 1) / κ ≤ (n : ℝ) := hceil.trans hnreal
    have hmul' := (div_le_iff₀ hκ).mp hdiv
    nlinarith [hmul']
  obtain ⟨Nvar, hvarSmall⟩ := eventually_evenPower_variance_small
    (d := d) (by omega : 0 < d) hκ hκone hC
  obtain ⟨Npower, hpower⟩ := eventually_gradeEvenPower_bounds hκ
  obtain ⟨Nlarge, hlarge⟩ := hlargeRate
  refine ⟨max Nvar (max Npower Nlarge), b, ?_, ?_⟩
  · dsimp [b]
    positivity
  · intro n hn
    have hnvar : Nvar ≤ n := by omega
    have hnpower : Npower ≤ n := by omega
    have hnlarge : Nlarge ≤ n := by omega
    have hbounds := hpower n hnpower
    have hrupper : (r n : ℝ) ≤ κ * ((n : ℝ) + 1) := by simpa [r] using hbounds.1
    have hrlower : κ * ((n : ℝ) + 1) / 2 ≤ (r n : ℝ) := by simpa [r] using hbounds.2.1
    have hrpos : 0 < (r n : ℝ) := by
      have hkn : 0 < κ * ((n : ℝ) + 1) := mul_pos hκ (by positivity)
      exact lt_of_lt_of_le (div_pos hkn (by norm_num : (0 : ℝ) < 2)) hrlower
    have hnpos : 0 < n := by
      have hnreal : 0 < (n : ℝ) := by
        have hlargeN := hlarge n hnlarge
        have hkprod : 0 < κ * (n : ℝ) := by
          exact lt_trans (mul_pos (by norm_num : (0 : ℝ) < 8)
            (Real.log_pos (by norm_num))) hlargeN
        rcases mul_pos_iff.mp hkprod with ⟨_, hnreal⟩ | ⟨hκneg, _⟩
        · exact hnreal
        · exact False.elim ((not_lt_of_ge hκ.le) hκneg)
      exact_mod_cast hnreal
    have hDpos : 0 < nativeDimension d n := by
      unfold nativeDimension hyperbolicCount
      have hc' : 0 < Nat.choose (n + d - 1) (d - 1) := Nat.choose_pos (by omega)
      positivity
    have hCsmall : C * (r n : ℝ) ^ 2 / nativeDimension d n ≤ 1 / 16 := by
      simpa [C, r] using hvarSmall n hnvar
    letI := smoothGoodGrid_nonempty (d := d) (n := n) (by omega : 0 < d)
    let U : (LayerIndex d n → ℝ) → ℝ := normalizedCoshAverage
      (2 * (r n : ℝ)) (fun i z => BrownianSharp.rowEvaluation (smoothGoodMatrix d n) z i)
    have hUvar : ProbabilityTheory.variance U
        (productStandardGaussian (LayerIndex d n)) ≤ C * (r n : ℝ) ^ 2 / nativeDimension d n := by
      simpa [U, C, r] using smoothGoodGrid_normalizedCoshAverage_variance_le
        (d := d) (n := n) (r := r n) hd hnpos hrupper
    have hsmall : Real.sqrt (ProbabilityTheory.variance U
        (productStandardGaussian (LayerIndex d n)) : ℝ) ≤ 1 / 2 := by
      calc
        _ ≤ Real.sqrt (1 / 16) := Real.sqrt_le_sqrt (hUvar.trans hCsmall)
        _ ≤ 1 / 2 := by norm_num
    let t := (1 / (16 * Real.sqrt C)) * Real.sqrt (nativeDimension d n)
    have ht : 0 < t := by dsimp [t]; positivity
    have hroot : Real.sqrt (ProbabilityTheory.variance U
        (productStandardGaussian (LayerIndex d n))) ≤
        Real.sqrt C * (r n : ℝ) / Real.sqrt (nativeDimension d n) := by
      have hbound : C * (r n : ℝ) ^ 2 / nativeDimension d n ≤
          (Real.sqrt C * (r n : ℝ) / Real.sqrt (nativeDimension d n)) ^ 2 := by
        rw [div_pow, mul_pow, Real.sq_sqrt hC.le, Real.sq_sqrt hDpos.le]
      calc
        _ ≤ Real.sqrt (C * (r n : ℝ) ^ 2 / nativeDimension d n) := Real.sqrt_le_sqrt hUvar
        _ ≤ _ := by
          calc
            _ ≤ Real.sqrt ((Real.sqrt C * (r n : ℝ) /
                Real.sqrt (nativeDimension d n)) ^ 2) := Real.sqrt_le_sqrt hbound
            _ = Real.sqrt C * (r n : ℝ) / Real.sqrt (nativeDimension d n) := by
                rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by positivity)]
    have hscale : 4 * t * Real.sqrt (ProbabilityTheory.variance U
        (productStandardGaussian (LayerIndex d n))) ≤ (2 * (r n : ℝ)) / 8 := by
      dsimp [t]
      calc
        _ ≤ 4 * ((1 / (16 * Real.sqrt C)) * Real.sqrt (nativeDimension d n)) *
            (Real.sqrt C * (r n : ℝ) / Real.sqrt (nativeDimension d n)) := by
              apply mul_le_mul_of_nonneg_left hroot
              positivity
        _ = (2 * (r n : ℝ)) / 8 := by
              field_simp [ne_of_gt hC, ne_of_gt hDpos]
              ring
    have hlarge' : 8 * Real.log 2 < 2 * (r n : ℝ) := by
      have := hlarge n hnlarge
      linarith [hrlower]
    have htail := productGaussian_normalizedCoshAverage_lower_tail_of_ehrhard
      (A := smoothGoodMatrix d n) (smoothGoodMatrix_unit_rows (by omega : 0 < d))
      (2 * (r n : ℝ)) (by positivity) (hEhrhard n)
      t ht hlarge' hsmall hscale
    have hexponent : -Real.pi * t ^ 2 / 512 = -b * nativeDimension d n := by
      dsimp [t, b]
      rw [mul_pow, Real.sq_sqrt hDpos.le]
      field_simp [ne_of_gt hC]
    have hthreshold : Real.exp (-(2 * (r n : ℝ)) / 4) =
        Real.exp (-(r n : ℝ) / 2) := by congr 1 <;> ring
    rw [hthreshold, hexponent] at htail
    simpa [U, r, κ, b] using htail

/-- Unconditional smooth-grid exponential confinement via the certified
finite-product Gaussian Ehrhard inequality. -/
theorem eventually_smoothGoodGrid_logMeanCosh_confinement
    {d : ℕ} (hd : 2 ≤ d) :
    ∃ N : ℕ, ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, N ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        {x | normalizedCoshAverage
          (2 * (gradeEvenPower (smoothMomentSlope d) n : ℝ))
          (fun i z => BrownianSharp.rowEvaluation (smoothGoodMatrix d n) z i) x ≤
            Real.exp (-(gradeEvenPower (smoothMomentSlope d) n : ℝ) / 2)} ≤
        Real.exp (-b * nativeDimension d n) := by
  apply eventually_smoothGoodGrid_logMeanCosh_confinement_of_ehrhard hd
  intro n
  exact finiteProductGaussianEhrhard_certified (κ := LayerIndex d n)

/-- The full smooth periodic synthesis confinement event forces every
standardized smooth good-grid row to be small; the deterministic cosh bound
then puts it inside the exponential-average lower-tail event. -/
theorem smoothPeriodicUniformEvent_subset_normalizedCoshAverage
    {d n p : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    (hp : 2 ≤ p) (heven : Even p) (hκ : 0 < smoothMomentSlope d)
    (hpLower : smoothMomentSlope d * (n : ℝ) ≤ 2 * (p : ℝ)) :
    {x : LayerIndex d n → ℝ | ∀ z : UnitAddTorus (Fin d),
      |smoothPeriodicSynthesis x z| ≤
        smoothPeriodicRadiusConstant d (smoothMomentSlope d) *
          Real.sqrt ((n : ℝ) * hyperbolicCount d n)} ⊆
    {x | normalizedCoshAverage (p : ℝ)
      (fun i z => BrownianSharp.rowEvaluation (smoothGoodMatrix d n) z i) x ≤
        Real.exp (-(p : ℝ) / 4)} := by
  letI := smoothGoodGrid_nonempty (d := d) (n := n) (by omega : 0 < d)
  have hM : 0 < standardGaussianMoment p := by
    obtain ⟨k, hk⟩ := heven
    rw [show p = 2 * k by omega]
    exact standardGaussianMoment_even_pos k
  let ε := smoothPeriodicRadiusConstant d (smoothMomentSlope d) *
    Real.sqrt ((n : ℝ) * hyperbolicCount d n)
  have hε : 0 ≤ ε := by
    dsimp [ε]
    exact mul_nonneg (smoothPeriodicRadiusConstant_pos d hκ).le (Real.sqrt_nonneg _)
  have hthreshold := smoothPeriodicRadius_threshold hd hn hp heven hκ hpLower
  have hrootUpper := standardGaussianMoment_evenOrder_root_upper hp heven
  intro x hx
  apply normalizedCoshAverage_le_exp_neg_quarter_of_row_bound
    (A := smoothGoodMatrix d n) (p : ℝ) (by positivity) x
  intro q
  have hraw : |∑ a : LayerIndex d n,
      smoothLayerAtom smoothAtom q.1 a * x a| ≤ ε := by
    have h := hx (BrownianSharp.periodicMidpoint q.1)
    rw [smoothPeriodicSynthesis_midpoint_eq] at h
    simpa [ε] using h
  have hv₀ : 0 < smoothVarianceMeanLowerBound d n / 2 :=
    half_pos (smoothVarianceMeanLowerBound_pos (by omega : 0 < d))
  have hvq : smoothVarianceMeanLowerBound d n / 2 ≤ smoothLayerVariance q.1 := q.2
  have hrow : |BrownianSharp.rowEvaluation (smoothGoodMatrix d n) x q| ≤
      ε / Real.sqrt (smoothVarianceMeanLowerBound d n / 2) := by
    change |∑ a : LayerIndex d n,
      smoothStandardMatrix (fun q : SmoothGoodGrid d n => q.1) q a * x a| ≤ _
    have hsum :
        (∑ a : LayerIndex d n,
          smoothStandardMatrix (fun q : SmoothGoodGrid d n => q.1) q a * x a) =
        (∑ a : LayerIndex d n,
          smoothLayerAtom smoothAtom q.1 a * x a) /
          Real.sqrt (smoothLayerVariance q.1) := by
      change (∑ a : LayerIndex d n,
          (smoothLayerAtom smoothAtom q.1 a /
            Real.sqrt (smoothLayerVariance q.1)) * x a) = _
      calc
        _ = ∑ a : LayerIndex d n,
            (smoothLayerAtom smoothAtom q.1 a * x a) /
              Real.sqrt (smoothLayerVariance q.1) := by
                apply Finset.sum_congr rfl
                intro a ha
                ring
        _ = _ := by rw [← Finset.sum_div]
    rw [hsum, abs_div,
      abs_of_pos (Real.sqrt_pos.mpr (smoothGoodGrid_variance_pos (by omega : 0 < d) q))]
    calc
      _ ≤ ε / Real.sqrt (smoothLayerVariance q.1) :=
        div_le_div_of_nonneg_right hraw (Real.sqrt_nonneg _)
      _ ≤ _ := div_le_div_of_nonneg_left hε (Real.sqrt_pos.mpr hv₀)
        (Real.sqrt_le_sqrt hvq)
  have hscaled : Real.sqrt (p : ℝ) *
      (ε / Real.sqrt (smoothVarianceMeanLowerBound d n / 2)) ≤ (p : ℝ) / 4 := by
    calc
      _ ≤ Real.sqrt (p : ℝ) *
          ((1 / 4 : ℝ) * standardGaussianMoment p ^ (1 / (p : ℝ))) :=
        mul_le_mul_of_nonneg_left hthreshold (Real.sqrt_nonneg _)
      _ ≤ (p : ℝ) / 4 := by
        have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ p)
        nlinarith [hrootUpper, Real.sqrt_nonneg (p : ℝ)]
  have habs : |Real.sqrt (p : ℝ) *
      BrownianSharp.rowEvaluation (smoothGoodMatrix d n) x q| ≤ (p : ℝ) / 4 := by
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (mul_le_mul_of_nonneg_left hrow (Real.sqrt_nonneg _)).trans hscaled
  exact habs

/-- Unconditional smooth periodic synthesis confinement from the certified
finite-product Gaussian Ehrhard inequality and the exponential-average
shortcut. -/
theorem eventually_smoothPeriodic_uniform_confinement_of_exponential_average
    {d : ℕ} (hd : 2 ≤ d) :
    ∃ N : ℕ, 2 * d ≤ N ∧ ∃ b : ℝ, 0 < b ∧ ∀ n : ℕ, N ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        {x : LayerIndex d n → ℝ | ∀ z : UnitAddTorus (Fin d),
          |smoothPeriodicSynthesis x z| ≤
            smoothPeriodicRadiusConstant d (smoothMomentSlope d) *
              Real.sqrt ((n : ℝ) * hyperbolicCount d n)} ≤
        Real.exp (-b * nativeDimension d n) := by
  obtain ⟨Nc, b, hb, hcosh⟩ := eventually_smoothGoodGrid_logMeanCosh_confinement hd
  obtain ⟨Np, hpow⟩ := eventually_gradeEvenPower_bounds (smoothMomentSlope_pos d)
  let N := max (2 * d) (max Nc Np)
  refine ⟨N, le_max_left _ _, b, hb, ?_⟩
  intro n hn
  have hnC : Nc ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnP : Np ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnD : 2 * d ≤ n := (le_max_left _ _).trans hn
  have hnpos : 0 < n := by omega
  obtain ⟨hpUpper, hpLower, hp2⟩ := hpow n hnP
  let p := 2 * gradeEvenPower (smoothMomentSlope d) n
  have heven : Even p := by dsimp [p]; exact even_two_mul _
  have hp2' : 2 ≤ p := by dsimp [p]; omega
  have hpLower' : smoothMomentSlope d * (n : ℝ) ≤ 2 * (p : ℝ) := by
    have hnle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hnle (smoothMomentSlope_pos d).le
    have hpl : smoothMomentSlope d * ((n : ℝ) + 1) ≤
        2 * (gradeEvenPower (smoothMomentSlope d) n : ℝ) := by
      simpa [mul_comm] using
        (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hpLower
    have hgrade : 0 ≤ (gradeEvenPower (smoothMomentSlope d) n : ℝ) := by
      exact_mod_cast (Nat.zero_le _)
    calc
      smoothMomentSlope d * (n : ℝ) ≤ smoothMomentSlope d * ((n : ℝ) + 1) := hmul
      _ ≤ 2 * (gradeEvenPower (smoothMomentSlope d) n : ℝ) := hpl
      _ ≤ 2 * (p : ℝ) := by
        dsimp [p]
        push_cast
        nlinarith [hgrade]
  have hsub := smoothPeriodicUniformEvent_subset_normalizedCoshAverage hd hnpos
    hp2' heven (smoothMomentSlope_pos d) hpLower'
  have hpcast : (p : ℝ) = 2 * (gradeEvenPower (smoothMomentSlope d) n : ℝ) := by simp [p]
  have hthreshold : Real.exp (-(p : ℝ) / 4) =
      Real.exp (-(gradeEvenPower (smoothMomentSlope d) n : ℝ) / 2) := by
    rw [hpcast]
    congr 1 <;> ring
  have hthreshold' :
      Real.exp (-(2 * (gradeEvenPower (smoothMomentSlope d) n : ℝ)) / 4) =
        Real.exp (-(gradeEvenPower (smoothMomentSlope d) n : ℝ) / 2) := by
    have h := hthreshold
    rw [hpcast] at h
    exact h
  have hset :
      {x | normalizedCoshAverage (p : ℝ)
          (fun i z => BrownianSharp.rowEvaluation (smoothGoodMatrix d n) z i) x ≤
        Real.exp (-(p : ℝ) / 4)} =
      {x | normalizedCoshAverage
          (2 * (gradeEvenPower (smoothMomentSlope d) n : ℝ))
          (fun i z => BrownianSharp.rowEvaluation (smoothGoodMatrix d n) z i) x ≤
        Real.exp (-(gradeEvenPower (smoothMomentSlope d) n : ℝ) / 2)} := by
    ext x
    simp only [Set.mem_setOf_eq, hpcast, hthreshold']
  calc
    _ ≤ (productStandardGaussian (LayerIndex d n)).real
        {x | normalizedCoshAverage (p : ℝ)
          (fun i z => BrownianSharp.rowEvaluation (smoothGoodMatrix d n) z i) x ≤
          Real.exp (-(p : ℝ) / 4)} := measureReal_mono hsub (measure_ne_top _ _)
    _ = (productStandardGaussian (LayerIndex d n)).real
        {x | normalizedCoshAverage
          (2 * (gradeEvenPower (smoothMomentSlope d) n : ℝ))
          (fun i z => BrownianSharp.rowEvaluation (smoothGoodMatrix d n) z i) x ≤
          Real.exp (-(gradeEvenPower (smoothMomentSlope d) n : ℝ) / 2)} := by rw [hset]
    _ ≤ Real.exp (-b * nativeDimension d n) := hcosh n hnC


end BrownianSharp.AlignmentExponential
