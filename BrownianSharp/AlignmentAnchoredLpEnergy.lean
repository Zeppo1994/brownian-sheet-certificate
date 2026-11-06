import BrownianSharp.FixedShapeDerivativeLp
import BrownianSharp.PeriodicAtomDerivatives
import BrownianSharp.LayerIndex
import BrownianSharp.GaussianRowLp
import BrownianSharp.AlignmentPaperAnchoredLp
import BrownianSharp.AlignmentPaperAnchoredLpOperator
import BrownianSharp.ProbabilisticCover
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic
import BrownianSharp.SmoothClassEvents
import BrownianSharp.PeriodicNativeCover
import BrownianSharp.AlignmentPaperConfinementBridge
import BrownianSharp.SmoothSobolevHigherPMean
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import BrownianSharp.AlignmentPaperQuantization
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-! Deterministic mixed-derivative energy for the paper's smooth tensor
atoms. This isolates the derivative source density used before Gaussian
averaging; the next stochastic step is to average the coefficient square sum. -/

noncomputable section
open MeasureTheory
open ProbabilityTheory
open scoped BigOperators ENNReal Pointwise

namespace BrownianSharp.AlignmentAnchoredLpEnergy

open BrownianSharp
open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open HaarQuarter

private theorem sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] (f : ∀ i, α i → ℝ) :
    (∑ x : (∀ i, α i), ∏ i, f i (x i)) = ∏ i, ∑ a : α i, f i a := by
  classical
  simpa using (Finset.prod_univ_sum
    (fun i => (Finset.univ : Finset (α i))) f).symm

/-- The finite Gaussian synthesis of the actual first mixed derivative
atoms, evaluated on cube coordinates through the quotient map. -/
def firstMixedDerivativeDensity {d n : ℕ}
    (z : LayerIndex d n → ℝ) (u : Fin d → ℝ) : ℝ :=
  GaussianRows.row (fun a z => z a)
    (fun a => dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
      (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
      (fun i => (u i : UnitAddCircle))) z

private theorem firstMixedDerivative_atom_continuous {d n : ℕ}
    (a : LayerIndex d n) :
    Continuous (fun u : Fin d → ℝ =>
      dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
        (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
        (fun i => (u i : UnitAddCircle))) := by
  unfold dyadicShapeDerivativeAtom
  apply continuous_finsetProd
  intro i hi
  exact (periodizedDyadicAtomDerivative1 (layerIndexDepth a i)
      (layerIndexCell a i) (layerIndexCell_lt a i) 1).continuous.comp
    ((AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i))

/-- Joint continuity of the source density in Gaussian coefficients and cube
coordinates. -/
theorem firstMixedDerivativeDensity_joint_continuous {d n : ℕ} :
    Continuous (fun y : (LayerIndex d n → ℝ) × (Fin d → ℝ) =>
      firstMixedDerivativeDensity y.1 y.2) := by
  unfold firstMixedDerivativeDensity GaussianRows.row
  apply continuous_finsetSum
  intro a ha
  exact ((firstMixedDerivative_atom_continuous a).comp continuous_snd).mul
    ((continuous_apply a).comp continuous_fst)

/-- Joint measurability of the nonnegative `p`th power used in cube Tonelli. -/
theorem firstMixedDerivativeDensity_rpow_joint_measurable {d n : ℕ}
    (p : ℝ) (hp : 0 ≤ p) :
    Measurable (fun y : (LayerIndex d n → ℝ) × (Fin d → ℝ) =>
      ENNReal.ofReal (|firstMixedDerivativeDensity y.1 y.2| ^ p)) := by
  exact ENNReal.measurable_ofReal.comp
    ((Real.continuous_rpow_const hp).measurable.comp
      firstMixedDerivativeDensity_joint_continuous.abs.measurable)

/-- The one-dimensional primitive of the actual periodized first derivative
atom is its original smooth bump, by the fundamental theorem of calculus. -/
theorem periodizedFirstDerivative_intervalIntegral_eq_atom
    (s j : ℕ) (hj : j < 2 ^ s) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ x in (0 : ℝ)..t,
      periodizedDyadicAtomDerivative1 s j hj 1 (x : UnitAddCircle)) =
      smoothAtom ((2 : ℝ) ^ s * t - (j : ℝ)) := by
  have htop : ContDiff ℝ (⊤ : ℕ∞) (smoothDyadicAtomReal s j) := by
    change ContDiff ℝ (⊤ : ℕ∞) (smoothAtom ∘ fun x : ℝ => (2 : ℝ) ^ s * x - (j : ℝ))
    exact smoothAtom_contDiff.comp (by fun_prop)
  have hcont' : ContDiff ℝ 1 (smoothDyadicAtomReal s j) :=
    htop.of_le (by simp)
  have hcont : ContDiffOn ℝ 1 (smoothDyadicAtomReal s j) (Set.Icc 0 t) :=
    hcont'.contDiffOn.mono fun x hx => by
      change 0 ≤ x ∧ x ≤ t at hx
      show x ∈ Set.Icc (0 : ℝ) 1
      exact ⟨hx.1, le_trans hx.2 ht1⟩
  have hFTC := intervalIntegral.integral_deriv_of_contDiffOn_Icc hcont ht0
  calc
    (∫ x in (0 : ℝ)..t,
      periodizedDyadicAtomDerivative1 s j hj 1 (x : UnitAddCircle)) =
      ∫ x in (0 : ℝ)..t, iteratedDeriv 1 (smoothDyadicAtomReal s j) x := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht0
        intro x hx
        change 0 < x ∧ x < t at hx
        have hx01 : x ∈ Set.Ico (0 : ℝ) 1 := by
          exact ⟨le_of_lt hx.1, lt_of_lt_of_le hx.2 ht1⟩
        exact periodizedDyadicAtomDerivative1_unit_interval s j hj 1 x hx01
    _ = ∫ x in (0 : ℝ)..t, deriv (smoothDyadicAtomReal s j) x := by
          simp only [iteratedDeriv_one]
    _ = smoothDyadicAtomReal s j t - smoothDyadicAtomReal s j 0 := hFTC
    _ = smoothAtom ((2 : ℝ) ^ s * t - (j : ℝ)) := by
          dsimp [smoothDyadicAtomReal]
          have hzero : smoothAtom ((2 : ℝ) ^ s * 0 - (j : ℝ)) = 0 :=
            smoothAtom_support _ (Or.inl (by simp))
          rw [hzero]
          ring_nf

/-- The one-coordinate rectangular integral of a first derivative atom. The
cube restriction contributes exactly the interval from zero to the anchor. -/
theorem periodizedFirstDerivative_cube_coordinate_integral
    (s j : ℕ) (hj : j < 2 ^ s) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ x : ℝ,
      (if x < t then (1 : ℝ) else 0) *
        periodizedDyadicAtomDerivative1 s j hj 1 (x : UnitAddCircle)
      ∂((volume : Measure ℝ).restrict (Set.Icc 0 1))) =
      smoothAtom ((2 : ℝ) ^ s * t - (j : ℝ)) := by
  have hset : Set.Icc (0 : ℝ) 1 ∩ Set.Iio t = Set.Ico 0 t := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iio, Set.mem_Ico]
    constructor
    · rintro ⟨⟨hx0, hx1⟩, hxt⟩
      exact ⟨hx0, hxt⟩
    · rintro ⟨hx0, hxt⟩
      exact ⟨⟨hx0, le_trans hxt.le ht1⟩, hxt⟩
  have hindicator (x : ℝ) :
      (if x < t then (1 : ℝ) else 0) *
        periodizedDyadicAtomDerivative1 s j hj 1 (x : UnitAddCircle) =
      (Set.Iio t).indicator
        (fun y => periodizedDyadicAtomDerivative1 s j hj 1 (y : UnitAddCircle)) x := by
    by_cases hx : x < t <;> simp [hx]
  calc
    _ = ∫ x in Set.Icc (0 : ℝ) 1,
        (Set.Iio t).indicator
          (fun y => periodizedDyadicAtomDerivative1 s j hj 1 (y : UnitAddCircle)) x
        ∂(volume : Measure ℝ) := by
          exact integral_congr_ae (ae_of_all _ (fun x => hindicator x))
    _ = ∫ x in Set.Icc (0 : ℝ) 1 ∩ Set.Iio t,
        periodizedDyadicAtomDerivative1 s j hj 1 (x : UnitAddCircle)
        ∂(volume : Measure ℝ) := by
          rw [MeasureTheory.setIntegral_indicator measurableSet_Iio]
    _ = ∫ x in Set.Ico (0 : ℝ) t,
        periodizedDyadicAtomDerivative1 s j hj 1 (x : UnitAddCircle)
        ∂(volume : Measure ℝ) := by rw [hset]
    _ = ∫ x in Set.Ioc (0 : ℝ) t,
        periodizedDyadicAtomDerivative1 s j hj 1 (x : UnitAddCircle)
        ∂(volume : Measure ℝ) := by
          rw [Measure.restrict_congr_set (μ := (volume : Measure ℝ)) Ico_ae_eq_Ioc]
    _ = ∫ x in (0 : ℝ)..t,
        periodizedDyadicAtomDerivative1 s j hj 1 (x : UnitAddCircle) := by
          rw [intervalIntegral.integral_of_le ht0]
    _ = smoothAtom ((2 : ℝ) ^ s * t - (j : ℝ)) :=
          periodizedFirstDerivative_intervalIntegral_eq_atom s j hj t ht0 ht1

/-- A tensor first mixed derivative integrates over an anchored rectangle to
the corresponding product of the original smooth bumps. -/
theorem firstMixedDerivative_atom_rectangular_integral_eq
    {d : ℕ} (s : Fin d → ℕ) (j : DyadicShapeCell d s)
    (t : BrownianCubeAnchor d) :
    (∫ u : Fin d → ℝ,
      rectangleKernel t u *
        dyadicShapeDerivativeAtom s (fun _ => 1) j
          (fun i => (u i : UnitAddCircle)) ∂cubeMeasure d) =
      ∏ i : Fin d, smoothAtom ((2 : ℝ) ^ (s i) * t.val i - (j i).val) := by
  classical
  rw [cubeMeasure, AlignmentFractionalTensor.unitCube_measure_eq_pi]
  have hfun : (fun u : Fin d → ℝ =>
      rectangleKernel t u *
        dyadicShapeDerivativeAtom s (fun _ => 1) j
          (fun i => (u i : UnitAddCircle))) =
      fun u => ∏ i : Fin d,
        (if u i < t.val i then (1 : ℝ) else 0) *
          periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 1
            (u i : UnitAddCircle) := by
    funext u
    simp only [rectangleKernel, dyadicShapeDerivativeAtom]
    rw [← Finset.prod_mul_distrib]
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)
  haveI : IsFiniteMeasure ν := by
    dsimp [ν]
    exact ⟨by simp⟩
  haveI : SigmaFinite ν := by infer_instance
  rw [hfun]
  change (∫ u : Fin d → ℝ,
      ∏ i : Fin d,
        (if u i < t.val i then (1 : ℝ) else 0) *
          periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 1
            (u i : UnitAddCircle) ∂Measure.pi (fun _ : Fin d => ν)) = _
  calc
    _ = ∏ i : Fin d,
        ∫ x : ℝ,
          (if x < t.val i then (1 : ℝ) else 0) *
            periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 1
              (x : UnitAddCircle) ∂ν :=
      MeasureTheory.integral_fintype_prod_eq_prod
        (fun i x => (if x < t.val i then (1 : ℝ) else 0) *
          periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 1
            (x : UnitAddCircle))
    _ = ∏ i : Fin d, smoothAtom ((2 : ℝ) ^ (s i) * t.val i - (j i).val) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact periodizedFirstDerivative_cube_coordinate_integral
        (s i) (j i).val (j i).isLt (t.val i) (t.property i).1 (t.property i).2

/-- The bump primitive product is the actual periodic native smooth atom. -/
theorem firstDerivativePrimitive_eq_periodicNativeAtom
    {d n : ℕ} (a : LayerIndex d n) (t : BrownianCubeAnchor d) :
    periodicNativeAtom a (fun i => (t.val i : UnitAddCircle)) =
      ∏ i : Fin d,
        smoothAtom ((2 : ℝ) ^ layerIndexDepth a i * t.val i -
          (layerIndexCell a i : ℝ)) := by
  change (∏ i : Fin d,
      PeriodicCover.periodizedDyadicAtom1 (layerIndexDepth a i)
        (layerIndexCell a i) (layerIndexCell_lt a i) (t.val i : UnitAddCircle)) = _
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hti : t.val i < 1
  · rw [← periodizedDyadicAtomDerivative1_zero_eq_existing
      (layerIndexDepth a i) (layerIndexCell a i) (layerIndexCell_lt a i)]
    rw [periodizedDyadicAtomDerivative1_unit_interval
      (layerIndexDepth a i) (layerIndexCell a i) (layerIndexCell_lt a i) 0
      (t.val i) ⟨(t.property i).1, hti⟩]
    simp [smoothDyadicAtomReal, iteratedDeriv_zero]
  · have htEq : t.val i = 1 := le_antisymm (t.property i).2 (le_of_not_gt hti)
    rw [htEq]
    have hperiod : ((1 : ℝ) : UnitAddCircle) = 0 := by
      simpa using (AddCircle.coe_add_period (p := (1 : ℝ)) (x := (0 : ℝ)))
    rw [hperiod]
    rw [← periodizedDyadicAtomDerivative1_zero_eq_existing
      (layerIndexDepth a i) (layerIndexCell a i) (layerIndexCell_lt a i)]
    change periodizedDyadicAtomDerivative1 (layerIndexDepth a i)
      (layerIndexCell a i) (layerIndexCell_lt a i) 0
      ((0 : ℝ) : UnitAddCircle) = _
    rw [periodizedDyadicAtomDerivative1_unit_interval
      (layerIndexDepth a i) (layerIndexCell a i) (layerIndexCell_lt a i) 0
      (0 : ℝ) (by norm_num)]
    have hj' : layerIndexCell a i + 1 ≤ 2 ^ layerIndexDepth a i :=
      Nat.succ_le_of_lt (layerIndexCell_lt a i)
    have hjr : (layerIndexCell a i : ℝ) + 1 ≤
        (2 : ℝ) ^ layerIndexDepth a i := by exact_mod_cast hj'
    have harg : 1 ≤ (2 : ℝ) ^ layerIndexDepth a i -
        (layerIndexCell a i : ℝ) := by linarith
    simp only [smoothDyadicAtomReal, iteratedDeriv_zero]
    have harg' : 1 ≤ (2 : ℝ) ^ layerIndexDepth a i * 1 -
        (layerIndexCell a i : ℝ) := by nlinarith
    rw [smoothAtom_support _ (Or.inr harg')]
    have harg'' : (2 : ℝ) ^ layerIndexDepth a i * 0 -
        (layerIndexCell a i : ℝ) ≤ 0 := by
      have : 0 ≤ (layerIndexCell a i : ℝ) := Nat.cast_nonneg _
      nlinarith
    rw [smoothAtom_support _ (Or.inl harg'')]

private theorem derivativeAtom_abs_le {d n : ℕ} (a : LayerIndex d n)
    (u : Fin d → ℝ) :
    |dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
      (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
      (fun i => (u i : UnitAddCircle))| ≤
      ∏ i : Fin d, (Classical.choose (exists_smoothAtom_iteratedDeriv_bound 1) *
        (2 : ℝ) ^ layerIndexDepth a i) := by
  classical
  let C := Classical.choose (exists_smoothAtom_iteratedDeriv_bound 1)
  have hC : ∀ x : ℝ, |iteratedDeriv 1 smoothAtom x| ≤ C :=
    (Classical.choose_spec (exists_smoothAtom_iteratedDeriv_bound 1)).2
  rw [dyadicShapeDerivativeAtom]
  have hprod : |∏ i : Fin d,
      periodizedDyadicAtomDerivative1 (layerIndexDepth a i)
        (layerIndexCell a i) (layerIndexCell_lt a i) 1
        (u i : UnitAddCircle)| =
      ∏ i : Fin d, |periodizedDyadicAtomDerivative1 (layerIndexDepth a i)
        (layerIndexCell a i) (layerIndexCell_lt a i) 1
        (u i : UnitAddCircle)| := by
    classical
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih => simp [Finset.prod_insert, hi, ih, abs_mul]
  rw [hprod]
  apply Finset.prod_le_prod₀
  · intro i hi
    positivity
  · intro i hi
    simpa [C, Nat.mul_one] using
      periodizedDyadicAtomDerivative1_abs_le (layerIndexDepth a i)
        (layerIndexCell a i) (layerIndexCell_lt a i) 1 hC
        (u i : UnitAddCircle)

private theorem derivativeAtom_integrable {d n : ℕ} (a : LayerIndex d n) :
    Integrable (fun u : Fin d → ℝ =>
      dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
        (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
        (fun i => (u i : UnitAddCircle))) (cubeMeasure d) := by
  classical
  let K : ℝ := ∏ i : Fin d,
    (Classical.choose (exists_smoothAtom_iteratedDeriv_bound 1) *
      (2 : ℝ) ^ layerIndexDepth a i)
  have hCpos : 0 < Classical.choose (exists_smoothAtom_iteratedDeriv_bound 1) :=
    (Classical.choose_spec (exists_smoothAtom_iteratedDeriv_bound 1)).1
  have hK : 0 ≤ K := by
    dsimp [K]
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg hCpos.le (by positivity)
  apply Integrable.of_bound
    (firstMixedDerivative_atom_continuous a).measurable.aestronglyMeasurable K
  filter_upwards with u
  rw [Real.norm_eq_abs]
  exact (derivativeAtom_abs_le a u).trans_eq (by rfl)

/-- Integrating the actual smooth Gaussian source density over an anchored
rectangle reproduces the paper's finite native smooth field. -/
theorem firstMixedDerivativeDensity_rectangular_integral_eq_native
    {d n : ℕ} (z : LayerIndex d n → ℝ) (t : BrownianCubeAnchor d) :
    (∫ u, rectangleKernel t u * firstMixedDerivativeDensity z u
      ∂cubeMeasure d) =
      periodicNativeSynthesisLinear z (fun i => (t.val i : UnitAddCircle)) := by
  classical
  have hterm (a : LayerIndex d n) :
      Integrable (fun u : Fin d → ℝ => rectangleKernel t u *
        (z a * dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
          (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
          (fun i => (u i : UnitAddCircle)))) (cubeMeasure d) := by
    exact integrable_kernel_mul _ ((derivativeAtom_integrable a).const_mul (z a)) t
  have hsum (u : Fin d → ℝ) :
      rectangleKernel t u * firstMixedDerivativeDensity z u =
        ∑ a : LayerIndex d n, rectangleKernel t u *
          (z a * dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
            (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
            (fun i => (u i : UnitAddCircle))) := by
    calc
      _ = ∑ a : LayerIndex d n, rectangleKernel t u *
          (dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
            (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
            (fun i => (u i : UnitAddCircle)) * z a) := by
        simp [firstMixedDerivativeDensity, GaussianRows.row, Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        ring
  calc
    _ = ∫ u, ∑ a : LayerIndex d n, rectangleKernel t u *
          (z a * dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
            (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
            (fun i => (u i : UnitAddCircle))) ∂cubeMeasure d := by
      apply integral_congr_ae
      exact ae_of_all _ hsum
    _ = ∑ a : LayerIndex d n, ∫ u, rectangleKernel t u *
          (z a * dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
            (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
            (fun i => (u i : UnitAddCircle))) ∂cubeMeasure d := by
      rw [integral_finsetSum Finset.univ (fun a ha => hterm a)]
    _ = ∑ a : LayerIndex d n, z a * periodicNativeAtom a
          (fun i => (t.val i : UnitAddCircle)) := by
      apply Finset.sum_congr rfl
      intro a ha
      have heq : (fun u : Fin d → ℝ => rectangleKernel t u *
          (z a * dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
            (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
            (fun i => (u i : UnitAddCircle)))) =
          (fun u => z a * (rectangleKernel t u *
            dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
              (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
              (fun i => (u i : UnitAddCircle)))) := by
        funext u
        ring
      rw [heq]
      rw [integral_const_mul]
      rw [firstMixedDerivative_atom_rectangular_integral_eq]
      rw [firstDerivativePrimitive_eq_periodicNativeAtom]
    _ = periodicNativeSynthesisLinear z (fun i => (t.val i : UnitAddCircle)) := by
      change (∑ a : LayerIndex d n, z a * periodicNativeAtom a
        (fun i => (t.val i : UnitAddCircle))) = _
      simp [periodicNativeSynthesisLinear, ContinuousMap.coe_sum, smul_eq_mul]

private theorem firstMixedDerivativeDensity_abs_le {d n : ℕ}
    (z : LayerIndex d n → ℝ) (u : Fin d → ℝ) :
    |firstMixedDerivativeDensity z u| ≤
      ∑ a : LayerIndex d n, |z a| *
        ∏ i : Fin d, (Classical.choose (exists_smoothAtom_iteratedDeriv_bound 1) *
          (2 : ℝ) ^ layerIndexDepth a i) := by
  classical
  rw [firstMixedDerivativeDensity, GaussianRows.row]
  calc
    |∑ a : LayerIndex d n,
        dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
          (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
          (fun i => (u i : UnitAddCircle)) * z a|
      ≤ ∑ a : LayerIndex d n,
        |dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
          (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
          (fun i => (u i : UnitAddCircle)) * z a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : LayerIndex d n, |z a| *
        ∏ i : Fin d, (Classical.choose (exists_smoothAtom_iteratedDeriv_bound 1) *
          (2 : ℝ) ^ layerIndexDepth a i) := by
      apply Finset.sum_le_sum
      intro a ha
      rw [abs_mul]
      calc
        |dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
            (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩)
            (fun i => (u i : UnitAddCircle))| * |z a| ≤
          (∏ i : Fin d, (Classical.choose (exists_smoothAtom_iteratedDeriv_bound 1) *
            (2 : ℝ) ^ layerIndexDepth a i)) * |z a| :=
              mul_le_mul_of_nonneg_right (derivativeAtom_abs_le a u)
                (abs_nonneg (z a))
        _ = _ := by ring

private theorem firstMixedDerivativeDensity_memLp {d n : ℕ}
    (z : LayerIndex d n → ℝ) {p : ℝ} (hp : 0 < p) :
    MemLp (firstMixedDerivativeDensity z) (ENNReal.ofReal p) (cubeMeasure d) := by
  classical
  haveI : IsProbabilityMeasure (cubeMeasure d) := cubeProbability d
  let D : ℝ := ∑ a : LayerIndex d n, |z a| *
    ∏ i : Fin d, (Classical.choose (exists_smoothAtom_iteratedDeriv_bound 1) *
      (2 : ℝ) ^ layerIndexDepth a i)
  have hD : 0 ≤ D := by
    dsimp [D]
    apply Finset.sum_nonneg
    intro a ha
    apply mul_nonneg (abs_nonneg _)
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg
      (Classical.choose_spec (exists_smoothAtom_iteratedDeriv_bound 1)).1.le
      (by positivity)
  apply MemLp.of_bound
    ((firstMixedDerivativeDensity_joint_continuous.comp
      (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable) D
  filter_upwards with u
  rw [Real.norm_eq_abs]
  exact (firstMixedDerivativeDensity_abs_le z u).trans (le_of_eq (by rfl))

/-- The source Lp norm to the `p`th power is exactly the spatial density
moment used in the Tonelli estimate. -/
theorem firstMixedDerivative_source_norm_rpow_eq {d n : ℕ}
    (z : LayerIndex d n → ℝ) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (‖(firstMixedDerivativeDensity_memLp z hp).toLp
      (firstMixedDerivativeDensity z)‖ ^ p) =
      ∫⁻ u, ENNReal.ofReal (|firstMixedDerivativeDensity z u| ^ p)
        ∂cubeMeasure d := by
  let hmem := firstMixedDerivativeDensity_memLp z hp
  rw [Lp.norm_def]
  rw [eLpNorm_congr_ae hmem.coeFn_toLp]
  have hformula := eLpNorm_rpow_eq_lintegral_ofReal_norm_rpow
    (firstMixedDerivativeDensity z) hp hmem.aestronglyMeasurable
  calc
    ENNReal.ofReal ((eLpNorm (firstMixedDerivativeDensity z)
        (ENNReal.ofReal p) (cubeMeasure d)).toReal ^ p) =
      (eLpNorm (firstMixedDerivativeDensity z) (ENNReal.ofReal p)
        (cubeMeasure d)) ^ p := by
          rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le,
            ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
    _ = ∫⁻ u, ENNReal.ofReal (|firstMixedDerivativeDensity z u| ^ p)
        ∂cubeMeasure d := by
          simpa [Real.norm_eq_abs] using hformula

/-- The actual Lp equivalence class represented by the smooth derivative
density. -/
def firstMixedDerivativeDensityLp {d n : ℕ} (z : LayerIndex d n → ℝ)
    (p : ℝ) (hp : 0 < p) : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d) :=
  (firstMixedDerivativeDensity_memLp z hp).toLp (firstMixedDerivativeDensity z)

/-- The smooth native Gaussian field is the image of its actual mixed
derivative density under the paper's operator T_{d,p}. -/
theorem firstMixedDerivativeDensityLp_image_eq_native
    {d n : ℕ} (z : LayerIndex d n → ℝ) (p : ℝ) (hp : 1 < p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)] :
    anchoredIntegrationOperator p hp
      (firstMixedDerivativeDensityLp z p (lt_trans zero_lt_one hp)) =
      ⟨fun t => periodicNativeSynthesisLinear z
        (fun i => (t.val i : UnitAddCircle)), by
          apply (periodicNativeSynthesisLinear z).continuous.comp
          apply continuous_pi
          intro i
          exact (AddCircle.continuous_mk' (1 : ℝ)).comp
            ((continuous_apply i).comp continuous_subtype_val)⟩ := by
  ext t
  rw [anchoredIntegrationOperator_apply]
  simp only [anchoredLpValue, ← rectangleKernel_eq]
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  change (∫ u, rectangleKernel t u *
      (firstMixedDerivativeDensityLp z p hp0 : (Fin d → ℝ) → ℝ) u
        ∂cubeMeasure d) = periodicNativeSynthesisLinear z
          (fun i => (t.val i : UnitAddCircle))
  have hcoe := (firstMixedDerivativeDensity_memLp z hp0).coeFn_toLp
  calc
    _ = ∫ u, rectangleKernel t u * firstMixedDerivativeDensity z u
        ∂cubeMeasure d := by
      apply integral_congr_ae
      filter_upwards [hcoe] with u hu
      rw [show (firstMixedDerivativeDensityLp z p hp0 :
        (Fin d → ℝ) → ℝ) u = firstMixedDerivativeDensity z u by
          simpa [firstMixedDerivativeDensityLp] using hu]
    _ = _ := firstMixedDerivativeDensity_rectangular_integral_eq_native z t

/-- At a fixed scale, the translated first derivatives have disjoint
supports, so their pointwise square sum is bounded by one atom's squared
supremum. -/
private theorem scalar_firstDerivative_square_sum_le (s : ℕ) (x : UnitAddCircle)
    {C : ℝ} (hC : 0 ≤ C)
    (hderiv : ∀ y : ℝ, |iteratedDeriv 1 smoothAtom y| ≤ C) :
    (∑ j : Fin (2 ^ s),
      (periodizedDyadicAtomDerivative1 s j.val j.isLt 1 x) ^ 2) ≤
      (C * (2 : ℝ) ^ s) ^ 2 := by
  classical
  let f : Fin (2 ^ s) → ℝ := fun j =>
    periodizedDyadicAtomDerivative1 s j.val j.isLt 1 x
  let B : ℝ := C * (2 : ℝ) ^ s
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound : ∀ j, |f j| ≤ B := by
    intro j
    simpa [f, B] using
      periodizedDyadicAtomDerivative1_abs_le s j.val j.isLt 1 hderiv x
  have hpair : ∀ i j, i ≠ j → f i * f j = 0 := by
    intro i j hij
    have hval : i.val ≠ j.val := by intro h; exact hij (Fin.ext h)
    have hc := periodizedDyadicAtomDerivative1_pairwise_product_eq_zero
      s i.val j.val i.isLt j.isLt hval 1 x
    have hr : ((f i * f j : ℝ) : ℂ) = 0 := by
      simpa [f, Complex.star_def] using hc
    exact_mod_cast hr
  by_cases hex : ∃ j, f j ≠ 0
  · let j₀ := Classical.choose hex
    have hj₀ : f j₀ ≠ 0 := Classical.choose_spec hex
    have hzero (j : Fin (2 ^ s)) (hji : j ≠ j₀) : f j = 0 := by
      have hz := hpair j j₀ hji
      exact (mul_eq_zero.mp hz).resolve_right hj₀
    have hsum : (∑ j : Fin (2 ^ s), (f j) ^ 2) = (f j₀) ^ 2 := by
      apply Finset.sum_eq_single j₀
      · intro j hj hne
        rw [hzero j hne]
        simp
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ j₀))
    calc
      (∑ j : Fin (2 ^ s), (f j) ^ 2) = (f j₀) ^ 2 := hsum
      _ ≤ B ^ 2 := by
        have habs := abs_le.mp (hbound j₀)
        nlinarith [sq_nonneg (f j₀)]
  · have hzero : ∀ j, f j = 0 := by
      intro j
      by_contra hj
      exact hex ⟨j, hj⟩
    simp [f, hzero]
    positivity

/-- The pointwise square sum over all derivative atoms in one rectangular
shape is bounded by the product of the coordinate derivative envelopes. -/
theorem firstMixedDerivative_shape_square_sum_le {d : ℕ}
    (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)) {C : ℝ}
    (hC : 0 ≤ C)
    (hderiv : ∀ y : ℝ, |iteratedDeriv 1 smoothAtom y| ≤ C) :
    (∑ j : DyadicShapeCell d s,
      (dyadicShapeDerivativeAtom s (fun _ => 1) j x) ^ 2) ≤
      ∏ i : Fin d, (C * (2 : ℝ) ^ (s i)) ^ 2 := by
  classical
  have hfactor (j : DyadicShapeCell d s) :
      (dyadicShapeDerivativeAtom s (fun _ => 1) j x) ^ 2 =
        ∏ i : Fin d,
          (periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 1
            (x i)) ^ 2 := by
    simp [dyadicShapeDerivativeAtom, Finset.prod_pow]
  rw [show (fun j : DyadicShapeCell d s =>
      (dyadicShapeDerivativeAtom s (fun _ => 1) j x) ^ 2) =
      fun j => ∏ i : Fin d,
        (periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 1
          (x i)) ^ 2 from funext hfactor]
  change (∑ j : (∀ i : Fin d, Fin (2 ^ s i)),
      ∏ i : Fin d,
        (periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 1
          (x i)) ^ 2) ≤ _
  have hsum := sum_pi_prod (fun i (j : Fin (2 ^ s i)) =>
    (periodizedDyadicAtomDerivative1 (s i) j.val j.isLt 1 (x i)) ^ 2)
  rw [hsum]
  apply Finset.prod_le_prod₀
  · intro i hi
    positivity
  · intro i hi
    simpa [pow_two] using
      scalar_firstDerivative_square_sum_le (s i) (x i) hC hderiv

/-- Whole-grade source variance bound for the actual smooth first mixed
derivatives. It is the pointwise envelope `2^(2n) C^(2d) S_n` from the
paper's Gaussian density route. -/
theorem firstMixedDerivative_layer_square_sum_le {d n : ℕ}
    (x : UnitAddTorus (Fin d)) {C : ℝ}
    (hC : 0 ≤ C)
    (hderiv : ∀ y : ℝ, |iteratedDeriv 1 smoothAtom y| ≤ C) :
    (∑ a : LayerIndex d n,
      (dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
        (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩) x) ^ 2) ≤
      (2 : ℝ) ^ (2 * n) * C ^ (2 * d) *
        (Fintype.card (Shape d n) : ℝ) := by
  classical
  rw [Fintype.sum_sigma]
  calc
    (∑ r : Shape d n,
      ∑ j : DyadicShapeCell d r.1,
        (dyadicShapeDerivativeAtom r.1 (fun _ => 1) j x) ^ 2) ≤
      ∑ r : Shape d n,
        (2 : ℝ) ^ (2 * n) * C ^ (2 * d) := by
          apply Finset.sum_le_sum
          intro r hr
          have hs := firstMixedDerivative_shape_square_sum_le r.1 x hC hderiv
          have hgrade : (r.1.sum fun _ v => v) = n :=
            (Finset.mem_finsuppAntidiag'.mp r.2).1
          have hprod : (∏ i : Fin d, (C * (2 : ℝ) ^ r.1 i) ^ 2) =
              (2 : ℝ) ^ (2 * n) * C ^ (2 * d) := by
            calc
              _ = (∏ i : Fin d, C ^ 2) *
                    (∏ i : Fin d, ((2 : ℝ) ^ r.1 i) ^ 2) := by
                    simp only [mul_pow, Finset.prod_mul_distrib]
              _ = C ^ (2 * d) * (2 : ℝ) ^ (2 * n) := by
                    rw [Finset.prod_const]
                    have hpow : (∏ i : Fin d, ((2 : ℝ) ^ r.1 i) ^ 2) =
                        (2 : ℝ) ^ (2 * n) := by
                      simp_rw [← pow_mul]
                      rw [Finset.prod_pow_eq_pow_sum]
                      have hsum : (∑ i : Fin d, r.1 i * 2) = 2 * n := by
                        have hgrade' : (∑ i : Fin d, r.1 i) = n := by
                          simpa [Finsupp.sum_fintype] using hgrade
                        rw [← Finset.sum_mul]
                        rw [hgrade']
                        omega
                      rw [hsum]
                    rw [hpow]
                    congr 1
                    simp [Fintype.card_fin, pow_mul]
              _ = (2 : ℝ) ^ (2 * n) * C ^ (2 * d) := by ring
          simpa only [hprod] using hs
    _ = (2 : ℝ) ^ (2 * n) * C ^ (2 * d) *
        (Fintype.card (Shape d n) : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ]
          ring

/-- The pointwise pth moment of the actual Gaussian first mixed derivative
row is controlled by the proved whole-layer variance envelope. -/
theorem firstMixedDerivative_gaussian_row_absRpow_integral_le
    {d n : ℕ} (x : UnitAddTorus (Fin d)) {C p : ℝ}
    (hC : 0 ≤ C)
    (hderiv : ∀ y : ℝ, |iteratedDeriv 1 smoothAtom y| ≤ C)
    (hp : 0 < p) :
    (∫ z : LayerIndex d n → ℝ,
      |GaussianRows.row (fun a z => z a)
        (fun a => dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
          (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩) x) z| ^ p
      ∂productStandardGaussian (LayerIndex d n)) ≤
      ((2 : ℝ) ^ n * C ^ d *
        Real.sqrt (Fintype.card (Shape d n) : ℝ)) ^ p *
        gaussianAbsoluteMoment p := by
  classical
  let G : LayerIndex d n → (LayerIndex d n → ℝ) → ℝ := fun a z => z a
  let P : Measure (LayerIndex d n → ℝ) := productStandardGaussian (LayerIndex d n)
  let c : LayerIndex d n → ℝ := fun a =>
    dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
      (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩) x
  let V : ℝ := (2 : ℝ) ^ (2 * n) * C ^ (2 * d) *
    (Fintype.card (Shape d n) : ℝ)
  let A : ℝ := (2 : ℝ) ^ n * C ^ d *
    Real.sqrt (Fintype.card (Shape d n) : ℝ)
  have hG : ∀ a, Measurable (G a) := fun a => measurable_pi_apply a
  have hLaw : ∀ a, P.map (G a) = gaussianReal 0 1 := by
    intro a
    dsimp [P, G, productStandardGaussian]
    exact productStandardGaussian_coordinate_law a
  have hIndep : iIndepFun G P := by
    dsimp [P, G, productStandardGaussian]
    exact productStandardGaussian_coordinates_independent (LayerIndex d n)
  have hvar : ∑ a : LayerIndex d n, c a ^ 2 ≤ V := by
    dsimp [c, V]
    exact firstMixedDerivative_layer_square_sum_le x hC hderiv
  have hV : 0 ≤ V := by
    dsimp [V]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hAsq : A ^ 2 = V := by
    dsimp [A, V]
    calc
      (2 ^ n * C ^ d * Real.sqrt (Fintype.card (Shape d n) : ℝ)) ^ 2 =
          (2 ^ n) ^ 2 * (C ^ d) ^ 2 *
            (Real.sqrt (Fintype.card (Shape d n) : ℝ)) ^ 2 := by ring
      _ = (2 : ℝ) ^ (2 * n) * C ^ (2 * d) *
          (Fintype.card (Shape d n) : ℝ) := by
        rw [Real.sq_sqrt (by positivity :
          0 ≤ (Fintype.card (Shape d n) : ℝ))]
        simp only [← pow_mul]
        rw [Nat.mul_comm n 2, Nat.mul_comm d 2]
  have hmoment : (∫ z : LayerIndex d n → ℝ,
      |GaussianRows.row G c z| ^ p ∂P) =
      (Real.sqrt (∑ a : LayerIndex d n, c a ^ 2)) ^ p *
        gaussianAbsoluteMoment p :=
    gaussianRow_absRpow_integral G hG hLaw hIndep c hp
  have hsqrt : Real.sqrt (∑ a : LayerIndex d n, c a ^ 2) ≤ A := by
    calc
      _ ≤ Real.sqrt V := Real.sqrt_le_sqrt hvar
      _ = A := by
        rw [← hAsq, Real.sqrt_sq_eq_abs, abs_of_nonneg hA]
  have hpow : (Real.sqrt (∑ a : LayerIndex d n, c a ^ 2)) ^ p ≤ A ^ p :=
    Real.rpow_le_rpow (Real.sqrt_nonneg _) hsqrt hp.le
  have hmnonneg : 0 ≤ gaussianAbsoluteMoment p := by
    unfold gaussianAbsoluteMoment
    exact integral_nonneg fun _ => by positivity
  change (∫ z : LayerIndex d n → ℝ,
      |GaussianRows.row G c z| ^ p ∂P) ≤ A ^ p * gaussianAbsoluteMoment p
  rw [hmoment]
  exact mul_le_mul_of_nonneg_right hpow hmnonneg

private theorem cubeMeasure_isProbability (d : ℕ) :
    IsProbabilityMeasure (cubeMeasure d) := by
  haveI : IsProbabilityMeasure
      ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  rw [cubeMeasure, AlignmentFractionalTensor.unitCube_measure_eq_pi]
  infer_instance

/-- Tonelli's theorem on the actual unit cube transfers the pointwise Gaussian
moment bound to the expected source-density `Lᵖ` energy. -/
theorem firstMixedDerivative_cube_expected_rpow_le
    {d n : ℕ} (p C : ℝ)
    (hC : 0 ≤ C)
    (hderiv : ∀ y : ℝ, |iteratedDeriv 1 smoothAtom y| ≤ C)
    (hp : 0 < p) :
    (∫⁻ z : LayerIndex d n → ℝ,
      ∫⁻ u : Fin d → ℝ,
        ENNReal.ofReal (|firstMixedDerivativeDensity z u| ^ p)
        ∂cubeMeasure d ∂productStandardGaussian (LayerIndex d n)) ≤
      ENNReal.ofReal (((2 : ℝ) ^ n * C ^ d *
        Real.sqrt (Fintype.card (Shape d n) : ℝ)) ^ p *
        gaussianAbsoluteMoment p) := by
  classical
  let μ := cubeMeasure d
  let P : Measure (LayerIndex d n → ℝ) :=
    productStandardGaussian (LayerIndex d n)
  let F : ((LayerIndex d n → ℝ) × (Fin d → ℝ)) → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (|firstMixedDerivativeDensity y.1 y.2| ^ p)
  have hF : Measurable F := by
    exact firstMixedDerivativeDensity_rpow_joint_measurable p hp.le
  haveI : IsProbabilityMeasure μ := by
    simpa [μ] using cubeMeasure_isProbability d
  haveI : IsProbabilityMeasure P := by
    dsimp [P]
    infer_instance
  let B : ℝ := ((2 : ℝ) ^ n * C ^ d *
    Real.sqrt (Fintype.card (Shape d n) : ℝ)) ^ p * gaussianAbsoluteMoment p
  have hB : 0 ≤ B := by
    dsimp [B]
    have hm : 0 ≤ gaussianAbsoluteMoment p := by
      unfold gaussianAbsoluteMoment
      exact integral_nonneg fun _ => by positivity
    positivity
  have hinner (u : Fin d → ℝ) :
      (∫⁻ z : LayerIndex d n → ℝ, F (z, u) ∂P) ≤ ENNReal.ofReal B := by
    let x : UnitAddTorus (Fin d) := fun i => (u i : UnitAddCircle)
    let G : LayerIndex d n → (LayerIndex d n → ℝ) → ℝ := fun a z => z a
    let c : LayerIndex d n → ℝ := fun a =>
      dyadicShapeDerivativeAtom (layerIndexDepth a) (fun _ => 1)
        (fun i => ⟨layerIndexCell a i, layerIndexCell_lt a i⟩) x
    have hInt := gaussianRow_absRpow_integrable G
      (fun a => measurable_pi_apply a)
      (by
        intro a
        dsimp [P, G, productStandardGaussian]
        exact productStandardGaussian_coordinate_law a)
      (by
        dsimp [P, G, productStandardGaussian]
        exact productStandardGaussian_coordinates_independent (LayerIndex d n))
      c hp
    have hnonneg : ∀ z, 0 ≤ |GaussianRows.row G c z| ^ p := by
      intro z
      positivity
    have hlin : (∫⁻ z : LayerIndex d n → ℝ,
        ENNReal.ofReal (|GaussianRows.row G c z| ^ p) ∂P) =
        ENNReal.ofReal (∫ z, |GaussianRows.row G c z| ^ p ∂P) := by
      symm
      exact ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ hnonneg)
    have hmoment := firstMixedDerivative_gaussian_row_absRpow_integral_le
      (d := d) (n := n) x hC hderiv hp
    have hle : (∫ z, |GaussianRows.row G c z| ^ p ∂P) ≤ B := by
      simpa [B, P, G, c] using hmoment
    have hrewrite : (fun z : LayerIndex d n → ℝ => F (z, u)) =
        fun z => ENNReal.ofReal (|GaussianRows.row G c z| ^ p) := by
      funext z
      simp [F, firstMixedDerivativeDensity, GaussianRows.row, G, c, x]
    rw [hrewrite, hlin]
    exact ENNReal.ofReal_le_ofReal hle
  have hfirst := MeasureTheory.lintegral_prod (μ := P) (ν := μ) F hF.aemeasurable
  have hsecond := MeasureTheory.lintegral_prod (μ := μ) (ν := P)
    (fun y => F y.swap) (hF.comp measurable_swap).aemeasurable
  have hswap := MeasureTheory.lintegral_prod_swap (μ := P) (ν := μ) F
  have hiter :
      (∫⁻ z : LayerIndex d n → ℝ, ∫⁻ u : Fin d → ℝ, F (z,u) ∂μ ∂P) =
      (∫⁻ u : Fin d → ℝ, ∫⁻ z : LayerIndex d n → ℝ, F (z,u) ∂P ∂μ) := by
    calc
      _ = ∫⁻ y : (LayerIndex d n → ℝ) × (Fin d → ℝ), F y ∂P.prod μ := hfirst.symm
      _ = ∫⁻ y : (Fin d → ℝ) × (LayerIndex d n → ℝ), F y.swap ∂μ.prod P := hswap.symm
      _ = _ := hsecond
  calc
    _ = ∫⁻ u : Fin d → ℝ, ∫⁻ z : LayerIndex d n → ℝ, F (z,u) ∂P ∂μ := by
      simpa [F, P, μ] using hiter
    _ ≤ ∫⁻ u : Fin d → ℝ, ENNReal.ofReal B ∂μ :=
      lintegral_mono fun u => hinner u
    _ = ENNReal.ofReal B := by
      rw [lintegral_const, MeasureTheory.measure_univ]
      simp [B]

/-- Literal cube source-density energy for one Gaussian coefficient vector. -/
def firstMixedDerivativeCubeEnergy {d n : ℕ} (p : ℝ)
    (z : LayerIndex d n → ℝ) : ℝ≥0∞ :=
  ∫⁻ u : Fin d → ℝ,
    ENNReal.ofReal (|firstMixedDerivativeDensity z u| ^ p) ∂cubeMeasure d

/-- The paper's smooth finite Gaussian field restricted to anchored cube paths. -/
def smoothNativeCubePath {d n : ℕ} (z : LayerIndex d n → ℝ) :
    C(BrownianCubeAnchor d, ℝ) :=
  ⟨fun t => periodicNativeSynthesisLinear z
      (fun i => (t.val i : UnitAddCircle)), by
    apply (periodicNativeSynthesisLinear z).continuous.comp
    apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_apply i).comp continuous_subtype_val)⟩

private def smoothNativeCubePathLinear {d n : ℕ} :
    (LayerIndex d n → ℝ) →ₗ[ℝ] C(BrownianCubeAnchor d, ℝ) where
  toFun := smoothNativeCubePath
  map_add' z w := by
    ext t
    simp [smoothNativeCubePath, periodicNativeSynthesisLinear,
      Finset.sum_add_distrib, add_mul]
  map_smul' c z := by
    ext t
    simp [smoothNativeCubePath, periodicNativeSynthesisLinear,
      ContinuousMap.smul_apply, smul_eq_mul]

/-- The arbitrary-center translated-ball cap for the literal finite smooth
Gaussian path, reduced to the centered sup-norm ball (Anderson). -/
theorem smoothNativeCubePath_translated_ball_mass_le
    {d n : ℕ} (hd : 0 < d) (ρ : NNReal) (Q : ℝ≥0∞)
    (hconf : productStandardGaussian (LayerIndex d n)
      {z | ‖smoothNativeCubePath z‖ ≤ 2 * (ρ : ℝ)} ≤ Q) :
    ∀ f : C(BrownianCubeAnchor d, ℝ),
      productStandardGaussian (LayerIndex d n)
        {z | edist (smoothNativeCubePath z) f ≤ (ρ : ℝ≥0∞)} ≤ Q := by
  haveI : Nonempty (LayerIndex d n) := nativeLayerIndex_nonempty d n hd
  intro f
  refine le_trans (measure_mono fun z hz => ?_) (le_trans
    (AlignmentPaperConfinementBridge.linearSynthesis_ball_mass_le
      (smoothNativeCubePathLinear (d := d) (n := n)) f ρ) hconf)
  change edist (smoothNativeCubePath z) f ≤ ρ at hz
  rw [edist_dist, dist_eq_norm] at hz
  have h : ‖smoothNativeCubePath z - f‖ ≤ (ρ : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff ρ.2).1 (by simpa using hz)
  exact h

/-- Energy sublevel control gives the actual cube Lp source norm sublevel for
the derivative density. -/
theorem firstMixedDerivative_cube_Lp_sublevel_mass
    {d n : ℕ} (p : ℝ) (hp : 1 < p) (L : ℝ) (hL : 0 < L)
    (hmean : (∫⁻ z : LayerIndex d n → ℝ,
      firstMixedDerivativeCubeEnergy p z
      ∂productStandardGaussian (LayerIndex d n)) ≤ ENNReal.ofReal ((L : ℝ) ^ p / 2)) :
    (1 / 2 : ℝ≥0∞) ≤ productStandardGaussian (LayerIndex d n)
      {z | ‖firstMixedDerivativeDensityLp z p (lt_trans zero_lt_one hp)‖ ≤ L} := by
  classical
  haveI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp.le⟩
  let P := productStandardGaussian (LayerIndex d n)
  let E := fun z : LayerIndex d n → ℝ => firstMixedDerivativeCubeEnergy p z
  haveI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hEmeas : Measurable E := by
    unfold E firstMixedDerivativeCubeEnergy
    exact Measurable.lintegral_prod_right
      (firstMixedDerivativeDensity_rpow_joint_measurable p
        (le_of_lt (lt_trans zero_lt_one hp)))
  have hmark := ennreal_energy_sublevel_mass P E hEmeas
    (ENNReal.ofReal_pos.mpr (by
      exact div_pos (Real.rpow_pos_of_pos hL p) (by norm_num)))
    ENNReal.ofReal_ne_top hmean
  have htwo : (2 : ℝ≥0∞) * ENNReal.ofReal ((L : ℝ) ^ p / 2) =
      ENNReal.ofReal ((L : ℝ) ^ p) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hmark' : (1 / 2 : ℝ≥0∞) ≤
      P {z | E z ≤ ENNReal.ofReal ((L : ℝ) ^ p)} := by
    rw [← htwo]
    exact hmark
  apply hmark'.trans
  apply measure_mono
  intro z hz
  change firstMixedDerivativeCubeEnergy p z ≤ ENNReal.ofReal (L ^ p) at hz
  have heq := firstMixedDerivative_source_norm_rpow_eq z (lt_trans zero_lt_one hp)
  rw [firstMixedDerivativeCubeEnergy] at hz
  rw [← heq] at hz
  have hpow : ‖firstMixedDerivativeDensityLp z p
      (lt_trans zero_lt_one hp)‖ ^ p ≤ L ^ p := by
    change ENNReal.ofReal (‖firstMixedDerivativeDensityLp z p
      (lt_trans zero_lt_one hp)‖ ^ p) ≤ ENNReal.ofReal (L ^ p) at hz
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hz
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  exact (Real.rpow_le_rpow_iff
    (norm_nonneg (firstMixedDerivativeDensityLp z p hp0)) hL.le hp0).mp hpow

/-- Combining source Markov control with the exact integration identity places
at least half the smooth field law in a dilation of the actual T_{d,p} image
of its closed source unit ball. -/
theorem firstMixedDerivative_smoothNative_image_ball_mass
    {d n : ℕ} (p : ℝ) (hp : 1 < p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)] (L : ℝ) (hL : 0 < L)
    (hmean : (∫⁻ z : LayerIndex d n → ℝ,
      firstMixedDerivativeCubeEnergy p z
      ∂productStandardGaussian (LayerIndex d n)) ≤ ENNReal.ofReal (L ^ p / 2)) :
    (1 / 2 : ℝ≥0∞) ≤ productStandardGaussian (LayerIndex d n)
      {z | smoothNativeCubePath z ∈ (L : ℝ) •
        (anchoredIntegrationOperator p hp '' Metric.closedBall
          (0 : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) 1)} := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal hp.le⟩
  have hsub := firstMixedDerivative_cube_Lp_sublevel_mass p hp L hL hmean
  apply hsub.trans
  apply measure_mono
  intro z hz
  change ‖firstMixedDerivativeDensityLp z p
    (lt_trans zero_lt_one hp)‖ ≤ L at hz
  let g := firstMixedDerivativeDensityLp z p (lt_trans zero_lt_one hp)
  have hpath : smoothNativeCubePath z = anchoredIntegrationOperator p hp g := by
    simpa [smoothNativeCubePath, g] using
      (firstMixedDerivativeDensityLp_image_eq_native z p hp).symm
  change smoothNativeCubePath z ∈ (L : ℝ) •
    (anchoredIntegrationOperator p hp '' Metric.closedBall
      (0 : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) 1)
  rw [hpath]
  let x := L⁻¹ • g
  have hx : x ∈ Metric.closedBall (0 : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp [x]
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hL]
    exact (inv_mul_le_iff₀ hL).2 (by simpa using hz)
  refine ⟨anchoredIntegrationOperator p hp x, ⟨x, hx, rfl⟩, ?_⟩
  change L • anchoredIntegrationOperator p hp x =
    anchoredIntegrationOperator p hp g
  rw [← map_smul]
  congr 1
  dsimp [x]
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hL), one_smul]

end BrownianSharp.AlignmentAnchoredLpEnergy
