import BrownianSharp.FixedShapeBlockConvolution
import BrownianSharp.UnitTorusMeasure
import BrownianSharp.AlignmentEndpointBesov
import Mathlib.Tactic

/-! Pointwise fixed-shape block estimate from the actual mixed Fourier kernel.
This is the L∞ counterpart of the existing finite-p convolution estimate.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open UnitAddTorus

/-- The mixed-kernel convolution bounds the smooth block pointwise by the
kernel's `L¹` norm times a uniform bound on the derivative synthesis. -/
theorem fixedShapeBlock_pointwise_le_kernelL1_mul_derivativeSup
    {d : ℕ} (s t k : Fin d → ℕ)
    (c : DyadicShapeCell d s → ℝ)
    (hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i)))
    (L U : ℝ) (hL : 0 ≤ L) (hU : 0 ≤ U)
    (hkernel : (∫ y : UnitAddTorus (Fin d),
      ‖coordinateProductKernel (fixedShapeMixedKernel t k) y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L)
    (hderiv : ∀ y : UnitAddTorus (Fin d),
      |fixedShapeDerivativeSynthesis s k c y| ≤ U) :
    ∀ x : UnitAddTorus (Fin d),
      ‖SmoothResolution.block t (fixedShapeSynthesis s c) x‖ ≤ L * U := by
  classical
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  let K : C(UnitAddTorus (Fin d), ℂ) := coordinateProductKernel
    (fixedShapeMixedKernel t k)
  let u : C(UnitAddTorus (Fin d), ℂ) :=
    ⟨fun y => (fixedShapeDerivativeSynthesis s k c y : ℝ),
      Complex.continuous_ofReal.comp (fixedShapeDerivativeSynthesis s k c).continuous⟩
  have hkernelSum := fixedShapeMixedKernel_eq_sum t k hscale
  have hkernelAt (x y : UnitAddTorus (Fin d)) :
      (∑ n ∈ frequencyBox t,
        fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) = K (x-y) := by
    have hh := congrArg (fun f : C(UnitAddTorus (Fin d), ℂ) => f (x-y)) hkernelSum
    simpa [K, fixedShapeMixedSumKernel, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply] using hh.symm
  have hconv (x : UnitAddTorus (Fin d)) :
      SmoothResolution.block t (fixedShapeSynthesis s c) x =
        ∫ y : UnitAddTorus (Fin d), K y * u (x-y) ∂μ := by
    rw [fixedShapeBlock_eq_mixedKernel_integral s t k c hscale x]
    letI : Measure.IsAddLeftInvariant μ := inferInstance
    have hneg : MeasurePreserving (fun y : UnitAddTorus (Fin d) => -y) μ μ := by
      change MeasurePreserving (fun y : (Fin d → UnitAddCircle) => -y)
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
      exact measurePreserving_pi
        (fun _ : Fin d => AddCircle.haarAddCircle)
        (fun _ : Fin d => AddCircle.haarAddCircle)
        (fun i : Fin d => Measure.measurePreserving_neg (AddCircle.haarAddCircle))
    have hadd : MeasurePreserving (fun y : UnitAddTorus (Fin d) => x + y) μ μ :=
      measurePreserving_add_left μ x
    have hmp : MeasurePreserving (fun y : UnitAddTorus (Fin d) => x-y) μ μ := by
      convert hadd.comp hneg using 1 <;> ext y <;> simp [sub_eq_add_neg]
    let g : UnitAddTorus (Fin d) → ℂ := fun y => K y * u (x-y)
    calc
      (∫ y : UnitAddTorus (Fin d),
          ∑ n ∈ frequencyBox t,
            (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
              ((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ) ∂μ) =
        ∫ y : UnitAddTorus (Fin d),
          (∑ n ∈ frequencyBox t,
            fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
            u y ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with y
              simp [u, Finset.sum_mul]
      _ = ∫ y : UnitAddTorus (Fin d), g (x-y) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with y
          change (∑ n ∈ frequencyBox t,
              fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) * u y =
            g (x-y)
          rw [hkernelAt x y]
          simp [g, u, sub_sub_cancel]
      _ = ∫ y : UnitAddTorus (Fin d), g y ∂μ :=
        hmp.integral_comp (Homeomorph.subLeft x).measurableEmbedding g
      _ = ∫ y : UnitAddTorus (Fin d), K y * u (x-y) ∂μ := rfl
  intro x
  have hKint : Integrable (fun y : UnitAddTorus (Fin d) => ‖K y‖) μ := by
    apply Integrable.of_bound K.continuous.norm.aestronglyMeasurable ‖K‖
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using K.norm_coe_le_norm y
  have hint : Integrable (fun y : UnitAddTorus (Fin d) => K y * u (x-y)) μ := by
    apply Integrable.of_bound (K.continuous.mul
      (u.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      (‖K‖ * U)
    filter_upwards [] with y
    change ‖K y * u (x-y)‖ ≤ ‖K‖ * U
    rw [norm_mul]
    have hu : ‖u (x-y)‖ ≤ U := by
      simpa [u, Complex.norm_real, Real.norm_eq_abs] using hderiv (x-y)
    calc
      ‖K y‖ * ‖u (x-y)‖ ≤ ‖K y‖ * U := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
      _ ≤ ‖K‖ * U := mul_le_mul_of_nonneg_right (K.norm_coe_le_norm y) hU
  have hnorm := norm_integral_le_integral_norm (μ := μ) (fun y => K y * u (x-y))
  have hk : (∫ y : UnitAddTorus (Fin d), ‖K y‖ ∂μ) ≤ L := by
    simpa [μ] using hkernel
  calc
    ‖SmoothResolution.block t (fixedShapeSynthesis s c) x‖ =
        ‖∫ y : UnitAddTorus (Fin d), K y * u (x-y) ∂μ‖ := by rw [hconv x]
    _ ≤ ∫ y : UnitAddTorus (Fin d), ‖K y * u (x-y)‖ ∂μ := hnorm
    _ ≤ ∫ y : UnitAddTorus (Fin d), ‖K y‖ * U ∂μ := by
      apply integral_mono_ae hint.norm
      · exact hKint.mul_const U
      · filter_upwards [] with y
        change ‖K y * u (x-y)‖ ≤ ‖K y‖ * U
        rw [norm_mul]
        have hu : ‖u (x-y)‖ ≤ U := by
          simpa [u, Complex.norm_real, Real.norm_eq_abs] using hderiv (x-y)
        exact mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    _ = (∫ y : UnitAddTorus (Fin d), ‖K y‖ ∂μ) * U := by
      rw [integral_mul_const]
    _ ≤ L * U := mul_le_mul_of_nonneg_right hk hU

/-- Pairwise disjoint tensor derivative atoms turn a coefficient box into a
uniform pointwise bound, with no cell-count loss. -/
theorem fixedShapeDerivativeSynthesis_abs_le_of_coeff_bound
    {d : ℕ} (s k : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hcoeff : ∀ j, |c j| ≤ M)
    (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hderiv : ∀ i y, |iteratedDeriv (k i) smoothAtom y| ≤ C i) :
    ∀ x : UnitAddTorus (Fin d),
      |fixedShapeDerivativeSynthesis s k c x| ≤
        M * ∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i)) := by
  classical
  intro x
  let a : DyadicShapeCell d s → ℝ := fun j =>
    c j * dyadicShapeDerivativeAtom s k j x
  have hpair (j j' : DyadicShapeCell d s) (hjj : j ≠ j') :
      a j * a j' = 0 := by
    dsimp [a]
    rw [show (c j * dyadicShapeDerivativeAtom s k j x) *
      (c j' * dyadicShapeDerivativeAtom s k j' x) =
      (c j * c j') * (dyadicShapeDerivativeAtom s k j x *
        dyadicShapeDerivativeAtom s k j' x) by ring]
    rw [dyadicShapeDerivativeAtom_mul_eq_zero_of_ne s k j j' hjj x]
    ring
  have hsum (j : DyadicShapeCell d s)
      (hj : a j ≠ 0) : (∑ j' : DyadicShapeCell d s, a j') = a j := by
    apply Finset.sum_eq_single j
    · intro j' hj' hneq
      by_contra hnonzero
      exact hj (by
        have hz := hpair j j' hneq.symm
        exact (mul_eq_zero.mp hz).resolve_right hnonzero)
    · intro hnot
      exact (hnot (Finset.mem_univ j)).elim
  by_cases hex : ∃ j : DyadicShapeCell d s, a j ≠ 0
  · obtain ⟨j, hj⟩ := hex
    rw [show fixedShapeDerivativeSynthesis s k c x = ∑ j' : DyadicShapeCell d s, a j' by
      simp [fixedShapeDerivativeSynthesis, a]]
    rw [hsum j hj]
    calc
      |c j * dyadicShapeDerivativeAtom s k j x| =
        |c j| * |dyadicShapeDerivativeAtom s k j x| := abs_mul _ _
      _ ≤ M * ∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i)) :=
        mul_le_mul (hcoeff j)
          (dyadicShapeDerivativeAtom_abs_le s k j x C hC hderiv)
          (abs_nonneg _) hM
  · have hz : ∀ j : DyadicShapeCell d s, a j = 0 := by
      intro j
      by_contra hne
      exact hex ⟨j, hne⟩
    rw [show fixedShapeDerivativeSynthesis s k c x = ∑ j : DyadicShapeCell d s, a j by
      simp [fixedShapeDerivativeSynthesis, a]]
    calc
      |∑ j : DyadicShapeCell d s, a j| = 0 := by simp [hz]
      _ ≤ M * ∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i)) := by
        apply mul_nonneg hM
        apply Finset.prod_nonneg
        intro i hi
        exact mul_nonneg (hC i) (by positivity)


/-- Fixed-shape block L∞ bound directly from the coefficient box and the
actual mixed-kernel L¹ budget. -/
theorem fixedShapeBlock_pointwise_le_of_coeff_bound
    {d : ℕ} (s t k : Fin d → ℕ)
    (c : DyadicShapeCell d s → ℝ)
    (hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i)))
    (M : ℝ) (hM : 0 ≤ M) (hcoeff : ∀ j, |c j| ≤ M)
    (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hderiv : ∀ i y, |iteratedDeriv (k i) smoothAtom y| ≤ C i)
    (L : ℝ) (hL : 0 ≤ L)
    (hkernel : (∫ y : UnitAddTorus (Fin d),
      ‖coordinateProductKernel (fixedShapeMixedKernel t k) y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L) :
    ∀ x : UnitAddTorus (Fin d),
      ‖SmoothResolution.block t (fixedShapeSynthesis s c) x‖ ≤
        L * (M * ∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i))) := by
  have hderivSup := fixedShapeDerivativeSynthesis_abs_le_of_coeff_bound
    s k c M hM hcoeff C hC hderiv
  have hU : 0 ≤ M * ∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i)) := by
    apply mul_nonneg hM
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg (hC i) (by positivity)
  intro x
  exact fixedShapeBlock_pointwise_le_kernelL1_mul_derivativeSup s t k c hscale
    L (M * ∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i))) hL hU hkernel hderivSup x


/-- The same coefficient-box estimate controls the literal weighted L∞ block
norm appearing in `SmoothResolution.BesovUnitBall`. -/
theorem fixedShape_weightedBlockNorm_top_le_of_coeff_bound
    {d : ℕ} (s t k : Fin d → ℕ)
    (c : DyadicShapeCell d s → ℝ)
    (hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i)))
    (M : ℝ) (hM : 0 ≤ M) (hcoeff : ∀ j, |c j| ≤ M)
    (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hderiv : ∀ i y, |iteratedDeriv (k i) smoothAtom y| ≤ C i)
    (L : ℝ) (hL : 0 ≤ L)
    (hkernel : (∫ y : UnitAddTorus (Fin d),
      ‖coordinateProductKernel (fixedShapeMixedKernel t k) y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L)
    (r : ℝ) :
    SmoothResolution.weightedBlockNorm (⊤ : ℝ≥0∞) r t
      (fixedShapeSynthesis s c) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (r * ∑ i, (t i : ℝ)) *
        (L * (M * ∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i))))) := by
  apply weightedBlockNorm_top_le_of_pointwise_bound r t
    (fixedShapeSynthesis s c)
    (L * (M * ∏ i : Fin d, (C i * (2 : ℝ) ^ (s i * k i))))
  · apply mul_nonneg hL
    apply mul_nonneg hM
    apply Finset.prod_nonneg
    intro i hi
    exact mul_nonneg (hC i) (by positivity)
  · exact fixedShapeBlock_pointwise_le_of_coeff_bound s t k c hscale M hM hcoeff
      C hC hderiv L hL hkernel


/-- The derivative envelope used by the fixed-shape L∞ estimate exists for
any fixed multi-order, from the actual compactly supported smooth atom. -/
theorem exists_coordinate_smoothAtom_derivative_envelope
    {d : ℕ} (k : Fin d → ℕ) :
    ∃ C : Fin d → ℝ, (∀ i, 0 < C i) ∧
      ∀ i y, |iteratedDeriv (k i) smoothAtom y| ≤ C i := by
  classical
  choose C hC hderiv using fun i : Fin d =>
    exists_smoothAtom_iteratedDeriv_bound (k i)
  exact ⟨C, hC, hderiv⟩

end BrownianSharp
