import BrownianSharp.FixedShapeBlockIntertwining
import BrownianSharp.FixedShapeDerivativeLp
import BrownianSharp.AtomicBlockKernel
import BrownianSharp.InverseDerivativeProfileIdentity

/-! Exact convolution identity for the fixed-shape mixed kernel. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.PeriodicCover
open BrownianSharp.ScalarHighFrequency
open BrownianSharp.ScalarKernelL1
open UnitAddTorus

/-- The finite tensor Fourier kernel for the mixed low-block / inverse
derivative multiplier. -/
def fixedShapeMixedSumKernel {d : ℕ} (t k : Fin d → ℕ) :
    C(UnitAddTorus (Fin d), ℂ) :=
  ∑ n ∈ frequencyBox t,
    fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n

private theorem fixedShapeMixedKernel_coordinate_coeff {d : ℕ}
    (t k : Fin d → ℕ) (hscale : ∀ i, k i = 0 ∨
      (0 < t i ∧ 0 < k i ∧ Even (k i))) (i : Fin d) (n : ℤ) :
    fourierCoeff (fixedShapeMixedKernel t k i) n =
      (if k i = 0 then (scalarBlock (t i) (n : ℝ) : ℂ)
        else inverseMultiplier (t i) (k i) n) := by
  rcases hscale i with hk | ⟨hti, hki, heven⟩
  · simpa [fixedShapeMixedKernel, hk] using
      (ScalarKernelL1.scalarBlockKernel_coefficient (t i) n)
  · have hk0 : k i ≠ 0 := by omega
    simpa [fixedShapeMixedKernel, hk0] using
      (inverseMultiplierKernel_coefficient (t i) (k i) hti n)

/-- Under the positive-grade condition, the coordinate product kernel in the
Lp estimate is exactly its finite product-multiplier expansion. -/
theorem fixedShapeMixedKernel_eq_sum {d : ℕ} (t k : Fin d → ℕ)
    (hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i))) :
    coordinateProductKernel (fixedShapeMixedKernel t k) =
      fixedShapeMixedSumKernel t k := by
  classical
  apply ContinuousMap.ext
  intro x
  simp only [coordinateProductKernel, fixedShapeMixedSumKernel,
    ContinuousMap.coe_mk, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
    smul_eq_mul]
  simp only [SmoothResolution.frequencyBox]
  have hterm (n : Fin d → ℤ) :
      fixedShapeMixedSymbol t k n * UnitAddTorus.mFourier n x =
        ∏ i : Fin d,
          (fourierCoeff (fixedShapeMixedKernel t k i) (n i) * fourier (n i) (x i)) := by
    rw [fixedShapeMixedSymbol, UnitAddTorus.mFourier]
    simp only [ContinuousMap.coe_mk]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [fixedShapeMixedKernel_coordinate_coeff t k hscale i]
  have hsum :
      (∑ n ∈ Fintype.piFinset
        (fun i : Fin d => Finset.Icc (-((2 : ℤ) ^ (t i + 1)))
          ((2 : ℤ) ^ (t i + 1))),
        fixedShapeMixedSymbol t k n * UnitAddTorus.mFourier n x) =
      ∑ n ∈ Fintype.piFinset
        (fun i : Fin d => Finset.Icc (-((2 : ℤ) ^ (t i + 1)))
          ((2 : ℤ) ^ (t i + 1))),
        ∏ i : Fin d,
          (fourierCoeff (fixedShapeMixedKernel t k i) (n i) * fourier (n i) (x i)) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact hterm n
  have hkernel (i : Fin d) (y : UnitAddCircle) :
      fixedShapeMixedKernel t k i y =
        ∑ m ∈ ScalarAtomVariance.scalarFrequencyBox (t i),
          (if k i = 0 then (scalarBlock (t i) (m : ℝ) : ℂ)
            else inverseMultiplier (t i) (k i) m) * fourier m y := by
    rcases hscale i with hk | ⟨hti, hki, heven⟩
    · simp [fixedShapeMixedKernel, hk, ScalarKernelL1.scalarBlockKernel,
        ScalarKernelL1.polynomialKernel]
    · have hk0 : k i ≠ 0 := by omega
      simp [fixedShapeMixedKernel, hk0, inverseMultiplierKernel,
        ScalarKernelL1.polynomialKernel]
  have hbox (i : Fin d) :
      ScalarAtomVariance.scalarFrequencyBox (t i) =
        Finset.Icc (-((2 : ℤ) ^ (t i + 1))) ((2 : ℤ) ^ (t i + 1)) := by rfl
  simp_rw [hbox] at hkernel
  simp_rw [hkernel]
  rw [Finset.prod_univ_sum
    (fun i : Fin d => Finset.Icc (-((2 : ℤ) ^ (t i + 1)))
      ((2 : ℤ) ^ (t i + 1)))
    (fun i m =>
      (if k i = 0 then (scalarBlock (t i) (m : ℝ) : ℂ)
        else inverseMultiplier (t i) (k i) m) * fourier m (x i))]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    ∏ i : Fin d,
        (if k i = 0 then (scalarBlock (t i) (n i : ℝ) : ℂ)
          else inverseMultiplier (t i) (k i) (n i)) * fourier (n i) (x i) =
      ∏ i : Fin d,
        fourierCoeff (fixedShapeMixedKernel t k i) (n i) * fourier (n i) (x i) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [fixedShapeMixedKernel_coordinate_coeff t k hscale i]
    _ = fixedShapeMixedSymbol t k n * UnitAddTorus.mFourier n x := (hterm n).symm

private theorem mFourier_sub_mul_fixed {d : ℕ} (n : Fin d → ℤ)
    (x y : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier n (x-y) =
      UnitAddTorus.mFourier n x * UnitAddTorus.mFourier (-n) y := by
  classical
  have hcoord : ∀ i : Fin d,
      fourier (n i) ((x-y) i) = fourier (n i) (x i) * fourier (-n i) (y i) := by
    intro i
    simp [sub_eq_add_neg, fourier_apply, zsmul_add, AddCircle.toCircle_add]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.prod_mul_distrib]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact hcoord i

private theorem integrable_mixed_term {d : ℕ} (s t k : Fin d → ℕ)
    (c : DyadicShapeCell d s → ℝ) (n : Fin d → ℤ)
    (x : UnitAddTorus (Fin d)) :
    Integrable (fun y : UnitAddTorus (Fin d) =>
      (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
        ((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ))
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  have hc : Continuous (fun y : UnitAddTorus (Fin d) =>
      (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
        ((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ)) := by fun_prop
  have hbound : ∀ y, ‖(fixedShapeMixedSymbol t k n •
        UnitAddTorus.mFourier n (x-y)) *
        ((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ)‖ ≤
      ‖fixedShapeMixedSymbol t k n‖ * ‖fixedShapeDerivativeSynthesis s k c‖ := by
    intro y
    rw [norm_mul, norm_smul]
    have hm : ‖UnitAddTorus.mFourier n (x-y)‖ ≤ 1 := by
      calc
        ‖UnitAddTorus.mFourier n (x-y)‖ ≤ ‖UnitAddTorus.mFourier n‖ :=
          (UnitAddTorus.mFourier n).norm_coe_le_norm _
        _ = 1 := UnitAddTorus.mFourier_norm
    have hf : ‖((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ)‖ ≤
        ‖fixedShapeDerivativeSynthesis s k c‖ := by
      simpa using (fixedShapeDerivativeSynthesis s k c).norm_coe_le_norm y
    calc
      ‖fixedShapeMixedSymbol t k n‖ * ‖UnitAddTorus.mFourier n (x-y)‖ *
          ‖((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ)‖ ≤
        ‖fixedShapeMixedSymbol t k n‖ * 1 *
          ‖fixedShapeDerivativeSynthesis s k c‖ := by gcongr
      _ = _ := by ring
  exact Integrable.of_bound hc.aestronglyMeasurable
    (‖fixedShapeMixedSymbol t k n‖ * ‖fixedShapeDerivativeSynthesis s k c‖)
    (ae_of_all _ hbound)

/-- The actual smooth Fourier block of a fixed-shape synthesis is convolution
by the mixed kernel acting on the corresponding mixed-derivative synthesis.
The Fourier coefficient identity is the only multiplier input. -/
theorem fixedShapeBlock_eq_mixedKernel_integral {d : ℕ}
    (s t k : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i)))
    (x : UnitAddTorus (Fin d)) :
    block t (fixedShapeSynthesis s c) x =
      ∫ y : UnitAddTorus (Fin d),
        (∑ n ∈ frequencyBox t,
          (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
            ((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ))
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  classical
  unfold block torusFourierPolynomial realPeriodicFourierCoeff
    complexifyRealPeriodic UnitAddTorus.mFourierCoeff
  simp only [ContinuousMap.coe_sum, ContinuousMap.coe_smul, smul_eq_mul,
    Finset.sum_apply]
  calc
    _ = ∑ n ∈ frequencyBox t,
        (tensorMultiplier t n : ℂ) *
          UnitAddTorus.mFourierCoeff
            (complexifyRealPeriodic (fixedShapeSynthesis s c)) n *
          UnitAddTorus.mFourier n x := by rfl
    _ = ∑ n ∈ frequencyBox t,
        fixedShapeMixedSymbol t k n *
          UnitAddTorus.mFourierCoeff
            (complexifyRealPeriodic (fixedShapeDerivativeSynthesis s k c)) n *
          UnitAddTorus.mFourier n x := by
          apply Finset.sum_congr rfl
          intro n hn
          change (tensorMultiplier t n : ℂ) *
              realPeriodicFourierCoeff (fixedShapeSynthesis s c) n *
              UnitAddTorus.mFourier n x =
            fixedShapeMixedSymbol t k n *
              realPeriodicFourierCoeff (fixedShapeDerivativeSynthesis s k c) n *
              UnitAddTorus.mFourier n x
          rw [← fixedShapeMixed_fourierCoeff_identity s t k c n hscale]
    _ = ∑ n ∈ frequencyBox t,
        ∫ y : UnitAddTorus (Fin d),
          (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
            ((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hfun : (fun y : UnitAddTorus (Fin d) =>
                (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
                  ((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ)) =
              fun y => (fixedShapeMixedSymbol t k n * UnitAddTorus.mFourier n x) *
                (UnitAddTorus.mFourier (-n) y *
                  ((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ)) := by
                funext y
                rw [smul_eq_mul, mFourier_sub_mul_fixed]
                ring
            rw [hfun]
            change fixedShapeMixedSymbol t k n *
                UnitAddTorus.mFourierCoeff
                  (complexifyRealPeriodic (fixedShapeDerivativeSynthesis s k c)) n *
                UnitAddTorus.mFourier n x = _
            rw [UnitAddTorus.mFourierCoeff]
            simp only [complexifyRealPeriodic, smul_eq_mul]
            calc
              fixedShapeMixedSymbol t k n *
                  (∫ y : UnitAddTorus (Fin d),
                    UnitAddTorus.mFourier (-n) y *
                      ((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ)
                    ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) *
                  UnitAddTorus.mFourier n x =
                (fixedShapeMixedSymbol t k n * UnitAddTorus.mFourier n x) *
                  ∫ y : UnitAddTorus (Fin d),
                    UnitAddTorus.mFourier (-n) y *
                      ((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ)
                    ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by ring
              _ = ∫ y : UnitAddTorus (Fin d),
                  (fixedShapeMixedSymbol t k n * UnitAddTorus.mFourier n x) *
                    (UnitAddTorus.mFourier (-n) y *
                      ((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ))
                  ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
                    rw [integral_const_mul]
    _ = ∫ y : UnitAddTorus (Fin d),
        ∑ n ∈ frequencyBox t,
          (fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) *
            ((fixedShapeDerivativeSynthesis s k c y : ℝ) : ℂ)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
          symm
          apply integral_finsetSum
          intro n hn
          exact integrable_mixed_term s t k c n x

/-- Finite-p block bound for a fixed rectangular synthesis, with the shape
parameter kept distinct from the output block parameter. All scale losses are
explicit; the derivative and one-dimensional kernel budgets are hypotheses. -/
theorem fixedShapeBlock_rpow_integral_le_general {d : ℕ}
    (s t k : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (p : ℝ) (hp : 1 ≤ p)
    (hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i)))
    (L0 : ℝ) (hL0 : 0 ≤ L0)
    (hscalar : ∀ q : ℕ,
      (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel q x‖
        ∂AddCircle.haarAddCircle) ≤ L0)
    (Linverse : Fin d → ℝ) (hLinverse : ∀ i, 0 ≤ Linverse i)
    (hhigh : ∀ i, k i ≠ 0 → 0 < t i ∧ Even (k i) ∧
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel (t i) (k i) x‖
        ∂AddCircle.haarAddCircle) ≤ Linverse i)
    (C : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hderiv : ∀ i y, |iteratedDeriv (k i) smoothAtom y| ≤ C i) :
    (∫ x : UnitAddTorus (Fin d),
      ‖block t (fixedShapeSynthesis s c) x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∏ i : Fin d, if k i = 0 then L0 else Linverse i) ^ p *
        (∏ i : Fin d,
          (((2 : ℝ) ^ (s i))⁻¹ *
            (C i * (2 : ℝ) ^ (s i * k i)) ^ p)) *
        ∑ j : DyadicShapeCell d s, |c j| ^ p := by
  let K := coordinateProductKernel (fixedShapeMixedKernel t k)
  let u : C(UnitAddTorus (Fin d), ℂ) :=
    ⟨fun x => (fixedShapeDerivativeSynthesis s k c x : ℂ),
      Complex.continuous_ofReal.comp (fixedShapeDerivativeSynthesis s k c).continuous⟩
  have hYoung := unitAddTorus_complex_convolution_rpow_le K u p hp
  have hkernel := fixedShapeMixedKernel_eq_sum t k hscale
  have hkernelAt (x y : UnitAddTorus (Fin d)) :
      (∑ n ∈ frequencyBox t,
        fixedShapeMixedSymbol t k n • UnitAddTorus.mFourier n (x-y)) = K (x-y) := by
    have hh := congrArg (fun f : C(UnitAddTorus (Fin d), ℂ) => f (x-y)) hkernel
    simpa [K, fixedShapeMixedSumKernel, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply] using hh.symm
  have hconv (x : UnitAddTorus (Fin d)) :
      block t (fixedShapeSynthesis s c) x =
        ∫ y : UnitAddTorus (Fin d), K y * u (x-y)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
    rw [fixedShapeBlock_eq_mixedKernel_integral s t k c hscale x]
    let μ : Measure (UnitAddTorus (Fin d)) :=
      Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
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
      _ = ∫ y : UnitAddTorus (Fin d), K y * u (x-y)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by rfl
  calc
    (∫ x : UnitAddTorus (Fin d), ‖block t (fixedShapeSynthesis s c) x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∫ y : UnitAddTorus (Fin d), ‖K y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p *
        ∫ x : UnitAddTorus (Fin d),
          |fixedShapeDerivativeSynthesis s k c x| ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
            calc
              _ = ∫ x : UnitAddTorus (Fin d),
                    ‖∫ y : UnitAddTorus (Fin d),
                      K y * u (x-y)
                      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)‖ ^ p
                    ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
                      apply integral_congr_ae
                      filter_upwards [] with x
                      rw [hconv x]
              _ ≤ (∫ y : UnitAddTorus (Fin d), ‖K y‖
                    ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p *
                  ∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
                    ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := hYoung
              _ = _ := by
                    congr 1
                    apply integral_congr_ae
                    filter_upwards [] with x
                    simp [u, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ _ := by
      have hK : (∫ y : UnitAddTorus (Fin d), ‖K y‖
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
          ∏ i : Fin d, if k i = 0 then L0 else Linverse i := by
            simpa [K] using fixedShapeMixedKernel_integral_le t k L0 hL0 hscalar
              Linverse hLinverse hhigh
      have hD := fixedShapeDerivativeSynthesis_rpow_integral_le s k c p
        (by linarith : 0 < p) C hC hderiv
      have hKnonneg : 0 ≤ ∫ y : UnitAddTorus (Fin d), ‖K y‖
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) :=
            integral_nonneg (fun _ => norm_nonneg _)
      have hBnonneg : 0 ≤ ∏ i : Fin d, if k i = 0 then L0 else Linverse i :=
        Finset.prod_nonneg fun i hi => by
          split_ifs with h
          · exact hL0
          · exact hLinverse i
      have hpPow := (Real.rpow_le_rpow hKnonneg hK (by linarith : 0 ≤ p))
      have hDnonneg : 0 ≤
          ∫ x : UnitAddTorus (Fin d),
            |fixedShapeDerivativeSynthesis s k c x| ^ p
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) :=
        integral_nonneg (fun _ => Real.rpow_nonneg (abs_nonneg _) _)
      have hRnonneg : 0 ≤
          (∏ i : Fin d,
            (((2 : ℝ) ^ (s i))⁻¹ *
              (C i * (2 : ℝ) ^ (s i * k i)) ^ p)) *
            ∑ j : DyadicShapeCell d s, |c j| ^ p := by
        apply mul_nonneg
        · apply Finset.prod_nonneg
          intro i hi
          apply mul_nonneg
          · positivity
          · exact Real.rpow_nonneg (mul_nonneg (hC i) (by positivity)) _
        · exact Finset.sum_nonneg fun j hj => Real.rpow_nonneg (abs_nonneg _) _
      have hD' :
          ∫ x : UnitAddTorus (Fin d),
            |fixedShapeDerivativeSynthesis s k c x| ^ p
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) ≤
          (∏ i : Fin d,
            (((2 : ℝ) ^ (s i))⁻¹ *
              (C i * (2 : ℝ) ^ (s i * k i)) ^ p)) *
            ∑ j : DyadicShapeCell d s, |c j| ^ p := hD
      calc
        (∫ y : UnitAddTorus (Fin d), ‖K y‖
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p *
          ∫ x : UnitAddTorus (Fin d),
            |fixedShapeDerivativeSynthesis s k c x| ^ p
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) ≤
          (∏ i : Fin d, if k i = 0 then L0 else Linverse i) ^ p *
            ((∏ i : Fin d,
              (((2 : ℝ) ^ (s i))⁻¹ *
                (C i * (2 : ℝ) ^ (s i * k i)) ^ p)) *
              ∑ j : DyadicShapeCell d s, |c j| ^ p) := by
                exact mul_le_mul hpPow hD' hDnonneg
                  (Real.rpow_nonneg hBnonneg p)
        _ = _ := by ring

end BrownianSharp
