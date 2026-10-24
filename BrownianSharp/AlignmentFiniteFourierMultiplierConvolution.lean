import BrownianSharp.TorusComplexYoung
import BrownianSharp.TorusFoundations
import BrownianSharp.AtomicTensorSynthesisLp
import BrownianSharp.TensorBlockKernelLp
import BrownianSharp.InverseDerivativeProfileIdentity
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped BigOperators
open UnitAddTorus

namespace BrownianSharp.AlignmentFiniteFourierMultiplierConvolution

open BrownianSharp.Torus

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : Measure.IsNegInvariant (volume : Measure UnitAddCircle) := by
  infer_instance
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance (d : ℕ) : IsProbabilityMeasure
    (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
  infer_instance

local instance (d : ℕ) : Measure.IsAddHaarMeasure
    (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
  infer_instance

/-- The trigonometric-polynomial multiplier with finite frequency set `S`.
The formula uses the actual Fourier coefficients of a continuous real-valued
periodic input and has complex-valued output. -/
def finiteMultiplier {d : ℕ} (S : Finset (Fin d → ℤ))
    (a : (Fin d → ℤ) → ℂ) (f : RealPeriodic d) : C(UnitAddTorus (Fin d), ℂ) :=
  torusFourierPolynomial S (fun k => a k * realPeriodicFourierCoeff f k)

/-- The finite trigonometric kernel associated with a multiplier symbol. -/
def finiteKernel {d : ℕ} (S : Finset (Fin d → ℤ))
    (a : (Fin d → ℤ) → ℂ) : C(UnitAddTorus (Fin d), ℂ) :=
  torusFourierPolynomial S a

/-- The finite Fourier multiplier on complex continuous input. -/
def complexFiniteMultiplier {d : ℕ} (S : Finset (Fin d → ℤ))
    (a : (Fin d → ℤ) → ℂ) (f : C(UnitAddTorus (Fin d), ℂ)) :
    C(UnitAddTorus (Fin d), ℂ) :=
  torusFourierPolynomial S (fun k => a k * UnitAddTorus.mFourierCoeff f k)

private theorem mFourier_sub_mul {d : ℕ} (k : Fin d → ℤ)
    (x y : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier k (x-y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  classical
  have hcoord : ∀ i : Fin d,
      fourier (k i) ((x-y) i) = fourier (k i) (x i) * fourier (-k i) (y i) := by
    intro i
    simp [sub_eq_add_neg, fourier_apply, zsmul_add, AddCircle.toCircle_add]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.prod_mul_distrib]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact hcoord i

private theorem integrable_kernel_term {d : ℕ}
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (f : RealPeriodic d) (x : UnitAddTorus (Fin d)) (k : Fin d → ℤ) :
    Integrable (fun y : UnitAddTorus (Fin d) =>
      (a k • UnitAddTorus.mFourier k (x-y)) * (f y : ℂ))
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  have hc : Continuous (fun y : UnitAddTorus (Fin d) =>
      (a k • UnitAddTorus.mFourier k (x-y)) * (f y : ℂ)) := by fun_prop
  have hb : ∀ y, ‖(a k • UnitAddTorus.mFourier k (x-y)) * (f y : ℂ)‖ ≤
      ‖a k‖ * ‖f‖ := by
    intro y
    rw [norm_mul, norm_smul]
    have hm : ‖UnitAddTorus.mFourier k (x-y)‖ ≤ 1 := by
      calc
        ‖UnitAddTorus.mFourier k (x-y)‖ ≤ ‖UnitAddTorus.mFourier k‖ :=
          (UnitAddTorus.mFourier k).norm_coe_le_norm _
        _ = 1 := UnitAddTorus.mFourier_norm
    have hf : ‖(f y : ℂ)‖ ≤ ‖f‖ := by simpa using f.norm_coe_le_norm y
    calc
      ‖a k‖ * ‖UnitAddTorus.mFourier k (x-y)‖ * ‖(f y : ℂ)‖ ≤
          ‖a k‖ * 1 * ‖f‖ := by gcongr
      _ = ‖a k‖ * ‖f‖ := by ring
  exact Integrable.of_bound hc.aestronglyMeasurable (‖a k‖ * ‖f‖)
    (ae_of_all _ hb)

private theorem integrable_complex_kernel_term {d : ℕ}
    (a : (Fin d → ℤ) → ℂ) (f : C(UnitAddTorus (Fin d), ℂ))
    (x : UnitAddTorus (Fin d)) (k : Fin d → ℤ) :
    Integrable (fun y : UnitAddTorus (Fin d) =>
      (a k • UnitAddTorus.mFourier k (x-y)) * f y)
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  have hc : Continuous (fun y : UnitAddTorus (Fin d) =>
      (a k • UnitAddTorus.mFourier k (x-y)) * f y) := by fun_prop
  have hb : ∀ y, ‖(a k • UnitAddTorus.mFourier k (x-y)) * f y‖ ≤
      ‖a k‖ * ‖f‖ := by
    intro y
    rw [norm_mul, norm_smul]
    have hm : ‖UnitAddTorus.mFourier k (x-y)‖ ≤ 1 := by
      calc
        ‖UnitAddTorus.mFourier k (x-y)‖ ≤ ‖UnitAddTorus.mFourier k‖ :=
          (UnitAddTorus.mFourier k).norm_coe_le_norm _
        _ = 1 := UnitAddTorus.mFourier_norm
    have hf : ‖f y‖ ≤ ‖f‖ := f.norm_coe_le_norm y
    calc
      ‖a k‖ * ‖UnitAddTorus.mFourier k (x-y)‖ * ‖f y‖ ≤
          ‖a k‖ * 1 * ‖f‖ := by gcongr
      _ = ‖a k‖ * ‖f‖ := by ring
  exact Integrable.of_bound hc.aestronglyMeasurable (‖a k‖ * ‖f‖)
    (ae_of_all _ hb)

/-- Young's inequality for any continuous complex-valued torus operator once
its actual output is identified pointwise with convolution by `K`.  This is
the reusable interface for kernels not defined using `finiteKernel`. -/
theorem convolution_Lp_bound_of_eq {d : ℕ}
    (K f g : C(UnitAddTorus (Fin d), ℂ)) (p : ℝ) (hp : 1 ≤ p)
    (hconv : ∀ x : UnitAddTorus (Fin d),
      g x = ∫ y : UnitAddTorus (Fin d), K y * f (x-y)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) :
    (∫ x : UnitAddTorus (Fin d), ‖g x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∫ y : UnitAddTorus (Fin d), ‖K y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p *
      (∫ x : UnitAddTorus (Fin d), ‖f x‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) := by
  have hyoung := unitAddTorus_complex_convolution_rpow_le K f p hp
  calc
    (∫ x : UnitAddTorus (Fin d), ‖g x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
        ∫ x : UnitAddTorus (Fin d),
          ‖∫ y : UnitAddTorus (Fin d), K y * f (x-y)
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
            congr 1
            funext x
            rw [hconv x]
    _ ≤ (∫ y : UnitAddTorus (Fin d), ‖K y‖
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p *
        (∫ x : UnitAddTorus (Fin d), ‖f x‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) := hyoung

/-- The endpoint (`L∞`) Young estimate, in pointwise supremum-norm form. -/
theorem convolution_sup_bound_of_eq {d : ℕ}
    (K f g : C(UnitAddTorus (Fin d), ℂ))
    (hconv : ∀ x : UnitAddTorus (Fin d),
      g x = ∫ y : UnitAddTorus (Fin d), K y * f (x-y)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) :
    ∀ x, ‖g x‖ ≤
      (∫ y : UnitAddTorus (Fin d), ‖K y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) * ‖f‖ := by
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  intro x
  have hKint : Integrable (fun y : UnitAddTorus (Fin d) => ‖K y‖) μ := by
    apply Integrable.of_bound K.continuous.norm.aestronglyMeasurable ‖K‖
    filter_upwards [] with y
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
      K.norm_coe_le_norm y
  have hint : Integrable (fun y : UnitAddTorus (Fin d) => K y * f (x-y)) μ := by
    apply Integrable.of_bound
      (K.continuous.mul (f.continuous.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
      (‖K‖ * ‖f‖)
    filter_upwards [] with y
    change ‖K y * f (x-y)‖ ≤ ‖K‖ * ‖f‖
    rw [norm_mul]
    calc
      ‖K y‖ * ‖f (x-y)‖ ≤ ‖K y‖ * ‖f‖ :=
        mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)
      _ ≤ ‖K‖ * ‖f‖ :=
        mul_le_mul_of_nonneg_right (K.norm_coe_le_norm _) (norm_nonneg _)
  have hnorm := norm_integral_le_integral_norm (μ := μ)
    (fun y : UnitAddTorus (Fin d) => K y * f (x-y))
  calc
    ‖g x‖ = ‖∫ y : UnitAddTorus (Fin d), K y * f (x-y) ∂μ‖ := by
      rw [hconv x]
    _ ≤ ∫ y : UnitAddTorus (Fin d), ‖K y * f (x-y)‖ ∂μ := hnorm
    _ ≤ ∫ y : UnitAddTorus (Fin d), ‖K y‖ * ‖f‖ ∂μ := by
      apply integral_mono_ae hint.norm (hKint.mul_const ‖f‖)
      filter_upwards [] with y
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (norm_nonneg _)
    _ = (∫ y : UnitAddTorus (Fin d), ‖K y‖ ∂μ) * ‖f‖ := by
      rw [integral_mul_const]
    _ = (∫ y : UnitAddTorus (Fin d), ‖K y‖
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) * ‖f‖ := rfl

/-- Every finite Fourier multiplier is convolution by its finite kernel.
The Haar measure is the normalized product Haar measure on the finite torus. -/
theorem finiteMultiplier_eq_kernel_convolution {d : ℕ}
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (f : RealPeriodic d) (x : UnitAddTorus (Fin d)) :
    finiteMultiplier S a f x =
      ∫ y : UnitAddTorus (Fin d),
        finiteKernel S a y * (f (x-y) : ℂ)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  classical
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  have hsub : MeasurePreserving (fun y : UnitAddTorus (Fin d) => x-y) μ μ := by
    letI : Measure.IsAddLeftInvariant μ := inferInstance
    have hneg : MeasurePreserving (fun y : UnitAddTorus (Fin d) => -y) μ μ := by
      change MeasurePreserving (fun y : (Fin d → UnitAddCircle) => -y)
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
      exact measurePreserving_pi
        (fun _ : Fin d => AddCircle.haarAddCircle)
        (fun _ : Fin d => AddCircle.haarAddCircle)
        (fun i : Fin d => Measure.measurePreserving_neg AddCircle.haarAddCircle)
    have hadd : MeasurePreserving (fun y : UnitAddTorus (Fin d) => x+y) μ μ :=
      measurePreserving_add_left μ x
    convert hadd.comp hneg using 1 <;> ext y <;> simp [sub_eq_add_neg]
  calc
    finiteMultiplier S a f x =
        ∑ k ∈ S, a k * realPeriodicFourierCoeff f k * UnitAddTorus.mFourier k x := by
          simp [finiteMultiplier, finiteKernel, torusFourierPolynomial,
            realPeriodicFourierCoeff, complexifyRealPeriodic,
            UnitAddTorus.mFourierCoeff, smul_eq_mul]
    _ = ∑ k ∈ S, ∫ y : UnitAddTorus (Fin d),
        (a k • UnitAddTorus.mFourier k (x-y)) * (f y : ℂ) ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show (fun y : UnitAddTorus (Fin d) =>
          (a k • UnitAddTorus.mFourier k (x-y)) * (f y : ℂ)) =
        fun y => (a k * UnitAddTorus.mFourier k x) *
          (UnitAddTorus.mFourier (-k) y * (f y : ℂ)) by
        funext y
        rw [smul_eq_mul, mFourier_sub_mul]
        ring]
      change a k * UnitAddTorus.mFourierCoeff (complexifyRealPeriodic f) k *
        UnitAddTorus.mFourier k x = _
      rw [UnitAddTorus.mFourierCoeff]
      simp only [complexifyRealPeriodic, smul_eq_mul]
      calc
        a k * (∫ y, UnitAddTorus.mFourier (-k) y * (f y : ℂ) ∂μ) *
            UnitAddTorus.mFourier k x =
            (a k * UnitAddTorus.mFourier k x) *
              (∫ y, UnitAddTorus.mFourier (-k) y * (f y : ℂ) ∂μ) := by ring
        _ = ∫ y, (a k * UnitAddTorus.mFourier k x) *
              (UnitAddTorus.mFourier (-k) y * (f y : ℂ)) ∂μ := by
            rw [integral_const_mul]
    _ = ∫ y : UnitAddTorus (Fin d),
        (∑ k ∈ S, (a k • UnitAddTorus.mFourier k (x-y)) * (f y : ℂ)) ∂μ := by
      symm
      apply integral_finsetSum
      intro k hk
      exact integrable_kernel_term S a f x k
    _ = ∫ y : UnitAddTorus (Fin d),
        finiteKernel S a (x-y) * (f y : ℂ) ∂μ := by
      congr 1
      funext y
      simp [finiteKernel, torusFourierPolynomial, ContinuousMap.sum_apply,
        ContinuousMap.smul_apply, smul_eq_mul, Finset.sum_mul]
    _ = ∫ y : UnitAddTorus (Fin d),
        finiteKernel S a y * (f (x-y) : ℂ) ∂μ := by
      simpa [sub_sub_cancel] using
        hsub.integral_comp (Homeomorph.subLeft x).measurableEmbedding
          (fun y => finiteKernel S a y * (f (x-y) : ℂ))

/-- The complex-input analogue of `finiteMultiplier_eq_kernel_convolution`.
The returned polynomial has Fourier coefficients equal to the symbol times
the input Fourier coefficients; this is the interface for composing smooth
cutoff blocks. -/
theorem complexFiniteMultiplier_eq_kernel_convolution {d : ℕ}
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (f : C(UnitAddTorus (Fin d), ℂ)) (x : UnitAddTorus (Fin d)) :
    complexFiniteMultiplier S a f x =
      ∫ y : UnitAddTorus (Fin d),
        finiteKernel S a y * f (x-y)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  classical
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  have hsub : MeasurePreserving (fun y : UnitAddTorus (Fin d) => x-y) μ μ := by
    letI : Measure.IsAddLeftInvariant μ := inferInstance
    have hneg : MeasurePreserving (fun y : UnitAddTorus (Fin d) => -y) μ μ := by
      change MeasurePreserving (fun y : (Fin d → UnitAddCircle) => -y)
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
      exact measurePreserving_pi
        (fun _ : Fin d => AddCircle.haarAddCircle)
        (fun _ : Fin d => AddCircle.haarAddCircle)
        (fun i : Fin d => Measure.measurePreserving_neg AddCircle.haarAddCircle)
    have hadd : MeasurePreserving (fun y : UnitAddTorus (Fin d) => x+y) μ μ :=
      measurePreserving_add_left μ x
    convert hadd.comp hneg using 1 <;> ext y <;> simp [sub_eq_add_neg]
  calc
    complexFiniteMultiplier S a f x =
        ∑ k ∈ S, a k * UnitAddTorus.mFourierCoeff f k *
          UnitAddTorus.mFourier k x := by
          simp [complexFiniteMultiplier, torusFourierPolynomial,
            ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
    _ = ∑ k ∈ S, ∫ y : UnitAddTorus (Fin d),
        (a k • UnitAddTorus.mFourier k (x-y)) * f y ∂μ := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [show (fun y : UnitAddTorus (Fin d) =>
          (a k • UnitAddTorus.mFourier k (x-y)) * f y) =
        fun y => (a k * UnitAddTorus.mFourier k x) *
          (UnitAddTorus.mFourier (-k) y * f y) by
        funext y
        rw [smul_eq_mul, mFourier_sub_mul]
        ring]
      change a k * UnitAddTorus.mFourierCoeff f k *
        UnitAddTorus.mFourier k x = _
      rw [UnitAddTorus.mFourierCoeff]
      simp only [smul_eq_mul]
      calc
        a k * (∫ y, UnitAddTorus.mFourier (-k) y * f y ∂μ) *
            UnitAddTorus.mFourier k x =
            (a k * UnitAddTorus.mFourier k x) *
              (∫ y, UnitAddTorus.mFourier (-k) y * f y ∂μ) := by ring
        _ = ∫ y, (a k * UnitAddTorus.mFourier k x) *
              (UnitAddTorus.mFourier (-k) y * f y) ∂μ := by
            rw [integral_const_mul]
    _ = ∫ y : UnitAddTorus (Fin d),
        (∑ k ∈ S, (a k • UnitAddTorus.mFourier k (x-y)) * f y) ∂μ := by
      symm
      apply integral_finsetSum
      intro k hk
      exact integrable_complex_kernel_term a f x k
    _ = ∫ y : UnitAddTorus (Fin d),
        finiteKernel S a (x-y) * f y ∂μ := by
      congr 1
      funext y
      simp [finiteKernel, torusFourierPolynomial, ContinuousMap.sum_apply,
        ContinuousMap.smul_apply, smul_eq_mul, Finset.sum_mul]
    _ = ∫ y : UnitAddTorus (Fin d),
        finiteKernel S a y * f (x-y) ∂μ := by
      simpa [sub_sub_cancel] using
        hsub.integral_comp (Homeomorph.subLeft x).measurableEmbedding
          (fun y => finiteKernel S a y * f (x-y))

/-- The actual finite multiplier obeys the usual Young estimate in every
finite `Lᵖ`, for every continuous real-periodic input. -/
theorem finiteMultiplier_Lp_bound {d : ℕ}
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (f : RealPeriodic d) (p : ℝ) (hp : 1 ≤ p) :
    (∫ x : UnitAddTorus (Fin d), ‖finiteMultiplier S a f x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∫ x : UnitAddTorus (Fin d), ‖finiteKernel S a x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p *
      (∫ x : UnitAddTorus (Fin d), ‖(f x : ℂ)‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) := by
  let u : C(UnitAddTorus (Fin d), ℂ) :=
    ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  let K := finiteKernel S a
  have hconv := finiteMultiplier_eq_kernel_convolution S a f
  have hyoung := unitAddTorus_complex_convolution_rpow_le K u p hp
  have hfun : (fun x : UnitAddTorus (Fin d) =>
      ‖finiteMultiplier S a f x‖ ^ p) =
      (fun x => ‖∫ y : UnitAddTorus (Fin d), K y * u (x-y)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)‖ ^ p) := by
    funext x
    rw [hconv x]
    simp [K, u]
  simpa [K, u, hfun] using hyoung

end BrownianSharp.AlignmentFiniteFourierMultiplierConvolution
