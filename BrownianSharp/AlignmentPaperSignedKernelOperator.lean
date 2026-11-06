import BrownianSharp.AlignmentPaperSignedKernelL2
import BrownianSharp.AlignmentPaperKernelHörmander
import BrownianSharp.AlignmentPaperWeakStrongOperator
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperSignedKernelOperator

open BrownianSharp.AlignmentPaperSignedKernelL2
open BrownianSharp.AlignmentPaperWeakStrongOperator
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel
open BrownianSharp.Torus

local instance circleMeasureSpace_operator : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance circleProbability_operator : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance circleNegInvariant_operator : Measure.IsNegInvariant
    (AddCircle.haarAddCircle : Measure UnitAddCircle) := by infer_instance
local instance oneTorusMeasureSpace_operator :
    MeasureSpace (UnitAddTorus (Fin 1)) :=
  ⟨Measure.pi fun _ : Fin 1 => AddCircle.haarAddCircle⟩
local instance oneTorusProbability_operator : IsProbabilityMeasure
    (volume : Measure (UnitAddTorus (Fin 1))) := by
  change IsProbabilityMeasure
    (Measure.pi fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
  infer_instance
local instance oneTorusHaar_operator : Measure.IsAddHaarMeasure
    (volume : Measure (UnitAddTorus (Fin 1))) := by
  change Measure.IsAddHaarMeasure
    (Measure.pi fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
  infer_instance
local instance oneTorusNegInvariant_operator : Measure.IsNegInvariant
    (volume : Measure (UnitAddTorus (Fin 1))) := by
  change Measure.IsNegInvariant
    (Measure.pi fun _ : Fin 1 => (AddCircle.haarAddCircle : Measure UnitAddCircle))
  infer_instance

/-- The actual scalar signed kernel on the period-one circle. -/
def circleSignedKernel (N : ℕ) (ε : Fin (N+1) → ℝ) : C(UnitAddCircle, ℂ) :=
  ∑ s : Fin (N+1), (ε s : ℂ) • scalarBlockKernel smoothResolutionCutoff s.val

/-- The full Circle convolution operator used by the weak-(1,1) argument. -/
def circleSignedConvolutionOperator (N : ℕ) (ε : Fin (N+1) → ℝ)
    (f : UnitAddCircle → ℂ) (x : UnitAddCircle) : ℂ :=
  ∫ y : UnitAddCircle, circleSignedKernel N ε (x-y) * f y
    ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)

lemma circleSignedKernel_continuous (N : ℕ) (ε : Fin (N+1) → ℝ) :
    Continuous (circleSignedKernel N ε : UnitAddCircle → ℂ) :=
  (circleSignedKernel N ε).continuous

lemma circleSignedKernel_bdd (N : ℕ) (ε : Fin (N+1) → ℝ) :
    BddAbove (Set.range fun x : UnitAddCircle => ‖circleSignedKernel N ε x‖) := by
  have hcompact : IsCompact
      ((fun x : UnitAddCircle => ‖circleSignedKernel N ε x‖) '' Set.univ) :=
    isCompact_univ.image (circleSignedKernel_continuous N ε).norm
  rw [← Set.image_univ]
  exact hcompact.bddAbove

private def circleToOneTorus (x : UnitAddCircle) : UnitAddTorus (Fin 1) :=
  fun _ => x

lemma signedDyadicKernel_eval_circle (N : ℕ) (ε : Fin (N+1) → ℝ)
    (x : UnitAddCircle) :
    signedDyadicKernel N ε (circleToOneTorus x) = circleSignedKernel N ε x := by
  dsimp [signedDyadicKernel]
  rw [circleSignedKernel]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [smul_eq_mul, admissibleBlockKernel_eq_product,
    admissibleBlockKernelProduct, BrownianSharp.coordinateProductKernel]
  congr 1
  change (∏ i : Fin 1, scalarBlockKernel smoothResolutionCutoff s.val x) = _
  simp

lemma circleSignedConvolutionOperator_integrand_integrable
    (N : ℕ) (ε : Fin (N+1) → ℝ) {f : UnitAddCircle → ℂ}
    (hf : Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (x : UnitAddCircle) :
    Integrable (fun y : UnitAddCircle => circleSignedKernel N ε (x-y) * f y)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  rcases circleSignedKernel_bdd N ε with ⟨M,hM⟩
  apply hf.bdd_mul (by fun_prop)
  filter_upwards with y
  exact hM ⟨x-y, rfl⟩

lemma circleSignedConvolutionOperator_add_eq
    (N : ℕ) (ε : Fin (N+1) → ℝ) {f g : UnitAddCircle → ℂ}
    (hf : Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (hg : Integrable g (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    circleSignedConvolutionOperator N ε (f+g) =
      circleSignedConvolutionOperator N ε f + circleSignedConvolutionOperator N ε g := by
  funext x
  change (∫ y : UnitAddCircle,
      circleSignedKernel N ε (x-y) * (f y + g y)
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) =
    (∫ y : UnitAddCircle, circleSignedKernel N ε (x-y) * f y
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) +
    (∫ y : UnitAddCircle, circleSignedKernel N ε (x-y) * g y
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
  rw [← integral_add
    (circleSignedConvolutionOperator_integrand_integrable N ε hf x)
    (circleSignedConvolutionOperator_integrand_integrable N ε hg x)]
  apply integral_congr_ae
  filter_upwards with y
  ring

lemma circleSignedConvolutionOperator_continuous
    (N : ℕ) (ε : Fin (N+1) → ℝ) {f : UnitAddCircle → ℂ}
    (hf : Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    Continuous (circleSignedConvolutionOperator N ε f) := by
  have hconv : Continuous (MeasureTheory.convolution f
      (circleSignedKernel N ε) (ContinuousLinearMap.mul ℂ ℂ)
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
    exact BddAbove.continuous_convolution_right_of_integrable
      (ContinuousLinearMap.mul ℂ ℂ) (circleSignedKernel_bdd N ε) hf
      (circleSignedKernel_continuous N ε)
  apply hconv.congr
  intro x
  simp only [MeasureTheory.convolution, circleSignedConvolutionOperator]
  congr 1
  ext y
  exact mul_comm _ _

private def oneTorusCircleEquiv :
    MeasurableEquiv (UnitAddTorus (Fin 1)) UnitAddCircle :=
  MeasurableEquiv.piUnique (fun _ : Fin 1 => UnitAddCircle)

private theorem oneTorusCircle_measurePreserving :
    MeasurePreserving oneTorusCircleEquiv
      (volume : Measure (UnitAddTorus (Fin 1)))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  exact measurePreserving_piUnique (fun _ : Fin 1 =>
    (AddCircle.haarAddCircle : Measure UnitAddCircle))

private lemma oneTorusCircleEquiv_sub (x : UnitAddCircle)
    (y : UnitAddTorus (Fin 1)) :
    oneTorusCircleEquiv (oneTorusCircleEquiv.symm x-y) = x-oneTorusCircleEquiv y := by
  simp [oneTorusCircleEquiv, MeasurableEquiv.piUnique]

private lemma oneTorusCircleEquiv_kernel (N : ℕ) (ε : Fin (N+1) → ℝ)
    (y : UnitAddTorus (Fin 1)) :
    signedDyadicKernel N ε y = circleSignedKernel N ε (oneTorusCircleEquiv y) := by
  rw [← signedDyadicKernel_eval_circle N ε (oneTorusCircleEquiv y)]
  congr 1
  funext i
  fin_cases i
  rfl

private lemma circleSignedConvolution_eq_torus
    (N : ℕ) (ε : Fin (N+1) → ℝ) {f : UnitAddCircle → ℂ}
    (hf : MemLp f (2 : ℝ≥0∞) (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (x : UnitAddCircle) :
    circleSignedConvolutionOperator N ε f x =
      signedDyadicConvolutionFunction N ε
        ((hf.comp_measurePreserving oneTorusCircle_measurePreserving).toLp
          (f ∘ oneTorusCircleEquiv)) (oneTorusCircleEquiv.symm x) := by
  let xt := oneTorusCircleEquiv.symm x
  let gLp := (hf.comp_measurePreserving oneTorusCircle_measurePreserving).toLp
    (f ∘ oneTorusCircleEquiv)
  have hrep : gLp =ᵐ[volume] f ∘ oneTorusCircleEquiv :=
    (hf.comp_measurePreserving oneTorusCircle_measurePreserving).coeFn_toLp
  have hshift := (volume.measurePreserving_sub_left xt).quasiMeasurePreserving.ae_eq_comp
    hrep
  change (∫ y : UnitAddCircle, circleSignedKernel N ε (x-y) * f y
      ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) =
    ∫ y : UnitAddTorus (Fin 1), signedDyadicKernel N ε y * gLp (xt-y) ∂volume
  have hcircle : ∫ z : UnitAddCircle,
      circleSignedKernel N ε z * f (x-z)
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) =
      ∫ z : UnitAddCircle, circleSignedKernel N ε (x-z) * f z
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    have hh := integral_sub_left_eq_self
      (fun z : UnitAddCircle => circleSignedKernel N ε z * f (x-z))
      (AddCircle.haarAddCircle : Measure UnitAddCircle) x
    simpa [sub_sub_cancel_left, mul_comm] using hh.symm
  rw [← hcircle]
  rw [← oneTorusCircle_measurePreserving.integral_comp'
    (fun z : UnitAddCircle => circleSignedKernel N ε z * f (x-z))]
  apply integral_congr_ae
  filter_upwards [hshift] with y hy
  rw [oneTorusCircleEquiv_kernel]
  have hsub : oneTorusCircleEquiv (xt-y) = x-oneTorusCircleEquiv y := by
    simpa [xt] using oneTorusCircleEquiv_sub x y
  have hy' : f (x-oneTorusCircleEquiv y) = gLp (xt-y) := by
    simpa [Function.comp_apply, hsub] using hy.symm
  exact congrArg (fun v : ℂ => circleSignedKernel N ε (oneTorusCircleEquiv y) * v) hy'

theorem circleSignedConvolutionOperator_lintegral_sq_le
    (N : ℕ) (ε : Fin (N+1) → ℝ) (hε : ∀ s, |ε s| ≤ 1)
    {f : UnitAddCircle → ℂ}
    (hf : MemLp f (2 : ℝ≥0∞) (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    ∫⁻ x : UnitAddCircle,
      ENNReal.ofReal (‖circleSignedConvolutionOperator N ε f x‖^2)
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) ≤
      ∫⁻ x : UnitAddCircle, ENNReal.ofReal (‖f x‖^2)
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  let mp := oneTorusCircle_measurePreserving
  let gLp := (hf.comp_measurePreserving mp).toLp (f ∘ oneTorusCircleEquiv)
  have hrep : gLp =ᵐ[volume] f ∘ oneTorusCircleEquiv :=
    (hf.comp_measurePreserving mp).coeFn_toLp
  have hop (x : UnitAddCircle) := circleSignedConvolution_eq_torus N ε hf x
  have htorus := signedDyadicConvolution_lintegral_sq_le N ε hε gLp
  have hleft :
      ∫⁻ x : UnitAddCircle,
        ENNReal.ofReal (‖circleSignedConvolutionOperator N ε f x‖^2)
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) =
      ∫⁻ x : UnitAddTorus (Fin 1),
        ENNReal.ofReal (‖signedDyadicConvolutionFunction N ε gLp x‖^2) ∂volume := by
    rw [← mp.lintegral_comp_emb oneTorusCircleEquiv.measurableEmbedding]
    refine lintegral_congr_ae ?_
    filter_upwards with y
    have hh := hop (oneTorusCircleEquiv y)
    rw [MeasurableEquiv.symm_apply_apply] at hh
    rw [← hh]
  have hright :
      ∫⁻ x : UnitAddTorus (Fin 1), ENNReal.ofReal (‖gLp x‖^2) ∂volume =
      ∫⁻ x : UnitAddCircle, ENNReal.ofReal (‖f x‖^2)
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    rw [← mp.lintegral_comp_emb oneTorusCircleEquiv.measurableEmbedding]
    refine lintegral_congr_ae ?_
    filter_upwards [hrep] with x hx
    rw [hx]
    rfl
  calc
    _ = ∫⁻ x : UnitAddTorus (Fin 1),
        ENNReal.ofReal (‖signedDyadicConvolutionFunction N ε gLp x‖^2) ∂volume := hleft
    _ ≤ ∫⁻ x : UnitAddTorus (Fin 1), ENNReal.ofReal (‖gLp x‖^2) ∂volume := htorus
    _ = _ := hright

/-- Actual strong-Lp moment bound for the finite signed smooth dyadic
convolution, once its weak-(1,1) estimate is supplied. The operator,
additivity, measurability, and strong-(2,2) inputs are the concrete Circle
operator proved in this module. -/
theorem circleSignedConvolutionOperator_lintegral_lp_le_of_weak_one
    (N : ℕ) (ε : Fin (N+1) → ℝ) (hε : ∀ s, |ε s| ≤ 1)
    {C₁ p : ℝ} (hC₁ : 0 ≤ C₁) (hp1 : 1 < p) (hp2 : p < 2)
    (hweak : ∀ f, Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle) →
      ∀ t > 0,
        (AddCircle.haarAddCircle : Measure UnitAddCircle)
            {y | t < ‖circleSignedConvolutionOperator N ε f y‖} ≤
          ENNReal.ofReal (C₁/t) *
            ∫⁻ x, ENNReal.ofReal (‖f x‖)
              ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
    (f : Lp ℂ (ENNReal.ofReal p)
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    ∫⁻ y : UnitAddCircle,
      ENNReal.ofReal (‖circleSignedConvolutionOperator N ε f y‖^p)
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) ≤
      ENNReal.ofReal ((2:ℝ)^p *
        (p*C₁/(p-1)+p/(2-p))) *
        ∫⁻ x : UnitAddCircle, ENNReal.ofReal (‖f x‖^p)
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  have hadd : ∀ g h, Integrable g (AddCircle.haarAddCircle : Measure UnitAddCircle) →
      Integrable h (AddCircle.haarAddCircle : Measure UnitAddCircle) →
      circleSignedConvolutionOperator N ε (g+h) =
        circleSignedConvolutionOperator N ε g + circleSignedConvolutionOperator N ε h := by
    intro g h hg hh
    exact circleSignedConvolutionOperator_add_eq N ε hg hh
  have hmeas : ∀ g, Integrable g (AddCircle.haarAddCircle : Measure UnitAddCircle) →
      AEStronglyMeasurable (circleSignedConvolutionOperator N ε g)
        (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    intro g hg
    exact (circleSignedConvolutionOperator_continuous N ε hg).aestronglyMeasurable
  simpa [mul_one] using lintegral_lp_output_le_of_weak_one_strong_two
    (AddCircle.haarAddCircle : Measure UnitAddCircle)
    (AddCircle.haarAddCircle : Measure UnitAddCircle)
    (circleSignedConvolutionOperator N ε) hadd hmeas (C₂ := (1 : ℝ))
    hC₁ (by norm_num) hp1 hp2 hweak
    (by
      intro g hg
      have hh := circleSignedConvolutionOperator_lintegral_sq_le N ε hε hg
      simpa [ENNReal.ofReal_pow] using hh)
    f

end BrownianSharp.AlignmentPaperSignedKernelOperator
