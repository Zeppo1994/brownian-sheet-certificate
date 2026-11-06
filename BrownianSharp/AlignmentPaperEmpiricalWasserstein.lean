import BrownianSharp.AlignmentPaperQuantization
import BrownianSharp.AlignmentPaperFiniteEmpiricalCoupling
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Empirical Wasserstein upper-bound ingredients

The sample law and empirical measure in this file are the actual i.i.d.
sample law and equal-weight Dirac empirical law. The small-ball-profile
estimate is proved separately; no Wasserstein bound is assumed here.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperEmpiricalWasserstein

open BrownianSharp
open BrownianSharp.AlignmentPaperFiniteEmpiricalCoupling

/-- Product law of `m` independent samples with common law `μ`. -/
def iidSampleLaw {X : Type*} [MeasurableSpace X] (μ : Measure X) (m : ℕ) :
    Measure (Fin m → X) :=
  Measure.pi fun _ : Fin m => μ

theorem iidSampleLaw_isProbability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (m : ℕ) :
    IsProbabilityMeasure (iidSampleLaw μ m) := by
  dsimp [iidSampleLaw]
  infer_instance

/-- Expected W₂ error of the actual empirical measure based on `m` i.i.d.
samples. The empirical law is not replaced by a deterministic codebook. -/
noncomputable def expectedEmpiricalWassersteinTwo
    {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X]
    (μ : Measure X) (m : ℕ) (hm : 0 < m) : ℝ≥0∞ :=
  ∫⁻ x : Fin m → X,
    wassersteinTwo μ (empiricalMeasure m hm x) ∂iidSampleLaw μ m

/-- Jensen's square-root estimate for an ENNReal function on a probability
space. This is the averaging step used after a pointwise coupling cost bound. -/
theorem lintegral_ennrealSqrt_le_sqrt_lintegral
    {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (f : α → ℝ≥0∞) (hf : AEMeasurable f P) :
    (∫⁻ x, ennrealSqrt (f x) ∂P) ≤ ennrealSqrt (∫⁻ x, f x ∂P) := by
  let g : α → ℝ≥0∞ := fun x => ennrealSqrt (f x)
  have hg : AEMeasurable g P := by
    exact (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hf)
  have hholder := ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
    Real.HolderConjugate.two_two
    (measurable_const : Measurable fun _ : α => (1 : ℝ≥0∞)).aemeasurable hg
  have hprob : (∫⁻ _ : α, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂P) = 1 := by
    simp
  have hsq : (∫⁻ x, g x ^ (2 : ℝ) ∂P) = ∫⁻ x, f x ∂P := by
    apply lintegral_congr_ae
    filter_upwards [] with x
    change (f x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = f x
    rw [← ENNReal.rpow_mul]
    norm_num
  calc
    (∫⁻ x, ennrealSqrt (f x) ∂P) = ∫⁻ x, (1 : ℝ≥0∞) * g x ^ (1 : ℝ) ∂P := by
      simp [g]
    _ ≤ (∫⁻ _ : α, (1 : ℝ≥0∞) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) *
        (∫⁻ x, g x ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
      convert hholder using 1 <;> norm_num
    _ = ennrealSqrt (∫⁻ x, f x ∂P) := by
      rw [hprob, hsq]
      simp [ennrealSqrt]

end BrownianSharp.AlignmentPaperEmpiricalWasserstein

end
