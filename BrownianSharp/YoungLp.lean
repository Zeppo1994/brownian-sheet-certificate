import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Tactic

/-! Jensen's weighted integral estimate, a reusable positive-kernel piece of
Young's convolution inequality. -/

noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

namespace BrownianSharp

/-- A nonnegative unit-mass weight contracts the `p`th absolute moment of an
integral for every `p ≥ 1`. The weighted measure is constructed from the
actual density; no positivity or normalization hypothesis is hidden. -/
theorem weighted_integral_rpow_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (w : α → ℝ) (hwmeas : Measurable w) (hw_nonneg : ∀ x, 0 ≤ w x)
    (hw_int : Integrable w μ) (hw_mass : (∫ x, w x ∂μ) = 1)
    (f : α → ℝ) (p : ℝ) (hp : 1 ≤ p)
    (hf : Integrable f (μ.withDensity fun x => ENNReal.ofReal (w x)))
    (hfabs : Integrable (fun x => |f x|)
      (μ.withDensity fun x => ENNReal.ofReal (w x)))
    (hfpower : Integrable (fun x => |f x| ^ p)
      (μ.withDensity fun x => ENNReal.ofReal (w x))) :
    |∫ x, w x * f x ∂μ| ^ p ≤ ∫ x, w x * |f x| ^ p ∂μ := by
  classical
  let ν : Measure α := μ.withDensity fun x => ENNReal.ofReal (w x)
  have hρmeas : Measurable (fun x : α => ENNReal.ofReal (w x)) :=
    ENNReal.measurable_ofReal.comp hwmeas
  have hνmass : ν Set.univ = 1 := by
    change (μ.withDensity (fun x => ENNReal.ofReal (w x))) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [setLIntegral_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hw_int (ae_of_all _ hw_nonneg), hw_mass]
    norm_num
  letI : IsProbabilityMeasure ν := ⟨hνmass⟩
  have hweighted_f :
      (∫ x, f x ∂ν) = ∫ x, w x * f x ∂μ := by
    change (∫ x, f x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hρmeas
      (ae_of_all _ fun x => by simp) f]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by simp [ENNReal.toReal_ofReal (hw_nonneg x), smul_eq_mul])
  have hweighted_abs :
      (∫ x, |f x| ∂ν) = ∫ x, w x * |f x| ∂μ := by
    change (∫ x, |f x| ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hρmeas
      (ae_of_all _ fun x => by simp) (fun x => |f x|)]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by simp [ENNReal.toReal_ofReal (hw_nonneg x), smul_eq_mul])
  have hweighted_pow :
      (∫ x, |f x| ^ p ∂ν) = ∫ x, w x * |f x| ^ p ∂μ := by
    change (∫ x, |f x| ^ p ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hρmeas
      (ae_of_all _ fun x => by simp) (fun x => |f x| ^ p)]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => by simp [ENNReal.toReal_ofReal (hw_nonneg x), smul_eq_mul])
  have hf_nonneg : ∀ᵐ x ∂ν, |f x| ∈ Set.Ici (0 : ℝ) :=
    ae_of_all _ fun x => by simpa using (abs_nonneg (f x))
  have hconv := (convexOn_rpow hp).map_integral_le
    (Real.continuous_rpow_const (le_trans (by norm_num) hp)).continuousOn
      isClosed_Ici hf_nonneg
      hfabs hfpower
  calc
    |∫ x, w x * f x ∂μ| ^ p = |∫ x, f x ∂ν| ^ p := by rw [← hweighted_f]
    _ ≤ (∫ x, |f x| ∂ν) ^ p := by
      apply Real.rpow_le_rpow (abs_nonneg _) _ (le_trans (by norm_num) hp)
      exact abs_integral_le_integral_abs
    _ ≤ ∫ x, |f x| ^ p ∂ν := hconv
    _ = ∫ x, w x * |f x| ^ p ∂μ := hweighted_pow

end BrownianSharp
