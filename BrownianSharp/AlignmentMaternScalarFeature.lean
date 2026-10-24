import BrownianSharp.AlignmentMaternSpectralFeature
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! A scalar real L2 realization of the Matérn kernel. Even spectral density
makes cos+sin have exactly the same Gram kernel as the cosine/sine pair.
This permits the existing scalar L2 tensor construction without changing the
stationary process covariance.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentMaternScalarFeature
open AlignmentMaternSpectralFeature

def scalarPhase (t ξ : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * ξ * t) + Real.sin (2 * Real.pi * ξ * t)

theorem scalarPhase_abs_le (t ξ : ℝ) : |scalarPhase t ξ| ≤ 2 := by
  unfold scalarPhase
  exact (abs_add_le _ _).trans (by
    have hc := Real.abs_cos_le_one (2 * Real.pi * ξ * t)
    have hs := Real.abs_sin_le_one (2 * Real.pi * ξ * t)
    linarith)

theorem scalarPhaseMemLp (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    MemLp (scalarPhase t) 2 (spectralMeasure κ h) := by
  letI := spectralMeasure_isFinite κ h hκ hh
  apply MemLp.of_bound (by
    exact (show Measurable (scalarPhase t) by unfold scalarPhase; fun_prop).aestronglyMeasurable) 2
  filter_upwards with ξ
  exact scalarPhase_abs_le t ξ

def scalarFeature (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    Lp ℝ 2 (spectralMeasure κ h) :=
  (scalarPhaseMemLp κ h t hκ hh).toLp (scalarPhase t)

theorem integral_spectral_eq_weighted (κ h : ℝ) (hκ : 0 < κ)
    (g : ℝ → ℝ) :
    ∫ ξ, g ξ ∂spectralMeasure κ h = ∫ ξ, density κ h ξ * g ξ := by
  have hd : Measurable (density κ h) := by
    apply Continuous.measurable
    unfold density
    refine continuous_iff_continuousAt.mpr fun ξ => ?_
    exact (by fun_prop : ContinuousAt (fun x : ℝ => κ^2+x^2) ξ).rpow_const
      (Or.inl (ne_of_gt (by positivity : 0 < κ^2+ξ^2)))
  unfold spectralMeasure
  rw [integral_withDensity_eq_integral_toReal_smul
    (hd.ennreal_ofReal) (by filter_upwards with ξ; exact ENNReal.ofReal_lt_top) g]
  apply integral_congr_ae
  filter_upwards with ξ
  simp [ENNReal.toReal_ofReal (density_pos κ h ξ hκ).le, smul_eq_mul]

theorem spectral_sine_integral_zero (κ h t : ℝ) (hκ : 0 < κ) :
    ∫ ξ, Real.sin (2 * Real.pi * ξ * t) ∂spectralMeasure κ h = 0 := by
  rw [integral_spectral_eq_weighted κ h hκ]
  have hn := integral_neg_eq_self
    (fun ξ : ℝ => density κ h ξ * Real.sin (2 * Real.pi * ξ * t)) volume
  have heq : (fun ξ : ℝ => density κ h (-ξ) * Real.sin (2 * Real.pi * (-ξ) * t)) =
      (fun ξ : ℝ => -(density κ h ξ * Real.sin (2 * Real.pi * ξ * t))) := by
    funext ξ
    simp [density, neg_sq, mul_neg, Real.sin_neg]
  change (∫ ξ, density κ h (-ξ) * Real.sin (2 * Real.pi * (-ξ) * t)) =
    ∫ ξ, density κ h ξ * Real.sin (2 * Real.pi * ξ * t) at hn
  rw [heq, integral_neg] at hn
  linarith

theorem scalarFeature_inner_eq_covariance (κ h t u : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) :
    inner ℝ (scalarFeature κ h t hκ hh) (scalarFeature κ h u hκ hh) =
      stationaryCovariance κ h t u := by
  letI := spectralMeasure_isFinite κ h hκ hh
  have hcos : Integrable (fun ξ => Real.cos (2 * Real.pi * ξ * (t-u)))
      (spectralMeasure κ h) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with ξ
    exact Real.abs_cos_le_one _
  have hsin : Integrable (fun ξ => Real.sin (2 * Real.pi * ξ * (t+u)))
      (spectralMeasure κ h) := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with ξ
    exact Real.abs_sin_le_one _
  have hcoe_t := (scalarPhaseMemLp κ h t hκ hh).coeFn_toLp
  have hcoe_u := (scalarPhaseMemLp κ h u hκ hh).coeFn_toLp
  rw [L2.inner_def]
  calc
    (∫ ξ, inner ℝ (scalarFeature κ h t hκ hh ξ) (scalarFeature κ h u hκ hh ξ)
      ∂spectralMeasure κ h) =
        ∫ ξ, (Real.cos (2*Real.pi*ξ*(t-u)) + Real.sin (2*Real.pi*ξ*(t+u)))
          ∂spectralMeasure κ h := by
      apply integral_congr_ae
      filter_upwards [hcoe_t,hcoe_u] with ξ ht hu
      change scalarFeature κ h t hκ hh ξ = scalarPhase t ξ at ht
      change scalarFeature κ h u hκ hh ξ = scalarPhase u ξ at hu
      rw [ht, hu, Real.inner_apply]
      unfold scalarPhase
      rw [show 2*Real.pi*ξ*(t-u) = 2*Real.pi*ξ*t-2*Real.pi*ξ*u by ring,
        show 2*Real.pi*ξ*(t+u) = 2*Real.pi*ξ*t+2*Real.pi*ξ*u by ring,
        Real.cos_sub, Real.sin_add]
      ring
    _ = stationaryCovariance κ h t u := by
      rw [integral_add hcos hsin, spectral_sine_integral_zero κ h (t+u) hκ, add_zero]
      rfl

end BrownianSharp.AlignmentMaternScalarFeature
