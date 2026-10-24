import BrownianSharp.AlignmentMaternScalarFeature
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-! Continuous, unit-norm Matérn spectral features for the actual stationary
covariance. Only the scalar variance normalization is changed. -/
noncomputable section
open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentMaternContinuousFeature
open AlignmentMaternSpectralFeature AlignmentMaternScalarFeature

def spectralMass (κ h : ℝ) : ℝ := ∫ ξ, density κ h ξ

theorem density_continuous (κ h : ℝ) (hκ : 0 < κ) :
    Continuous (density κ h) := by
  unfold density
  refine continuous_iff_continuousAt.mpr fun ξ => ?_
  exact (by fun_prop : ContinuousAt (fun x : ℝ => κ^2+x^2) ξ).rpow_const
    (Or.inl (ne_of_gt (by positivity : 0 < κ^2+ξ^2)))

theorem spectralMass_pos (κ h : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    0 < spectralMass κ h := by
  exact integral_pos_of_integrable_nonneg_nonzero
    (density_continuous κ h hκ) (density_integrable κ h hκ hh)
    (fun ξ => (density_pos κ h ξ hκ).le) (ne_of_gt (density_pos κ h 0 hκ))

theorem scalarFeature_norm_sq (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    ‖scalarFeature κ h t hκ hh‖^2 = spectralMass κ h := by
  rw [← real_inner_self_eq_norm_sq, scalarFeature_inner_eq_covariance]
  unfold stationaryCovariance
  simp only [sub_self, mul_zero, Real.cos_zero]
  rw [integral_spectral_eq_weighted κ h hκ]
  simp [spectralMass]

theorem scalarFeature_norm_pos (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    0 < ‖scalarFeature κ h t hκ hh‖ := by
  have hs := scalarFeature_norm_sq κ h t hκ hh
  have hp := spectralMass_pos κ h hκ hh
  nlinarith [norm_nonneg (scalarFeature κ h t hκ hh)]

theorem scalarFeature_norm_constant (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    ‖scalarFeature κ h t hκ hh‖ = ‖scalarFeature κ h 0 hκ hh‖ := by
  have ht := scalarFeature_norm_sq κ h t hκ hh
  have hz := scalarFeature_norm_sq κ h 0 hκ hh
  nlinarith [norm_nonneg (scalarFeature κ h t hκ hh),
    norm_nonneg (scalarFeature κ h 0 hκ hh)]

theorem scalarFeature_norm_sub (κ h s t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    ‖scalarFeature κ h s hκ hh - scalarFeature κ h t hκ hh‖ =
      Real.sqrt (spectralMass κ h - 2*stationaryCovariance κ h s t + spectralMass κ h) := by
  rw [← Real.sqrt_sq (norm_nonneg (scalarFeature κ h s hκ hh - scalarFeature κ h t hκ hh))]
  rw [norm_sub_sq_real, scalarFeature_norm_sq, scalarFeature_norm_sq,
    scalarFeature_inner_eq_covariance]

theorem scalarFeature_continuous (κ h : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    Continuous (fun t => scalarFeature κ h t hκ hh) := by
  rw [continuous_iff_continuous_dist]
  have hc := continuous_stationaryCovariance κ h hκ hh
  have hr : Continuous (fun p : ℝ × ℝ =>
      Real.sqrt (spectralMass κ h - 2*stationaryCovariance κ h p.1 p.2 + spectralMass κ h)) :=
    Real.continuous_sqrt.comp
      ((continuous_const.sub (continuous_const.mul hc)).add continuous_const)
  simpa only [dist_eq_norm, scalarFeature_norm_sub] using hr

def normalizedAxis (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    Lp ℝ 2 (spectralMeasure κ h) :=
  ‖scalarFeature κ h 0 hκ hh‖⁻¹ • scalarFeature κ h t hκ hh

theorem normalizedAxis_norm (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    ‖normalizedAxis κ h t hκ hh‖ = 1 := by
  have hp := scalarFeature_norm_pos κ h 0 hκ hh
  rw [normalizedAxis, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp),
    scalarFeature_norm_constant κ h t hκ hh, inv_mul_cancel₀ hp.ne']

theorem normalizedAxis_continuous (κ h : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    Continuous (fun t => normalizedAxis κ h t hκ hh) := by
  change Continuous (fun t : ℝ =>
    ‖scalarFeature κ h 0 hκ hh‖⁻¹ • scalarFeature κ h t hκ hh)
  have hc : Continuous (fun _ : ℝ => (‖scalarFeature κ h 0 hκ hh‖⁻¹ : ℝ)) := continuous_const
  exact hc.smul (scalarFeature_continuous κ h hκ hh)

def normalizedCovariance (κ h s t : ℝ) (hκ : 0 < κ) (hh : 0 < h) : ℝ :=
  (‖scalarFeature κ h 0 hκ hh‖⁻¹)^2 * stationaryCovariance κ h s t

theorem normalizedAxis_inner (κ h s t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    inner ℝ (normalizedAxis κ h s hκ hh) (normalizedAxis κ h t hκ hh) =
      normalizedCovariance κ h s t hκ hh := by
  rw [normalizedAxis, normalizedAxis, real_inner_smul_left, real_inner_smul_right,
    scalarFeature_inner_eq_covariance, normalizedCovariance]
  ring

end BrownianSharp.AlignmentMaternContinuousFeature
