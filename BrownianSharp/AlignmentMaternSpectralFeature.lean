import BrownianSharp.AlignmentMaternSpectralWeights
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic

/-!
An actual one-dimensional stationary Matérn spectral feature.  The spectral
measure has density `(κ² + ξ²)^(-h-1/2)` and the feature is the cosine/sine
phase vector in its real `L²` space.  This file supplies the finite-dimensional
covariance Gram identity; it does not identify the restricted RKHS on an
interval or cube.
-/

noncomputable section

open MeasureTheory
open Filter
open scoped ENNReal InnerProductSpace Topology

set_option maxHeartbeats 400000

namespace BrownianSharp.AlignmentMaternSpectralFeature

def density (κ h ξ : ℝ) : ℝ := Real.rpow (κ ^ 2 + ξ ^ 2) (-(h + 1 / 2))

theorem density_pos (κ h ξ : ℝ) (hκ : 0 < κ) : 0 < density κ h ξ := by
  apply Real.rpow_pos_of_pos
  positivity

/-- The stationary Matérn spectral density is integrable exactly in the
positive-smoothness regime used here. -/
theorem density_integrable (κ h : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    Integrable (density κ h) volume := by
  let s : ℝ := h + 1 / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hdim : (Module.finrank ℝ ℝ : ℝ) < 2 * s := by
    simp [s]
    linarith
  have hbessel : Integrable (fun ξ : ℝ => (1 + ‖ξ‖ ^ 2) ^ (-(2 * s) / 2)) volume :=
    integrable_rpow_neg_one_add_norm_sq hdim
  have hbase (ξ : ℝ) : 0 < min 1 (κ ^ 2) * (1 + ξ ^ 2) := by
    positivity
  have hcompare (ξ : ℝ) :
      density κ h ξ ≤ (Real.rpow (min 1 (κ ^ 2)) (-s)) *
        ((1 + ‖ξ‖ ^ 2) ^ (-(2 * s) / 2)) := by
    have hlow : min 1 (κ ^ 2) * (1 + ξ ^ 2) ≤ κ ^ 2 + ξ ^ 2 := by
      by_cases hk : κ ^ 2 ≤ 1
      · rw [min_eq_right hk]
        nlinarith [sq_nonneg ξ]
      · rw [min_eq_left (le_of_not_ge hk)]
        nlinarith [sq_nonneg ξ]
    have hc : 0 < min 1 (κ ^ 2) := lt_min (by norm_num) (sq_pos_of_pos hκ)
    have hx : 0 < κ ^ 2 + ξ ^ 2 := by positivity
    have hm := Real.rpow_le_rpow_of_nonpos (hbase ξ) hlow (by linarith : -s ≤ 0)
    have hm' : Real.rpow (κ ^ 2 + ξ ^ 2) (-s) ≤
        Real.rpow (min 1 (κ ^ 2) * (1 + ξ ^ 2)) (-s) := hm
    rw [show density κ h ξ = Real.rpow (κ ^ 2 + ξ ^ 2) (-s) by
      simp [density, s, add_comm, add_left_comm, add_assoc]]
    calc
      Real.rpow (κ ^ 2 + ξ ^ 2) (-s) ≤
          Real.rpow (min 1 (κ ^ 2) * (1 + ξ ^ 2)) (-s) := hm'
      _ = Real.rpow (min 1 (κ ^ 2)) (-s) *
          Real.rpow (1 + ξ ^ 2) (-s) := Real.mul_rpow hc.le (by positivity)
      _ = Real.rpow (min 1 (κ ^ 2)) (-s) *
          ((1 + ‖ξ‖ ^ 2) ^ (-(2 * s) / 2)) := by
            congr 2
            · congr 1
              simp [Real.norm_eq_abs, sq_abs]
            · congr 1
              congr 1
              ring
  have hmeas : Measurable (density κ h) := by
    apply Continuous.measurable
    unfold density
    refine continuous_iff_continuousAt.mpr fun ξ => ?_
    have hcont : ContinuousAt (fun x : ℝ => κ ^ 2 + x ^ 2) ξ := by fun_prop
    exact hcont.rpow_const (Or.inl (ne_of_gt (by positivity)))
  refine hbessel.const_mul (Real.rpow (min 1 (κ ^ 2)) (-s)) |>.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (density_pos κ h ξ hκ))]
  exact hcompare ξ

def spectralMeasure (κ h : ℝ) : Measure ℝ :=
  volume.withDensity (fun ξ => ENNReal.ofReal (density κ h ξ))

theorem spectralMeasure_isFinite (κ h : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    IsFiniteMeasure (spectralMeasure κ h) := by
  apply isFiniteMeasure_withDensity
  have hi := (density_integrable κ h hκ hh).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at hi
  have hnonneg : ∀ ξ, 0 ≤ density κ h ξ := fun ξ => (density_pos κ h ξ hκ).le
  have heq : (∫⁻ ξ : ℝ, ENNReal.ofReal (density κ h ξ) ∂volume) =
      ∫⁻ ξ : ℝ, ‖density κ h ξ‖ₑ ∂volume := by
    congr 1
    ext ξ
    rw [ENNReal.ofReal_eq_coe_nnreal (hnonneg ξ)]
    congr 1
    apply Subtype.ext
    simp [Real.norm_eq_abs, abs_of_nonneg (hnonneg ξ)]
  rw [heq]
  exact hi.ne

def phase (t ξ : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (![Real.cos (2 * Real.pi * ξ * t), Real.sin (2 * Real.pi * ξ * t)])

theorem phase_norm (t ξ : ℝ) : ‖phase t ξ‖ = 1 := by
  rw [phase, EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.norm_eq_abs, sq_abs]
  rw [Real.cos_sq_add_sin_sq]
  norm_num

theorem phaseMemLp (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    MemLp (fun ξ : ℝ => phase t ξ) 2 (spectralMeasure κ h) := by
  let μ := spectralMeasure κ h
  letI : IsFiniteMeasure μ := spectralMeasure_isFinite κ h hκ hh
  apply MemLp.of_bound (by
    change AEStronglyMeasurable (fun ξ : ℝ => phase t ξ) μ
    apply (show Measurable (fun ξ : ℝ => phase t ξ) by
      unfold phase
      fun_prop).aestronglyMeasurable) 1
  filter_upwards with ξ
  rw [phase_norm]

def feature (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    Lp (EuclideanSpace ℝ (Fin 2)) 2 (spectralMeasure κ h) :=
  (phaseMemLp κ h t hκ hh).toLp (fun ξ => phase t ξ)

def stationaryCovariance (κ h t u : ℝ) : ℝ :=
  ∫ ξ : ℝ, Real.cos (2 * Real.pi * ξ * (t - u)) ∂spectralMeasure κ h

theorem continuous_spectralCovariance_lag (κ h : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    Continuous (fun τ : ℝ =>
      ∫ ξ : ℝ, Real.cos (2 * Real.pi * ξ * τ) ∂spectralMeasure κ h) := by
  let μ := spectralMeasure κ h
  haveI : IsFiniteMeasure μ := spectralMeasure_isFinite κ h hκ hh
  rw [continuous_iff_continuousAt]
  intro τ
  have hmeas : ∀ᶠ x in 𝓝 τ,
      AEStronglyMeasurable (fun ξ : ℝ => Real.cos (2 * Real.pi * ξ * x)) μ := by
    filter_upwards with x
    exact Measurable.aestronglyMeasurable
      (show Measurable (fun ξ : ℝ => Real.cos (2 * Real.pi * ξ * x)) by fun_prop)
  have hbound : ∀ᶠ x in 𝓝 τ, ∀ᵐ ξ ∂μ,
      ‖Real.cos (2 * Real.pi * ξ * x)‖ ≤ (1 : ℝ) := by
    filter_upwards with x
    filter_upwards with ξ
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hpoint : ∀ᵐ ξ ∂μ,
      Tendsto (fun x : ℝ => Real.cos (2 * Real.pi * ξ * x)) (𝓝 τ)
        (𝓝 (Real.cos (2 * Real.pi * ξ * τ))) := by
    filter_upwards with ξ
    exact (show Continuous (fun x : ℝ => Real.cos (2 * Real.pi * ξ * x)) by fun_prop)
      |>.continuousAt.tendsto
  simpa [ContinuousAt, μ] using
    (tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝 τ)
      (F := fun x ξ => Real.cos (2 * Real.pi * ξ * x))
      (f := fun ξ => Real.cos (2 * Real.pi * ξ * τ)) (bound := fun _ => (1 : ℝ))
      hmeas hbound (integrable_const (1 : ℝ)) hpoint)

theorem continuous_stationaryCovariance (κ h : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    Continuous (fun p : ℝ × ℝ => stationaryCovariance κ h p.1 p.2) := by
  have hc := continuous_spectralCovariance_lag κ h hκ hh
  simpa [stationaryCovariance, Function.comp_def] using
    hc.comp (continuous_fst.sub continuous_snd)

theorem feature_inner_eq_stationaryCovariance (κ h t u : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) :
    inner ℝ (feature κ h t hκ hh) (feature κ h u hκ hh) = stationaryCovariance κ h t u := by
  rw [MeasureTheory.L2.inner_def, stationaryCovariance]
  dsimp [feature]
  have hcoe_t := (phaseMemLp κ h t hκ hh).coeFn_toLp
  have hcoe_u := (phaseMemLp κ h u hκ hh).coeFn_toLp
  apply integral_congr_ae
  filter_upwards [hcoe_t, hcoe_u] with ξ ht hu
  rw [ht, hu]
  simp only [phase, EuclideanSpace.inner_toLp_toLp]
  simp [dotProduct, Fin.sum_univ_two, Pi.star_apply, star_trivial]
  rw [← Real.cos_sub]
  rw [show 2 * Real.pi * ξ * u - 2 * Real.pi * ξ * t =
      -(2 * Real.pi * ξ * (t - u)) by ring, Real.cos_neg]

end BrownianSharp.AlignmentMaternSpectralFeature
