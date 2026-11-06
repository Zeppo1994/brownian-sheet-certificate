import BrownianSharp.AlignmentPaperFractionalFourier
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.RealDeriv

/-! The pinned Fourier API gives a rigorous multiplier and Plancherel identity
for integer derivatives of Schwartz functions.  This is the available
Fourier-side part of the Liouville route; it does not identify the Fourier
transform of the non-Schwartz causal Riemann--Liouville profile. -/

noncomputable section

open scoped FourierTransform SchwartzMap
open scoped LineDeriv
open MeasureTheory Function Filter
open scoped Topology

namespace BrownianSharp.AlignmentPaperFractionalFourierMultiplier

/-- The exponentially damped causal fractional kernel. -/
def dampedFractionalKernel (β ε t : ℝ) : ℝ :=
  (Real.Gamma β)⁻¹ * t^(β-1) * Real.exp (-(ε*t))

/-- Its true one-sided Laplace mass, obtained from Mathlib's Gamma integral
formula.  This is the zero-frequency case of the damped Fourier transform. -/
theorem dampedFractionalKernel_laplace_mass {β ε : ℝ}
    (hβ : 0 < β) (hε : 0 < ε) :
    ∫ t : ℝ in Set.Ioi 0, dampedFractionalKernel β ε t = (1/ε)^β := by
  simp only [dampedFractionalKernel]
  have hfun : (fun t : ℝ => (Real.Gamma β)⁻¹ * t^(β-1) * Real.exp (-(ε*t))) =
      (fun t => (Real.Gamma β)⁻¹ * (t^(β-1) * Real.exp (-(ε*t)))) := by
    funext t
    ring
  rw [hfun]
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hβ hε]
  have hΓ : Real.Gamma β ≠ 0 := (Real.Gamma_pos_of_pos hβ).ne'
  field_simp [hΓ]

/-- Integrability of the complex-frequency damped power kernel on the positive
half-line. The oscillatory factor has modulus one, leaving the usual real
Gamma integrand as a dominator. -/
theorem integrableOn_dampedComplexPower {β ε ω : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    IntegrableOn
      (fun t : ℝ => (t ^ (β - 1) : ℝ) * Complex.exp (-(ε + (ω : ℂ) * Complex.I) * t))
      (Set.Ioi 0) := by
  have hbase : IntegrableOn
      (fun x : ℝ => Complex.exp (-(x : ℂ)) * (x : ℂ) ^ ((β : ℂ) - 1)) (Set.Ioi 0) :=
    by
      simpa [Complex.ofReal_exp] using
        (Complex.GammaIntegral_convergent (s := (β : ℂ)) (by simpa using hβ))
  have hscale := (integrableOn_Ioi_comp_mul_left_iff
    (f := fun x : ℝ => Complex.exp (-(x : ℂ)) * (x : ℂ) ^ ((β : ℂ) - 1))
    0 (a := ε) hε).mpr (by simpa using hbase)
  have hscaled : IntegrableOn
      (fun t : ℝ => Complex.exp (-(ε * t : ℂ)) * (ε * t : ℂ) ^ ((β : ℂ) - 1)) (Set.Ioi 0) :=
    by simpa [Complex.ofReal_mul] using hscale
  have hdom : IntegrableOn (fun t : ℝ => ε ^ (1 - β : ℝ) *
      ‖Complex.exp (-(ε * t : ℂ)) * (ε * t : ℂ) ^ ((β : ℂ) - 1)‖) (Set.Ioi 0) :=
    (hscaled.norm.const_mul _)
  apply Integrable.mono' hdom
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt fun t ht => ?_
    have hpow := Real.continuousAt_rpow_const t (β - 1) (Or.inl (ne_of_gt ht))
    have hexp : ContinuousAt (fun t : ℝ => Complex.exp (-(ε + (ω : ℂ) * Complex.I) * t)) t := by
      fun_prop
    exact hpow.ofReal.mul hexp
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := ht
    rw [norm_mul, Complex.norm_exp]
    have hre : (-(ε + (ω : ℂ) * Complex.I) * t).re = -(ε*t) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    rw [hre]
    have hpow : t ^ (β - 1) = ε ^ (1 - β) * ‖(ε * t : ℂ) ^ ((β : ℂ) - 1)‖ := by
      rw [← Complex.ofReal_mul]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < ε*t)
        ((β : ℂ) - 1)]
      rw [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
      -- The remaining equality is the real scaling law for rpow.
      rw [Real.mul_rpow (le_of_lt hε) (le_of_lt htpos)]
      rw [← mul_assoc, ← Real.rpow_add hε]
      rw [show (1 - β) + (β - 1) = 0 by ring, Real.rpow_zero, one_mul]
    rw [hpow]
    have heps : 0 < ε ^ (1 - β) := Real.rpow_pos_of_pos hε _
    simp [Complex.norm_exp, norm_mul, abs_of_pos heps, hpow, mul_assoc, mul_left_comm, mul_comm]

/-- One extra power of `t` remains integrable, providing the common
dominator for differentiation in frequency. -/
theorem integrableOn_dampedPowerMoment {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    IntegrableOn (fun t : ℝ => (t ^ β : ℝ) * Complex.exp (-(ε : ℂ) * t)) (Set.Ioi 0) := by
  convert integrableOn_dampedComplexPower (β := β + 1) (ε := ε) (ω := 0)
      (by linarith) hε using 1 <;> simp [Complex.ofReal_mul, add_sub_cancel_right]

/-- The damped Fourier-Laplace integral of the causal power kernel. -/
def dampedFractionalTransform (β ε ω : ℝ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 0,
    (t ^ (β - 1) : ℝ) * Complex.exp (-(ε + (ω : ℂ) * Complex.I) * t)

/-- Differentiation in real frequency is justified by the integrable `t^β`
Gamma majorant. -/
theorem dampedFractionalTransform_hasDerivAt {β ε ω : ℝ}
    (hβ : 0 < β) (hε : 0 < ε) :
    HasDerivAt (fun x : ℝ => dampedFractionalTransform β ε x)
      (∫ t : ℝ in Set.Ioi 0,
        (-Complex.I * t) * ((t ^ (β - 1) : ℝ) *
          Complex.exp (-(ε + (ω : ℂ) * Complex.I) * t))) ω := by
  let F : ℝ → ℝ → ℂ := fun x t =>
    (t ^ (β - 1) : ℝ) * Complex.exp (-(ε + (x : ℂ) * Complex.I) * t)
  let F' : ℝ → ℝ → ℂ := fun x t => (-Complex.I * t) * F x t
  let μ := volume.restrict (Set.Ioi (0 : ℝ))
  let bound : ℝ → ℝ := fun t => t ^ β * Real.exp (-(ε*t))
  have hF_int : Integrable (F ω) μ := by
    change IntegrableOn (F ω) (Set.Ioi 0)
    simpa [F, dampedFractionalTransform] using
      (integrableOn_dampedComplexPower hβ hε (ω := ω))
  have hF_meas : ∀ᶠ x in 𝓝 ω, AEStronglyMeasurable (F x) μ := by
    filter_upwards [] with x
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt fun t ht => ?_
    have hp := Real.continuousAt_rpow_const t (β - 1) (Or.inl (ne_of_gt ht))
    have he : ContinuousAt (fun t : ℝ => Complex.exp (-(ε + (x : ℂ) * Complex.I) * t)) t := by
      fun_prop
    exact (Complex.continuous_ofReal.continuousAt.comp hp).mul he
  have hF'_meas : AEStronglyMeasurable (F' ω) μ := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt fun t ht => ?_
    have hp := Real.continuousAt_rpow_const t (β - 1) (Or.inl (ne_of_gt ht))
    have he : ContinuousAt (fun t : ℝ => Complex.exp (-(ε + (ω : ℂ) * Complex.I) * t)) t := by
      fun_prop
    exact ((continuousAt_const.mul Complex.continuous_ofReal.continuousAt).mul
      ((Complex.continuous_ofReal.continuousAt.comp hp).mul he))
  have hbound_int : Integrable bound μ := by
    have hm := (integrableOn_dampedPowerMoment hβ hε).norm
    have heq : (fun t : ℝ => ‖(t ^ β : ℝ) * Complex.exp (-(ε : ℂ) * t)‖) =ᵐ[μ] bound := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := ht
      simp [bound, norm_mul, Complex.norm_real, Complex.norm_exp,
        Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos htpos β), Complex.ofReal_mul]
    exact hm.congr heq
  have h_bound : ∀ᵐ t ∂μ, ∀ x : ℝ, ‖F' x t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x
    have htpos : 0 < t := ht
    have hpow : t * t ^ (β - 1) = t ^ β := by
      calc
        t * t ^ (β - 1) = t ^ (1 : ℝ) * t ^ (β - 1) := by rw [Real.rpow_one]
        _ = t ^ (1 + (β - 1)) := (Real.rpow_add htpos 1 (β - 1)).symm
        _ = t ^ β := by congr 1 <;> ring
    rw [norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos htpos]
    have hF : ‖F x t‖ = t ^ (β - 1) * Real.exp (-(ε*t)) := by
      change ‖(t ^ (β - 1) : ℝ) * Complex.exp (-(ε + (x : ℂ) * Complex.I) * t)‖ = _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos htpos _), Complex.norm_exp]
      have hre : (-(ε + (x : ℂ) * Complex.I) * t).re = -(ε*t) := by
        simp [mul_comm, mul_left_comm, mul_assoc]
      rw [hre]
    rw [hF]
    change 1 * t * (t ^ (β - 1) * Real.exp (-(ε*t))) ≤ t ^ β * Real.exp (-(ε*t))
    apply le_of_eq
    rw [← hpow]
    ring
  have h_diff : ∀ᵐ t ∂μ, ∀ x : ℝ, HasDerivAt (F · t) (F' x t) x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht x
    have hxarg : HasDerivAt (fun y : ℝ => -(ε + (y : ℂ) * Complex.I) * t)
        (-Complex.I * t) x := by
      have hlin : HasDerivAt (fun y : ℝ => (y : ℂ) * (-Complex.I * t) + (-ε*t : ℂ))
          (-Complex.I * t) x := by
        have hcast := (HasDerivAt.ofReal_comp (hasDerivAt_id x)).const_mul (-Complex.I*t)
        have hadd := hcast.add_const (-ε*t : ℂ)
        convert hadd using 1
        · ext y
          simp only [id_eq]
          ring_nf
        · simp
      convert hlin using 1
      · ext y
        ring_nf
    have hexp := (Complex.hasDerivAt_exp _).comp x hxarg
    simpa [F, F', mul_assoc, mul_comm, mul_left_comm] using
      (hexp.mul_const (t ^ (β - 1) : ℝ))
  have h_diff' : ∀ᵐ t ∂μ, ∀ x ∈ Set.univ, HasDerivAt (F · t) (F' x t) x := by
    filter_upwards [h_diff] with t ht x hx
    exact ht x
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (x₀ := ω) (μ := μ) (F := F) (F' := F') (bound := bound)
    Filter.univ_mem hF_meas hF_int hF'_meas (by
      filter_upwards [h_bound] with t ht x hx
      exact ht x) hbound_int h_diff'
  simpa [dampedFractionalTransform, F, F'] using hmain.2

/-- The real-frequency transform satisfies the first-order ODE obtained by
integration by parts on the positive half-line. -/
theorem dampedFractionalTransform_ode {β ε ω : ℝ}
    (hβ : 0 < β) (hε : 0 < ε) :
    HasDerivAt (fun x : ℝ => dampedFractionalTransform β ε x)
      ((-Complex.I * β) / (ε + (ω : ℂ) * Complex.I) *
        dampedFractionalTransform β ε ω) ω := by
  let z : ℂ := (ε : ℂ) + (ω : ℂ) * Complex.I
  let a : ℂ := -(Complex.I * (ω : ℂ)) + (-(ε : ℂ))
  let u : ℝ → ℂ := fun t => (t ^ β : ℝ)
  let u' : ℝ → ℂ := fun t => (β * t ^ (β - 1) : ℝ)
  let v : ℝ → ℂ := fun t => Complex.exp (a * (t : ℂ))
  let v' : ℝ → ℂ := fun t => a * v t
  have hu : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt u (u' t) t := by
    intro t ht
    have hd := HasDerivAt.ofReal_comp
      (Real.hasDerivAt_rpow_const (x := t) (p := β) (Or.inl (ne_of_gt ht)))
    simpa [u, u', Complex.ofReal_mul] using hd
  have hv : ∀ t ∈ Set.Ioi (0:ℝ), HasDerivAt v (v' t) t := by
    intro t ht
    have harg := (HasDerivAt.ofReal_comp (hasDerivAt_id t)).const_mul a
    have hexp := (Complex.hasDerivAt_exp (a * ((id t : ℝ) : ℂ))).comp t harg
    convert hexp using 1
    · ext y
      simp [v, mul_comm]
    · simp [v, v', mul_comm]
  have hu'v : IntegrableOn (fun t => u' t * v t) (Set.Ioi 0) := by
    have h := (integrableOn_dampedComplexPower hβ hε (ω := ω)).const_mul (β : ℂ)
    change Integrable (fun t => u' t * v t) (volume.restrict (Set.Ioi 0))
    simpa [u', v, z, a, mul_assoc, mul_comm, mul_left_comm, Complex.ofReal_mul] using h
  have huv' : IntegrableOn (fun t => u t * v' t) (Set.Ioi 0) := by
    have h := (integrableOn_dampedComplexPower (β := β + 1) (ε := ε) (ω := ω)
      (by linarith) hε).const_mul a
    change Integrable (fun t => u t * v' t) (volume.restrict (Set.Ioi 0))
    simpa [u, v', v, z, a, add_sub_cancel_right, mul_assoc, mul_comm, mul_left_comm,
      Complex.ofReal_mul] using h
  have hzero : Tendsto (fun t => u t * v t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hid : Tendsto id (𝓝[>] (0:ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
    have hp := hid.rpow_const_nhds_zero hβ
    have he : Tendsto (fun t : ℝ => Complex.exp (a*(t:ℂ))) (𝓝[>] 0)
        (𝓝 (Complex.exp 0)) := by
      have hc : Continuous (fun t : ℝ => Complex.exp (a*(t:ℂ))) := by fun_prop
      simpa using (hc.continuousAt (x := 0)).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0:ℝ) ≤ 𝓝 0)
    simpa [u, v] using hp.ofReal.mul he
  have hinfty : Tendsto (fun t => u t * v t) atTop (𝓝 0) := by
    have hnorm : (fun t : ℝ => ‖u t * v t‖) =ᶠ[atTop]
        fun t => t ^ β * Real.exp (-ε*t) := by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
      simp [u, v, z, a, norm_mul, Complex.norm_real, abs_of_nonneg (Real.rpow_nonneg ht _),
        Complex.norm_exp, Complex.ofReal_mul, mul_comm, neg_mul]
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [mul_assoc, neg_mul] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero β ε hε).congr' hnorm.symm
  have hibp := integral_Ioi_mul_deriv_eq_deriv_mul hu hv huv' hu'v hzero hinfty
  have hbase : ∫ t : ℝ in Set.Ioi 0,
      (u' t * v t + u t * v' t) = 0 := by
    rw [integral_add hu'v huv', hibp]
    simp
  have hz : z ≠ 0 := by
    intro hz0
    have : z.re = 0 := congrArg Complex.re hz0
    simp [z, Complex.add_re] at this
    linarith
  have hmoment : (∫ t : ℝ in Set.Ioi 0, (t ^ β : ℝ) * v t) =
      (β / z) * (∫ t : ℝ in Set.Ioi 0, (t ^ (β - 1) : ℝ) * v t) := by
    have h1 : ∫ t : ℝ in Set.Ioi 0, u' t * v t =
        β * ∫ t : ℝ in Set.Ioi 0, (t ^ (β - 1) : ℝ) * v t := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      simp [u', Complex.ofReal_mul, mul_assoc]
    have h2 : ∫ t : ℝ in Set.Ioi 0, u t * v' t =
        -z * ∫ t : ℝ in Set.Ioi 0, (t ^ β : ℝ) * v t := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      simp [u, v', v, a, z, mul_assoc, mul_comm, mul_left_comm]
    rw [h1, h2] at hibp
    have hrelation : z * (∫ t : ℝ in Set.Ioi 0, (t ^ β : ℝ) * v t) =
        β * (∫ t : ℝ in Set.Ioi 0, (t ^ (β - 1) : ℝ) * v t) := by
      linear_combination -hibp
    calc
      (∫ t : ℝ in Set.Ioi 0, (t ^ β : ℝ) * v t) =
          (z * (∫ t : ℝ in Set.Ioi 0, (t ^ β : ℝ) * v t)) / z := by
            field_simp [hz]
      _ = (β * (∫ t : ℝ in Set.Ioi 0, (t ^ (β - 1) : ℝ) * v t)) / z := by
            rw [hrelation]
      _ = (β / z) * (∫ t : ℝ in Set.Ioi 0, (t ^ (β - 1) : ℝ) * v t) := by ring
  have hderiv := dampedFractionalTransform_hasDerivAt hβ hε (ω := ω)
  have hderiv_eq : (∫ t : ℝ in Set.Ioi 0,
      (-Complex.I * t) * ((t ^ (β - 1) : ℝ) * v t)) =
      (-Complex.I) * (∫ t : ℝ in Set.Ioi 0, (t ^ β : ℝ) * v t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hpow : t * t ^ (β - 1) = t ^ β := by
      calc
        t * t ^ (β - 1) = t ^ (1:ℝ) * t ^ (β - 1) := by rw [Real.rpow_one]
        _ = t ^ (1 + (β - 1)) := (Real.rpow_add ht 1 (β - 1)).symm
        _ = t ^ β := by congr 1 <;> ring
    calc
      (-Complex.I * t) * ((t ^ (β - 1) : ℝ) * v t) =
          -Complex.I * ((t : ℂ) * (t ^ (β - 1) : ℝ)) * v t := by ring
      _ = -Complex.I * ((t * t ^ (β - 1) : ℝ) : ℂ) * v t := by
        rw [← Complex.ofReal_mul]
      _ = -Complex.I * ((t * t ^ (β - 1) : ℝ) : ℂ) * v t := by rfl
      _ = -Complex.I * (((t * t ^ (β - 1) : ℝ) : ℂ) * v t) := by rw [mul_assoc]
      _ = -Complex.I * ((t ^ β : ℝ) * v t) := by
        rw [congrArg Complex.ofReal hpow]
  have htransform : dampedFractionalTransform β ε ω =
      ∫ t : ℝ in Set.Ioi 0, (t ^ (β - 1) : ℝ) * v t := by
    rw [dampedFractionalTransform]
    apply integral_congr_ae
    filter_upwards with t
    congr 1
    dsimp [v, a, z]
    ring_nf
  rw [show ((-Complex.I * β) / (ε + (ω:ℂ)*Complex.I) *
      dampedFractionalTransform β ε ω) =
      (-Complex.I) * (β / z * dampedFractionalTransform β ε ω) by
        simp [z]; ring]
  have hderivInt : (∫ t : ℝ in Set.Ioi 0,
      (-Complex.I * t) * ((t ^ (β - 1) : ℝ) *
        Complex.exp (-(ε + (ω : ℂ) * Complex.I) * t))) =
      ∫ t : ℝ in Set.Ioi 0, (-Complex.I * t) * ((t ^ (β - 1) : ℝ) * v t) := by
    apply integral_congr_ae
    filter_upwards with t
    congr 2
    simp only [v, a, z]
    congr 1
    ring
  have hderiv' : HasDerivAt (fun x : ℝ => dampedFractionalTransform β ε x)
      ((-Complex.I) * (∫ t : ℝ in Set.Ioi 0, (t ^ β : ℝ) * v t)) ω := by
    convert hderiv using 1
    · calc
        (-Complex.I) * (∫ t : ℝ in Set.Ioi 0, (t ^ β : ℝ) * v t) =
            ∫ t : ℝ in Set.Ioi 0, (-Complex.I * t) *
              ((t ^ (β - 1) : ℝ) * v t) := hderiv_eq.symm
        _ = ∫ t : ℝ in Set.Ioi 0, (-Complex.I * t) *
              ((t ^ (β - 1) : ℝ) *
                Complex.exp (-(ε + (ω : ℂ) * Complex.I) * t)) := hderivInt.symm
  rw [hmoment] at hderiv'
  rw [← htransform] at hderiv'
  exact hderiv'

/-- The damped causal power has the genuine complex Laplace transform, proved
from the real-frequency ODE and its value at zero. -/
theorem dampedFractionalTransform_eq_gamma_cpow {β ε ω : ℝ}
    (hβ : 0 < β) (hε : 0 < ε) :
    dampedFractionalTransform β ε ω =
      (Real.Gamma β : ℂ) * ((ε : ℂ) + (ω : ℂ) * Complex.I) ^ (-(β : ℂ)) := by
  let Z : ℝ → ℂ := fun x => (ε : ℂ) + (x : ℂ) * Complex.I
  let W : ℝ → ℂ := fun x => Complex.exp (Complex.log (Z x) * (β : ℂ))
  let P : ℝ → ℂ := fun x => W x * dampedFractionalTransform β ε x
  have hzpos (x : ℝ) : 0 < (Z x).re := by simp [Z, Complex.add_re, hε]
  have hz (x : ℝ) : Z x ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [Z, Complex.add_re] at hr
    linarith
  have hPderiv : ∀ x : ℝ, HasDerivAt P 0 x := by
    intro x
    have hZ : HasDerivAt Z Complex.I x := by
      have h := (HasDerivAt.ofReal_comp (hasDerivAt_id x)).const_mul Complex.I
      convert h.const_add (ε : ℂ) using 1
      · ext y
        simp only [id_eq]
        ring
      · simp
    have hslit : Z x ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      exact Or.inl (by simpa [Z] using hε)
    have hlog := hZ.clog_real hslit
    have harg := hlog.mul_const (β : ℂ)
    have hpow : HasDerivAt W (W x * (Complex.I / Z x * (β : ℂ))) x := by
      simpa [W, mul_comm, mul_left_comm, mul_assoc] using harg.cexp
    have hT := dampedFractionalTransform_ode hβ hε (ω := x)
    have hmul := hpow.mul hT
    have hcancel : W x * (Complex.I / Z x * (β : ℂ)) *
        dampedFractionalTransform β ε x + W x *
          ((-Complex.I * (β : ℂ)) / Z x * dampedFractionalTransform β ε x) = 0 := by
      field_simp [hz x]
      <;> ring
    convert hmul using 1
    simpa [Z] using hcancel.symm
  have hPconst : ∀ x y : ℝ, P x = P y := by
    intro x y
    apply is_const_of_deriv_eq_zero (fun z => (hPderiv z).differentiableAt) ?_ x y
    intro z
    rw [(hPderiv z).deriv]
  have hzero : dampedFractionalTransform β ε 0 =
      (Real.Gamma β : ℂ) * (((1 / ε : ℝ) ^ β : ℝ) : ℂ) := by
    have hreal := dampedFractionalKernel_laplace_mass hβ hε
    have hΓ : Real.Gamma β ≠ 0 := (Real.Gamma_pos_of_pos hβ).ne'
    have hTreal : dampedFractionalTransform β ε 0 =
        (∫ t : ℝ in Set.Ioi 0, t ^ (β - 1) * Real.exp (-(ε*t)) : ℝ) := by
      rw [dampedFractionalTransform]
      have hfun : (fun t : ℝ => (t ^ (β - 1) : ℝ) *
          Complex.exp (-(ε + (0 : ℝ) * Complex.I) * t)) =
          fun t => ((t ^ (β - 1) * Real.exp (-(ε*t)) : ℝ) : ℂ) := by
        funext t
        simp [Complex.ofReal_exp]
      rw [hfun]
      exact (integral_ofReal.symm.trans <| setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => by simp [Complex.ofReal_exp])).symm
    rw [hTreal]
    have hkernel : dampedFractionalKernel β ε = fun t : ℝ =>
        (Real.Gamma β)⁻¹ * (t ^ (β - 1) * Real.exp (-(ε*t))) := by
      funext t
      simp [dampedFractionalKernel]
      ring
    have hmass : (Real.Gamma β)⁻¹ *
        (∫ t : ℝ in Set.Ioi 0, t ^ (β - 1) * Real.exp (-(ε*t)) : ℝ) = (1/ε)^β := by
      rw [hkernel, integral_const_mul] at hreal
      exact hreal
    have hinterm : (∫ t : ℝ in Set.Ioi 0, t ^ (β - 1) * Real.exp (-(ε*t)) : ℝ) =
        Real.Gamma β * (1/ε)^β := by
      calc
        _ = Real.Gamma β * ((Real.Gamma β)⁻¹ *
            (∫ t : ℝ in Set.Ioi 0, t ^ (β - 1) * Real.exp (-(ε*t)) : ℝ)) := by field_simp [hΓ]
        _ = _ := by rw [hmass]
    rw [hinterm]
    push_cast
    ring
  have hconst := hPconst ω 0
  have hcpow (x : ℝ) : W x = Z x ^ (β : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (hz x)]
  have hP0 : P 0 = Real.Gamma β := by
    change W 0 * dampedFractionalTransform β ε 0 = _
    rw [hcpow 0, show Z 0 = (ε : ℂ) by simp [Z], hzero]
    have hbase : ε ^ β * (1 / ε : ℝ) ^ β = 1 := by
      rw [← Real.mul_rpow (le_of_lt hε) (by positivity : 0 ≤ (1 / ε : ℝ))]
      rw [show ε * (1 / ε : ℝ) = 1 by field_simp [hε.ne'], Real.one_rpow]
    rw [← Complex.ofReal_cpow (le_of_lt hε) β]
    calc
      ((ε ^ β : ℝ) : ℂ) * ((Real.Gamma β : ℂ) * (((1 / ε : ℝ) ^ β : ℝ) : ℂ)) =
          (Real.Gamma β : ℂ) * (((ε ^ β : ℝ) : ℂ) * (((1 / ε : ℝ) ^ β : ℝ) : ℂ)) := by ring
      _ = (Real.Gamma β : ℂ) * ((ε ^ β * (1 / ε : ℝ) ^ β : ℝ) : ℂ) := by
            rw [← Complex.ofReal_mul]
      _ = Real.Gamma β := by rw [hbase]; simp
  have hPω : W ω * dampedFractionalTransform β ε ω =
      (Real.Gamma β : ℂ) := by
    simpa [P] using hconst.trans hP0
  calc
    dampedFractionalTransform β ε ω =
        (Z ω ^ (β : ℂ))⁻¹ * (Real.Gamma β : ℂ) := by
          rw [← hPω, hcpow]
          field_simp [hz ω]
    _ = (Real.Gamma β : ℂ) * Z ω ^ (-(β : ℂ)) := by
          rw [Complex.cpow_neg]
          ring
    _ = _ := by rfl

/-- Exact Mathlib-normalized Fourier transform of the damped causal kernel.
The frequency is `2 * π * ξ`, matching the pinned Fourier convention. -/
theorem dampedFractionalKernel_fourier {β ε ξ : ℝ}
    (hβ : 0 < β) (hε : 0 < ε) :
    (∫ t : ℝ in Set.Ioi 0,
      (dampedFractionalKernel β ε t : ℂ) *
        Complex.exp (-((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I * t)) =
      ((ε : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) ^ (-(β : ℂ)) := by
  have hΓ : (Real.Gamma β : ℂ) ≠ 0 := by
    exact_mod_cast (Real.Gamma_pos_of_pos hβ).ne'
  have hpoint : (fun t : ℝ =>
      (dampedFractionalKernel β ε t : ℂ) *
        Complex.exp (-((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I * t)) =
      fun t => (Real.Gamma β : ℂ)⁻¹ *
        ((t ^ (β - 1) : ℝ) *
          Complex.exp (-((ε : ℂ) + ((2 * Real.pi * ξ : ℝ) : ℂ) * Complex.I) * t)) := by
    funext t
    simp [dampedFractionalKernel, Complex.ofReal_mul, Complex.ofReal_exp,
      Complex.exp_add, mul_add, mul_assoc, mul_left_comm, mul_comm]
  rw [hpoint, integral_const_mul]
  change (Real.Gamma β : ℂ)⁻¹ * dampedFractionalTransform β ε (2 * Real.pi * ξ) = _
  rw [dampedFractionalTransform_eq_gamma_cpow hβ hε (ω := 2 * Real.pi * ξ)]
  field_simp [hΓ]

/-- The damped kernel multiplier followed by a `q`-th derivative is
uniformly bounded by the paper's fractional weight. The `2π` is retained to
match Mathlib's Fourier convention. -/
theorem dampedFractionalDerivativeMultiplier_bound {q : ℕ} {r ε ξ : ℝ}
    (hr : 0 < r) (hrq : r < q) (hε : 0 < ε) :
    ‖(((ε : ℂ) + (2 * Real.pi * ξ : ℝ) * Complex.I) ^ (-(↑((q : ℝ) - r) : ℂ)) *
        (2 * Real.pi * Complex.I * ξ) ^ q)‖ ≤ (2 * Real.pi * |ξ|) ^ r := by
  let x : ℝ := 2 * Real.pi * |ξ|
  let z : ℂ := (ε : ℂ) + (2 * Real.pi * ξ : ℝ) * Complex.I
  have hβ : 0 < (q : ℝ) - r := by exact_mod_cast (sub_pos.mpr hrq)
  have hz : z ≠ 0 := by
    intro h
    have hrz := congrArg Complex.re h
    simp [z, Complex.add_re] at hrz
    linarith
  have hx : 0 ≤ x := by positivity
  have hxle : x ≤ ‖z‖ := by
    have him := Complex.abs_im_le_norm z
    have him' : |(2 * Real.pi * ξ : ℝ)| ≤ ‖z‖ := by
      simpa [z, Complex.add_im] using him
    simpa [x, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] using him'
  have hβeq : (q : ℝ) = r + ((q : ℝ) - r) := by ring
  have hscalar : x ^ (q : ℝ) * ‖z‖ ^ (-((q : ℝ) - r)) ≤ x ^ r := by
    by_cases hξ : ξ = 0
    · have hqpos : 0 < (q : ℝ) := lt_trans hr hrq
      simp [x, hξ, Real.zero_rpow (ne_of_gt hqpos), Real.zero_rpow (ne_of_gt hr)]
    have hxpos : 0 < x := by
      dsimp [x]
      positivity
    have hypos : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [Real.rpow_neg (le_of_lt hypos)]
    rw [show (q : ℝ) = r + ((q : ℝ) - r) by ring,
      Real.rpow_add hxpos]
    rw [show r + ((q : ℝ) - r) - r = (q : ℝ) - r by ring]
    have hratio : x ^ ((q : ℝ) - r) / ‖z‖ ^ ((q : ℝ) - r) ≤ 1 :=
      (div_le_one (Real.rpow_pos_of_pos hypos _)).2
        (Real.rpow_le_rpow hx hxle (le_of_lt hβ))
    calc
      (x ^ r * x ^ ((q : ℝ) - r)) * (‖z‖ ^ ((q : ℝ) - r))⁻¹ =
          x ^ r * (x ^ ((q : ℝ) - r) / ‖z‖ ^ ((q : ℝ) - r)) := by
            rw [div_eq_mul_inv]
            ring
      _ ≤ x ^ r * 1 := mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hx r)
      _ = x ^ r := by ring
  have hnormz : ‖z ^ (-(↑((q : ℝ) - r) : ℂ))‖ =
      ‖z‖ ^ (-((q : ℝ) - r)) := by
    rw [Complex.norm_cpow_of_ne_zero hz]
    simp
  have hnormderiv : ‖(2 * Real.pi * Complex.I * ξ) ^ q‖ = x ^ (q : ℝ) := by
    rw [norm_pow]
    simp [x, norm_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  rw [norm_mul, hnormz, hnormderiv]
  simpa [x, mul_comm] using hscalar

open scoped ComplexInnerProductSpace

/-- Fourier transform of one directional derivative on the real line. -/
theorem fourier_lineDerivative_multiplier (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕 (∂_{(1:ℝ)} f)) ξ =
      (2 * Real.pi * Complex.I * ξ) * (𝓕 f) ξ := by
  have h := congrArg (fun g : 𝓢(ℝ, ℂ) => g ξ)
    (SchwartzMap.fourier_lineDerivOp_eq f (1:ℝ))
  rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply (by fun_prop)] at h
  simpa [innerSL_apply_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h

/-- Iterated integer derivatives contribute the expected integer-power
Fourier multiplier.  This is a genuine consequence of Mathlib's derivative
formula, rather than a multiplier identity supplied as an assumption. -/
def iteratedLineDerivative : ℕ → 𝓢(ℝ, ℂ) → 𝓢(ℝ, ℂ)
  | 0, f => f
  | q+1, f => ∂_{(1:ℝ)} (iteratedLineDerivative q f)

theorem fourier_iteratedLineDerivative_multiplier (q : ℕ)
    (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕 (iteratedLineDerivative q f)) ξ =
      (2 * Real.pi * Complex.I * ξ)^q * (𝓕 f) ξ := by
  induction q with
  | zero => simp [iteratedLineDerivative]
  | succ q ih =>
      change (𝓕 (∂_{(1:ℝ)} (iteratedLineDerivative q f))) ξ = _
      rw [fourier_lineDerivative_multiplier]
      rw [ih]
      simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]

end BrownianSharp.AlignmentPaperFractionalFourierMultiplier
