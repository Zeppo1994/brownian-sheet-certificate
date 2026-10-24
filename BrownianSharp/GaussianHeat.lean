import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic
import BrownianSharp.GaussianHeatDef

/-!
# Gaussian heat-flow calculus

This module starts with the real Gaussian integration-by-parts identity needed
for the heat semigroup proof of Ehrhard interpolation.  The test function is
compactly supported, so the boundary term vanishes without a tail assumption.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace BrownianSharp

/-- The absolute first moment is integrable under the standard real Gaussian.
This follows from the exponential-moment neighborhood at zero. -/
theorem integrable_abs_id_standardGaussian :
    Integrable (fun x : ℝ => |x|) (ProbabilityTheory.gaussianReal 0 1) := by
  have hzero : (0 : ℝ) ∈ interior
      (integrableExpSet id (ProbabilityTheory.gaussianReal 0 1)) := by
    rw [ProbabilityTheory.integrableExpSet_id_gaussianReal]
    simp
  have hid : Integrable (fun x : ℝ => x) (ProbabilityTheory.gaussianReal 0 1) := by
    have h := integrable_pow_of_mem_interior_integrableExpSet hzero 1
    simpa using h
  simpa [id] using hid.abs

private noncomputable def heatStdPdf (x : ℝ) : ℝ :=
  ProbabilityTheory.gaussianPDFReal 0 1 x

private theorem hasDerivAt_heatStdPdf (x : ℝ) :
    HasDerivAt heatStdPdf (-x * heatStdPdf x) x := by
  rw [heatStdPdf, ProbabilityTheory.gaussianPDFReal_def]
  have hquad : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    convert ((hasDerivAt_id x).pow 2).const_mul (-1 / 2 : ℝ) using 1
    · ext y
      simp
      ring
    · simp
      ring
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(y ^ 2) / 2))
      (Real.exp (-(x ^ 2) / 2) * -x) x := by
    convert (Real.hasDerivAt_exp (-(x ^ 2) / 2)).comp x hquad using 1
    · ext y
      simp
  convert hexp.const_mul ((Real.sqrt (2 * Real.pi))⁻¹) using 1
  · ext y
    simp [heatStdPdf, ProbabilityTheory.gaussianPDFReal_def]
  · simp
    ring

/-- Gaussian integration by parts for a continuously differentiable compactly
supported scalar test function. -/
theorem integral_id_mul_gaussian_eq_integral_deriv_gaussian
    {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) :
    (∫ x, x * f x ∂ProbabilityTheory.gaussianReal 0 1) =
      ∫ x, deriv f x ∂ProbabilityTheory.gaussianReal 0 1 := by
  have hfdc : HasCompactSupport (deriv f) := hfc.deriv
  have hpdfc : Continuous heatStdPdf := by
    change Continuous (ProbabilityTheory.gaussianPDFReal 0 1)
    rw [ProbabilityTheory.gaussianPDFReal_def]
    fun_prop
  have hpdfd : Continuous (fun x => deriv heatStdPdf x) := by
    have h : ContDiff ℝ 1 heatStdPdf := by
      change ContDiff ℝ 1 (ProbabilityTheory.gaussianPDFReal 0 1)
      rw [ProbabilityTheory.gaussianPDFReal_def]
      fun_prop
    exact h.continuous_deriv le_rfl
  have hfc_pdf : HasCompactSupport (fun x => f x * heatStdPdf x) :=
    hfc.mul_right
  have hf'_pdf : HasCompactSupport (fun x => deriv f x * heatStdPdf x) :=
    hfdc.mul_right
  have hf_pdf' : HasCompactSupport (fun x => f x * deriv heatStdPdf x) :=
    hfc.mul_right
  have hi1 : Integrable (fun x => deriv f x * heatStdPdf x) :=
    (hf.continuous_deriv le_rfl).mul hpdfc |>.integrable_of_hasCompactSupport hf'_pdf
  have hi2 : Integrable (fun x => f x * deriv heatStdPdf x) :=
    hf.continuous.mul hpdfd |>.integrable_of_hasCompactSupport hf_pdf'
  have hi3 : Integrable (fun x => f x * heatStdPdf x) :=
    hf.continuous.mul hpdfc |>.integrable_of_hasCompactSupport hfc_pdf
  have hiparts := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
      (u := f) (u' := deriv f) (v := heatStdPdf) (v' := deriv heatStdPdf)
      (fun x _ => (hf.differentiable one_ne_zero x).hasDerivAt)
      (fun x _ => (show ContDiff ℝ 1 heatStdPdf by
        change ContDiff ℝ 1 (ProbabilityTheory.gaussianPDFReal 0 1)
        rw [ProbabilityTheory.gaussianPDFReal_def]
        fun_prop).differentiable one_ne_zero x |>.hasDerivAt)
      hi2 hi1 hi3
  have hderivpdf (x : ℝ) : deriv heatStdPdf x = -x * heatStdPdf x :=
    (hasDerivAt_heatStdPdf x).deriv
  have hmeasure : (∫ x, x * f x ∂ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) =
      ∫ x, heatStdPdf x * (x * f x) := by
    simpa [heatStdPdf, smul_eq_mul] using
      (ProbabilityTheory.integral_gaussianReal_eq_integral_smul
        (μ := (0 : ℝ)) (v := (1 : NNReal)) (f := fun x => x * f x)
        (show (1 : NNReal) ≠ 0 by norm_num))
  have hmeasure' : (∫ x, deriv f x ∂ProbabilityTheory.gaussianReal (0 : ℝ) (1 : NNReal)) =
      ∫ x, heatStdPdf x * deriv f x := by
    simpa [heatStdPdf, smul_eq_mul] using
      (ProbabilityTheory.integral_gaussianReal_eq_integral_smul
        (μ := (0 : ℝ)) (v := (1 : NNReal)) (f := deriv f)
        (show (1 : NNReal) ≠ 0 by norm_num))
  rw [hmeasure, hmeasure']
  calc
    ∫ x, heatStdPdf x * (x * f x) = ∫ x, x * f x * heatStdPdf x := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ =
        - ∫ x, f x * deriv heatStdPdf x := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      rw [hderivpdf]
      ring
    _ = ∫ x, deriv f x * heatStdPdf x := by
      rw [hiparts]
      ring
    _ = ∫ x, heatStdPdf x * deriv f x := by
      apply integral_congr_ae
      filter_upwards with x
      ring

/-- Directional differentiation of finite-dimensional Gaussian heat averaging.
For a constant plus smooth compactly supported perturbation the two global
bounds are automatic. This form keeps the parameter scalar and works in every
finite-dimensional product space without choosing a basis. -/
theorem hasDerivAt_gaussianHeat_directional_of_bounded_deriv
    {κ : Type*} [Fintype κ] (q : (κ → ℝ) → ℝ) (t : ℝ)
    (x₀ v : κ → ℝ) (hq : ContDiff ℝ 1 q)
    (hq_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖q y‖ ≤ C)
    (hderiv_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ q y‖ ≤ C) :
    HasDerivAt (fun s : ℝ => gaussianHeat q t (x₀ + s • v))
      (∫ z, fderiv ℝ q (x₀ + Real.sqrt t • z) v ∂productStandardGaussian κ) 0 := by
  let μ := productStandardGaussian κ
  let F : ℝ → (κ → ℝ) → ℝ := fun s z => q (x₀ + s • v + Real.sqrt t • z)
  let F' : ℝ → (κ → ℝ) → ℝ := fun s z =>
    fderiv ℝ q (x₀ + s • v + Real.sqrt t • z) v
  obtain ⟨Cq, hCq0, hCq⟩ := hq_bound
  obtain ⟨Cd, hCd0, hCd⟩ := hderiv_bound
  have hF_meas : ∀ᶠ s in 𝓝 (0 : ℝ), AEStronglyMeasurable (F s) μ := by
    filter_upwards [] with s
    change AEStronglyMeasurable (fun z => q (x₀ + s • v + Real.sqrt t • z)) μ
    have hmap : Continuous (fun z : κ → ℝ => x₀ + s • v + Real.sqrt t • z) := by fun_prop
    exact ((hq.continuous.comp hmap).measurable).aestronglyMeasurable (μ := μ)
  have hF_int : Integrable (F (0 : ℝ)) μ := by
    apply (integrable_const Cq).mono'
    · change AEStronglyMeasurable (fun z => q (x₀ + (0 : ℝ) • v + Real.sqrt t • z)) μ
      have hmap : Continuous (fun z : κ → ℝ => x₀ + (0 : ℝ) • v + Real.sqrt t • z) := by fun_prop
      simpa only [Function.comp_def] using
        (((hq.continuous.comp hmap).measurable).aestronglyMeasurable (μ := μ))
    · filter_upwards [] with z
      simpa [F, zero_smul] using hCq (x₀ + Real.sqrt t • z)
  have hF'_meas : AEStronglyMeasurable (F' (0 : ℝ)) μ := by
    change AEStronglyMeasurable
      (fun z => fderiv ℝ q (x₀ + (0 : ℝ) • v + Real.sqrt t • z) v) μ
    have hmap : Continuous (fun z : κ → ℝ => x₀ + (0 : ℝ) • v + Real.sqrt t • z) := by fun_prop
    have hd : Continuous (fun z : κ → ℝ => fderiv ℝ q (x₀ + (0 : ℝ) • v + Real.sqrt t • z) v) :=
      (ContinuousLinearMap.apply ℝ ℝ v).continuous.comp
        ((hq.continuous_fderiv one_ne_zero).comp hmap)
    exact hd.measurable.aestronglyMeasurable (μ := μ)
  have hbound : ∀ᵐ z ∂μ, ∀ s ∈ Set.univ, ‖F' s z‖ ≤ Cd * ‖v‖ := by
    filter_upwards [] with z
    intro s hs
    calc
      ‖F' s z‖ ≤ ‖fderiv ℝ q (x₀ + s • v + Real.sqrt t • z)‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ Cd * ‖v‖ := mul_le_mul_of_nonneg_right
        (hCd _) (norm_nonneg _)
  have hbound_int : Integrable (fun _ : κ → ℝ => Cd * ‖v‖) μ := integrable_const _
  have hdiff : ∀ᵐ z ∂μ, ∀ s ∈ Set.univ, HasDerivAt (F · z) (F' s z) s := by
    filter_upwards [] with z
    intro s hs
    have hlinear := (hasDerivAt_id s).smul_const v
    have hline : HasDerivAt (fun r : ℝ => x₀ + r • v + Real.sqrt t • z) v s := by
      simpa [one_smul] using hlinear.const_add x₀ |>.add_const (Real.sqrt t • z)
    have hq' := (hq.differentiable one_ne_zero
      (x₀ + s • v + Real.sqrt t • z)).hasFDerivAt
    have hcomp := hq'.comp_hasDerivAt s hline
    simpa only [F, F', Function.comp_def] using hcomp
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.univ) (x₀ := (0 : ℝ)) (F := F) (F' := F')
    (bound := fun _ => Cd * ‖v‖)
    (show Set.univ ∈ 𝓝 (0 : ℝ) by exact Filter.univ_mem)
    hF_meas hF_int hF'_meas hbound hbound_int hdiff
  simpa [gaussianHeat, μ, F, F'] using h.2


end BrownianSharp
