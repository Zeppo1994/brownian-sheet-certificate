import Mathlib.MeasureTheory.Integral.Prod

/-!
A small, source-attributed integrated bad-part estimate for the periodic
weak-(1,1) route.

The proof pattern is the cancellation/Fubini step in
`fpvandoorn/carleson`, `Carleson/TwoSidedCarleson/WeakCalderonZygmund.lean`,
revision `f10c441921273ee2a04cea802f2c32b7c6ebc5ea` (Apache-2.0; see
`LICENSE` beside this file). This file is an independent Lean proof of the
integrated estimate and does not import the upstream package or its
pointwise-kernel / truncated-operator hypotheses.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace BrownianSharp.External.WeakCZ

/-- A zero-mean input cancels the constant kernel value at its center. -/
theorem integral_kernel_difference_eq_of_zeroMean
    {β : Type*} [MeasurableSpace β] (ν : Measure β)
    (K b : β → ℂ) (c : ℂ)
    (hK : Integrable (fun y => K y * b y) ν)
    (hK₀ : Integrable (fun y => c * b y) ν)
    (hmean : ∫ y, b y ∂ν = 0) :
    ∫ y, (K y - c) * b y ∂ν = ∫ y, K y * b y ∂ν := by
  calc
    ∫ y, (K y - c) * b y ∂ν
        = ∫ y, (K y * b y - c * b y) ∂ν := by
            congr 1
            funext y
            ring
    _ = (∫ y, K y * b y ∂ν) - (∫ y, c * b y ∂ν) := integral_sub hK hK₀
    _ = (∫ y, K y * b y ∂ν) - c * (∫ y, b y ∂ν) := by
          rw [integral_const_mul]
    _ = ∫ y, K y * b y ∂ν := by rw [hmean, mul_zero, sub_zero]

/-- Restrict a real integral majorant to a measurable exceptional region and
convert it to the ENNReal norm integral used by the cancellation estimate. -/
theorem lintegral_restrict_enorm_le_of_real_majorant
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    (μ : Measure α) (s : Set α) (f : α → E) (g : α → ℝ) (C : ℝ)
    (hs : MeasurableSet s) (hf : Integrable f μ) (hg : Integrable g μ)
    (hg₀ : 0 ≤ᵐ[μ] g)
    (hpoint : ∀ x ∈ s, ‖f x‖ ≤ g x)
    (hbound : ∫ x, g x ∂μ ≤ C) :
    ∫⁻ x, ‖f x‖ₑ ∂(μ.restrict s) ≤ ENNReal.ofReal C := by
  have hfr : Integrable f (μ.restrict s) := hf.mono_measure Measure.restrict_le_self
  have hgr : Integrable g (μ.restrict s) := hg.mono_measure Measure.restrict_le_self
  calc
    ∫⁻ x, ‖f x‖ₑ ∂(μ.restrict s)
        = ENNReal.ofReal (∫ x, ‖f x‖ ∂(μ.restrict s)) :=
          (ofReal_integral_norm_eq_lintegral_enorm hfr).symm
    _ ≤ ENNReal.ofReal (∫ x, g x ∂(μ.restrict s)) := by
      apply ENNReal.ofReal_le_ofReal
      apply integral_mono_ae hfr.norm hgr
      filter_upwards [ae_restrict_mem hs] with x hx
      exact hpoint x hx
    _ ≤ ENNReal.ofReal (∫ x, g x ∂μ) := by
      apply ENNReal.ofReal_le_ofReal
      exact integral_mono_measure (μ := μ.restrict s) Measure.restrict_le_self hg₀ hg
    _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hbound

end BrownianSharp.External.WeakCZ
