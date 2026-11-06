import BrownianSharp.AlignmentPaperFiniteKernelLpDensity
import BrownianSharp.AlignmentPaperProductSquareFunctionLp

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace BrownianSharp.AlignmentPaperProductSquareFunctionLpDensity

open BrownianSharp.AlignmentPaperFiniteKernelLpDensity
open BrownianSharp.AlignmentPaperProductSquareFunctionLp
open BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.Torus
open UnitAddTorus

local instance productDensityMeasureSpace (d : ℕ) : MeasureSpace (UnitAddTorus (Fin d)) :=
  ⟨Measure.pi fun _ : Fin d => AddCircle.haarAddCircle⟩
local instance productDensityProbability (d : ℕ) :
    IsProbabilityMeasure
      (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
  infer_instance

def productBlockIntegralKernel {d : ℕ} (s : Fin d → ℕ) :
    C(UnitAddTorus (Fin d) × UnitAddTorus (Fin d), ℂ) :=
  ⟨fun q => admissibleBlockKernel smoothResolutionCutoff s (q.1-q.2), by fun_prop⟩

theorem applyKernel_productBlockIntegralKernel {d : ℕ} (s : Fin d → ℕ)
    (f : UnitAddTorus (Fin d) → ℂ) (x : UnitAddTorus (Fin d)) :
    applyKernel (μ := Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
        (productBlockIntegralKernel s) f x = productSmoothBlockConvolution s f x := by
  simp [applyKernel, productBlockIntegralKernel, productSmoothBlockConvolution]

/-- The actual finite product smooth-block square function is bounded for every
Lp source, with a constant independent of the finite block depth. -/
theorem productSmoothSquareFunction_lintegral_lp_le_of_memLp
    (N d : ℕ) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : Lp ℂ (ENNReal.ofReal p)
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) :
    (∫⁻ x : UnitAddTorus (Fin d),
      ENNReal.ofReal ((∑ s : Fin d → Fin (N+1),
        ‖productSmoothBlockConvolution (fun i => (s i).val) (f : _ → ℂ) x‖^2)^(p/2))
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      ENNReal.ofReal (((24*(2:ℝ)^(p/2))^2 *
        (2^p*(p*BrownianSharp.AlignmentPaperSignedKernelLp.uniformSignedKernelWeakConstant/
          (p-1)+p/(2-p))))^d) *
      ∫⁻ x : UnitAddTorus (Fin d), ENNReal.ofReal (‖f x‖^p)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  classical
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  let ι := Fin d → Fin (N+1)
  let K : ι → C(UnitAddTorus (Fin d) × UnitAddTorus (Fin d),ℂ) :=
    fun s => productBlockIntegralKernel (fun i => (s i).val)
  let C : ℝ := (24*(2:ℝ)^(p/2))^2 *
    (2^p*(p*BrownianSharp.AlignmentPaperSignedKernelLp.uniformSignedKernelWeakConstant/
      (p-1)+p/(2-p)))
  let Γ : ℝ≥0∞ := ENNReal.ofReal (C^d)
  have hp0 : 0 < p := by linarith
  haveI : Fact ((1:ℝ≥0∞) ≤ ENNReal.ofReal p) :=
    ⟨by simpa using ENNReal.ofReal_le_ofReal (by linarith : 1 ≤ p)⟩
  have hcont : ∀ g : C(UnitAddTorus (Fin d),ℂ),
      (∫⁻ x, ENNReal.ofReal
        ((∑ s : ι, ‖applyKernel (μ := μ) (K s) g x‖^2)^(p/2)) ∂μ) ≤
      Γ * ∫⁻ x, ENNReal.ofReal (‖g x‖^p) ∂μ := by
    intro g
    have h := productSmoothSquareFunction_lintegral_lp_le N d hp1 hp2 g
    simpa [μ, K, Γ, C, applyKernel_productBlockIntegralKernel,
      productSmoothSquareFunction, productSmoothBlockConvolution] using h
  have hΓ : Γ ≠ ∞ := by simp [Γ]
  have h := finiteKernel_moment_le_of_continuous
    (α := UnitAddTorus (Fin d)) (μ := μ) (K := K) (p := p)
    hp0 (by linarith : 1 ≤ p) hΓ hcont f
  simpa [μ, K, Γ, C, applyKernel_productBlockIntegralKernel] using h

end BrownianSharp.AlignmentPaperProductSquareFunctionLpDensity
