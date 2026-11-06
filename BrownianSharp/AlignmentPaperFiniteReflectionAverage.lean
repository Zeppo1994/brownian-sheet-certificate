import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-! Finite measure-preserving symmetrization for Fourier integrals. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperFiniteReflectionAverage

/-- Source parity under finitely many measure-preserving maps identifies the
original integral with the averaged reflected phase. The hypotheses concern
actual integrability and actual maps, not the desired coefficient identity. -/
theorem integral_eq_finite_reflection_average
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    (A : Finset ι) (hA : A.Nonempty)
    (σ : ι → α → α) (χ : ι → ℂ) (F phase : α → ℂ)
    (hMP : ∀ i ∈ A, MeasurePreserving (σ i) μ μ)
    (hparity : ∀ i ∈ A, (fun x => F (σ i x)) =ᵐ[μ] fun x => χ i * F x)
    (hInt : Integrable (fun x => F x * phase x) μ)
    (hIntRef : ∀ i ∈ A, Integrable (fun x => F x * phase (σ i x)) μ) :
    (∫ x, F x * phase x ∂μ) = (A.card : ℂ)⁻¹ *
      ∫ x, F x * (∑ i ∈ A, χ i * phase (σ i x)) ∂μ := by
  classical
  have hterm (i : ι) (hi : i ∈ A) :
      (∫ x, F x * phase x ∂μ) = χ i * ∫ x, F x * phase (σ i x) ∂μ := by
    have hmapMeas : AEStronglyMeasurable (fun x => F x * phase x)
        (μ.map (σ i)) := by
      rw [(hMP i hi).map_eq]
      exact hInt.aestronglyMeasurable
    have hmap := integral_map (hMP i hi).measurable.aemeasurable hmapMeas
    rw [(hMP i hi).map_eq] at hmap
    calc
      (∫ x, F x * phase x ∂μ) = ∫ x, F (σ i x) * phase (σ i x) ∂μ := hmap
      _ = ∫ x, χ i * (F x * phase (σ i x)) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hparity i hi] with x hx
        rw [hx]
        ring
      _ = _ := integral_const_mul _ _
  have hsum : (∫ x, F x * (∑ i ∈ A, χ i * phase (σ i x)) ∂μ) =
      (A.card : ℂ) * (∫ x, F x * phase x ∂μ) := by
    have hfun : (fun x => F x * (∑ i ∈ A, χ i * phase (σ i x))) =
        fun x => ∑ i ∈ A, χ i * (F x * phase (σ i x)) := by
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hfun,integral_finset_sum A (fun i hi => (hIntRef i hi).const_mul (χ i))]
    simp_rw [integral_const_mul]
    calc
      (∑ i ∈ A, χ i * ∫ x, F x * phase (σ i x) ∂μ) =
          ∑ _i ∈ A, (∫ x, F x * phase x ∂μ) :=
        Finset.sum_congr rfl (fun i hi => (hterm i hi).symm)
      _ = _ := by simp
  have hcard : (A.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hA).ne'
  rw [hsum,← mul_assoc,inv_mul_cancel₀ hcard,one_mul]

end BrownianSharp.AlignmentPaperFiniteReflectionAverage
