import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace BrownianSharp.AlignmentPeriodicP2BesovIdentity

/-- A single weighted block contributes exactly the square of its weighted
`L²` norm to the integrated square function. -/
theorem lintegral_weighted_block_sq_eq
    {α F : Type*} [MeasurableSpace α] [MeasurableSpace F] [NormedAddCommGroup F]
    [BorelSpace F]
    {μ : Measure α} (g : α → F) (w : ℝ) (hw : 0 ≤ w)
    (hg : AEStronglyMeasurable g μ) :
    (∫⁻ x, ENNReal.ofReal (w^2 * ‖g x‖^2) ∂μ) =
      (ENNReal.ofReal w * eLpNorm g 2 μ)^2 := by
  have hp := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : NNReal))
    (μ := μ) (by norm_num) hg
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at hp
  simp only [ENNReal.rpow_two] at hp
  have hpoint (x : α) :
      ENNReal.ofReal (w^2 * ‖g x‖^2) =
        ENNReal.ofReal w ^ 2 * ‖g x‖ₑ ^ 2 := by
    rw [ENNReal.ofReal_mul (sq_nonneg w), ENNReal.ofReal_pow hw,
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  calc
    _ = ∫⁻ x, ENNReal.ofReal w ^ 2 * ‖g x‖ₑ ^ 2 ∂μ := by
      apply lintegral_congr
      exact hpoint
    _ = ENNReal.ofReal w ^ 2 * ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
      rw [lintegral_const_mul'' _ (((hg.enorm).pow_const 2))]
    _ = ENNReal.ofReal w ^ 2 * (eLpNorm g 2 μ) ^ 2 := by
      exact congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal w ^ 2 * z) hp.symm
    _ = _ := by rw [mul_pow]

/-- Tonelli's theorem turns the `p=2` integrated dyadic square function into
the `theta=2` Besov sum. This is independent of how the block family was
constructed (in particular, it applies to any admissible cutoff resolution).
-/
theorem lintegral_tsum_weighted_block_sq_eq_tsum
    {α ι F : Type*} [MeasurableSpace α] [MeasurableSpace F] [Countable ι]
    [NormedAddCommGroup F] [BorelSpace F]
    (μ : Measure α) (g : ι → α → F) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i)
    (hg : ∀ i, AEStronglyMeasurable (g i) μ) :
    (∫⁻ x, ∑' i, ENNReal.ofReal (w i ^ 2 * ‖g i x‖ ^ 2) ∂μ) =
      ∑' i, (ENNReal.ofReal (w i) * eLpNorm (g i) 2 μ) ^ 2 := by
  rw [lintegral_tsum]
  · apply tsum_congr
    intro i
    exact lintegral_weighted_block_sq_eq (g i) (w i) (hw i) (hg i)
  · intro i
    have hn : AEMeasurable (fun x => ‖g i x‖) μ := (hg i).norm.aemeasurable
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_const.mul (hn.pow_const 2))

end BrownianSharp.AlignmentPeriodicP2BesovIdentity
