import Mathlib.MeasureTheory.Integral.Average

/-! Basic L¹ facts for Calderón–Zygmund bad pieces defined using set averages.

The estimates include null cells without a separate positive-measure
hypothesis: the normalized set average is defined by Mathlib on every set.
-/

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

namespace BrownianSharp.External.WeakCZ

/-- The bad part of `f` on a measurable cell `E`, formed with its set average. -/
def badPiece {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (E : Set α) (f : α → ℂ) : α → ℂ :=
  E.indicator (fun x => f x - ⨍ y in E, f y ∂μ)

theorem integrable_badPiece {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (E : Set α) (f : α → ℂ)
    (hE : MeasurableSet E) (hf : Integrable f μ) :
    Integrable (badPiece μ E f) μ := by
  apply (integrable_indicator_iff hE).2
  exact (hf.sub (integrable_const _)).integrableOn

theorem integral_badPiece_eq_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (E : Set α) (f : α → ℂ)
    (hE : MeasurableSet E) (_hf : Integrable f μ) :
    ∫ x, badPiece μ E f x ∂μ = 0 := by
  rw [badPiece, integral_indicator hE]
  exact setAverage_sub_setAverage (measure_ne_top μ E) f

theorem lintegral_enorm_badPiece_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (E : Set α) (f : α → ℂ)
    (hE : MeasurableSet E) (hf : Integrable f μ) :
    ∫⁻ x, ‖badPiece μ E f x‖ₑ ∂μ ≤
      2 * ∫⁻ x in E, ‖f x‖ₑ ∂μ := by
  let avg : ℂ := ⨍ y in E, f y ∂μ
  let avgNorm : ℝ := ⨍ y in E, ‖f y‖ ∂μ
  have havg : ‖avg‖ ≤ avgNorm := by
    dsimp [avg, avgNorm]
    rw [setAverage_eq', setAverage_eq']
    exact norm_integral_le_integral_norm _
  have hmass : ‖avg‖ * μ.real E ≤ ∫ x in E, ‖f x‖ ∂μ := by
    calc
      ‖avg‖ * μ.real E ≤ avgNorm * μ.real E :=
        mul_le_mul_of_nonneg_right havg (measureReal_nonneg)
      _ = ∫ x in E, ‖f x‖ ∂μ := by
        simpa [avgNorm, smul_eq_mul, mul_comm] using
          (measure_smul_setAverage (μ := μ) (f := fun x => ‖f x‖)
            (measure_ne_top μ E))
  have hfr : Integrable f (μ.restrict E) :=
    hf.mono_measure Measure.restrict_le_self
  have hnorm :
      ∫⁻ x in E, ‖f x‖ₑ ∂μ = ENNReal.ofReal (∫ x in E, ‖f x‖ ∂μ) :=
    (ofReal_integral_norm_eq_lintegral_enorm hfr).symm
  have havgTerm : ‖avg‖ₑ * μ E = ENNReal.ofReal (‖avg‖ * μ.real E) := by
    rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq, coe_nnnorm,
      ENNReal.ofReal_mul (norm_nonneg _),
      ofReal_measureReal (measure_ne_top μ E)]
  have havgBound : ‖avg‖ₑ * μ E ≤ ∫⁻ x in E, ‖f x‖ₑ ∂μ := by
    rw [havgTerm]
    calc
      ENNReal.ofReal (‖avg‖ * μ.real E) ≤
          ENNReal.ofReal (∫ x in E, ‖f x‖ ∂μ) :=
        ENNReal.ofReal_le_ofReal hmass
      _ = ∫⁻ x in E, ‖f x‖ₑ ∂μ := hnorm.symm
  have hpoint : ∀ x, ‖f x - avg‖ₑ ≤ ‖f x‖ₑ + ‖avg‖ₑ := by
    intro x
    exact enorm_sub_le
  calc
    ∫⁻ x, ‖badPiece μ E f x‖ₑ ∂μ
        = ∫⁻ x in E, ‖f x - avg‖ₑ ∂μ := by
          calc
            _ = ∫⁻ x, E.indicator (fun x => ‖f x - avg‖ₑ) x ∂μ := by
              congr 1
              funext x
              simp [badPiece, avg, enorm_indicator_eq_indicator_enorm]
            _ = _ := by rw [lintegral_indicator hE]
    _ ≤ ∫⁻ x in E, ‖f x‖ₑ + ‖avg‖ₑ ∂μ := by
          apply lintegral_mono
          intro x
          exact hpoint x
    _ = (∫⁻ x in E, ‖f x‖ₑ ∂μ) + ‖avg‖ₑ * μ E := by
          calc
            _ = ∫⁻ x, ‖avg‖ₑ + ‖f x‖ₑ ∂(μ.restrict E) := by
              congr 1
              funext x
              exact add_comm _ _
            _ = _ := by
              rw [lintegral_add_left measurable_const]
              simp [lintegral_const, add_comm]
    _ ≤ (∫⁻ x in E, ‖f x‖ₑ ∂μ) + ∫⁻ x in E, ‖f x‖ₑ ∂μ := by
          exact add_le_add (le_of_eq rfl) havgBound
    _ = 2 * ∫⁻ x in E, ‖f x‖ₑ ∂μ := by ring

theorem tsum_lintegral_enorm_badPiece_le {α ι : Type*}
    [MeasurableSpace α] [Countable ι]
    (μ : Measure α) [IsFiniteMeasure μ] (E : ι → Set α) (f : α → ℂ)
    (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j)) (hf : Integrable f μ) :
    ∑' i, ∫⁻ x, ‖badPiece μ (E i) f x‖ₑ ∂μ ≤
      2 * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  calc
    ∑' i, ∫⁻ x, ‖badPiece μ (E i) f x‖ₑ ∂μ
        ≤ ∑' i, 2 * ∫⁻ x in E i, ‖f x‖ₑ ∂μ :=
          ENNReal.tsum_le_tsum fun i => lintegral_enorm_badPiece_le μ (E i) f (hE i) hf
    _ = 2 * ∑' i, ∫⁻ x in E i, ‖f x‖ₑ ∂μ := ENNReal.tsum_mul_left
    _ = 2 * ∫⁻ x in ⋃ i, E i, ‖f x‖ₑ ∂μ := by
          rw [lintegral_iUnion hE hdisj]
    _ ≤ 2 * ∫⁻ x, ‖f x‖ₑ ∂μ := by
          gcongr
          exact Measure.restrict_le_self

end BrownianSharp.External.WeakCZ
