import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! Quantitative mean control for measurable CZ cells which contain a
positive-measure reserved core. This avoids assuming that a disjointified
enlarged ball has volume comparable to the original ball. -/
noncomputable section
open MeasureTheory
namespace BrownianSharp.External.WeakCZ

/-- A controlled integral over a cell and a positive-measure core inside it
bound the actual complex cell average. -/
theorem norm_cell_average_le_of_core
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℂ) {A E : Set α} (hAE : A ⊆ E)
    (hA : 0 < μ.real A) (_hInt : IntegrableOn f E μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : (∫ x in E, ‖f x‖ ∂μ) ≤ C * μ.real A) :
    ‖(μ.real E)⁻¹ • (∫ x in E, f x ∂μ)‖ ≤ C := by
  have hmeasure : μ.real A ≤ μ.real E :=
    measureReal_mono hAE (measure_ne_top μ E)
  have hE : 0 < μ.real E := hA.trans_le hmeasure
  have hn : ‖∫ x in E, f x ∂μ‖ ≤ C * μ.real E := by
    calc
      _ ≤ ∫ x in E, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
      _ ≤ C * μ.real A := hbound
      _ ≤ C * μ.real E := mul_le_mul_of_nonneg_left hmeasure hC
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hE]
  exact (inv_mul_le_iff₀ hE).2 (by simpa only [mul_comm] using hn)

end BrownianSharp.External.WeakCZ
