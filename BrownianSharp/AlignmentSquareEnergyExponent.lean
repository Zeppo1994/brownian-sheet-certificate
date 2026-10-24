import BrownianSharp.SmoothBesovGeneralMean

/-! Probability-space exponent inclusion for square-function unit balls. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentSquareEnergyExponent

theorem unit_rpow_energy_mono
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (S : X → ℝ≥0∞) (hS : AEMeasurable S μ)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hq : (∫⁻ x, S x ^ q ∂μ) ≤ 1) :
    (∫⁻ x, S x ^ p ∂μ) ≤ 1 := by
  rcases eq_or_lt_of_le hpq with heq | hlt
  · simpa [heq] using hq
  have hqpos : 0 < q := lt_of_lt_of_le hp hpq
  have ha0 : 0 < p / q := div_pos hp hqpos
  have ha1 : p / q < 1 := (div_lt_one hqpos).2 hlt
  have hJ := BrownianSharp.lintegral_rpow_le_rpow_lintegral_of_probability
    (μ := μ) (fun x => S x ^ q) ha0 ha1 (hS.pow_const q)
  have hpower (x : X) : (S x ^ q) ^ (p / q) = S x ^ p := by
    rw [← ENNReal.rpow_mul]
    congr 1
    field_simp
  calc
    (∫⁻ x, S x ^ p ∂μ) =
        ∫⁻ x, (S x ^ q) ^ (p / q) ∂μ := by simp only [hpower]
    _ ≤ (∫⁻ x, S x ^ q ∂μ) ^ (p / q) := hJ
    _ ≤ 1 ^ (p / q) := ENNReal.rpow_le_rpow hq ha0.le
    _ = 1 := ENNReal.one_rpow _

theorem squareFunction_unit_energy_mono
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (S : X → ℝ≥0∞) (hS : AEMeasurable S μ)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q)
    (hq : (∫⁻ x, S x ^ (q / 2) ∂μ) ≤ 1) :
    (∫⁻ x, S x ^ (p / 2) ∂μ) ≤ 1 :=
  unit_rpow_energy_mono S hS (by positivity) (by linarith) hq

end BrownianSharp.AlignmentSquareEnergyExponent
