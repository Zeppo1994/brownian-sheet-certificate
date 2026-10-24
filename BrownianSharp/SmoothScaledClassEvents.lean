import BrownianSharp.SmoothClassScaling

/-! Exact normalization of genuine smooth-class Gaussian energy events. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp
open Torus SmoothResolution

theorem smoothSobolev_scaled_unitBall_mass
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (p r : ℝ) (hp : 0 ≤ p) (Y : Ω → RealPeriodic d)
    {A : ℝ} (hA : 0 < A) {M : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hmeas : Measurable (fun ω => ∫⁻ x : UnitAddTorus (Fin d),
      (squareFunctionSquared r (Y ω) x)^(p/2)))
    (hmean : (∫⁻ ω, (∫⁻ x : UnitAddTorus (Fin d),
      (squareFunctionSquared r (Y ω) x)^(p/2)) ∂μ) ≤ M)
    (hscale : ENNReal.ofReal (A^p) * (2*M) ≤ 1) :
    (1/2:ℝ≥0∞) ≤ μ {ω | SobolevUnitBall p r (A • Y ω)} := by
  have hmass := smoothSobolevEnergy_sublevel_mass μ p r Y M hM hMtop hmeas hmean
  apply hmass.trans
  apply measure_mono
  intro ω hω
  change (∫⁻ x : UnitAddTorus (Fin d),
    (squareFunctionSquared r (A • Y ω) x)^(p/2)) ≤ 1
  rw [smoothSobolevEnergy_smul hA hp]
  exact (mul_le_mul_of_nonneg_left hω (by positivity : 0 ≤ ENNReal.ofReal (A^p))).trans hscale

theorem smoothBesov_scaled_unitBall_mass
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (p : ℝ≥0∞) (r : ℝ) {θ : ℝ≥0∞} (hθ : θ ≠ ∞)
    (Y : Ω → RealPeriodic d) {A : ℝ} (hA : 0 < A)
    {M : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hmeas : Measurable (fun ω => smoothBesovEnergy p r θ (Y ω)))
    (hmean : (∫⁻ ω, smoothBesovEnergy p r θ (Y ω) ∂μ) ≤ M)
    (hscale : ENNReal.ofReal (A^θ.toReal) * (2*M) ≤ 1) :
    (1/2:ℝ≥0∞) ≤ μ {ω | BesovUnitBall p r θ (A • Y ω)} := by
  have hmass := smoothBesovEnergy_sublevel_mass μ p r hθ Y M hM hMtop hmeas hmean
  apply hmass.trans
  apply measure_mono
  intro ω hω
  change BesovUnitBall p r θ (A • Y ω)
  rw [smoothBesovUnitBall_iff_energy_le_one p r hθ,
    smoothBesovEnergy_smul hA]
  exact (mul_le_mul_of_nonneg_left hω (by positivity : 0 ≤ ENNReal.ofReal (A^θ.toReal))).trans hscale

end BrownianSharp
