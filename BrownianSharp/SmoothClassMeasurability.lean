import BrownianSharp.AtomicBlockVariance
import BrownianSharp.SmoothClassEvents
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Prod

/-! Measurability of the literal smooth-resolution energies of a finite
Gaussian synthesis, including the infinite block sums. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BrownianSharp
open Torus PeriodicCover SmoothResolution

/-- Actual smooth blocks are jointly measurable in coefficients and position. -/
theorem smoothBlock_gaussian_joint_measurable {d ι : ℕ}
    (s : Fin d → ℕ) (atoms : Fin ι → RealPeriodic d) :
    Measurable (fun y : (Fin ι → ℝ) × UnitAddTorus (Fin d) =>
      block s (gaussianSynthesis atoms y.1) y.2) := by
  have heq : (fun y : (Fin ι → ℝ) × UnitAddTorus (Fin d) =>
      block s (gaussianSynthesis atoms y.1) y.2) =
      (fun y => ∑ i : Fin ι, (y.1 i : ℂ) * block s (atoms i) y.2) := by
    funext y
    exact AtomicBlockVariance.smoothBlock_gaussianSynthesis s atoms y.1 y.2
  rw [heq]
  fun_prop

/-- The exact infinite square function is jointly measurable. -/
theorem smoothSquare_gaussian_joint_measurable {d ι : ℕ}
    (r : ℝ) (atoms : Fin ι → RealPeriodic d) :
    Measurable (fun y : (Fin ι → ℝ) × UnitAddTorus (Fin d) =>
      squareFunctionSquared r (gaussianSynthesis atoms y.1) y.2) := by
  unfold squareFunctionSquared
  apply Measurable.tsum
  intro s
  exact ENNReal.measurable_ofReal.comp
    ((measurable_const.mul ((smoothBlock_gaussian_joint_measurable s atoms).norm.pow_const (2:ℕ))))

/-- The literal Sobolev energy is measurable for every real exponent. -/
theorem smoothSobolevEnergy_gaussian_measurable {d ι : ℕ}
    (p r : ℝ) (atoms : Fin ι → RealPeriodic d) :
    Measurable (fun z : Fin ι → ℝ =>
      ∫⁻ x : UnitAddTorus (Fin d),
        (squareFunctionSquared r (gaussianSynthesis atoms z) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d)))) := by
  apply Measurable.lintegral_prod_right
  exact (smoothSquare_gaussian_joint_measurable r atoms).pow_const _

/-- Every finite-exponent block Lp norm is a measurable coefficient function. -/
theorem smoothBlock_eLpNorm_gaussian_measurable {d ι : ℕ}
    (s : Fin d → ℕ) (atoms : Fin ι → RealPeriodic d)
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    Measurable (fun z : Fin ι → ℝ =>
      eLpNorm (fun x => block s (gaussianSynthesis atoms z) x) p
        (volume : Measure (UnitAddTorus (Fin d)))) := by
  have heq (z : Fin ι → ℝ) :
      eLpNorm (fun x => block s (gaussianSynthesis atoms z) x) p
        (volume : Measure (UnitAddTorus (Fin d))) =
      (∫⁻ x : UnitAddTorus (Fin d),
        ‖block s (gaussianSynthesis atoms z) x‖ₑ ^ p.toReal) ^ (1 / p.toReal) := by
    exact eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop
      (block s (gaussianSynthesis atoms z)).continuous.aestronglyMeasurable
  simp_rw [heq]
  apply Measurable.pow_const
  apply Measurable.lintegral_prod_right
  exact (smoothBlock_gaussian_joint_measurable s atoms).enorm.pow_const _

/-- The infinite literal finite-theta Besov energy is measurable. -/
theorem smoothBesovEnergy_gaussian_measurable {d ι : ℕ}
    (atoms : Fin ι → RealPeriodic d) (p : ℝ≥0∞)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (r : ℝ) (θ : ℝ≥0∞) :
    Measurable (fun z : Fin ι → ℝ =>
      smoothBesovEnergy p r θ (gaussianSynthesis atoms z)) := by
  unfold smoothBesovEnergy weightedBlockNorm
  apply Measurable.tsum
  intro s
  exact (measurable_const.mul
    (smoothBlock_eLpNorm_gaussian_measurable s atoms p hp0 hpTop)).pow_const _

end BrownianSharp
