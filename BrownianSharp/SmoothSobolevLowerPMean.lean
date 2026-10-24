import BrownianSharp.SmoothBesovGeneralMean
import BrownianSharp.SmoothSobolevGaussianMean

/-! Jensen transfers the actual p=2 Sobolev energy estimate to exponents
`1 ≤ p ≤ 2` on the joint Gaussian-coefficient / normalized-torus probability
space. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.PeriodicCover

local instance instSmoothSobolevLowerPMeasureSpace : MeasureSpace UnitAddCircle :=
  AddCircle.measureSpace 1
local instance instSmoothSobolevLowerPCircleVolume :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  simpa using (inferInstance : IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Expected literal square-function energy for `1 ≤ p ≤ 2`, obtained by
Jensen from the actual p=2 block-series estimate. -/
theorem smoothSobolev_lowerP_expected_energy_le {d ι : ℕ}
    (p r : ℝ) (hp : 1 ≤ p) (hp2 : p < 2)
    (atoms : Fin ι → RealPeriodic d) (V : (Fin d → ℕ) → ℝ)
    (hV : ∀ s, 0 ≤ V s)
    (hvariance : ∀ (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)),
      (∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ≤ V s)
    {M : ℝ≥0∞}
    (hsummable : (∑' s : Fin d → ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
        (4 * V s * gaussianAbsoluteMoment 2))) ≤ M) :
    (∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
      (SmoothResolution.squareFunctionSquared r
        (gaussianSynthesis atoms z) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d)))
        ∂productStandardGaussian (Fin ι)) ≤ M ^ (p / 2) := by
  classical
  let μx := (volume : Measure (UnitAddTorus (Fin d)))
  let P := productStandardGaussian (Fin ι)
  let F : (Fin ι → ℝ) × UnitAddTorus (Fin d) → ℝ≥0∞ :=
    fun y => SmoothResolution.squareFunctionSquared r
      (gaussianSynthesis atoms y.1) y.2
  have hp2pos : 0 < p / 2 := by linarith
  have hp2lt : p / 2 < 1 := by linarith
  have hFmeas : Measurable F :=
    smoothSquare_gaussian_joint_measurable r atoms
  letI : IsProbabilityMeasure μx := by dsimp [μx]; infer_instance
  letI : IsProbabilityMeasure (P.prod μx) := inferInstance
  have hbase : (∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d), F y
      ∂P.prod μx) ≤ M := by
    have hprod := MeasureTheory.lintegral_prod (μ := P) (ν := μx)
      F hFmeas.aemeasurable
    have hmean := smoothSobolev_p2_expected_energy_le r atoms V hV
      hvariance hsummable
    calc
      (∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d), F y ∂P.prod μx)
          = ∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d), F (z,x) ∂μx ∂P :=
              hprod
      _ ≤ M := by simpa [F, P, μx] using hmean
  have hJensen := lintegral_rpow_le_rpow_lintegral_of_probability
    (μ := P.prod μx) F hp2pos hp2lt hFmeas.aemeasurable
  have htarget := MeasureTheory.lintegral_prod (μ := P) (ν := μx)
    (fun y : (Fin ι → ℝ) × UnitAddTorus (Fin d) => F y ^ (p / 2))
    (hFmeas.pow_const _).aemeasurable
  calc
    (∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
      (SmoothResolution.squareFunctionSquared r
        (gaussianSynthesis atoms z) x) ^ (p / 2) ∂μx ∂P)
        = ∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d),
          F y ^ (p / 2) ∂P.prod μx := by
            simpa [F, P, μx] using htarget.symm
    _ ≤ (∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d), F y ∂P.prod μx) ^ (p / 2) :=
          hJensen
    _ ≤ M ^ (p / 2) := ENNReal.rpow_le_rpow hbase (by positivity)

/-- Half-mass for the actual smooth Sobolev p-unit ball for `1 ≤ p < 2`,
from the p=2 variance budget and the explicit rescaled mean condition. -/
theorem smoothSobolev_lowerP_unitBall_mass {d ι : ℕ}
    (p r : ℝ) (hp : 1 ≤ p) (hp2 : p < 2)
    (atoms : Fin ι → RealPeriodic d) (V : (Fin d → ℕ) → ℝ)
    (hV : ∀ s, 0 ≤ V s)
    (hvariance : ∀ (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)),
      (∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ≤ V s)
    {M : ℝ≥0∞}
    (hsummable : (∑' s : Fin d → ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
        (4 * V s * gaussianAbsoluteMoment 2))) ≤ M)
    (hsmall : M ^ (p / 2) ≤ 1 / 2) :
    (1 / 2 : ℝ≥0∞) ≤ (productStandardGaussian (Fin ι))
      {z | SmoothResolution.SobolevUnitBall p r
        (gaussianSynthesis atoms z)} := by
  have hmean := smoothSobolev_lowerP_expected_energy_le p r hp hp2
    atoms V hV hvariance hsummable
  have hmean' : (∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
      (SmoothResolution.squareFunctionSquared r
        (gaussianSynthesis atoms z) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d)))
        ∂productStandardGaussian (Fin ι)) ≤ 1 / 2 :=
    hmean.trans hsmall
  have hmeas := smoothSobolevEnergy_gaussian_measurable p r atoms
  exact smoothSobolevUnitBall_mass_of_mean_le_half
    (productStandardGaussian (Fin ι)) p r
    (fun z => gaussianSynthesis atoms z) hmeas hmean'

end BrownianSharp
