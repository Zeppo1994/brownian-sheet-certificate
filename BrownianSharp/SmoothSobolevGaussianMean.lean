import BrownianSharp.SmoothGaussianLp
import BrownianSharp.SmoothClassEvents
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-! Expected literal square-function energy for the actual Gaussian smooth
resolution. The first theorem treats the manuscript's Sobolev exponent `p=2`;
it uses the actual dyadic block series and only assumes a deterministic
per-block coefficient-variance envelope plus its weighted summability. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.PeriodicCover

private def smoothSquareTerm {d ι : ℕ} (r : ℝ)
    (atoms : Fin ι → RealPeriodic d) (s : Fin d → ℕ)
    (z : Fin ι → ℝ) (x : UnitAddTorus (Fin d)) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
    ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ 2)

/-- For the actual finite Gaussian smooth synthesis, the expected literal
Sobolev square-function energy with exponent two is bounded by the sum of the
weighted actual block-variance estimates. The theorem is conditional only on
the explicit coefficient-variance envelope and weighted summability; no
independence of the smooth blocks is used. -/
theorem smoothSobolev_p2_expected_energy_le {d ι : ℕ}
    (r : ℝ) (atoms : Fin ι → RealPeriodic d) (V : (Fin d → ℕ) → ℝ)
    (hV : ∀ s, 0 ≤ V s)
    (hvariance : ∀ (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)),
      (∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ≤ V s)
    {M : ℝ≥0∞}
    (hsummable : (∑' s : Fin d → ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
        (4 * V s * gaussianAbsoluteMoment 2))) ≤ M) :
    (∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
      (SmoothResolution.squareFunctionSquared r
        (gaussianSynthesis atoms z) x) ^ (2 / 2 : ℝ)
        ∂(volume : Measure (UnitAddTorus (Fin d)))
        ∂productStandardGaussian (Fin ι)) ≤ M := by
  classical
  let μx := (volume : Measure (UnitAddTorus (Fin d)))
  let P := productStandardGaussian (Fin ι)
  let T : (Fin d → ℕ) → (Fin ι → ℝ) × UnitAddTorus (Fin d) → ℝ≥0∞ :=
    fun s y => smoothSquareTerm r atoms s y.1 y.2
  have hTmeas (s : Fin d → ℕ) :
      Measurable (T s) := by
    have hrepr : T s = fun y => ENNReal.ofReal
        ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
          ‖∑ i : Fin ι, (y.1 i : ℂ) *
            SmoothResolution.block s (atoms i) y.2‖ ^ 2) := by
      funext y
      dsimp [T, smoothSquareTerm]
      rw [AtomicBlockVariance.smoothBlock_gaussianSynthesis]
    rw [hrepr]
    fun_prop (disch := positivity)
  let F : (Fin ι → ℝ) × UnitAddTorus (Fin d) → ℝ≥0∞ :=
    fun y => ∑' s : Fin d → ℕ, T s y
  have hFmeas : Measurable F := by
    exact Measurable.tsum hTmeas
  have hF_eq (z : Fin ι → ℝ) (x : UnitAddTorus (Fin d)) :
      F (z, x) = SmoothResolution.squareFunctionSquared r
        (gaussianSynthesis atoms z) x := by
    simp [F, T, smoothSquareTerm, SmoothResolution.squareFunctionSquared]
  have hproduct := MeasureTheory.lintegral_prod (μ := P) (ν := μx)
    F hFmeas.aemeasurable
  have htsum := MeasureTheory.lintegral_tsum
    (μ := P.prod μx) (fun s => (hTmeas s).aemeasurable)
  have hseries :
      (∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d), F y ∂P.prod μx) =
        ∑' s : Fin d → ℕ,
          ∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d), T s y ∂P.prod μx := by
    change (∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d),
      (∑' s : Fin d → ℕ, T s y) ∂P.prod μx) = _
    exact htsum
  have hterm (s : Fin d → ℕ) :
      (∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d), T s y ∂P.prod μx) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
          (4 * V s * gaussianAbsoluteMoment 2)) := by
    have hbase := smoothBlock_gaussian_spatialEnergy_le s atoms
      (p := 2) (V := V s) (by norm_num) (hV s) (hvariance s)
    have hweight : 0 ≤ (2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) := by positivity
    have hmul : ∀ z x,
        ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
          ‖SmoothResolution.block s (gaussianSynthesis atoms z) x‖ ^ 2) =
        ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ))) *
          ENNReal.ofReal (‖SmoothResolution.block s
            (gaussianSynthesis atoms z) x‖ ^ 2) := by
      intro z x
      rw [ENNReal.ofReal_mul hweight]
    have hbasefun : Measurable (fun y : (Fin ι → ℝ) × UnitAddTorus (Fin d) =>
        ENNReal.ofReal (‖SmoothResolution.block s
          (gaussianSynthesis atoms y.1) y.2‖ ^ 2)) := by
      have hrepr : (fun y : (Fin ι → ℝ) × UnitAddTorus (Fin d) =>
          SmoothResolution.block s (gaussianSynthesis atoms y.1) y.2) =
        (fun y => ∑ i : Fin ι, (y.1 i : ℂ) *
          SmoothResolution.block s (atoms i) y.2) := by
        funext y
        exact AtomicBlockVariance.smoothBlock_gaussianSynthesis s atoms y.1 y.2
      rw [show (fun y : (Fin ι → ℝ) × UnitAddTorus (Fin d) =>
          ENNReal.ofReal (‖SmoothResolution.block s
            (gaussianSynthesis atoms y.1) y.2‖ ^ 2)) =
          (fun y => ENNReal.ofReal (‖∑ i : Fin ι, (y.1 i : ℂ) *
            SmoothResolution.block s (atoms i) y.2‖ ^ 2)) by
          funext y
          rw [congrFun hrepr y]]
      fun_prop
    have hterm_eq : (fun y : (Fin ι → ℝ) × UnitAddTorus (Fin d) => T s y) =
        (fun y => ENNReal.ofReal ((2 : ℝ) ^
          (2 * r * ∑ i, (s i : ℝ))) *
          ENNReal.ofReal (‖SmoothResolution.block s
            (gaussianSynthesis atoms y.1) y.2‖ ^ 2)) := by
      funext y
      exact hmul y.1 y.2
    have hbase' : (∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
        ENNReal.ofReal (‖SmoothResolution.block s
          (gaussianSynthesis atoms z) x‖ ^ 2) ∂μx ∂P) ≤
        ENNReal.ofReal (4 * V s * gaussianAbsoluteMoment 2) := by
      norm_num at hbase
      simpa [P, μx, Real.rpow_natCast, gaussianAbsoluteMoment,
        ← ofReal_norm, ENNReal.ofReal_pow] using hbase
    have hbaseprod := MeasureTheory.lintegral_prod (μ := P) (ν := μx)
      (fun y : (Fin ι → ℝ) × UnitAddTorus (Fin d) =>
        ENNReal.ofReal (‖SmoothResolution.block s
          (gaussianSynthesis atoms y.1) y.2‖ ^ 2)) hbasefun.aemeasurable
    have hbaseprod_le :
        (∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d),
          ENNReal.ofReal (‖SmoothResolution.block s
            (gaussianSynthesis atoms y.1) y.2‖ ^ 2) ∂P.prod μx) ≤
          ENNReal.ofReal (4 * V s * gaussianAbsoluteMoment 2) := by
      rw [hbaseprod]
      exact hbase'
    have hconst : ENNReal.ofReal ((2 : ℝ) ^
        (2 * r * ∑ i, (s i : ℝ))) *
        (∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d),
          ENNReal.ofReal (‖SmoothResolution.block s
            (gaussianSynthesis atoms y.1) y.2‖ ^ 2) ∂P.prod μx) ≤
        ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
          (4 * V s * gaussianAbsoluteMoment 2)) := by
      rw [ENNReal.ofReal_mul hweight]
      exact mul_le_mul_of_nonneg_left hbaseprod_le (by positivity)
    rw [hterm_eq, MeasureTheory.lintegral_const_mul'' _
      hbasefun.aemeasurable]
    simpa [T, smoothSquareTerm] using hconst
  have hsum : (∑' s : Fin d → ℕ,
      ∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d), T s y ∂P.prod μx) ≤ M :=
    (ENNReal.tsum_le_tsum hterm).trans hsummable
  have htotal : (∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d), F y ∂P.prod μx) ≤ M :=
    hseries ▸ hsum
  calc
    _ = ∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d), F (z, x) ∂μx ∂P := by
      simp [F, P, μx, hF_eq]
    _ = ∫⁻ y : (Fin ι → ℝ) × UnitAddTorus (Fin d), F y ∂P.prod μx := hproduct.symm
    _ ≤ M := htotal

/-- A half-mass lower bound for the literal Sobolev `p=2` unit ball of the
actual finite Gaussian smooth synthesis. The only additional input beyond the
block-variance and summability bounds is measurability of the displayed energy
map (the block series itself is handled in `smoothSobolev_p2_expected_energy_le`). -/
theorem smoothSobolev_p2_unitBall_mass {d ι : ℕ}
    (r : ℝ) (atoms : Fin ι → RealPeriodic d) (V : (Fin d → ℕ) → ℝ)
    (hV : ∀ s, 0 ≤ V s)
    (hvariance : ∀ (s : Fin d → ℕ) (x : UnitAddTorus (Fin d)),
      (∑ i : Fin ι, ‖SmoothResolution.block s (atoms i) x‖ ^ 2) ≤ V s)
    (hsummable : (∑' s : Fin d → ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
        (4 * V s * gaussianAbsoluteMoment 2))) ≤ 1 / 2)
    (hmeas : Measurable (fun z : Fin ι → ℝ =>
      ∫⁻ x : UnitAddTorus (Fin d),
        (SmoothResolution.squareFunctionSquared r
          (gaussianSynthesis atoms z) x) ^ (2 / 2 : ℝ)
        ∂(volume : Measure (UnitAddTorus (Fin d))))) :
    (1 / 2 : ℝ≥0∞) ≤
      (productStandardGaussian (Fin ι))
        {z | SmoothResolution.SobolevUnitBall 2 r
          (gaussianSynthesis atoms z)} := by
  have hmean :
      (∫⁻ z : Fin ι → ℝ, ∫⁻ x : UnitAddTorus (Fin d),
        (SmoothResolution.squareFunctionSquared r
          (gaussianSynthesis atoms z) x) ^ (2 / 2 : ℝ)
        ∂(volume : Measure (UnitAddTorus (Fin d)))
        ∂productStandardGaussian (Fin ι)) ≤ 1 / 2 :=
    (smoothSobolev_p2_expected_energy_le r atoms V hV hvariance hsummable)
  exact smoothSobolevUnitBall_mass_of_mean_le_half
    (productStandardGaussian (Fin ι)) 2 r
    (fun z => gaussianSynthesis atoms z) hmeas hmean

end BrownianSharp
