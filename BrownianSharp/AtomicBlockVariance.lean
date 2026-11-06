import BrownianSharp.PeriodicCover
import BrownianSharp.SmoothResolution
import BrownianSharp.GaussianGridStatistics
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Probability.Moments.Variance

/-!
Finite-dimensional deterministic estimates for the actual atom synthesis.
These are separated from `PeriodicCover` so the covering bridge remains a
stable dependency while the analytic norm estimates are developed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BrownianSharp.AtomicBlockVariance
open BrownianSharp.Torus
open BrownianSharp.PeriodicCover

private theorem periodicFourierIntegrable {d : ℕ} (f : RealPeriodic d)
    (k : Fin d → ℤ) :
    Integrable (fun x : UnitAddTorus (Fin d) =>
      UnitAddTorus.mFourier (-k) x • (f x : ℂ))
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  have hcont : Continuous (fun x : UnitAddTorus (Fin d) =>
      UnitAddTorus.mFourier (-k) x • (f x : ℂ)) := by fun_prop
  have hbound : ∀ x, ‖UnitAddTorus.mFourier (-k) x • (f x : ℂ)‖ ≤ ‖f‖ := by
    intro x
    rw [norm_smul]
    have hm : ‖UnitAddTorus.mFourier (-k) x‖ ≤ 1 := by
      calc
        ‖UnitAddTorus.mFourier (-k) x‖ ≤ ‖UnitAddTorus.mFourier (-k)‖ :=
          (UnitAddTorus.mFourier (-k)).norm_coe_le_norm x
        _ = 1 := UnitAddTorus.mFourier_norm
    have hf : ‖(f x : ℂ)‖ ≤ ‖f‖ := by
      simpa using f.norm_coe_le_norm x
    calc
      ‖UnitAddTorus.mFourier (-k) x‖ * ‖(f x : ℂ)‖ ≤ 1 * ‖f‖ :=
        mul_le_mul hm hf (norm_nonneg _) (by norm_num)
      _ = ‖f‖ := one_mul _
  exact Integrable.of_bound hcont.aestronglyMeasurable ‖f‖
    (ae_of_all _ hbound)

/-- The actual smooth-resolution Fourier coefficient is additive on real
periodic functions. -/
theorem realPeriodicFourierCoeff_add {d : ℕ} (f g : RealPeriodic d)
    (k : Fin d → ℤ) :
    BrownianSharp.Torus.realPeriodicFourierCoeff (f + g) k =
      BrownianSharp.Torus.realPeriodicFourierCoeff f k +
        BrownianSharp.Torus.realPeriodicFourierCoeff g k := by
  classical
  unfold BrownianSharp.Torus.realPeriodicFourierCoeff
    BrownianSharp.Torus.complexifyRealPeriodic UnitAddTorus.mFourierCoeff
  simp only [ContinuousMap.coe_add, Pi.add_apply, Complex.ofReal_add, smul_add]
  exact integral_add (periodicFourierIntegrable f k) (periodicFourierIntegrable g k)

/-- Real scalar homogeneity of the actual torus Fourier coefficient. -/
theorem realPeriodicFourierCoeff_smul {d : ℕ} (c : ℝ) (f : RealPeriodic d)
    (k : Fin d → ℤ) :
    BrownianSharp.Torus.realPeriodicFourierCoeff (c • f) k =
      (c : ℂ) * BrownianSharp.Torus.realPeriodicFourierCoeff f k := by
  classical
  unfold BrownianSharp.Torus.realPeriodicFourierCoeff
    BrownianSharp.Torus.complexifyRealPeriodic UnitAddTorus.mFourierCoeff
  simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  have hfun : (fun t : UnitAddTorus (Fin d) =>
      UnitAddTorus.mFourier (-k) t * ((c : ℂ) * (f t : ℂ))) =
      fun t => (c : ℂ) * (UnitAddTorus.mFourier (-k) t * (f t : ℂ)) := by
    funext t
    ring
  rw [hfun, integral_const_mul]

/-- Each actual smooth tensor Fourier block is additive. -/
theorem smoothBlock_add {d : ℕ} (s : Fin d → ℕ) (f g : RealPeriodic d) :
    BrownianSharp.SmoothResolution.block s (f + g) =
      BrownianSharp.SmoothResolution.block s f +
        BrownianSharp.SmoothResolution.block s g := by
  classical
  ext x
  simp [BrownianSharp.SmoothResolution.block,
    BrownianSharp.Torus.torusFourierPolynomial, realPeriodicFourierCoeff_add,
    Finset.sum_add_distrib, mul_add, add_smul]

/-- Each actual smooth tensor Fourier block is homogeneous under real scaling. -/
theorem smoothBlock_smul {d : ℕ} (s : Fin d → ℕ) (c : ℝ) (f : RealPeriodic d) :
    BrownianSharp.SmoothResolution.block s (c • f) =
      (c : ℂ) • BrownianSharp.SmoothResolution.block s f := by
  classical
  ext x
  simp [BrownianSharp.SmoothResolution.block,
    BrownianSharp.Torus.torusFourierPolynomial, realPeriodicFourierCoeff_smul,
    Finset.smul_sum, smul_smul, mul_assoc]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- The actual smooth Fourier block, as a real-linear operator on continuous
periodic functions. -/
noncomputable def smoothBlockLinear {d : ℕ} (s : Fin d → ℕ) :
    RealPeriodic d →ₗ[ℝ] C(UnitAddTorus (Fin d), ℂ) where
  toFun := BrownianSharp.SmoothResolution.block s
  map_add' := smoothBlock_add s
  map_smul' := smoothBlock_smul s

/-- Fourier-block evaluation of a finite Gaussian atom synthesis is the
corresponding finite real Gaussian linear form. -/
theorem smoothBlock_gaussianSynthesis {ι d : ℕ}
    (s : Fin d → ℕ) (atoms : Fin ι → RealPeriodic d) (z : Fin ι → ℝ)
    (x : UnitAddTorus (Fin d)) :
    BrownianSharp.SmoothResolution.block s (gaussianSynthesis atoms z) x =
      ∑ i : Fin ι, (z i : ℂ) *
        BrownianSharp.SmoothResolution.block s (atoms i) x := by
  classical
  change smoothBlockLinear s (gaussianSynthesis atoms z) x = _
  simp [smoothBlockLinear, gaussianSynthesis, map_sum, map_smul]

end BrownianSharp.AtomicBlockVariance
