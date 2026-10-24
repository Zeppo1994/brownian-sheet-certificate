import BrownianSharp.SmoothClassMeasurability
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! Exact homogeneity of the manuscript's literal smooth class energies. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BrownianSharp
open Torus SmoothResolution

theorem squareFunctionSquared_smul {d : ℕ} (r A : ℝ) (f : RealPeriodic d)
    (x : UnitAddTorus (Fin d)) :
    squareFunctionSquared r (A • f) x =
      ENNReal.ofReal (A^2) * squareFunctionSquared r f x := by
  unfold squareFunctionSquared
  have hterm (s : Fin d → ℕ) :
      ENNReal.ofReal ((2:ℝ)^(2*r*∑ i, (s i:ℝ)) * ‖block s (A • f) x‖^2) =
      ENNReal.ofReal (A^2) *
        ENNReal.ofReal ((2:ℝ)^(2*r*∑ i, (s i:ℝ)) * ‖block s f x‖^2) := by
    rw [← ENNReal.ofReal_mul (sq_nonneg A), AtomicBlockVariance.smoothBlock_smul]
    congr 1
    simp only [ContinuousMap.coe_smul, Pi.smul_apply, norm_smul, Complex.norm_real,
      Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  simp_rw [hterm]
  exact ENNReal.tsum_mul_left

theorem smoothSobolevEnergy_smul {d : ℕ} {A : ℝ} (hA : 0 < A)
    {p : ℝ} (hp : 0 ≤ p) (r : ℝ) (f : RealPeriodic d) :
    (∫⁻ x : UnitAddTorus (Fin d), (squareFunctionSquared r (A • f) x)^(p/2)) =
      ENNReal.ofReal (A^p) *
        (∫⁻ x : UnitAddTorus (Fin d), (squareFunctionSquared r f x)^(p/2)) := by
  have hfactor : ENNReal.ofReal (A^2)^(p/2) = ENNReal.ofReal (A^p) := by
    rw [ENNReal.ofReal_rpow_of_pos (sq_pos_of_pos hA),
      ← Real.rpow_natCast A 2, ← Real.rpow_mul hA.le]
    congr 2
    ring
  simp_rw [squareFunctionSquared_smul,
    ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p/2), hfactor]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem weightedBlockNorm_smul {d : ℕ} {A : ℝ} (hA : 0 < A)
    (p : ℝ≥0∞) (r : ℝ) (s : Fin d → ℕ) (f : RealPeriodic d) :
    weightedBlockNorm p r s (A • f) =
      ENNReal.ofReal A * weightedBlockNorm p r s f := by
  unfold weightedBlockNorm
  rw [AtomicBlockVariance.smoothBlock_smul]
  have hfun : (fun x => ((A:ℂ) • block s f) x) =
      (A:ℂ) • (fun x => block s f x) := rfl
  rw [hfun, eLpNorm_const_smul]
  have hnorm : ‖(A:ℂ)‖ₑ = ENNReal.ofReal A := by
    rw [← ofReal_norm]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
  rw [hnorm]
  ac_rfl

theorem smoothBesovEnergy_smul {d : ℕ} {A : ℝ} (hA : 0 < A)
    (p : ℝ≥0∞) (r : ℝ) (θ : ℝ≥0∞) (f : RealPeriodic d) :
    smoothBesovEnergy p r θ (A • f) =
      ENNReal.ofReal (A^θ.toReal) * smoothBesovEnergy p r θ f := by
  unfold smoothBesovEnergy
  simp_rw [weightedBlockNorm_smul hA,
    ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
    ENNReal.ofReal_rpow_of_pos hA]
  exact ENNReal.tsum_mul_left

end BrownianSharp
