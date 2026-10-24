import BrownianSharp.AlignmentPeriodicCutoffClasses
import BrownianSharp.AtomicBlockVariance
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BrownianSharp.AlignmentPeriodicCutoffScaling
open BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AtomicBlockVariance

theorem admissibleBlock_smul {d : ℕ} (φ : AdmissibleCutoff)
    (s : Fin d → ℕ) (c : ℝ) (f : RealPeriodic d) :
    admissibleBlock φ s (c • f) = (c : ℂ) • admissibleBlock φ s f := by
  classical
  ext x
  simp [admissibleBlock, torusFourierPolynomial, realPeriodicFourierCoeff_smul,
    Finset.smul_sum, smul_smul, mul_assoc]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem weightedBlockNorm_smul {d : ℕ} (φ : AdmissibleCutoff)
    {A : ℝ} (hA : 0 < A) (p : ℝ≥0∞) (r : ℝ) (s : Fin d → ℕ)
    (f : RealPeriodic d) :
    weightedBlockNorm φ p r s (A • f) =
      ENNReal.ofReal A * weightedBlockNorm φ p r s f := by
  unfold weightedBlockNorm
  rw [admissibleBlock_smul]
  have hfun : (fun x => ((A : ℂ) • admissibleBlock φ s f) x) =
      (A : ℂ) • (fun x => admissibleBlock φ s f x) := rfl
  rw [hfun, eLpNorm_const_smul]
  have hnorm : ‖(A : ℂ)‖ₑ = ENNReal.ofReal A := by
    rw [← ofReal_norm]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
  rw [hnorm]
  ac_rfl

theorem BesovEnergy_smul {d : ℕ} (φ : AdmissibleCutoff)
    {A : ℝ} (hA : 0 < A) (p : ℝ≥0∞) (r : ℝ) (θ : ℝ≥0∞)
    (f : RealPeriodic d) :
    (∑' s, weightedBlockNorm φ p r s (A • f) ^ θ.toReal) =
      ENNReal.ofReal (A ^ θ.toReal) *
        (∑' s, weightedBlockNorm φ p r s f ^ θ.toReal) := by
  simp_rw [weightedBlockNorm_smul φ hA,
    ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg,
    ENNReal.ofReal_rpow_of_pos hA]
  exact ENNReal.tsum_mul_left

end BrownianSharp.AlignmentPeriodicCutoffScaling
