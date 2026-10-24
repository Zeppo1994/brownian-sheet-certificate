import BrownianSharp.AtomicBlockKernelL2
import BrownianSharp.UnitTorusMeasure
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BrownianSharp.AlignmentTrigonometricL2
open Torus SmoothResolution AtomicBlockKernelL2 UnitAddTorus
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
private instance torusProbability (d : ℕ) :
    IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
  infer_instance

theorem fourierPolynomial_toLp {d : ℕ} (S : Finset (Fin d → ℤ))
    (a : (Fin d → ℤ) → ℂ) :
    (torusFourierPolynomial S a).toLp 2 volume ℂ =
      ∑ k ∈ S, a k • mFourierLp 2 k := by
  simp only [torusFourierPolynomial, map_sum, map_smul]

theorem fourierPolynomial_L2_norm_sq {d : ℕ} (S : Finset (Fin d → ℤ))
    (a : (Fin d → ℤ) → ℂ) :
    ‖(torusFourierPolynomial S a).toLp 2 volume ℂ‖ ^ 2 =
      ∑ k ∈ S, ‖a k‖ ^ 2 := by
  rw [fourierPolynomial_toLp]
  exact norm_sq_orthonormal_finset_sum _ orthonormal_mFourier S a

/-- Exact finite-dimensional Nikolskii bound. -/
theorem fourierPolynomial_sup_le_sqrt_card_L2 {d : ℕ}
    (S : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ) :
    ‖torusFourierPolynomial S a‖ ≤ Real.sqrt (S.card : ℝ) *
      ‖(torusFourierPolynomial S a).toLp 2 volume ℂ‖ := by
  have hsum : (∑ k ∈ S, ‖a k‖) ≤ Real.sqrt (S.card : ℝ) *
      ‖(torusFourierPolynomial S a).toLp 2 volume ℂ‖ := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1:ℝ)) (fun k => ‖a k‖)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
    rw [← fourierPolynomial_L2_norm_sq S a] at hcs
    have hs := Real.sq_sqrt (show 0 ≤ (S.card : ℝ) by positivity)
    have hn : 0 ≤ ∑ k ∈ S, ‖a k‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    have hp : 0 ≤ Real.sqrt (S.card : ℝ) *
        ‖(torusFourierPolynomial S a).toLp 2 volume ℂ‖ := by positivity
    nlinarith
  calc
    ‖torusFourierPolynomial S a‖ ≤ ∑ k ∈ S, ‖a k‖ := by
      unfold torusFourierPolynomial
      calc
        ‖∑ k ∈ S, a k • mFourier k‖ ≤ ∑ k ∈ S, ‖a k • mFourier k‖ :=
          norm_sum_le _ _
        _ = ∑ k ∈ S, ‖a k‖ := by simp only [norm_smul, mFourier_norm, mul_one]
    _ ≤ _ := hsum

theorem smoothBlock_sup_le_sqrt_card_L2 {d : ℕ} (s : Fin d → ℕ)
    (f : RealPeriodic d) :
    ‖block s f‖ ≤ Real.sqrt ((frequencyBox s).card : ℝ) *
      ‖(block s f).toLp 2 volume ℂ‖ :=
  fourierPolynomial_sup_le_sqrt_card_L2 _ _
end BrownianSharp.AlignmentTrigonometricL2
