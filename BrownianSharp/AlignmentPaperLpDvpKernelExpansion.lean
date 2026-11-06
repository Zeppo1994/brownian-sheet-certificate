import BrownianSharp.FejerCoefficients
import BrownianSharp.ScalarKernelL1
import BrownianSharp.ScalarPolynomialKernel
import BrownianSharp.FourierExtractionKernel

/-! A finite Fourier expansion of the actual scalar DVP kernel. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperLpDvpKernelExpansion

open HaarQuarter.TheoremD.FejerFourier
open HaarQuarter.FourierExtractionKernel
open BrownianSharp.ScalarKernelL1

def dvpFrequencyBox (N : ℕ) : Finset ℤ := Finset.Icc (-(2 * (N : ℤ))) (2 * (N : ℤ))

def dvpFourierCoefficient (N : ℕ) (k : ℤ) : ℂ :=
  fourierCoeff (T := (1 : ℝ)) (deLaValleePoussinCircleKernel N) k

theorem dvpCircleKernel_eq_finiteFourierPolynomial (N : ℕ) (hN : 0 < N) :
    deLaValleePoussinCircleKernel N =
      finiteCircleFourierPolynomial (dvpFrequencyBox N) (dvpFourierCoefficient N) := by
  apply continuous_eq_of_fourierCoeff_eq
  intro k
  have hrepr : finiteCircleFourierPolynomial (dvpFrequencyBox N)
      (dvpFourierCoefficient N) =
      polynomialKernel (dvpFrequencyBox N) (dvpFourierCoefficient N) := rfl
  rw [hrepr, polynomialKernel_coefficient]
  by_cases hk : k ∈ dvpFrequencyBox N
  · simp [dvpFourierCoefficient, hk]
  · have habs : 2 * N < k.natAbs := by
      have hk' : ¬ (-(2 * (N : ℤ)) ≤ k ∧ k ≤ 2 * (N : ℤ)) := by
        simpa [dvpFrequencyBox, Finset.mem_Icc] using hk
      rcases not_and_or.mp hk' with hlow | hhigh
      · have : k < -(2 * (N : ℤ)) := by omega
        have hcast : ((2 * N : ℕ) : ℤ) < k.natAbs := by
          rw [Int.natCast_natAbs]
          have : (2 * (N : ℤ)) < -k := by omega
          rw [abs_of_neg (by omega : k < 0)]
          exact this
        exact_mod_cast hcast
      · have : 2 * (N : ℤ) < k := by omega
        have hcast : ((2 * N : ℕ) : ℤ) < k.natAbs := by
          rw [Int.natCast_natAbs]
          rw [abs_of_nonneg (by omega : 0 ≤ k)]
          exact this
        exact_mod_cast hcast
    have h2 : 2 * N ≤ k.natAbs := by omega
    have hNle : N ≤ k.natAbs := by omega
    have hcoeff : dvpFourierCoefficient N k = 0 := by
      change fourierCoeff (T := (1 : ℝ)) (deLaValleePoussinPolynomial N) k = 0
      unfold deLaValleePoussinPolynomial
      have hI1 : Integrable (fejerFourierPolynomial (2 * N) : UnitAddCircle → ℂ)
          AddCircle.haarAddCircle :=
        (fejer_continuous (2 * N)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      have hI2 : Integrable (fejerFourierPolynomial N : UnitAddCircle → ℂ)
          AddCircle.haarAddCircle :=
        (fejer_continuous N).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      rw [show (fun x : UnitAddCircle =>
          2 * fejerFourierPolynomial (2 * N) x - fejerFourierPolynomial N x) =
          (fun x => (2 : ℂ) * fejerFourierPolynomial (2 * N) x) +
            (fun x => (-1 : ℂ) * fejerFourierPolynomial N x) by
          funext x; simp [sub_eq_add_neg]]
      rw [fourierCoeff.add
        (hI1.const_mul (2 : ℂ)) (hI2.const_mul (-1 : ℂ))]
      simp only [Pi.add_apply, fourierCoeff.const_mul]
      rw [fejer_coefficient_outside (2 * N) k h2,
        fejer_coefficient_outside N k hNle]
      simp
    simpa [dvpFourierCoefficient, hk] using hcoeff

end BrownianSharp.AlignmentPaperLpDvpKernelExpansion
