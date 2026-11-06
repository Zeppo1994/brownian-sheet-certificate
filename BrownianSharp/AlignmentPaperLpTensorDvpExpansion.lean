import BrownianSharp.AlignmentPaperLpDvpKernelExpansion
import BrownianSharp.AlignmentPaperLpDvpReproduction
import BrownianSharp.AlignmentMaternComplexWindow

/-! The tensor DVP kernel as an actual finite torus Fourier polynomial. -/

noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperLpTensorDvpExpansion

open BrownianSharp.Torus
open BrownianSharp.AlignmentPaperLpDvpReproduction
open BrownianSharp.AlignmentPaperLpDvpKernelExpansion
open HaarQuarter.TheoremD.FejerFourier
open HaarQuarter.FourierExtractionKernel

def tensorDvpFrequencyBox {d : ℕ} (N : Fin d → ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun i => dvpFrequencyBox (N i))

def tensorDvpFourierCoefficient {d : ℕ} (N : Fin d → ℕ)
    (k : Fin d → ℤ) : ℂ := ∏ i, dvpFourierCoefficient (N i) (k i)

theorem tensorDvpKernel_eq_finiteFourierPolynomial {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i) :
    tensorDvpKernel N =
      torusFourierPolynomial (tensorDvpFrequencyBox N)
        (tensorDvpFourierCoefficient N) := by
  classical
  ext x
  change (∏ i, deLaValleePoussinCircleKernel (N i) (x i)) = _
  simp only [BrownianSharp.AlignmentMaternComplexWindow.torusFourierPolynomial_apply]
  have hcoord (i : Fin d) :
      deLaValleePoussinCircleKernel (N i) (x i) =
        ∑ q ∈ dvpFrequencyBox (N i),
          dvpFourierCoefficient (N i) q * fourier (T := (1 : ℝ)) q (x i) := by
    have h := congrArg (fun f : C(UnitAddCircle, ℂ) => f (x i))
      (dvpCircleKernel_eq_finiteFourierPolynomial (N i) (hN i))
    simpa [finiteCircleFourierPolynomial, fourier_apply, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul] using h
  simp_rw [hcoord]
  rw [Finset.prod_univ_sum (fun i => dvpFrequencyBox (N i))]
  simp only [Finset.sum_apply, ContinuousMap.coe_mk, UnitAddTorus.mFourier,
    Finset.prod_mul_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  simp [tensorDvpFrequencyBox, tensorDvpFourierCoefficient,
    Fintype.mem_piFinset, dvpCircleKernel_eq_finiteFourierPolynomial,
    hN]

end BrownianSharp.AlignmentPaperLpTensorDvpExpansion
