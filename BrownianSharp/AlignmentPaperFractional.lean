import BrownianSharp.AlignmentFractionalSheetStatement
import BrownianSharp.AlignmentGaussianIntegratedReverse
import BrownianSharp.AlignmentOperatorStatements
import BrownianSharp.AlignmentOperatorWidthIndexShift
import BrownianSharp.AlignmentFractionalGradedPolynomialWidth
import BrownianSharp.AlignmentEndpointWidthExtraction
import BrownianSharp.AlignmentEndpointDyadicEntropy
import BrownianSharp.AlignmentExponentialFractionalEntropy
import BrownianSharp.AlignmentFractionalAnisotropicEntropy
import BrownianSharp.AlignmentWidthRates
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentAuditPeriodicBoundedness
import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.LayerIndex
import Mathlib.Tactic
import BrownianSharp.AlignmentPaperFractionalFourierPreimage
import BrownianSharp.AlignmentPaperFractionalCarlRoute
import BrownianSharp.AlignmentPaperFractionalSheetScalarLower
import BrownianSharp.AlignmentPaperIntegratedSheetFourierCommonOrder

/-! Paper-exact specializations of the fractional and integrated sheet results.

These are the parameterizations of Theorems 5.1 and 5.2: common order `r` for
`T_d^{(r)}` and a common integer order `m` for the integrated sheets. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open HaarQuarter
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperFractional

open BrownianSharp.AlignmentOperatorStatements
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.Latest

def PaperFractionalTensorStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ r : ℝ, 1/2 < r →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c * logarithmicIndexRate r
          (r * (d - 1 : ℕ) + 1/2) k) ≤
            HaarQuarter.TheoremD.entropyNumber k
              (fractionalIntegrationBall (fun _ : Fin d => r)) ∧
        HaarQuarter.TheoremD.entropyNumber k
          (fractionalIntegrationBall (fun _ : Fin d => r)) ≤
            ENNReal.ofReal (C * logarithmicIndexRate r
              (r * (d - 1 : ℕ) + 1/2) k) ∧
        ENNReal.ofReal (c * logarithmicIndexRate r
          (r * (d - 1 : ℕ) + 1/2) k) ≤
            AlignmentOperatorNumbers.operatorKolmogorovNumber
              (fractionalIntegrationBall (fun _ : Fin d => r)) k ∧
        AlignmentOperatorNumbers.operatorKolmogorovNumber
          (fractionalIntegrationBall (fun _ : Fin d => r)) k ≤
            ENNReal.ofReal (C * logarithmicIndexRate r
              (r * (d - 1 : ℕ) + 1/2) k)

theorem paperFractionalTensor_certified : PaperFractionalTensorStatement := by
  intro d hd r hr
  exact AlignmentPaperFractionalCarlRoute.isotropic_operator_rates_of_scalar hd hr
    (fun α hα =>
      AlignmentPaperFractionalFourierPreimage.smoothAtom_dyadic_fractional_preimage_fourier hα)

/-- The common-Hurst lower bound followed by the actual minimum-coordinate
restriction, on the same probability space as the original sheet. -/
theorem paperFractionalSheet_certified : Latest.FractionalSheetStatement := by
  intro d hd H hH h ν hν hm
  exact AlignmentPaperFractionalSheetScalarLower.latest_fractionalSheet_of_scalar
    d hd H hH h ν hν hm
    (fun α hα =>
      AlignmentPaperFractionalFourierPreimage.smoothAtom_dyadic_fractional_preimage_fourier hα)

def PaperIntegratedSheetStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ m : ℕ,
    ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (B : BrownianSheetOnCube d Ω P)
        (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          c * smallBallRate (2 / (2 * (m : ℝ) + 1))
            ((d - 1 : ℕ) + (d : ℝ) / (2 * (m : ℝ) + 1)) ε ≤
              -Real.log (P.real
                {ω | ‖integrateSheetPath (fun _ : Fin d => m)
                    (B.path ω)‖ ≤ ε}) ∧
          -Real.log (P.real
            {ω | ‖integrateSheetPath (fun _ : Fin d => m)
                (B.path ω)‖ ≤ ε}) ≤
              C * smallBallRate (2 / (2 * (m : ℝ) + 1))
                ((d - 1 : ℕ) + (d : ℝ) / (2 * (m : ℝ) + 1)) ε

theorem paperIntegratedSheet_certified : PaperIntegratedSheetStatement :=
  AlignmentPaperIntegratedSheetFourierCommonOrder.paperIntegratedSheet_commonOrder_fourier_certified

end BrownianSharp.AlignmentPaperFractional
