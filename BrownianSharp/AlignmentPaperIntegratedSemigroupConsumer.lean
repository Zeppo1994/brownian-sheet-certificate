import BrownianSharp.AlignmentPaperIntegratedSemigroup
import BrownianSharp.AlignmentGaussianIntegratedSmallBall
import BrownianSharp.AlignmentPaperFractionalEntropyRoute
import BrownianSharp.AlignmentPaperFractionalFourierPreimage

/-! The integrated-sheet Cameron--Martin shift is transported to the explicit
coordinatewise order-one semigroup path using the proved common-order fold
identity. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperIntegratedSemigroupConsumer

open BrownianSharp.AlignmentGaussianIntegratedSmallBall
open BrownianSharp.AlignmentPaperIntegratedSemigroup
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentGaussianEntropySmallBall
open BrownianSharp.AlignmentPaperFractionalEntropyRoute
open BrownianSharp.AlignmentPaperFractionalFourierPreimage
open BrownianSharp.Latest
open HaarQuarter

/-- Law of the actual coordinatewise order-one RL semigroup representation of
the integrated sheet path. -/
def integratedSheetSemigroupLaw {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ) :
    Measure C(BrownianCubeAnchor d, ℝ) :=
  P.map (fun ω => integrateSheetSemigroupPath m (B.path ω))

/-- The semigroup representation is pathwise equal to the actual iterated
integral path, hence it has exactly the same law. -/
theorem integratedSheetSemigroupLaw_eq_integratedSheetLaw {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ) :
    integratedSheetSemigroupLaw B m = integratedSheetLaw B m := by
  have hfun : (fun ω => integrateSheetSemigroupPath m (B.path ω)) =
      integrateBrownianSheetPath B m := by
    funext ω
    ext x
    rw [integrateBrownianSheetPath_apply]
    exact (congrArg (fun q : C(BrownianCubeAnchor d, ℝ) => q x)
      (integrateSheetPath_eq_integrateSheetSemigroupPath m (B.path ω))).symm
  calc
    integratedSheetSemigroupLaw B m = P.map (integrateBrownianSheetPath B m) :=
      Measure.map_congr (Filter.Eventually.of_forall (fun ω => congrFun hfun ω))
    _ = integratedSheetLaw B m := rfl

/-- The actual integrated-sheet Cameron--Martin shift lower bound stated for
the semigroup path law. Its proof transports the genuine shift through the
proved pathwise semigroup identity. -/
theorem integratedSheetSemigroupLaw_ball_shift_lower {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ)
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (x : C(BrownianCubeAnchor d, ℝ))
    (hx : x ∈ fractionalIntegrationBall (fun i => (m i : ℝ) + 1)) :
    ENNReal.ofReal (Real.exp (-(R ^ 2) / 2)) *
        integratedSheetSemigroupLaw B m (Metric.closedBall 0 ε) ≤
      integratedSheetSemigroupLaw B m (Metric.closedBall (R • x) ε) := by
  have hshift := integratedSheetLaw_ball_shift_lower B m R ε hR hε x hx
  rw [integratedSheetSemigroupLaw_eq_integratedSheetLaw]
  exact hshift

end BrownianSharp.AlignmentPaperIntegratedSemigroupConsumer
