import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentGaussianFractionalHaar
import BrownianSharp.AlignmentFractionalHaarProjection
import BrownianSharp.FiniteHaarGeometry
import BrownianSharp.FiniteHaarGradeEnergy
import Mathlib.Tactic

/-! Actual tensor RL coefficients against finite tensor-Haar source vectors.
The finite index carries one father or one normalized mother in each source
coordinate.  This file starts from the actual L² kernel and scalar Haar
features; it does not postulate a tensor coefficient envelope. -/

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
open HaarQuarter
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalTensorHaar

open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentL2TensorProduct
open BrownianSharp.AlignmentGaussianFractionalHaar
open BrownianSharp.AlignmentFractionalHaarProjection
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.CameronMartin
open BrownianSharp

abbrev AxisL2 := AlignmentGaussianFractionalHaar.SourceL2

theorem fractionalRL_eq_kernel_inner (α : ℝ) (hα : 1/2 < α)
    (g : AxisL2) (t : UnitInterval) :
    fractionalRL α hα g t =
      inner ℝ (kernelVector α t.1 hα
        (Set.mem_Icc.mp t.2).1 (Set.mem_Icc.mp t.2).2) g := by
  change fractionalEvaluation α t.1 hα
    (Set.mem_Icc.mp t.2).1 (Set.mem_Icc.mp t.2).2 g = _
  rw [fractionalEvaluation, evaluationFunctional, innerSL_apply_apply]

end BrownianSharp.AlignmentFractionalTensorHaar
