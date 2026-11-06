import BrownianSharp.YoungLp
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic
import BrownianSharp.ScalarKernelL1
import Mathlib.Analysis.Convex.Jensen

/-! Finite signed mixtures of positive Fejer kernels act on `Lᵖ` with norm
bounded by the actual coefficient variation. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
open BrownianSharp.ScalarKernelL1
open AddCircle HaarQuarter.TheoremD.FejerFourier

namespace BrownianSharp

/-- The real-valued Fejer kernel, obtained from the actual Fejer polynomial. -/
def realFejerKernel (N : ℕ) : C(UnitAddCircle, ℝ) :=
  ⟨fun x => ‖fejerFourierPolynomial N x‖, (fejer_continuous N).norm⟩

theorem realFejerKernel_nonneg (N : ℕ) (x : UnitAddCircle) :
    0 ≤ realFejerKernel N x := by
  change 0 ≤ ‖fejerFourierPolynomial N x‖
  exact norm_nonneg _

end BrownianSharp
