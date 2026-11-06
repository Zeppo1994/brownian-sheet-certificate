import BrownianSharp.TensorBlockKernelLp
import BrownianSharp.AtomicTensorSynthesisLp
import BrownianSharp.TorusComplexYoung
import BrownianSharp.InverseDerivativeProfileIdentity
import BrownianSharp.SmoothAtom

/-! A first operator estimate for a finite synthesis on one fixed tensor
shape. The multiplier block has a uniform Lp bound, and the synthesis input
has the exact cellwise Lp budget. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AtomicBlockKernel
open BrownianSharp.ScalarKernelL1
open UnitAddTorus

local instance fixedShapeBlockFact : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance fixedShapeBlockMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance fixedShapeBlockAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance fixedShapeBlockNegInvariant : Measure.IsNegInvariant (volume : Measure UnitAddCircle) := by
  infer_instance
local instance fixedShapeBlockProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Real synthesis of a finite family of periodized smooth atoms at one fixed
rectangular shape. -/
def fixedShapeSynthesis {d : ℕ} (s : Fin d → ℕ)
    (c : DyadicShapeCell d s → ℝ) : RealPeriodic d where
  toFun x := ∑ j : DyadicShapeCell d s,
    c j * dyadicShapeDerivativeAtom s (fun _ => 0) j x
  continuous_toFun := by
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (continuous_finsetProd Finset.univ fun i hi =>
      (periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 0).continuous.comp
        (continuous_apply i))

end BrownianSharp
