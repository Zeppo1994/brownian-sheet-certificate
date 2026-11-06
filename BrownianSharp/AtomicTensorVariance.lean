import BrownianSharp.AtomicBlockBessel
import BrownianSharp.AtomicTensorSynthesisLp
import BrownianSharp.ScalarAtomSpecialization

/-! Fixed-rectangular-shape specialization of the generic Fourier-block Bessel
bound to the actual tensor-product periodic dyadic atoms. -/

noncomputable section
set_option maxHeartbeats 500000
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AtomicTensorVariance

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AtomicBlockBessel
open BrownianSharp.PeriodicCover
open UnitAddTorus

abbrev ShapeCell (d : ℕ) (s : Fin d → ℕ) := DyadicShapeCell d s

def shapePeriodicAtom {d : ℕ} (s : Fin d → ℕ) (j : ShapeCell d s) :
    RealPeriodic d where
  toFun := dyadicShapeAtom s j
  continuous_toFun := by
    unfold dyadicShapeAtom
    exact continuous_finsetProd Finset.univ fun i hi =>
      (periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 0).continuous.comp
        (continuous_apply i)

end BrownianSharp.AtomicTensorVariance
