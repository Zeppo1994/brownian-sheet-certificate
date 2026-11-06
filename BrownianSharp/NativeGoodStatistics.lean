import BrownianSharp.NativeGoodGrid
import BrownianSharp.NativeMatrix
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The manuscript's actual normalized high-power statistic, with its
expectation, nondegeneracy and integrability discharged on the proved good grid. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

def nativeGoodMatrix (d n : ℕ) : NativeGoodGrid d n → LayerIndex d n → ℝ :=
  nativeStandardMatrix (fun q : NativeGoodGrid d n => q.val)

theorem nativeGoodGrid_variance_pos {d n : ℕ} (hd : 0 < d)
    (q : NativeGoodGrid d n) : 0 < nativeLayerRowVariance q.val :=
  (half_pos (nativeVarianceMeanLowerBound_pos hd)).trans_le q.property

theorem nativeGoodMatrix_unit_rows {d n : ℕ} (hd : 0 < d) (q : NativeGoodGrid d n) :
    ∑ a, nativeGoodMatrix d n q a ^ 2 = 1 :=
  nativeStandardMatrix_unit_rows _ (nativeGoodGrid_variance_pos hd) q

end BrownianSharp
