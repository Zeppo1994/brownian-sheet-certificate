import BrownianSharp.AlignmentFractionalL2Semigroup

/-! Actual Riemann--Liouville maps on the scalar source `L²` space. The target
is returned to `L²` through the canonical continuous-profile embedding. -/

noncomputable section
open MeasureTheory

namespace BrownianSharp.AlignmentFractionalL2OperatorSemigroup

open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentFractionalL2Semigroup

/-- The genuine bounded RL map from the unit-interval source `L²` space back
to itself: first evaluate the RL integral as a continuous profile, then embed
that profile into the same `L²` space. -/
noncomputable def fractionalRLOnL2 (α : ℝ) (hα : 1/2 < α) :
    UnitL2 →L[ℝ] UnitL2 :=
  profileToL2.comp (fractionalRL α hα)

/-- The actual `L² → L²` RL maps form a semigroup. This follows by applying the
continuous-profile embedding to the already established exact RL semigroup
identity, so the equality is on all `L²` inputs, not merely continuous ones. -/
theorem fractionalRLOnL2_semigroup {a b : ℝ}
    (ha : 1/2 < a) (hb : 1/2 < b) :
    (fractionalRLOnL2 a ha).comp (fractionalRLOnL2 b hb) =
      fractionalRLOnL2 (a+b) (by linarith) := by
  apply ContinuousLinearMap.ext
  intro f
  have hsem := fractionalRL_semigroup ha hb
  exact congrArg profileToL2 (congrArg (fun T => T f) hsem)

end BrownianSharp.AlignmentFractionalL2OperatorSemigroup
