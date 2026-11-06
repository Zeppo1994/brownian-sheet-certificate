import BrownianSharp.AlignmentPaperAnchoredLpReflection
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperAnchoredLpReflectionTensor

open BrownianSharp.AlignmentPaperAnchoredLpReflection

/-- Lebesgue measure restricted to the unit interval. -/
def unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)

end BrownianSharp.AlignmentPaperAnchoredLpReflectionTensor
