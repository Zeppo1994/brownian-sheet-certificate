import BrownianSharp.UnitTorusMeasure
import Mathlib.MeasureTheory.Group.AddCircle

/-! Global quantitative doubling for the actual normalized circle measure.
Mathlib already supplies the local-doubling/Vitali framework; these formulas
provide the explicit constant needed by the periodic CZ decomposition. -/
noncomputable section
open MeasureTheory Metric
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperCircleDoubling

theorem haar_ball (x : UnitAddCircle) (r : ℝ) :
    AddCircle.haarAddCircle (ball x r) = ENNReal.ofReal (min 1 (2*r)) := by
  rw [← BrownianSharp.unitAddCircle_volume_eq_haar]
  have heq := measure_congr
    (AddCircle.closedBall_ae_eq_ball (x := x) (ε := r))
  rw [← heq, AddCircle.volume_closedBall]

/-- A dilation by any factor at least one costs at most that factor in
normalized circle volume, including radii beyond the injectivity radius. -/
theorem haar_ball_scale_le (x : UnitAddCircle) (r cScale : ℝ) (hcScale : 1 ≤ cScale) :
    AddCircle.haarAddCircle (ball x (cScale*r)) ≤
      ENNReal.ofReal cScale * AddCircle.haarAddCircle (ball x r) := by
  have hcScale0 : 0 ≤ cScale := by linarith
  rw [haar_ball,haar_ball, ← ENNReal.ofReal_mul hcScale0]
  apply ENNReal.ofReal_le_ofReal
  rw [mul_min_of_nonneg _ _ hcScale0]
  have heq : 2*(cScale*r) = cScale*(2*r) := by ring
  rw [heq,mul_one]
  exact min_le_min hcScale le_rfl

theorem haar_ball_pos (x : UnitAddCircle) {r : ℝ} (hr : 0 < r) :
    0 < AddCircle.haarAddCircle (ball x r) := by
  rw [haar_ball]
  exact ENNReal.ofReal_pos.mpr (lt_min (by norm_num) (by positivity))

end BrownianSharp.AlignmentPaperCircleDoubling
