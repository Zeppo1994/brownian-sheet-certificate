import BrownianSharp.External.WeakCZ.CircleWhitneyPartition
import BrownianSharp.External.WeakCZ.CircleMaximal
import BrownianSharp.AlignmentPaperCircleDoubling

/-! The total measure of the 64-fold Whitney exception is controlled by the
measure of the actual high-average set, using normalized circle Haar scaling. -/

noncomputable section
set_option maxHeartbeats 1000000
open Set Metric MeasureTheory
open scoped ENNReal

namespace BrownianSharp.External.WeakCZ

variable {Ω : Set UnitAddCircle}

/-- The union of the 64-fold core balls has measure at most 64 times the
measure of the open set covered by the Whitney pieces. -/
theorem circleWhitney_exception_measure_le (d : CircleWhitneyPieceData Ω) :
    circleMaximalMeasure (⋃ i, ball (d.center i) (64*d.radius i)) ≤
      ENNReal.ofReal 64 * circleMaximalMeasure Ω := by
  calc
    _ ≤ ∑' i, circleMaximalMeasure (ball (d.center i) (64*d.radius i)) :=
      measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal 64 * circleMaximalMeasure (d.core i) := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [d.core_eq_ball i]
      exact BrownianSharp.AlignmentPaperCircleDoubling.haar_ball_scale_le
        (d.center i) (d.radius i) 64 (by norm_num)
    _ = ENNReal.ofReal 64 * ∑' i, circleMaximalMeasure (d.core i) :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal 64 * circleMaximalMeasure (⋃ i, d.core i) := by
      rw [measure_iUnion d.core_pairwiseDisjoint (fun i => by
        rw [d.core_eq_ball]
        exact measurableSet_ball)]
    _ ≤ ENNReal.ofReal 64 * circleMaximalMeasure Ω := by
      gcongr
      apply iUnion_subset
      intro i x hx
      have hx' := d.core_subset_piece i hx
      exact d.piece_subset_Ω i hx'

end BrownianSharp.External.WeakCZ
