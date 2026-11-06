import BrownianSharp.AlignmentPaperKernelHörmander
import Mathlib.Analysis.Normed.Group.AddCircle

/-! Translate the kernel's character-chord cutoff to the actual circle
metric used by the Whitney bad-ball decomposition. -/
noncomputable section
open Metric
namespace BrownianSharp.AlignmentPaperCircleKernelGeometry
open BrownianSharp.AlignmentPaperFejerPointwise
open BrownianSharp.AlignmentPaperKernelTranslation
open BrownianSharp.AlignmentPaperKernelHörmander
open HaarQuarter.TrigonometricHaarExtraction

private theorem circleChord_coe (t : ℝ) :
    circleCharacterChord (t:UnitAddCircle) = characterChord t := by
  unfold circleCharacterChord characterChord
  rw [show fourier (T := (1:ℝ)) 1 (t:UnitAddCircle) = character 1 t by
    simpa [HaarQuarter.TrigonometricHaarExtraction.addCircleCharacter] using
      HaarQuarter.TrigonometricHaarExtraction.addCircleCharacter_coe (1:ℤ) t]

theorem circleCharacterChord_ge_four_dist (x : UnitAddCircle) :
    4*dist x 0 ≤ circleCharacterChord x := by
  let t := AddCircle.equivIoc (1:ℝ) (-1/2:ℝ) x
  have ht : |(t:ℝ)| ≤ 1/2 := by
    have hmem := t.property
    norm_num only at hmem
    rw [abs_le]
    constructor <;> linarith [hmem.1,hmem.2]
  have hcoe : ((t:ℝ):UnitAddCircle) = x := AddCircle.coe_equivIoc
  have hnorm : ‖((t:ℝ):UnitAddCircle)‖ = |(t:ℝ)| := by
    apply (AddCircle.norm_coe_eq_abs_iff (1:ℝ) (by norm_num : (1:ℝ) ≠ 0)).2
    simpa using ht
  have hchord := characterChord_lower_four_abs ht
  rw [← circleChord_coe] at hchord
  rw [← hnorm,hcoe] at hchord
  simpa only [dist_zero_right] using hchord

/-- Enlarging the exceptional core balls by 64 is sufficient for the
analytic Hörmander cutoff for every source point in a 5-fold core ball. -/
theorem circle_far_of_outside_sixtyFour_ball
    {r h : ℝ} (hr : 0 ≤ r) (hh : |h| ≤ 5*r) (x : UnitAddCircle)
    (hx : x ∉ ball (0:UnitAddCircle) (64*r)) :
    8*Real.pi*|h| ≤ circleCharacterChord x := by
  have hdist : 64*r ≤ dist x 0 := by
    exact not_lt.mp hx
  calc
    8*Real.pi*|h| ≤ 8*Real.pi*(5*r) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = 40*Real.pi*r := by ring
    _ ≤ 160*r := by nlinarith [mul_nonneg hr (show 0 ≤ 4-Real.pi by linarith [Real.pi_lt_four])]
    _ ≤ 256*r := by linarith
    _ ≤ 4*dist x 0 := by linarith
    _ ≤ circleCharacterChord x := circleCharacterChord_ge_four_dist x

end BrownianSharp.AlignmentPaperCircleKernelGeometry
