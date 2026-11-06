import BrownianSharp.External.WeakCZ.CircleMaximal
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! The actual norm bound outside the circle bad set, using Mathlib's
Lebesgue differentiation theorem for centered closed balls. -/
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology
namespace BrownianSharp.External.WeakCZ
open BrownianSharp.AlignmentPaperCircleDoubling

local instance circleMaximalDoubling : IsUnifLocDoublingMeasure circleMaximalMeasure := by
  dsimp [circleMaximalMeasure]
  rw [← BrownianSharp.unitAddCircle_volume_eq_haar]
  infer_instance

theorem average_norm_ball_le_of_notMem_highAverageSet
    (f : UnitAddCircle → ℂ) (hf : Integrable f circleMaximalMeasure)
    {level : ℝ} (hlevel : 0 < level) {x center : UnitAddCircle}
    (hx : x ∉ circleHighAverageSet f level) {r : ℝ} (hr : 0 < r)
    (hball : x ∈ ball center r) :
    (⨍ z in ball center r, ‖f z‖ ∂circleMaximalMeasure) ≤ level := by
  have hI := circle_ball_integral_le_of_notMem_highAverageSet f level hx hr hball
  have hconv : ENNReal.ofReal (∫ z in ball center r, ‖f z‖ ∂circleMaximalMeasure) =
      ∫⁻ z in ball center r, ‖f z‖ₑ ∂circleMaximalMeasure := by
    exact ofReal_integral_norm_eq_lintegral_enorm
      (hf.mono_measure Measure.restrict_le_self)
  have hR : ENNReal.ofReal level * circleMaximalMeasure (ball center r) =
      ENNReal.ofReal (level * circleMaximalMeasure.real (ball center r)) := by
    symm
    rw [ENNReal.ofReal_mul hlevel.le]
    congr 1
    exact ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [← hconv,hR] at hI
  have hreal : (∫ z in ball center r, ‖f z‖ ∂circleMaximalMeasure) ≤
      level * circleMaximalMeasure.real (ball center r) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hI
  have hBpos : 0 < circleMaximalMeasure.real (ball center r) :=
    ENNReal.toReal_pos (haar_ball_pos center hr).ne' (measure_ne_top _ _)
  rw [setAverage_eq,smul_eq_mul]
  exact (inv_mul_le_iff₀ hBpos).2 (by simpa only [mul_comm] using hreal)

theorem average_norm_closedBall_le_of_notMem_highAverageSet
    (f : UnitAddCircle → ℂ) (hf : Integrable f circleMaximalMeasure)
    {level : ℝ} (hlevel : 0 < level) {x center : UnitAddCircle}
    (hx : x ∉ circleHighAverageSet f level) {r : ℝ} (hr : 0 < r)
    (hball : x ∈ ball center r) :
    (⨍ z in closedBall center r, ‖f z‖ ∂circleMaximalMeasure) ≤ level := by
  have hAE : closedBall center r =ᵐ[circleMaximalMeasure] ball center r := by
    dsimp [circleMaximalMeasure]
    rw [← BrownianSharp.unitAddCircle_volume_eq_haar]
    exact AddCircle.closedBall_ae_eq_ball
  rw [setAverage_congr hAE]
  exact average_norm_ball_le_of_notMem_highAverageSet f hf hlevel hx hr hball

/-- Outside the actual open high-average set, the original source has norm
at most the threshold almost everywhere. No extra differentiation premise. -/
theorem ae_norm_le_of_notMem_circleHighAverageSet
    (f : UnitAddCircle → ℂ) (hf : Integrable f circleMaximalMeasure)
    {level : ℝ} (hlevel : 0 < level) :
    ∀ᵐ x ∂circleMaximalMeasure, x ∉ circleHighAverageSet f level → ‖f x‖ ≤ level := by
  let δ : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hδpos : ∀ n, 0 < δ n := by intro n; dsimp [δ]; positivity
  have hδzero : Tendsto δ atTop (𝓝 (0:ℝ)) := by
    simpa [δ] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hδlim : Tendsto δ atTop (𝓝[>] (0:ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδzero,Eventually.of_forall hδpos⟩
  have hDiff := IsUnifLocDoublingMeasure.ae_tendsto_average circleMaximalMeasure
    hf.norm.locallyIntegrable (1:ℝ)
  filter_upwards [hDiff] with x hx
  intro hxout
  have hcenter : ∀ᶠ n in atTop, x ∈ closedBall x (1*δ n) := by
    filter_upwards with n
    exact mem_closedBall_self (by simpa using (hδpos n).le)
  have hconv := hx (fun _ : ℕ => x) δ hδlim hcenter
  apply le_of_tendsto hconv
  filter_upwards with n
  exact average_norm_closedBall_le_of_notMem_highAverageSet f hf hlevel hxout
    (hδpos n) (mem_ball_self (hδpos n))

end BrownianSharp.External.WeakCZ
