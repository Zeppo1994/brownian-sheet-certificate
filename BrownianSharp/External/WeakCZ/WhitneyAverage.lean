import BrownianSharp.External.WeakCZ.AverageControl
import BrownianSharp.External.WeakCZ.CircleMaximal
import BrownianSharp.AlignmentPaperCircleDoubling
import BrownianSharp.UnitTorusMeasure
import Mathlib.MeasureTheory.Group.AddCircle

/-!
The contact geometry of the Whitney balls bounds the average of the input on
an expanded partition piece. The estimate uses the actual Haar ball scaling on
the normalized circle.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace BrownianSharp.External.WeakCZ

/-- If a Whitney expanded piece is contained in the fivefold ball and its
sevenfold ball touches the complement of the uncentered high-average set,
then its input mass is bounded by twelve times the threshold times the core
mass. -/
theorem lintegral_whitney_piece_le
    (f : UnitAddCircle → ℂ) (Ω E : Set UnitAddCircle)
    (center : UnitAddCircle) (r level : ℝ)
    (hr : 0 < r) (hlevel : 0 ≤ level)
    (hE : E ⊆ ball center (5*r))
    (hcontact : ¬ Disjoint (ball center (7*r)) Ωᶜ)
    (houtside : ∀ z ∉ Ω, ∀ R : ℝ, 0 < R →
      ∫⁻ x in ball z R, ‖f x‖ₑ ∂volume ≤ ENNReal.ofReal level * volume (ball z R)) :
    ∫⁻ x in E, ‖f x‖ₑ ∂volume ≤
      ENNReal.ofReal (12*level) * volume (ball center r) := by
  obtain ⟨z, hz⟩ := (not_disjoint_iff_nonempty_inter.mp hcontact)
  have hz₁ : z ∈ ball center (7*r) := hz.1
  have hz₂ : z ∉ Ω := hz.2
  have hEball : E ⊆ ball z (12*r) := by
    intro x hx
    have hxc := hE hx
    rw [mem_ball] at hz₁ hxc ⊢
    have htri : dist z x ≤ dist z center + dist center x := dist_triangle _ _ _
    have hz' : dist z center < 7*r := by simpa [dist_comm] using hz₁
    have hxc' : dist center x < 5*r := by simpa [dist_comm] using hxc
    calc
      dist x z = dist z x := dist_comm _ _
      _ ≤ dist z center + dist center x := htri
      _ < 12*r := by nlinarith [hz', hxc', hr]
  have hmass : ∫⁻ x in E, ‖f x‖ₑ ∂volume ≤
      ENNReal.ofReal level * volume (ball z (12*r)) := by
    calc
      _ ≤ ∫⁻ x in ball z (12*r), ‖f x‖ₑ ∂volume :=
        lintegral_mono_set hEball
    _ ≤ ENNReal.ofReal level * volume (ball z (12*r)) := houtside z hz₂ (12*r) (by positivity)
  have hscale : volume (ball z (12*r)) ≤ ENNReal.ofReal 12 * volume (ball center r) := by
    calc
      volume (ball z (12*r)) = AddCircle.haarAddCircle (ball z (12*r)) := by
        rw [BrownianSharp.unitAddCircle_volume_eq_haar]
      _ ≤ ENNReal.ofReal 12 * AddCircle.haarAddCircle (ball z r) :=
        BrownianSharp.AlignmentPaperCircleDoubling.haar_ball_scale_le z r 12 (by norm_num)
      _ = ENNReal.ofReal 12 * AddCircle.haarAddCircle (ball center r) := by
        rw [BrownianSharp.AlignmentPaperCircleDoubling.haar_ball,
          BrownianSharp.AlignmentPaperCircleDoubling.haar_ball]
      _ = ENNReal.ofReal 12 * volume (ball center r) := by
        rw [← BrownianSharp.unitAddCircle_volume_eq_haar]
  calc
    _ ≤ ENNReal.ofReal level * volume (ball z (12*r)) := hmass
    _ ≤ ENNReal.ofReal level * (ENNReal.ofReal 12 * volume (ball center r)) :=
      mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = ENNReal.ofReal (12*level) * volume (ball center r) := by
      calc
        ENNReal.ofReal level * (ENNReal.ofReal 12 * volume (ball center r)) =
            (ENNReal.ofReal level * ENNReal.ofReal 12) * volume (ball center r) := by ac_rfl
        _ = ENNReal.ofReal (level*12) * volume (ball center r) := by
          rw [← ENNReal.ofReal_mul hlevel]
        _ = ENNReal.ofReal (12*level) * volume (ball center r) := by congr 2; ring

/-- The actual complex average over a Whitney partition piece is bounded by
twelve times the high-average threshold. -/
theorem norm_whitney_piece_average_le
    (f : UnitAddCircle → ℂ) (Ω E : Set UnitAddCircle)
    (center : UnitAddCircle) (r level : ℝ)
    (hfi : Integrable f volume) (_hEmeas : MeasurableSet E)
    (hcore : ball center r ⊆ E) (hcorepos : 0 < volume.real (ball center r))
    (hr : 0 < r) (hlevel : 0 ≤ level)
    (hE : E ⊆ ball center (5*r))
    (hcontact : ¬ Disjoint (ball center (7*r)) Ωᶜ)
    (houtside : ∀ z ∉ Ω, ∀ R : ℝ, 0 < R →
      ∫⁻ x in ball z R, ‖f x‖ₑ ∂volume ≤ ENNReal.ofReal level * volume (ball z R)) :
    ‖(volume.real E)⁻¹ • (∫ x in E, f x ∂volume)‖ ≤ 12*level := by
  apply norm_cell_average_le_of_core volume f hcore hcorepos
    ((hfi.integrableOn) ) (by positivity) ?_
  have hmass := lintegral_whitney_piece_le f Ω E center r level hr hlevel hE hcontact houtside
  have hmassReal : (∫ x in E, ‖f x‖ ∂volume) ≤
      12*level * volume.real (ball center r) := by
    have hcast : ∫⁻ x in E, (‖f x‖₊ : ℝ≥0∞) ≤
        ENNReal.ofReal (12*level) * volume (ball center r) := by
      simpa [enorm] using hmass
    have hfinite : (ENNReal.ofReal (12*level) * volume (ball center r)) ≠ ∞ := by
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    have hreal := ENNReal.toReal_mono hfinite hcast
    have hfiNN : Integrable (fun x => (‖f x‖₊ : ℝ)) (volume.restrict E) := by
      simpa [coe_nnnorm] using (hfi.integrableOn.norm)
    rw [lintegral_coe_eq_integral _ hfiNN] at hreal
    have hintnonneg : 0 ≤ ∫ x in E, (‖f x‖₊ : ℝ) ∂volume :=
      integral_nonneg (fun x => NNReal.coe_nonneg _)
    rw [ENNReal.toReal_ofReal hintnonneg] at hreal
    have hfactor : (ENNReal.ofReal (12*level) * volume (ball center r)).toReal =
        12*level * volume.real (ball center r) := by
      simp [Measure.real_def, ENNReal.toReal_mul, hlevel]
    calc
      ∫ x in E, ‖f x‖ ∂volume = ∫ x in E, (‖f x‖₊ : ℝ) ∂volume := by
        simp [coe_nnnorm]
      _ ≤ (ENNReal.ofReal (12*level) * volume (ball center r)).toReal := hreal
      _ = 12*level * volume.real (ball center r) := hfactor
  exact hmassReal

/-- Actual high-average-set specialization of the Whitney average bound. -/
theorem norm_circleHighAverage_piece_average_le
    (f : UnitAddCircle → ℂ) (level : ℝ) (E : Set UnitAddCircle)
    (center : UnitAddCircle) (r : ℝ)
    (hfi : Integrable f volume) (hEmeas : MeasurableSet E)
    (hcore : ball center r ⊆ E) (hcorepos : 0 < volume.real (ball center r))
    (hr : 0 < r) (hlevel : 0 ≤ level)
    (hE : E ⊆ ball center (5*r))
    (hcontact : ¬ Disjoint (ball center (7*r))
      (circleHighAverageSet f level)ᶜ) :
    ‖(volume.real E)⁻¹ • (∫ x in E, f x ∂volume)‖ ≤ 12*level := by
  apply norm_whitney_piece_average_le f (circleHighAverageSet f level) E
    center r level hfi hEmeas hcore hcorepos hr hlevel hE hcontact
  intro z hz R hR
  have h := circle_ball_integral_le_of_notMem_highAverageSet f level hz hR
    (mem_ball_self hR)
  simpa [circleMaximalMeasure, BrownianSharp.unitAddCircle_volume_eq_haar] using h

end BrownianSharp.External.WeakCZ
