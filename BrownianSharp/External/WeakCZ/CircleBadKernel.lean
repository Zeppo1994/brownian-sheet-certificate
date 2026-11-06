import BrownianSharp.External.WeakCZ.IntegratedBadKernel
import BrownianSharp.AlignmentPaperCircleKernelGeometry
import BrownianSharp.AlignmentPaperKernelHörmander
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
The actual finite signed smooth-resolution kernel satisfies the integrated bad-piece
bound outside a 64-fold Whitney ball. The proof translates the output variable
to the center, applies the actual circle Hörmander estimate, then converts the
real norm integral into the restricted ENNReal form used by Tonelli.
-/

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4096
open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace BrownianSharp.External.WeakCZ

open BrownianSharp.AlignmentPaperKernelHörmander
open BrownianSharp.AlignmentPaperCircleKernelGeometry
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPaperFejerPointwise
open BrownianSharp.AlignmentPaperKernelTranslation

/-- The actual signed finite smooth-resolution kernel difference obeys a
uniform integral bound outside a 64-fold ball. The source point `y` may lie
anywhere in the fivefold core ball reserved by the CZ partition. -/
theorem exists_uniform_signedKernel_badPiece_lintegral :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (S : Finset ℕ) (coeff : ℕ → ℝ),
      (∀ s ∈ S, |coeff s| ≤ 1) → ∀ (center y : UnitAddCircle) (r : ℝ),
      0 ≤ r → y ∈ ball center (5*r) →
      ∫⁻ x, ‖circleSignedKernelDifference S coeff
          (AddCircle.equivIoc (1:ℝ) (-1/2:ℝ) (center-y) : ℝ) (x-center)‖ₑ ∂
          (volume.restrict (ball center (64*r))ᶜ) ≤ ENNReal.ofReal H := by
  obtain ⟨H, hH, hfar⟩ :=
    exists_smoothResolution_signedKernel_circle_norm_integral_and_integrable
  obtain ⟨C₀, hC₀, hsize⟩ :=
    BrownianSharp.AlignmentPaperSmoothKernelDecay.exists_smoothResolution_scalarKernel_chord_decay
  refine ⟨H, hH, ?_⟩
  intro S coeff hcoeff center y r hr hy
  let hrep := AddCircle.equivIoc (1:ℝ) (-1/2:ℝ) (center-y)
  let h : ℝ := hrep
  have hrep_mem := hrep.property
  have hhfund : |h| ≤ 1/2 := by
    rw [abs_le]
    constructor <;> dsimp [h] at * <;> norm_num only at hrep_mem <;> linarith [hrep_mem.1, hrep_mem.2]
  have hcoe : (h : UnitAddCircle) = center-y := by
    dsimp [h]
    exact AddCircle.coe_equivIoc
  have hnorm : ‖(h : UnitAddCircle)‖ = |h| := by
    apply (AddCircle.norm_coe_eq_abs_iff (p := (1:ℝ)) (by norm_num)).2
    simpa using hhfund
  have hh : |h| ≤ 5*r := by
    rw [← hnorm, hcoe, ← dist_eq_norm]
    have hy' : dist center y < 5*r := by
      simpa [Metric.mem_ball, dist_comm] using hy
    exact hy'.le
  let τ : UnitAddCircle → UnitAddCircle := fun x => x-center
  have hMP : MeasurePreserving τ volume volume := by
    simpa only [τ, sub_eq_add_neg] using
      (measurePreserving_add_right volume (-center))
  have hEmb : MeasurableEmbedding τ := by
    convert (MeasurableEquiv.subRight center).measurableEmbedding using 1
    ext x
    rfl
  have hfarData := hfar S coeff hcoeff h
  rcases hfarData with ⟨hfarInt, hfarBound⟩
  let f₀ : UnitAddCircle → ℂ := circleSignedKernelDifference S coeff h
  let g₀ : UnitAddCircle → ℝ := fun x => ‖circleFarSignedKernelDifference S coeff h x‖
  let f : UnitAddCircle → ℂ := f₀ ∘ τ
  let g : UnitAddCircle → ℝ := g₀ ∘ τ
  have hf : Integrable f volume := by
    exact (hMP.integrable_comp_of_integrable (f := τ) (g := f₀)
      (circleSignedKernelDifference_integrable C₀ hC₀ hsize S coeff hcoeff h))
  have hg : Integrable g volume := by
    exact hMP.integrable_comp_of_integrable (f := τ) (g := g₀) hfarInt.norm
  have hg₀ : 0 ≤ᵐ[volume] g := ae_of_all _ fun x => norm_nonneg _
  have hgbound : ∫ x, g x ∂volume ≤ H := by
    change ∫ x, g₀ (τ x) ∂volume ≤ H
    calc
      ∫ x, g₀ (τ x) ∂volume =
          ∫ x, ‖circleFarSignedKernelDifference S coeff h x‖ ∂volume :=
        hMP.integral_comp hEmb g₀
      _ ≤ H := hfarBound
  have hmeas : MeasurableSet ((ball center (64*r))ᶜ) := measurableSet_ball.compl
  have hpoint : ∀ x ∈ (ball center (64*r))ᶜ, ‖f x‖ ≤ g x := by
    intro x hx
    have hx' : x-center ∉ ball (0:UnitAddCircle) (64*r) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hcut := circle_far_of_outside_sixtyFour_ball hr hh (x-center) hx'
    dsimp [f, g]
    change ‖circleSignedKernelDifference S coeff h (x-center)‖ ≤
      ‖circleFarSignedKernelDifference S coeff h (x-center)‖
    simp [circleSignedKernelDifference, circleFarSignedKernelDifference,
      hcut, Real.norm_eq_abs]
  have h := lintegral_restrict_enorm_le_of_real_majorant
    volume (ball center (64*r))ᶜ f g H
    hmeas hf hg hg₀ hpoint hgbound
  simpa [f] using h

end BrownianSharp.External.WeakCZ
