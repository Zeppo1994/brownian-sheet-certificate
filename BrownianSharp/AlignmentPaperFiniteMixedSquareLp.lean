import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

namespace BrownianSharp.AlignmentPaperFiniteMixedSquareLp

/-- Finite mixed-norm Minkowski: the ℓ² sum of the scalar Lp norms is bounded
by the Lp norm of the pointwise ℓ² sum, for `1 < p ≤ 2`. -/
theorem finite_mixed_square_le_integral
    {S X : Type*} [Fintype S] [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    {p : ℝ} (hp1 : 1 < p) (hp2 : p ≤ 2)
    (u : S → C(X,ℂ)) :
    (∑ s : S, (∫ x, ‖u s x‖^p ∂μ)^(2/p))^(p/2) ≤
      ∫ x, (∑ s : S, ‖u s x‖^2)^(p/2) ∂μ := by
  classical
  have hp0 : 0 < p := by linarith
  have hqreal : 1 ≤ (2:ℝ)/p := by
    rw [one_le_div₀ hp0]
    linarith
  let q : ℝ≥0∞ := ENNReal.ofReal ((2:ℝ)/p)
  have hq : (1:ℝ≥0∞) ≤ q := by
    dsimp [q]
    simpa using ENNReal.ofReal_le_ofReal hqreal
  have hqtop : q ≠ ∞ := ENNReal.ofReal_ne_top
  haveI : Fact ((1:ℝ≥0∞) ≤ q) := ⟨hq⟩
  have hqpos : 0 < q.toReal := q.toReal_pos_iff_ne_top.mpr hqtop
  have hqreal' : q.toReal = (2:ℝ)/p := by
    dsimp [q]
    exact ENNReal.toReal_ofReal (by positivity)
  let F : X → PiLp q (fun _ : S => ℝ) :=
    fun x => WithLp.toLp q (fun s : S => ‖u s x‖^p)
  have hFcont : Continuous F := by
    dsimp [F]
    have ht : Continuous (@WithLp.toLp q (S → ℝ)) :=
      PiLp.continuous_toLp (p := q) (β := fun _ : S => ℝ)
    exact ht.comp (continuous_pi fun s => ((u s).continuous.norm).rpow_const
      (fun _ => Or.inr (le_of_lt hp0)))
  have hFint : Integrable F μ :=
    hFcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
  have hexp : (1:ℝ)/(2/p) = p/2 := by
    field_simp [ne_of_gt hp0]
  have hcoord (s : S) :
      (∫ x, F x ∂μ) s = ∫ x, ‖u s x‖^p ∂μ := by
    change PiLp.proj (p := q) (𝕜 := ℝ) (β := fun _ : S => ℝ) s
      (∫ x, F x ∂μ) = _
    exact (PiLp.proj (p := q) (𝕜 := ℝ) (β := fun _ : S => ℝ) s).integral_comp_comm
      hFint |>.symm
  have hnorm_integral :
      ‖∫ x, F x ∂μ‖ = (∑ s : S, (∫ x, ‖u s x‖^p ∂μ)^(2/p))^(p/2) := by
    rw [PiLp.norm_eq_sum hqpos, hqreal']
    rw [hexp]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    rw [hcoord s]
    have hnonnegI : 0 ≤ ∫ x, ‖u s x‖^p ∂μ :=
      integral_nonneg (fun x => by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonnegI]
  have hnorm_point (x : X) :
      ‖F x‖ = (∑ s : S, ‖u s x‖^2)^(p/2) := by
    rw [PiLp.norm_eq_sum hqpos, hqreal']
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    change ‖(WithLp.toLp q (fun t : S => ‖u t x‖^p) : PiLp q (fun _ : S => ℝ)) s‖^(2/p) = _
    rw [PiLp.toLp_apply]
    have hnonneg : 0 ≤ ‖u s x‖^p := Real.rpow_nonneg (norm_nonneg _) _
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    rw [← Real.rpow_mul (norm_nonneg (u s x))]
    rw [show p * (2 / p) = 2 by field_simp [ne_of_gt hp0]]
    exact Real.rpow_two _
  calc
    _ = ‖∫ x, F x ∂μ‖ := hnorm_integral.symm
    _ ≤ ∫ x, ‖F x‖ ∂μ := norm_integral_le_integral_norm F
    _ = ∫ x, (∑ s : S, ‖u s x‖^2)^(p/2) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact hnorm_point x

end BrownianSharp.AlignmentPaperFiniteMixedSquareLp
