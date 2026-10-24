import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.Real

/-! Positivity of origin balls from a self-difference scaling identity.
The argument uses only support and product-measure facts, not Gaussianity. -/

open MeasureTheory
open scoped Topology

namespace HaarQuarter.BrownianOriginBallPositivity

theorem originBall_pos_of_difference_scaling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hLaw : (μ.prod μ).map (fun z : E × E => z.1 - z.2) =
      μ.map (fun x : E => c • x)) :
    ∀ ε : ℝ, 0 < ε → 0 < μ (Metric.ball (0 : E) ε) := by
  intro ε hε
  have hμne : μ ≠ 0 := by
    intro hzero
    have h : μ Set.univ = 0 := by rw [hzero]; simp
    rw [measure_univ] at h
    norm_num at h
  obtain ⟨a, ha⟩ := μ.nonempty_support hμne
  let δ : ℝ := c * ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hnear : 0 < μ (Metric.ball a δ) := by
    apply (Measure.mem_support_iff_forall a).mp ha (Metric.ball a δ)
    exact Metric.ball_mem_nhds _ hδ
  have hproduct : 0 < (μ.prod μ)
      (Metric.ball a δ ×ˢ Metric.ball a δ) := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_pos (ne_of_gt hnear) (ne_of_gt hnear)
  let diff : E × E → E := fun z => z.1 - z.2
  have hsubset : Metric.ball a δ ×ˢ Metric.ball a δ ⊆
      diff ⁻¹' Metric.ball (0 : E) (c * ε) := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hx' : ‖x - a‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hy' : ‖y - a‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hy
    have hxy : ‖x - y‖ ≤ ‖x - a‖ + ‖y - a‖ := by
      calc
        ‖x - y‖ = ‖(x - a) - (y - a)‖ := by congr 1; abel
        _ ≤ ‖x - a‖ + ‖y - a‖ := norm_sub_le _ _
    have hbound : ‖x - y‖ < c * ε := by
      dsimp [δ] at hx' hy'
      nlinarith [hxy]
    change diff (x, y) ∈ Metric.ball (0 : E) (c * ε)
    simpa [Metric.mem_ball, dist_eq_norm, diff] using hbound
  have hdiff : 0 < (μ.prod μ) (diff ⁻¹' Metric.ball (0 : E) (c * ε)) :=
    lt_of_lt_of_le hproduct (measure_mono hsubset)
  have hmeasDiff : Measurable diff := by
    dsimp [diff]
    exact measurable_fst.sub measurable_snd
  have hpush : 0 < ((μ.prod μ).map diff) (Metric.ball (0 : E) (c * ε)) := by
    rw [Measure.map_apply hmeasDiff measurableSet_ball]
    exact hdiff
  have hscaled : 0 < (μ.map (fun x : E => c • x))
      (Metric.ball (0 : E) (c * ε)) := by
    rw [← hLaw]
    exact hpush
  have hpre : (fun x : E => c • x) ⁻¹' Metric.ball (0 : E) (c * ε) =
      Metric.ball (0 : E) ε := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hc]
    constructor
    · intro hx
      by_contra hn
      have hle : ε ≤ ‖x‖ := le_of_not_gt hn
      have hmul := mul_le_mul_of_nonneg_left hle hc.le
      nlinarith
    · intro hx
      exact mul_lt_mul_of_pos_left hx hc
  have hmeasScale : Measurable (fun x : E => c • x) := by fun_prop
  rw [Measure.map_apply hmeasScale measurableSet_ball, hpre] at hscaled
  exact hscaled

theorem originClosedBall_pos_of_difference_scaling
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (c : ℝ) (hc : 0 < c)
    (hLaw : (μ.prod μ).map (fun z : E × E => z.1 - z.2) =
      μ.map (fun x : E => c • x)) :
    ∀ ε : ℝ, 0 < ε → 0 < μ (Metric.closedBall (0 : E) ε) := by
  intro ε hε
  have hopen := originBall_pos_of_difference_scaling μ c hc hLaw ε hε
  exact lt_of_lt_of_le hopen (measure_mono Metric.ball_subset_closedBall)

end HaarQuarter.BrownianOriginBallPositivity

namespace HaarQuarter

/-- A measurable random vector with the centered-Gaussian copy-difference
scaling law has positive probability in every closed ball about zero. -/
theorem probability_norm_le_pos_of_copyDifferenceLaw
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Ω → E) (hF : Measurable F) (c : ℝ) (hc : 0 < c)
    (hcopy : (P.prod P).map (fun z : Ω × Ω => F z.1 - F z.2) =
      P.map (fun ω => c • F ω)) :
    ∀ ε : ℝ, 0 < ε → 0 < P.real {ω | ‖F ω‖ ≤ ε} := by
  intro ε hε
  let μ : Measure E := P.map F
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  have hprod : μ.prod μ = (P.prod P).map (Prod.map F F) :=
    Measure.map_prod_map P P hF hF
  have hdiff : Measurable (fun z : E × E => z.1 - z.2) :=
    measurable_fst.sub measurable_snd
  have hscale : Measurable (fun x : E => c • x) := by fun_prop
  have hLaw : (μ.prod μ).map (fun z : E × E => z.1 - z.2) =
      μ.map (fun x : E => c • x) := by
    rw [hprod, Measure.map_map hdiff (hF.prodMap hF)]
    change (P.prod P).map (fun z : Ω × Ω => F z.1 - F z.2) =
      (P.map F).map (fun x : E => c • x)
    rw [Measure.map_map hscale hF]
    exact hcopy
  have hpos := BrownianOriginBallPositivity.originClosedBall_pos_of_difference_scaling
    μ c hc hLaw ε hε
  have hpre : F ⁻¹' Metric.closedBall (0 : E) ε = {ω | ‖F ω‖ ≤ ε} := by
    ext ω
    simp [Metric.mem_closedBall, dist_zero_right]
  change 0 < (P.map F) (Metric.closedBall (0 : E) ε) at hpos
  rw [Measure.map_apply hF measurableSet_closedBall, hpre] at hpos
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top P _)


end HaarQuarter
