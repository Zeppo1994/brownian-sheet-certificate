import BrownianSharp.AlignmentPaperWeakStrongInterpolation
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Actual Lp-input interpolation for operators additive on integrable
functions. Source truncation membership and the output decomposition are
proved here, not left as unverified callback assumptions. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperWeakStrongOperator
open BrownianSharp.AlignmentPaperWeakStrongInterpolation

theorem lintegral_lp_output_le_of_weak_one_strong_two
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsFiniteMeasure μ] (ν : Measure β)
    (T : (α → ℂ) → β → ℂ)
    (hadd : ∀ f g, Integrable f μ → Integrable g μ → T (f+g) = T f + T g)
    (hmeas : ∀ f, Integrable f μ → AEStronglyMeasurable (T f) ν)
    {C₁ C₂ p : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hp1 : 1 < p) (hp2 : p < 2)
    (hweak : ∀ f, Integrable f μ → ∀ t > 0,
      ν {y | t < ‖T f y‖} ≤ ENNReal.ofReal (C₁/t) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖) ∂μ)
    (hstrong : ∀ f, MemLp f 2 μ →
      (∫⁻ y, ENNReal.ofReal (‖T f y‖^2) ∂ν) ≤
        ENNReal.ofReal C₂ * ∫⁻ x, ENNReal.ofReal (‖f x‖^2) ∂μ)
    (f : Lp ℂ (ENNReal.ofReal p) μ) :
    (∫⁻ y, ENNReal.ofReal (‖T f y‖^p) ∂ν) ≤
      ENNReal.ofReal ((2:ℝ)^p*(p*C₁/(p-1)+p*C₂/(2-p))) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ := by
  have hfMeas : Measurable (f : α → ℂ) := (Lp.stronglyMeasurable f).measurable
  have hfInt : Integrable (f : α → ℂ) μ :=
    (Lp.memLp f).integrable (by
      simpa using ENNReal.ofReal_le_ofReal hp1.le)
  have hHiInt : ∀ t : ℝ, Integrable (highPart (f : α → ℂ) t) μ := by
    intro t
    apply hfInt.norm.mono' (highPart_measurable hfMeas t).aestronglyMeasurable
    filter_upwards [] with x
    by_cases hx : t < ‖f x‖
    · simp [highPart,hx]
    · simp [highPart,hx]
  have hLoMem : ∀ t > 0, MemLp (lowPart (f : α → ℂ) t) 2 μ := by
    intro t ht
    apply MemLp.of_bound (lowPart_measurable hfMeas t).aestronglyMeasurable t
    filter_upwards [] with x
    by_cases hx : ‖f x‖ ≤ t
    · simpa [lowPart,hx] using hx
    · simpa [lowPart,hx] using ht.le
  have hLoInt : ∀ t > 0, Integrable (lowPart (f : α → ℂ) t) μ := by
    intro t ht
    exact (hLoMem t ht).integrable (by norm_num)
  have hHalf := half_moment_le_of_weak_strong_truncations μ ν
    (f : α → ℂ) (T f)
    (fun t => T (highPart (f : α → ℂ) t))
    (fun t => T (lowPart (f : α → ℂ) t))
    hfMeas (hmeas f hfInt) hp1 hp2 hC₁ hC₂
    (by
      intro t ht y
      have h := hadd (highPart (f : α → ℂ) t) (lowPart (f : α → ℂ) t)
        (hHiInt t) (hLoInt t ht)
      rw [highPart_add_lowPart] at h
      exact congrFun h y)
    (by intro t ht; exact hmeas _ (hLoInt t ht))
    (by intro t ht; exact hweak _ (hHiInt t) t ht)
    (by intro t ht; exact hstrong _ (hLoMem t ht))
  exact norm_moment_le_of_half_moment μ ν (f : α → ℂ) (T f) p _ hHalf

end BrownianSharp.AlignmentPaperWeakStrongOperator
