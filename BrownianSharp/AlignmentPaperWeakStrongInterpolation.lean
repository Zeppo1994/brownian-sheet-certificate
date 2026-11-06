import BrownianSharp.AlignmentPaperLpTailInterpolation
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic

/-! Weak-L1/strong-L2 truncation adapter. The operator decomposition and its
endpoint bounds are explicit inputs; the resulting p-moment estimate is
proved by Markov, a union bound, and Mathlib's layer-cake/Tonelli machinery.
This does not assume an Lp operator estimate. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperWeakStrongInterpolation

open BrownianSharp.AlignmentPaperLpTailInterpolation

def highPart {α E : Type*} [NormedAddCommGroup E]
    (f : α → E) (t : ℝ) (x : α) : E := if t < ‖f x‖ then f x else 0

def lowPart {α E : Type*} [NormedAddCommGroup E]
    (f : α → E) (t : ℝ) (x : α) : E := if ‖f x‖ ≤ t then f x else 0

theorem highPart_add_lowPart {α E : Type*} [NormedAddCommGroup E]
    (f : α → E) (t : ℝ) : highPart f t + lowPart f t = f := by
  funext x
  by_cases hx : t < ‖f x‖ <;> simp [highPart, lowPart, hx, not_lt.mp, not_le.mpr]

theorem highPart_measurable {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {f : α → E} (hf : Measurable f) (t : ℝ) : Measurable (highPart f t) := by
  exact Measurable.ite (measurableSet_lt measurable_const hf.norm) hf measurable_const

theorem lowPart_measurable {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {f : α → E} (hf : Measurable f) (t : ℝ) : Measurable (lowPart f t) := by
  exact Measurable.ite (measurableSet_le hf.norm measurable_const) hf measurable_const

/-- Markov's inequality in squared norm, with no default-valued Bochner
integral and no integrability assumption hidden in the statement. -/
theorem norm_tail_le_squared_moment
    {β E : Type*} [MeasurableSpace β] [NormedAddCommGroup E]
    (ν : Measure β) {g : β → E} (hg : AEStronglyMeasurable g ν)
    {t : ℝ} (ht : 0 < t) :
    ν {y | t < ‖g y‖} ≤
      (∫⁻ y, ENNReal.ofReal (‖g y‖ ^ 2) ∂ν) / ENNReal.ofReal (t^2) := by
  have hmeas : AEMeasurable (fun y => ENNReal.ofReal (‖g y‖ ^ 2)) ν :=
    (hg.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have hthreshold : ENNReal.ofReal (t^2) ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sq_pos_of_pos ht))
  apply (measure_mono (show {y | t < ‖g y‖} ⊆
    {y | ENNReal.ofReal (t^2) ≤ ENNReal.ofReal (‖g y‖ ^ 2)} from ?_)).trans
    (meas_ge_le_lintegral_div hmeas hthreshold ENNReal.ofReal_ne_top)
  intro y hy
  change t < ‖g y‖ at hy
  apply ENNReal.ofReal_le_ofReal
  nlinarith [norm_nonneg (g y)]

/-- Splitting an output into the high/low source responses turns endpoint
weak-L1 and squared-L2 bounds into the precise tails used by interpolation. -/
theorem norm_tail_le_of_weak_strong_truncations
    {α β E F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (μ : Measure α) (ν : Measure β)
    (f : α → E) (g : β → F) (H L : ℝ → β → F)
    {C₁ C₂ t : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (ht : 0 < t)
    (hdecomp : ∀ y, g y = H t y + L t y)
    (hLmeas : AEStronglyMeasurable (L t) ν)
    (hweak : ν {y | t < ‖H t y‖} ≤ ENNReal.ofReal (C₁/t) *
      ∫⁻ x, ENNReal.ofReal (‖highPart f t x‖) ∂μ)
    (hstrong : (∫⁻ y, ENNReal.ofReal (‖L t y‖^2) ∂ν) ≤
      ENNReal.ofReal C₂ * ∫⁻ x, ENNReal.ofReal (‖lowPart f t x‖^2) ∂μ) :
    ν {y | 2*t < ‖g y‖} ≤
      ENNReal.ofReal (C₁/t) *
        (∫⁻ x, if t < ‖f x‖ then ENNReal.ofReal (‖f x‖) else 0 ∂μ) +
      ENNReal.ofReal (C₂/t^2) *
        (∫⁻ x, if ‖f x‖ ≤ t then ENNReal.ofReal (‖f x‖ ^ (2:ℝ)) else 0 ∂μ) := by
  have hsubset : {y | 2*t < ‖g y‖} ⊆
      {y | t < ‖H t y‖} ∪ {y | t < ‖L t y‖} := by
    intro y hy
    change 2*t < ‖g y‖ at hy
    by_contra hn
    simp only [mem_union, mem_setOf_eq, not_or, not_lt] at hn
    obtain ⟨hn1,hn2⟩ := hn
    have hnorm := norm_add_le (H t y) (L t y)
    rw [← hdecomp y] at hnorm
    linarith
  have hdiv : (∫⁻ y, ENNReal.ofReal (‖L t y‖^2) ∂ν) / ENNReal.ofReal (t^2) ≤
      (ENNReal.ofReal C₂ * ∫⁻ x, ENNReal.ofReal (‖lowPart f t x‖^2) ∂μ) /
        ENNReal.ofReal (t^2) := by
    gcongr
  have hlo := (norm_tail_le_squared_moment ν hLmeas ht).trans hdiv
  have hhigh : (∫⁻ x, ENNReal.ofReal (‖highPart f t x‖) ∂μ) =
      ∫⁻ x, if t < ‖f x‖ then ENNReal.ofReal (‖f x‖) else 0 ∂μ := by
    apply lintegral_congr
    intro x
    by_cases hx : t < ‖f x‖ <;> simp [highPart, hx]
  have hlow : (∫⁻ x, ENNReal.ofReal (‖lowPart f t x‖^2) ∂μ) =
      ∫⁻ x, if ‖f x‖ ≤ t then ENNReal.ofReal (‖f x‖ ^ (2:ℝ)) else 0 ∂μ := by
    apply lintegral_congr
    intro x
    by_cases hx : ‖f x‖ ≤ t <;> simp [lowPart, hx]
  have hfactor : (ENNReal.ofReal C₂ *
      ∫⁻ x, ENNReal.ofReal (‖lowPart f t x‖^2) ∂μ) / ENNReal.ofReal (t^2) =
      ENNReal.ofReal (C₂/t^2) *
        ∫⁻ x, if ‖f x‖ ≤ t then ENNReal.ofReal (‖f x‖ ^ (2:ℝ)) else 0 ∂μ := by
    rw [ENNReal.ofReal_div_of_pos (sq_pos_of_pos ht), hlow]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hfactor] at hlo
  rw [hhigh] at hweak
  exact ((measure_mono hsubset).trans (measure_union_le _ _)).trans
    (add_le_add hweak hlo)

/-- Uniform endpoint bounds on the actual truncated responses imply a finite
p-moment bound; no desired Lp estimate appears as a premise. -/
theorem half_moment_le_of_weak_strong_truncations
    {α β E F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F]
    (μ : Measure α) [SFinite μ] (ν : Measure β)
    (f : α → E) (g : β → F) (H L : ℝ → β → F)
    (hf : Measurable f) (hg : AEStronglyMeasurable g ν)
    {p C₁ C₂ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hdecomp : ∀ t > 0, ∀ y, g y = H t y + L t y)
    (hLmeas : ∀ t > 0, AEStronglyMeasurable (L t) ν)
    (hweak : ∀ t > 0, ν {y | t < ‖H t y‖} ≤ ENNReal.ofReal (C₁/t) *
      ∫⁻ x, ENNReal.ofReal (‖highPart f t x‖) ∂μ)
    (hstrong : ∀ t > 0, (∫⁻ y, ENNReal.ofReal (‖L t y‖^2) ∂ν) ≤
      ENNReal.ofReal C₂ * ∫⁻ x, ENNReal.ofReal (‖lowPart f t x‖^2) ∂μ) :
    (∫⁻ y, ENNReal.ofReal ((‖g y‖/2)^p) ∂ν) ≤
      ENNReal.ofReal (p*C₁/(p-1) + p*C₂/(2-p)) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ := by
  apply half_moment_le_const_mul_source_of_truncated_tails μ ν hf.norm
    hg.norm.aemeasurable (fun x => norm_nonneg _) (fun y => norm_nonneg _)
    hp1 hp2 hC₁ hC₂
  intro t ht
  exact norm_tail_le_of_weak_strong_truncations μ ν f g H L hC₁ hC₂ ht
    (hdecomp t ht) (hLmeas t ht) (hweak t ht) (hstrong t ht)

/-- The harmless factor two in the tail split contributes exactly 2^p. -/
theorem norm_moment_eq_two_rpow_mul_half
    {β F : Type*} [MeasurableSpace β] [NormedAddCommGroup F]
    (ν : Measure β) (g : β → F) (p : ℝ) :
    (∫⁻ y, ENNReal.ofReal (‖g y‖^p) ∂ν) =
      ENNReal.ofReal ((2:ℝ)^p) *
        ∫⁻ y, ENNReal.ofReal ((‖g y‖/2)^p) ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro y
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) p),
    Real.div_rpow (norm_nonneg _) (by norm_num)]
  congr 1
  field_simp [ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) p)]

/-- Remove the half-output normalization after the interpolation estimate. -/
theorem norm_moment_le_of_half_moment
    {α β E F : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (μ : Measure α) (ν : Measure β) (f : α → E) (g : β → F)
    (p C : ℝ)
    (h : (∫⁻ y, ENNReal.ofReal ((‖g y‖/2)^p) ∂ν) ≤
      ENNReal.ofReal C * ∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ) :
    (∫⁻ y, ENNReal.ofReal (‖g y‖^p) ∂ν) ≤
      ENNReal.ofReal ((2:ℝ)^p*C) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ := by
  rw [norm_moment_eq_two_rpow_mul_half ν g p,
    ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) p), mul_assoc]
  gcongr

end BrownianSharp.AlignmentPaperWeakStrongInterpolation
