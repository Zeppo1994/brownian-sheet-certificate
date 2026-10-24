import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-! A bounded second derivative controls centered second differences. -/

open Set

namespace BrownianSharp

private theorem abs_centeredSecondDifference_le_of_pos
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : ∀ y, |iteratedDeriv 2 f y| ≤ M) {x h : ℝ} (hh : 0 < h) :
    |f (x + h) - 2 * f x + f (x - h)| ≤ 2 * M * h ^ 2 := by
  have hMnonneg : 0 ≤ M := le_trans (abs_nonneg (iteratedDeriv 2 f x)) (hM x)
  have hcont : Continuous f := hf.continuous
  have hdiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hcontPlus : ContinuousOn f (Icc x (x + h)) := hcont.continuousOn
  have hcontMinus : ContinuousOn f (Icc (x - h) x) := hcont.continuousOn
  have hdiffPlus : DifferentiableOn ℝ f (Ioo x (x + h)) := hdiff.differentiableOn
  have hdiffMinus : DifferentiableOn ℝ f (Ioo (x - h) x) := hdiff.differentiableOn
  obtain ⟨u, hu, huEq⟩ := exists_deriv_eq_slope (a := x) (b := x + h)
    f (by linarith) hcontPlus hdiffPlus
  obtain ⟨v, hv, hvEq⟩ := exists_deriv_eq_slope (a := x - h) (b := x)
    f (sub_lt_self x hh) hcontMinus hdiffMinus
  have huBounds : x < u ∧ u < x + h := hu
  have hvBounds : x - h < v ∧ v < x := hv
  have huv : 0 ≤ u - v ∧ u - v ≤ 2 * h := by
    constructor <;> linarith
  have hderivDiff : ∀ y, HasDerivAt (deriv f) (iteratedDeriv 2 f y) y := by
    intro y
    have hd := hf.differentiable_iteratedDeriv 1 (by norm_num)
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using hd y |>.hasDerivAt
  have hLip : |deriv f u - deriv f v| ≤ M * (u - v) := by
    have hseg := norm_image_sub_le_of_norm_deriv_le_segment' (f := deriv f)
      (a := v) (b := u) (C := M)
      (fun y hy => (hderivDiff y).hasDerivWithinAt)
      (fun y hy => by simpa [Real.norm_eq_abs] using hM y)
      u (right_mem_Icc.mpr (sub_nonneg.mp huv.1))
    simpa [Real.norm_eq_abs] using hseg
  have hcenter : f (x + h) - 2 * f x + f (x - h) =
      h * (deriv f u - deriv f v) := by
    rw [huEq, hvEq]
    field_simp [ne_of_gt hh]
    ring
  rw [hcenter, abs_mul, abs_of_pos hh]
  calc
    h * |deriv f u - deriv f v| ≤ h * (M * (u - v)) := mul_le_mul_of_nonneg_left hLip hh.le
    _ ≤ h * (M * (2 * h)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left huv.2 hMnonneg) hh.le
    _ = 2 * M * h ^ 2 := by ring

theorem abs_centeredSecondDifference_le_of_iteratedDeriv_two
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M : ℝ}
    (hM : ∀ y, |iteratedDeriv 2 f y| ≤ M) (x h : ℝ) :
    |f (x + h) - 2 * f x + f (x - h)| ≤ 2 * M * h ^ 2 := by
  by_cases hh : 0 ≤ h
  · rcases eq_or_lt_of_le hh with rfl | hh
    · have hz : f (x + 0) - 2 * f x + f (x - 0) = 0 := by simp; ring
      rw [hz]
      norm_num
    · exact abs_centeredSecondDifference_le_of_pos hf hM hh
  · have hp : 0 < -h := neg_pos.mpr (lt_of_not_ge hh)
    have hbound := abs_centeredSecondDifference_le_of_pos (x := x) (h := -h) hf hM hp
    have hswap : f (x + h) - 2 * f x + f (x - h) =
        f (x + -h) - 2 * f x + f (x - (-h)) := by simp; ring
    rw [hswap]
    simpa [sub_eq_add_neg, pow_two] using hbound

end BrownianSharp
