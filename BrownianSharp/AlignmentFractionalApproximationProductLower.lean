import BrownianSharp.AlignmentApproximationNumberClosure
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The quantitative lower-bound consequence of the actual product law. -/
noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentFractionalApproximationProductLower
open AlignmentFractionalApproximationNumbers AlignmentApproximationNumberClosure
universe u
variable {X Y Z : Type u}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem approximationNumber_lower_of_composition
    (S : Y →L[ℝ] Z) (T : X →L[ℝ] Y)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (A B : ℝ) (hB : 0 < B)
    (hlower : ENNReal.ofReal A ≤ approximationNumber (S.comp T) (m+n-1))
    (hupper : approximationNumber T n ≤ ENNReal.ofReal B) :
    ENNReal.ofReal (A/B) ≤ approximationNumber S m := by
  rw [ENNReal.ofReal_div_of_pos hB]
  apply (ENNReal.div_le_iff (ENNReal.ofReal_ne_zero_iff.mpr hB) ENNReal.ofReal_ne_top).mpr
  exact hlower.trans ((approximationNumber_product S T hm hn).trans
    (mul_le_mul' le_rfl hupper))

theorem power_log_rate_quotient (x y c C M β a : ℝ) (hx : 0 < x) (hy : 0 < y) :
    (c*(x^(-M+1/2)*y^(M*a))) / (C*(x^(-β)*y^(β*a))) =
      (c/C)*(x^(-(M-β)+1/2)*y^((M-β)*a)) := by
  have heqX : -(M-β)+1/2 = (-M+1/2)-(-β) := by ring
  have heqY : (M-β)*a = M*a-β*a := by ring
  rw [heqX,heqY,Real.rpow_sub hx,Real.rpow_sub hy]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

theorem approximationNumber_lower_power_log
    (S : Y →L[ℝ] Z) (T : X →L[ℝ] Y)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (x y c C M β a : ℝ) (hx : 0 < x) (hy : 0 < y) (hC : 0 < C)
    (hlower : ENNReal.ofReal (c*(x^(-M+1/2)*y^(M*a))) ≤
      approximationNumber (S.comp T) (m+n-1))
    (hupper : approximationNumber T n ≤
      ENNReal.ofReal (C*(x^(-β)*y^(β*a)))) :
    ENNReal.ofReal ((c/C)*(x^(-(M-β)+1/2)*y^((M-β)*a))) ≤
      approximationNumber S m := by
  have hden : 0 < C*(x^(-β)*y^(β*a)) :=
    mul_pos hC (mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _))
  have h := approximationNumber_lower_of_composition S T hm hn
    (c*(x^(-M+1/2)*y^(M*a))) (C*(x^(-β)*y^(β*a))) hden hlower hupper
  simpa only [power_log_rate_quotient x y c C M β a hx hy] using h

end BrownianSharp.AlignmentFractionalApproximationProductLower
