import BrownianSharp.AlignmentMaternSpectralWindow
import BrownianSharp.AlignmentPeriodicWindowEntropy
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! A fixed positive spectral window on the whole unit cube. -/
noncomputable section
open HaarQuarter
open scoped BigOperators
namespace BrownianSharp.AlignmentMaternWindowWeight
open AlignmentMaternSpectralWindow


theorem windowMultiplier_eq_sinc (a t : ℝ) :
    windowMultiplier a t = a * Real.sinc (Real.pi*a*t) := by
  by_cases ht : t=0
  · subst t
    simp [windowMultiplier]
  by_cases ha : a=0
  · subst a
    simp [windowMultiplier,ht]
  rw [windowMultiplier,if_neg ht,Real.sinc_of_ne_zero
    (mul_ne_zero (mul_ne_zero Real.pi_ne_zero ha) ht)]
  field_simp

def cubeWindowWeight (d : ℕ) (a : ℝ) : C(BrownianCubeAnchor d,ℝ) where
  toFun t := ∏ i, windowMultiplier a (t.1 i)
  continuous_toFun := by
    simp_rw [windowMultiplier_eq_sinc]
    apply continuous_finset_prod
    intro i hi
    have ht : Continuous (fun t : BrownianCubeAnchor d => t.1 i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact continuous_const.mul (Real.continuous_sinc.comp (continuous_const.mul ht))

theorem cubeWindowWeight_apply (d : ℕ) (a : ℝ) (t : BrownianCubeAnchor d) :
    cubeWindowWeight d a t = ∏ i, windowMultiplier a (t.1 i) := rfl

theorem cubeWindowWeight_lower (d : ℕ) (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1/2)
    (t : BrownianCubeAnchor d) :
    (a*(2/Real.pi))^d ≤ ‖cubeWindowWeight d a t‖ := by
  have hpos : 0 < ∏ i : Fin d, windowMultiplier a (t.1 i) := by
    apply Finset.prod_pos
    intro i hi
    exact windowMultiplier_pos_on_unit a ha0 ha1 (t.1 i) (t.2 i).1 (t.2 i).2
  rw [Real.norm_eq_abs, cubeWindowWeight_apply,abs_of_pos hpos]
  calc
    (a*(2/Real.pi))^d = ∏ _i : Fin d, a*(2/Real.pi) := by simp
    _ ≤ ∏ i : Fin d, windowMultiplier a (t.1 i) := by
      apply Finset.prod_le_prod₀
      · intro i hi; positivity
      · intro i hi
        exact windowMultiplier_lower_on_unit a ha0 ha1 (t.1 i) (t.2 i).1 (t.2 i).2

theorem fixedCubeWindowWeight_lower (d : ℕ) :
    0 < ((1/4:ℝ)*(2/Real.pi))^d ∧
    ∀ t, ((1/4:ℝ)*(2/Real.pi))^d ≤ ‖cubeWindowWeight d (1/4) t‖ :=
  ⟨by positivity, cubeWindowWeight_lower d (1/4) (by norm_num) (by norm_num)⟩

end BrownianSharp.AlignmentMaternWindowWeight
