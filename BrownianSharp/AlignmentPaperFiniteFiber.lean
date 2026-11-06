import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Tactic

noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperFiniteFiber

def multiplicity {m : ℕ} {X : Type*} [DecidableEq X] (x : Fin m → X) (y : X) : ℕ :=
  (Finset.univ.filter (fun j => x j = y)).card

theorem sum_inverse_multiplicity {m : ℕ} {X : Type*} [DecidableEq X]
    (x : Fin m → X) (y : X) (hy : y ∈ Set.range x) :
    ∑ i : Fin m, (if y = x i then (multiplicity x (x i) : ℝ≥0∞)⁻¹ else 0) = 1 := by
  classical
  have hpos : 0 < multiplicity x y := by
    obtain ⟨j,rfl⟩ := hy
    exact Finset.card_pos.mpr ⟨j, by simp [multiplicity]⟩
  calc
    _ = ∑ i : Fin m, (if x i = y then (multiplicity x y : ℝ≥0∞)⁻¹ else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases h : x i = y
      · simp [h]
      · simp [h, Ne.symm h]
    _ = (multiplicity x y : ℝ≥0∞) * (multiplicity x y : ℝ≥0∞)⁻¹ := by
      rw [← Finset.sum_filter]
      simp [multiplicity, nsmul_eq_mul]
    _ = 1 := ENNReal.mul_inv_cancel (by exact_mod_cast hpos.ne') (by simp)

end BrownianSharp.AlignmentPaperFiniteFiber
