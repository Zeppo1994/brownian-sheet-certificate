import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperMixedWeight

def mixedWeight {d : ℕ} (r : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∏ i, (1 + x i ^ 2) ^ r

theorem scalarWeight_moderate (r : ℝ) (hr : 0 ≤ r) (x y : ℝ) :
    (1 + x ^ 2) ^ r ≤
      (2 : ℝ) ^ r * (1 + (x - y) ^ 2) ^ r * (1 + y ^ 2) ^ r := by
  have hbase : 1 + x ^ 2 ≤ 2 * (1 + (x-y)^2) * (1 + y^2) := by
    nlinarith [sq_nonneg (x - 2*y), sq_nonneg ((x-y)*y)]
  have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1 + x^2) hbase hr
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * (1 + (x-y)^2)) (by positivity),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)] at h
  exact h

theorem mixedWeight_pos {d : ℕ} (r : ℝ) (x : Fin d → ℝ) :
    0 < mixedWeight r x := by
  apply Finset.prod_pos
  intro i _
  exact Real.rpow_pos_of_pos (by positivity) _

theorem mixedWeight_moderate {d : ℕ} (r : ℝ) (hr : 0 ≤ r) (x y : Fin d → ℝ) :
    mixedWeight r x ≤ (2 : ℝ) ^ (r * d) * mixedWeight r (x-y) * mixedWeight r y := by
  unfold mixedWeight
  calc
    (∏ i, (1 + x i ^ 2) ^ r) ≤
        ∏ i, ((2 : ℝ) ^ r * (1 + (x i-y i)^2) ^ r * (1+y i^2)^r) := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact Real.rpow_nonneg (by positivity) _
      · intro i _
        exact scalarWeight_moderate r hr (x i) (y i)
    _ = (2 : ℝ) ^ (r * d) *
        (∏ i, (1 + (x i-y i)^2)^r) * (∏ i, (1+y i^2)^r) := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2)]
    _ = _ := by rfl

theorem mixedWeight_ratio_le {d : ℕ} (r : ℝ) (hr : 0 ≤ r) (x y : Fin d → ℝ) :
    mixedWeight r x / mixedWeight r y ≤
      (2 : ℝ) ^ (r * d) * mixedWeight r (x-y) := by
  apply (div_le_iff₀ (mixedWeight_pos r y)).2
  exact mixedWeight_moderate r hr x y

end BrownianSharp.AlignmentPaperMixedWeight
