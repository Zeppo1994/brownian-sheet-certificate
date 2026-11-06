import BrownianSharp.AlignmentPaperJointAdaptiveScalarSums

/-! The fixed low-grade radii have a uniformly summable geometric profile. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperJointLowGradeRadiusSum

open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums

/-- The low-grade target radii sum to at most twice the top-grade scale. -/
theorem low_target_radius_sum_le (N : ℕ) :
    (∑ i : Fin (N + 1),
      (2 : ℝ) ^ (-(N : ℝ)) * Real.sqrt (N + 1 : ℝ) *
        (2 : ℝ) ^ (-((N - i.val : ℕ) : ℝ))) ≤
      2 * (2 : ℝ) ^ (-(N : ℝ)) * Real.sqrt (N + 1 : ℝ) := by
  let E : ℝ := (2 : ℝ) ^ (-(N : ℝ)) * Real.sqrt (N + 1 : ℝ)
  have hgeom :
      (∑ i : Fin (N + 1), (2 : ℝ) ^ (-((N - i.val : ℕ) : ℝ))) =
        dyadicRadiusSum N 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (2 : ℝ) ^ (-((N - i : ℕ) : ℝ)))]
    calc
      (∑ i ∈ Finset.range (N + 1),
          (2 : ℝ) ^ (-((N - i : ℕ) : ℝ))) =
          ∑ i ∈ Finset.range (N + 1), ((1 : ℝ) / 2) ^ (N - i) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
            rw [Real.rpow_natCast]
            simp [div_eq_mul_inv, inv_pow]
      _ = ∑ i ∈ Finset.range (N + 1), ((1 : ℝ) / 2) ^ i := by
        rw [← Finset.sum_range_reflect]
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        have hiN : i ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        omega
      _ = dyadicRadiusSum N 1 := by simp [dyadicRadiusSum]
  have hsum :
      (∑ i : Fin (N + 1),
        (2 : ℝ) ^ (-(N : ℝ)) * Real.sqrt (N + 1 : ℝ) *
          (2 : ℝ) ^ (-((N - i.val : ℕ) : ℝ))) =
        E * dyadicRadiusSum N 1 := by
    calc
      _ = ∑ i : Fin (N + 1), E *
          (2 : ℝ) ^ (-((N - i.val : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro i hi
            dsimp [E]
      _ = E * ∑ i : Fin (N + 1),
          (2 : ℝ) ^ (-((N - i.val : ℕ) : ℝ)) := by rw [Finset.mul_sum]
      _ = E * dyadicRadiusSum N 1 := by rw [hgeom]
  rw [hsum]
  have hE : 0 ≤ E := by positivity
  have hradius := dyadicRadiusSum_le N (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [E]
  calc
    E * dyadicRadiusSum N 1 ≤ E * 2 := by
      have hradius' : dyadicRadiusSum N 1 ≤ 2 := by simpa using hradius
      exact mul_le_mul_of_nonneg_left hradius' hE
    _ = 2 * (2 : ℝ) ^ (-(N : ℝ)) * Real.sqrt (N + 1 : ℝ) := by
      dsimp [E]
      ring

end BrownianSharp.AlignmentPaperJointLowGradeRadiusSum

end
