import BrownianSharp.AlignmentPaperJointHeadOnly
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Scalar simplifications for the actual sparse-head tail radius. -/

noncomputable section

namespace BrownianSharp.AlignmentPaperJointRateScalars

theorem thresholdTailRadius_eq {p B : ℝ} {m : ℕ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B) (hm : 0 < m) :
    Real.sqrt ((B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p) =
      B * (m : ℝ) ^ (1 / 2 - 1 / p) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < (m : ℝ) ^ (1 / p) := by positivity
  have hbase : 0 < B / (m : ℝ) ^ (1 / p) := div_pos hB hden
  have hpow : 0 < 2 - p := by linarith
  have hprod : (B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p =
      (B * (m : ℝ) ^ (1 / 2 - 1 / p)) ^ 2 := by
    calc
      _ = (B ^ (2 - p) / ((m : ℝ) ^ (1 / p)) ^ (2 - p)) * B ^ p := by
        rw [Real.div_rpow hB.le (le_of_lt hden)]
      _ = (B ^ (2 - p) * B ^ p) * (m : ℝ) ^ (-((1 / p) * (2 - p))) := by
        rw [← Real.rpow_mul hmR.le, div_eq_mul_inv, ← Real.rpow_neg hmR.le]
        ring
      _ = B ^ 2 * (m : ℝ) ^ (2 * (1 / 2 - 1 / p)) := by
        rw [← Real.rpow_add hB]
        rw [show (2 - p) + p = (2 : ℝ) by ring]
        rw [show -((1 / p) * (2 - p)) = 2 * (1 / 2 - 1 / p) by field_simp; ring]
        rw [Real.rpow_two]
      _ = (B * (m : ℝ) ^ (1 / 2 - 1 / p)) ^ 2 := by
        rw [mul_pow]
        rw [show 2 * (1 / 2 - 1 / p) = (1 / 2 - 1 / p) * 2 by ring,
          Real.rpow_mul hmR.le]
        rw [Real.rpow_two]
  rw [hprod, Real.sqrt_sq_eq_abs,
    abs_of_pos (mul_pos hB (Real.rpow_pos_of_pos hmR _))]

theorem thresholdTailRadius_le_of_small_rank {p B L : ℝ} {m : ℕ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B) (hm : 0 < m)
    (hL : 0 < L) (hmL : (m : ℝ) ≤ 400 * L) :
    Real.sqrt ((B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p) ≤
      20 * B * Real.sqrt L * (m : ℝ) ^ (-1 / p) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  rw [thresholdTailRadius_eq hp hp2 hB hm]
  rw [show (1 / 2 - 1 / p : ℝ) = 1 / 2 + (-1 / p) by ring,
    Real.rpow_add hmR, ← Real.sqrt_eq_rpow]
  have hroot : Real.sqrt (m : ℝ) ≤ 20 * Real.sqrt L := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by norm_num)
      (Real.sqrt_nonneg _))).mp
    calc
      (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hmR.le
      _ ≤ 400 * L := hmL
      _ = (20 * Real.sqrt L) ^ 2 := by rw [mul_pow, Real.sq_sqrt hL.le]; norm_num
  have hfactor : 0 ≤ (m : ℝ) ^ (-1 / p) := Real.rpow_nonneg hmR.le _
  calc
    B * (Real.sqrt (m : ℝ) * (m : ℝ) ^ (-1 / p)) =
        (B * Real.sqrt (m : ℝ)) * (m : ℝ) ^ (-1 / p) := by ring
    _ ≤ (B * (20 * Real.sqrt L)) * (m : ℝ) ^ (-1 / p) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hroot hB.le) hfactor
    _ = 20 * B * Real.sqrt L * (m : ℝ) ^ (-1 / p) := by ring

theorem stageRadius_over_sqrt_le {p L : ℝ} {m s : ℕ}
    (hp : 1 < p) (hm : 0 < m) (hs : 0 < s) (hL : 0 < L)
    (hms : (m : ℝ) / (400 * L) ≤ (s : ℝ)) :
    (m : ℝ) ^ (1 / 2 - 1 / p) / Real.sqrt (s : ℝ) ≤
      20 * Real.sqrt L * (m : ℝ) ^ (-1 / p) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hs
  have hden : 0 < 400 * L := by positivity
  have hmprod : (m : ℝ) ≤ 400 * L * (s : ℝ) := by
    calc
      (m : ℝ) ≤ (s : ℝ) * (400 * L) := (div_le_iff₀ hden).mp hms
      _ = 400 * L * (s : ℝ) := by ring
  have hsqrt : Real.sqrt (m : ℝ) ≤
      20 * Real.sqrt L * Real.sqrt (s : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · calc
        (m : ℝ) ≤ 400 * L * (s : ℝ) := hmprod
        _ = (20 * Real.sqrt L * Real.sqrt (s : ℝ)) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hL.le, Real.sq_sqrt hsR.le]
          ring
  have hratio : Real.sqrt (m : ℝ) / Real.sqrt (s : ℝ) ≤ 20 * Real.sqrt L :=
    (div_le_iff₀ (Real.sqrt_pos.2 hsR)).2 hsqrt
  rw [show (1 / 2 - 1 / p : ℝ) = 1 / 2 + (-1 / p) by ring,
    Real.rpow_add hmR, ← Real.sqrt_eq_rpow]
  calc
    (Real.sqrt (m : ℝ) * (m : ℝ) ^ (-1 / p)) / Real.sqrt (s : ℝ) =
        (Real.sqrt (m : ℝ) / Real.sqrt (s : ℝ)) * (m : ℝ) ^ (-1 / p) := by ring
    _ ≤ 20 * Real.sqrt L * (m : ℝ) ^ (-1 / p) :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hmR.le _)

end BrownianSharp.AlignmentPaperJointRateScalars
