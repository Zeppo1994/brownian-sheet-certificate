import BrownianSharp.AlignmentPaperAdaptiveCardinalityCost
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Uniform binary coding bound for a coarse dyadic cover followed by a
volumetric refinement. The gap, source dimension, and radii enter only after
the logarithmic constant has been fixed. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperJointRefinementBinaryBudget

open BrownianSharp.AlignmentPaperAdaptiveCardinalityCost

/-- The product of a coarse dyadic budget and a refined volumetric count is
bounded by a single dyadic budget whose constant depends only on the original
coarse exponent and the uniform radius-ratio constant. -/
theorem exists_joint_refinement_binary_budget
    {a K : ℝ} (ha : 0 < a) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : ℕ), 1 ≤ D → ∀ (gap : ℕ) (ε η : ℝ),
      0 ≤ ε → 0 < η → ε / η ≤ K * (2 : ℝ) ^ (2 * gap) →
      2 ^ Nat.ceil (a * (D : ℝ)) *
          Nat.ceil ((1 + 4 * ε / η) ^ D) ≤
        2 ^ Nat.ceil (C * (D : ℝ) * (gap + 1)) := by
  let C : ℝ := a + Real.log (1 + 4 * K) / Real.log 2 + 6
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogK : 0 < Real.log (1 + 4 * K) := Real.log_pos (by linarith)
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro D hD gap ε η hε hη hratio
  have hηpos : 0 < η := hη
  have hratioBase : 1 + 4 * ε / η ≤
      (1 + 4 * K) * (2 : ℝ) ^ (2 * gap) := by
    have hpow : 1 ≤ (2 : ℝ) ^ (2 * gap) := one_le_pow₀ (by norm_num)
    have hratio' := mul_le_mul_of_nonneg_left hratio (by norm_num : 0 ≤ (4 : ℝ))
    have hdivEq : 4 * ε / η = 4 * (ε / η) := by
      field_simp
    calc
      1 + 4 * ε / η = 1 + 4 * (ε / η) := by rw [hdivEq]
      _ ≤ 1 + 4 * (K * (2 : ℝ) ^ (2 * gap)) := by linarith [hratio']
      _ ≤ (1 + 4 * K) * (2 : ℝ) ^ (2 * gap) := by nlinarith
  have hbasepos : 0 < 1 + 4 * ε / η := by positivity
  have hmajorpos : 0 < (1 + 4 * K) * (2 : ℝ) ^ (2 * gap) := by positivity
  have hlogbase : Real.log (1 + 4 * ε / η) ≤
      Real.log (1 + 4 * K) + (2 * (gap : ℝ)) * Real.log 2 := by
    calc
      Real.log (1 + 4 * ε / η) ≤
          Real.log ((1 + 4 * K) * (2 : ℝ) ^ (2 * gap)) :=
        Real.log_le_log hbasepos hratioBase
      _ = Real.log (1 + 4 * K) + (2 * (gap : ℝ)) * Real.log 2 := by
        rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
        norm_num [Nat.cast_mul]
  have hpow : (1 + 4 * ε / η) ^ D ≤ Real.exp
      ((D : ℝ) * Real.log (1 + 4 * K) +
        2 * (gap : ℝ) * (D : ℝ) * Real.log 2) := by
    have hexpEq : (1 + 4 * ε / η) ^ D =
        Real.exp ((D : ℝ) * Real.log (1 + 4 * ε / η)) := by
      rw [Real.exp_nat_mul, Real.exp_log hbasepos]
    rw [hexpEq]
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hlogbase (Nat.cast_nonneg D)
    nlinarith [hmul]
  have hceil : (Nat.ceil ((1 + 4 * ε / η) ^ D) : ℝ) ≤
      2 * (1 + 4 * ε / η) ^ D := by
    have hratioNonneg : 0 ≤ 4 * ε / η :=
      div_nonneg (mul_nonneg (by norm_num) hε) hη.le
    have hbaseone : 1 ≤ 1 + 4 * ε / η := by linarith
    have hpowone : 1 ≤ (1 + 4 * ε / η) ^ D := one_le_pow₀ hbaseone
    have hceil_lt := Nat.ceil_lt_add_one (show 0 ≤ (1 + 4 * ε / η) ^ D by positivity)
    linarith
  have hMexp : (Nat.ceil ((1 + 4 * ε / η) ^ D) : ℝ) ≤ Real.exp
      (Real.log 2 + (D : ℝ) * Real.log (1 + 4 * K) +
        2 * (gap : ℝ) * (D : ℝ) * Real.log 2) := by
    calc
      _ ≤ 2 * (1 + 4 * ε / η) ^ D := hceil
      _ ≤ 2 * Real.exp ((D : ℝ) * Real.log (1 + 4 * K) +
          2 * (gap : ℝ) * (D : ℝ) * Real.log 2) := by
            exact mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = _ := by
            have htwo : Real.exp (Real.log (2 : ℝ)) = 2 :=
              Real.exp_log (by norm_num : (0 : ℝ) < 2)
            have htwoexp (x : ℝ) : 2 * Real.exp x = Real.exp (Real.log 2 + x) := by
              calc
                2 * Real.exp x = Real.exp (Real.log 2) * Real.exp x := by rw [htwo]
                _ = Real.exp (Real.log 2 + x) := by rw [← Real.exp_add]
            rw [htwoexp]
            congr 1
            ring
  have hcount : Nat.ceil ((1 + 4 * ε / η) ^ D) ≤
      2 ^ Nat.ceil ((Real.log 2 + (D : ℝ) * Real.log (1 + 4 * K) +
        2 * (gap : ℝ) * (D : ℝ) * Real.log 2) / Real.log 2) :=
    nat_le_two_pow_ceil_of_le_exp hMexp
  have hceilA : (Nat.ceil (a * (D : ℝ)) : ℝ) < a * (D : ℝ) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hceilB :
      (Nat.ceil ((Real.log 2 + (D : ℝ) * Real.log (1 + 4 * K) +
        2 * (gap : ℝ) * (D : ℝ) * Real.log 2) / Real.log 2) : ℝ) <
      ((Real.log 2 + (D : ℝ) * Real.log (1 + 4 * K) +
        2 * (gap : ℝ) * (D : ℝ) * Real.log 2) / Real.log 2) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hbits : Nat.ceil (a * (D : ℝ)) +
      Nat.ceil ((Real.log 2 + (D : ℝ) * Real.log (1 + 4 * K) +
        2 * (gap : ℝ) * (D : ℝ) * Real.log 2) / Real.log 2) ≤
      Nat.ceil (C * (D : ℝ) * (gap + 1)) := by
    have hbitsReal :
        ((Nat.ceil (a * (D : ℝ)) + Nat.ceil
          ((Real.log 2 + (D : ℝ) * Real.log (1 + 4 * K) +
            2 * (gap : ℝ) * (D : ℝ) * Real.log 2) / Real.log 2) : ℕ) : ℝ) ≤
          C * (D : ℝ) * (gap + 1 : ℝ) := by
      dsimp [C]
      have hD1 : 1 ≤ (D : ℝ) := by exact_mod_cast hD
      have hD0 : 0 ≤ (D : ℝ) := by exact_mod_cast Nat.zero_le D
      have hgap : 0 ≤ (gap : ℝ) := Nat.cast_nonneg _
      have hden : 0 < Real.log 2 := hlog2
      have hratioBits :
          (Real.log 2 + (D : ℝ) * Real.log (1 + 4 * K) +
            2 * (gap : ℝ) * (D : ℝ) * Real.log 2) / Real.log 2 =
          1 + (D : ℝ) * (Real.log (1 + 4 * K) / Real.log 2) +
            2 * (gap : ℝ) * (D : ℝ) := by
        field_simp
      rw [Nat.cast_add, hratioBits]
      have hceilB' := hceilB
      rw [hratioBits] at hceilB'
      have haD : 0 ≤ a * (D : ℝ) := mul_nonneg ha.le hD0
      have hLD : 0 ≤ (Real.log (1 + 4 * K) / Real.log 2) * (D : ℝ) :=
        mul_nonneg (div_nonneg hlogK.le hlog2.le) hD0
      have hgapD : 0 ≤ (gap : ℝ) * (D : ℝ) := mul_nonneg hgap hD0
      have haDgap : 0 ≤ a * (D : ℝ) * (gap : ℝ) :=
        mul_nonneg haD hgap
      have hLDgap : 0 ≤ (Real.log (1 + 4 * K) / Real.log 2) *
          (D : ℝ) * (gap : ℝ) := mul_nonneg hLD hgap
      nlinarith [hceilA, hceilB', haD, hLD, hgapD, haDgap, hLDgap]
    have hnat :
        Nat.ceil (a * (D : ℝ)) + Nat.ceil
          ((Real.log 2 + (D : ℝ) * Real.log (1 + 4 * K) +
            2 * (gap : ℝ) * (D : ℝ) * Real.log 2) / Real.log 2) ≤
          Nat.ceil (C * (D : ℝ) * (gap + 1)) := by
      exact_mod_cast hbitsReal.trans (Nat.le_ceil _)
    exact hnat
  calc
    _ ≤ 2 ^ (Nat.ceil (a * (D : ℝ)) +
        Nat.ceil ((Real.log 2 + (D : ℝ) * Real.log (1 + 4 * K) +
          2 * (gap : ℝ) * (D : ℝ) * Real.log 2) / Real.log 2)) := by
      rw [pow_add]
      exact Nat.mul_le_mul_left _ hcount
    _ ≤ 2 ^ Nat.ceil (C * (D : ℝ) * (gap + 1)) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) hbits

end BrownianSharp.AlignmentPaperJointRefinementBinaryBudget

end
