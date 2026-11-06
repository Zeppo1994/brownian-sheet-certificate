import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import BrownianSharp.IntegratedHaarTent
import BrownianSharp.DiscrepancyHaarCoefficient

/-! Finite four-cell algebra for the one-axis critical projection used in the
Brownian-sheet residual construction. The coordinates are exact cell means:
the statements below isolate the normalization and projection arithmetic;
they do not assert the still-separate continuous cell-averaging / sheet
representation bridge. -/

open scoped BigOperators
open MeasureTheory

namespace HaarQuarter

theorem critical_right_le_left_of_lt {r c d : ℕ} (hcd : c < d) :
    realDyadicRight r c ≤ realDyadicLeft r d := by
  dsimp [realDyadicRight, realDyadicLeft]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ r)
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ r)).2
  push_cast
  exact_mod_cast (Nat.mul_le_mul_right (2 ^ r) (Nat.succ_le_of_lt hcd))

private theorem critical_dyadic_left_scaled {r s c : ℕ} (hrs : r ≤ s) :
    realDyadicLeft r c =
      ((c * 2 ^ (s - r) : ℕ) : ℝ) / (2 : ℝ) ^ s := by
  have hpowN : 2 ^ r * 2 ^ (s - r) = 2 ^ s := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hrs]
  have hpow : (2 : ℝ) ^ r * (2 : ℝ) ^ (s - r) = (2 : ℝ) ^ s := by
    exact_mod_cast hpowN
  dsimp [realDyadicLeft]
  push_cast
  field_simp
  nlinarith [hpow]

private theorem critical_dyadic_right_scaled {r s c : ℕ} (hrs : r ≤ s) :
    realDyadicRight r c =
      (((c + 1) * 2 ^ (s - r) : ℕ) : ℝ) / (2 : ℝ) ^ s := by
  have hpowN : 2 ^ r * 2 ^ (s - r) = 2 ^ s := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hrs]
  have hpow : (2 : ℝ) ^ r * (2 : ℝ) ^ (s - r) = (2 : ℝ) ^ s := by
    exact_mod_cast hpowN
  dsimp [realDyadicRight]
  push_cast
  field_simp
  nlinarith [hpow]

private theorem critical_dyadic_mid_scaled {r s c : ℕ} (hrs : r < s) :
    realDyadicMid r c =
      (((2 * c + 1) * 2 ^ (s - r - 1) : ℕ) : ℝ) / (2 : ℝ) ^ s := by
  have hpowN : 2 ^ r * 2 ^ (s - r) = 2 ^ s := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hrs.le]
  have hpow : (2 : ℝ) ^ r * (2 : ℝ) ^ (s - r) = (2 : ℝ) ^ s := by
    exact_mod_cast hpowN
  have hhalf : 2 ^ (s - r) = 2 * 2 ^ (s - r - 1) := by
    have _hpos : 1 ≤ s - r := by omega
    conv_lhs => rw [show s - r = (s - r - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hhalfR : (2 : ℝ) ^ (s - r) = 2 * (2 : ℝ) ^ (s - r - 1) := by
    exact_mod_cast hhalf
  have hmid : realDyadicMid r c =
      (realDyadicLeft r c + realDyadicRight r c) / 2 := by
    dsimp [realDyadicMid, realDyadicLeft, realDyadicRight]
    field_simp
    ring
  rw [hmid, critical_dyadic_left_scaled hrs.le,
    critical_dyadic_right_scaled hrs.le]
  push_cast
  field_simp
  rw [hhalfR]
  ring

theorem critical_fine_cell_position {r s c d : ℕ} (hrs : r < s) :
    realDyadicRight s d ≤ realDyadicLeft r c ∨
      (realDyadicLeft r c ≤ realDyadicLeft s d ∧
        realDyadicRight s d ≤ realDyadicMid r c) ∨
      (realDyadicMid r c ≤ realDyadicLeft s d ∧
        realDyadicRight s d ≤ realDyadicRight r c) ∨
      realDyadicRight r c ≤ realDyadicLeft s d := by
  let A : ℕ := c * 2 ^ (s - r)
  let M : ℕ := (2 * c + 1) * 2 ^ (s - r - 1)
  let C : ℕ := (c + 1) * 2 ^ (s - r)
  have hpow : 2 ^ (s - r) = 2 * 2 ^ (s - r - 1) := by
    conv_lhs => rw [show s - r = (s - r - 1) + 1 by omega]
    rw [pow_succ]
    omega
  have hAM : M = A + 2 ^ (s - r - 1) := by
    dsimp [A, M]
    rw [hpow]
    ring
  have hMC : C = M + 2 ^ (s - r - 1) := by
    dsimp [M, C]
    rw [hpow]
    ring
  have hpos : 0 < 2 ^ (s - r - 1) := by positivity
  have hAMlt : A < M := by rw [hAM]; exact Nat.lt_add_of_pos_right hpos
  have hMClt : M < C := by rw [hMC]; exact Nat.lt_add_of_pos_right hpos
  have hcases : d + 1 ≤ A ∨ (A ≤ d ∧ d + 1 ≤ M) ∨
      (M ≤ d ∧ d + 1 ≤ C) ∨ C ≤ d := by omega
  have hden : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hcmp (u v : ℕ) (huv : u ≤ v) :
      (u : ℝ) / (2 : ℝ) ^ s ≤ (v : ℝ) / (2 : ℝ) ^ s := by
    apply (div_le_div_iff₀ hden hden).2
    exact_mod_cast (Nat.mul_le_mul_right (2 ^ s) huv)
  have hleft : realDyadicLeft r c = (A : ℝ) / (2 : ℝ) ^ s := by
    simpa [A] using critical_dyadic_left_scaled (r := r) (s := s) (c := c) hrs.le
  have hmid : realDyadicMid r c = (M : ℝ) / (2 : ℝ) ^ s := by
    simpa [M] using critical_dyadic_mid_scaled (r := r) (s := s) (c := c) hrs
  have hright : realDyadicRight r c = (C : ℝ) / (2 : ℝ) ^ s := by
    simpa [C] using critical_dyadic_right_scaled (r := r) (s := s) (c := c) hrs.le
  have hfineL : realDyadicLeft s d = (d : ℝ) / (2 : ℝ) ^ s := by
    simp [realDyadicLeft]
  have hfineR : realDyadicRight s d = ((d + 1 : ℕ) : ℝ) / (2 : ℝ) ^ s := by
    simp [realDyadicRight]
  rcases hcases with hbefore | ⟨hA, hM⟩ | ⟨hM, hC⟩ | hafter
  · left
    rw [hfineR, hleft]
    exact hcmp (d + 1) A hbefore
  · right; left
    constructor
    · rw [hleft, hfineL]
      exact hcmp A d hA
    · rw [hfineR, hmid]
      exact hcmp (d + 1) M hM
  · right; right; left
    constructor
    · rw [hmid, hfineL]
      exact hcmp M d hM
    · rw [hfineR, hright]
      exact hcmp (d + 1) C hC
  · right; right; right
    rw [hright, hfineL]
    exact hcmp C d hafter

end HaarQuarter
