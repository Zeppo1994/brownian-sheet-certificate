import BrownianSharp.AlignmentPaperJointSamplingBudget
import BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
import BrownianSharp.ShapeGrowth
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Log

/-! Feasibility and scale comparability for the capped high-grade dyadic ranks
used in the global grade-series covering argument. -/

noncomputable section
set_option maxHeartbeats 600000
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperJointGlobalRankProfile

open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperJointSamplingBudget

def highProfileEta (p : ℝ) : ℝ := (p - 1) / (8 * p)

def highProfileWindow (p : ℝ) (N : ℕ) : ℕ :=
  Nat.ceil (4 * p * (N : ℝ) / (p - 1))

def highProfileDrop (p : ℝ) (j : ℕ) : ℕ :=
  Nat.floor (highProfileEta p * (j : ℝ) / Real.log 2)

def highProfileRank (d : ℕ) (p : ℝ) (N j : ℕ) : ℕ :=
  Nat.log2 (JointSampleDimension d N) - highProfileDrop p j

/-- The actual sample dimension is exactly the number of shapes times the
common dyadic grid size, including the two real coordinates per grid point. -/
theorem jointSampleDimension_eq (d n : ℕ) :
    JointSampleDimension d n = Fintype.card (Shape d n) * 2 ^ (n + 3 * d + 1) := by
  classical
  change Fintype.card (Σ r : Shape d n, ShapeGrid r × Bool) = _
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_bool]
  calc
    (∑ r : Shape d n, Fintype.card (ShapeGrid r) * 2) =
        ∑ r : Shape d n, 2 ^ (n + 3 * d) * 2 := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [shapeGrid_card_eq]
    _ = Fintype.card (Shape d n) * (2 ^ (n + 3 * d) * 2) := by
      simp [Finset.sum_const]
    _ = Fintype.card (Shape d n) * 2 ^ (n + 3 * d + 1) := by
      rw [pow_succ]

private theorem shape_card_mono {d n j : ℕ} (hd : 1 ≤ d) :
    Fintype.card (Shape d n) ≤ Fintype.card (Shape d (n + j)) := by
  rw [shape_card d n (by omega : 0 < d), shape_card d (n + j) (by omega : 0 < d)]
  apply Nat.choose_le_choose
  omega

private theorem jointSampleDimension_mono {d n j : ℕ} (hd : 1 ≤ d) :
    JointSampleDimension d n ≤ JointSampleDimension d (n + j) := by
  rw [jointSampleDimension_eq, jointSampleDimension_eq]
  apply Nat.mul_le_mul
  · exact shape_card_mono hd
  · exact Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)

/-- Every high-window rank is feasible for the actual next-grade sample space,
and remains comparable from below to the starting sample dimension. -/
theorem highProfileRank_feasible {d N j : ℕ} {p : ℝ}
    (hd : 2 ≤ d) (hp1 : 1 < p) (hp2 : p < 2)
    (hj : j ≤ highProfileWindow p N) :
    highProfileDrop p j ≤ Nat.log2 (JointSampleDimension d N) ∧
    2 ^ highProfileRank d p N j ≤ JointSampleDimension d (N + j) ∧
    (JointSampleDimension d N : ℝ) / 2 *
        Real.exp (-highProfileEta p * (j : ℝ)) ≤
      (2 : ℝ) ^ highProfileRank d p N j := by
  classical
  let D : ℕ := JointSampleDimension d N
  let L : ℕ := Nat.log2 D
  let η : ℝ := highProfileEta p
  let W : ℕ := highProfileWindow p N
  let q : ℕ := highProfileDrop p j
  let J : ℕ := highProfileRank d p N j
  have hp0 : 0 < p := by linarith
  have hpden : 0 < p - 1 := by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hloghalf : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hηpos : 0 < η := by
    dsimp [η, highProfileEta]
    positivity
  have hηsmall : η < 1 / 16 := by
    dsimp [η, highProfileEta]
    rw [div_lt_iff₀ (by positivity : 0 < 8 * p)]
    nlinarith
  have hW : (W : ℝ) < 4 * p * (N : ℝ) / (p - 1) + 1 := by
    dsimp [W, highProfileWindow]
    exact Nat.ceil_lt_add_one (by positivity)
  have hqfloor : (q : ℝ) ≤ η * (j : ℝ) / Real.log 2 := by
    dsimp [q, highProfileDrop]
    exact Nat.floor_le (by positivity)
  have hratio : η * (j : ℝ) / Real.log 2 ≤ 2 * η * (j : ℝ) := by
    apply (div_le_iff₀ hlog).2
    have hnum : 0 ≤ η * (j : ℝ) := mul_nonneg hηpos.le (Nat.cast_nonneg _)
    nlinarith [mul_nonneg hnum (by linarith : 0 ≤ 2 * Real.log 2 - 1)]
  have hjreal : (j : ℝ) ≤ (W : ℝ) := by exact_mod_cast hj
  have hqreal : (q : ℝ) < (N : ℝ) + 1 := by
    have hWmul : 2 * η * (W : ℝ) <
        2 * η * (4 * p * (N : ℝ) / (p - 1) + 1) :=
      mul_lt_mul_of_pos_left hW (by positivity)
    have hformula :
        2 * η * (4 * p * (N : ℝ) / (p - 1) + 1) =
          (N : ℝ) + 2 * η := by
      dsimp [η, highProfileEta]
      field_simp
      <;> ring
    have hfinal : (N : ℝ) + 2 * η < (N : ℝ) + 1 := by linarith
    calc
      (q : ℝ) ≤ η * (j : ℝ) / Real.log 2 := hqfloor
      _ ≤ 2 * η * (j : ℝ) := hratio
      _ ≤ 2 * η * (W : ℝ) := by
        exact mul_le_mul_of_nonneg_left hjreal (by positivity)
      _ < 2 * η * (4 * p * (N : ℝ) / (p - 1) + 1) := hWmul
      _ = (N : ℝ) + 2 * η := hformula
      _ < (N : ℝ) + 1 := hfinal
  have hqN : q ≤ N := by
    have hqNat : q < N + 1 := by exact_mod_cast hqreal
    omega
  have hDlower : 2 ^ N ≤ D := by
    have hcardpos : 0 < Fintype.card (Shape d N) := by
      rw [shape_card d N (by omega : 0 < d)]
      exact Nat.choose_pos (by omega)
    have hpow : 2 ^ N ≤ 2 ^ (N + 3 * d + 1) :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    dsimp [D]
    rw [jointSampleDimension_eq]
    calc
      2 ^ N ≤ 2 ^ (N + 3 * d + 1) := hpow
      _ = 1 * 2 ^ (N + 3 * d + 1) := by simp
      _ ≤ Fintype.card (Shape d N) * 2 ^ (N + 3 * d + 1) :=
        Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hcardpos)
  have hDpos : D ≠ 0 := by
    have hpowpos : 0 < 2 ^ N := Nat.pow_pos (by omega)
    omega
  have hLlower : N ≤ L := by
    by_contra h
    have hLt : L < N := by omega
    have hupper : D < 2 ^ (L + 1) := by
      dsimp [L]
      rw [Nat.log2_eq_log_two]
      exact Nat.lt_pow_of_log_lt (by omega : 1 < 2)
        (Nat.lt_succ_self (Nat.log 2 D))
    have hpow : 2 ^ (L + 1) ≤ 2 ^ N :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
    omega
  have hqL : q ≤ L := le_trans hqN hLlower
  have hJleL : J ≤ L := by
    dsimp [J, highProfileRank]
    exact Nat.sub_le _ _
  have hDnext : D ≤ JointSampleDimension d (N + j) := by
    dsimp [D]
    exact jointSampleDimension_mono (d := d) (n := N) (j := j) (by omega)
  have hfeas : 2 ^ J ≤ JointSampleDimension d (N + j) := by
    dsimp [J, highProfileRank]
    calc
      2 ^ (Nat.log2 (JointSampleDimension d N) - q) ≤
          2 ^ Nat.log2 (JointSampleDimension d N) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.sub_le _ _)
      _ ≤ JointSampleDimension d N := by
        simpa [D] using Nat.log2_self_le hDpos
      _ ≤ JointSampleDimension d (N + j) := hDnext
  have hDupper : D < 2 ^ (L + 1) := by
    dsimp [L]
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_of_log_lt (by omega : 1 < 2)
      (Nat.lt_succ_self (Nat.log 2 D))
  have hDupperReal : (D : ℝ) / 2 ≤ (2 : ℝ) ^ L := by
    have hcast : (D : ℝ) < (2 : ℝ) ^ (L + 1) := by exact_mod_cast hDupper
    rw [pow_succ] at hcast
    nlinarith
  have hqlog : (q : ℝ) * Real.log 2 ≤ η * (j : ℝ) :=
    (le_div_iff₀ hlog).mp hqfloor
  have hexp : Real.exp (-η * (j : ℝ)) ≤
      Real.exp (-(q : ℝ) * Real.log 2) := by
    apply Real.exp_le_exp.mpr
    linarith [hqlog]
  have hexpEq : Real.exp (-(q : ℝ) * Real.log 2) =
      (2 : ℝ) ^ (-(q : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
    congr 1
    ring
  have hpowEq : (2 : ℝ) ^ L * (2 : ℝ) ^ (-(q : ℝ)) = (2 : ℝ) ^ J := by
    rw [← Real.rpow_natCast (2 : ℝ) L,
      ← Real.rpow_natCast (2 : ℝ) J,
      ← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
    have hcastJ : (L : ℝ) - (q : ℝ) = (J : ℝ) := by
      dsimp [J, highProfileRank]
      rw [Nat.cast_sub hqL]
    rw [← sub_eq_add_neg, hcastJ]
  have hlower : (D : ℝ) / 2 * Real.exp (-η * (j : ℝ)) ≤ (2 : ℝ) ^ J := by
    calc
      _ ≤ (2 : ℝ) ^ L * Real.exp (-(q : ℝ) * Real.log 2) :=
        mul_le_mul hDupperReal hexp (by positivity) (by positivity)
      _ = (2 : ℝ) ^ L * (2 : ℝ) ^ (-(q : ℝ)) := by rw [hexpEq]
      _ = (2 : ℝ) ^ J := hpowEq
  refine ⟨hqL, hfeas, ?_⟩
  simpa [D, η, J, highProfileEta, highProfileRank, highProfileDrop] using hlower

end BrownianSharp.AlignmentPaperJointGlobalRankProfile

end
