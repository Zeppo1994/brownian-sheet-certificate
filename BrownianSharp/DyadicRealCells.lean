import BrownianSharp.DyadicDigitBridge
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open MeasureTheory

namespace HaarQuarter

noncomputable def dyadicGridPoint (N k : ℕ) : ℝ := (k : ℝ) / (2 : ℝ) ^ N

noncomputable def realDyadicCell (l c : ℕ) : Set ℝ :=
  Set.Ico ((c : ℝ) / (2 : ℝ) ^ l) (((c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ l)

noncomputable def realDyadicLeftHalf (l c : ℕ) : Set ℝ :=
  Set.Ico ((2 * c : ℕ) / (2 : ℝ) ^ (l + 1))
    (((2 * c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (l + 1))

noncomputable def realDyadicRightHalf (l c : ℕ) : Set ℝ :=
  Set.Ico (((2 * c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (l + 1))
    (((2 * c + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (l + 1))

noncomputable def realDyadicHaar (l c : ℕ) (x : ℝ) : ℝ := by
  classical
  exact (if x ∈ realDyadicRightHalf l c then 1 else 0) -
    (if x ∈ realDyadicLeftHalf l c then 1 else 0)

def dyadicCellContainsAtLevel (N l c k : ℕ) : Prop :=
  c * 2 ^ (N - l) ≤ k ∧ k < (c + 1) * 2 ^ (N - l)

private lemma dyadic_endpoint_grid_eq {N l c : ℕ} (hl : l ≤ N) :
    ((c * 2 ^ (N - l) : ℕ) : ℝ) / (2 : ℝ) ^ N =
      (c : ℝ) / (2 : ℝ) ^ l := by
  have hpowN : 2 ^ l * 2 ^ (N - l) = 2 ^ N := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hl]
  have hpow : (2 : ℝ) ^ l * (2 : ℝ) ^ (N - l) = (2 : ℝ) ^ N := by
    exact_mod_cast hpowN
  push_cast
  field_simp
  nlinarith [hpow]

private lemma dyadic_endpoint_bound_iff {N l c k : ℕ} (hl : l ≤ N) :
    (c : ℝ) / (2 : ℝ) ^ l ≤ dyadicGridPoint N k ↔
      c * 2 ^ (N - l) ≤ k := by
  rw [dyadicGridPoint, ← dyadic_endpoint_grid_eq hl]
  have hden : 0 < (2 : ℝ) ^ N := by positivity
  rw [div_le_div_iff₀ hden hden]
  constructor
  · intro h
    have h' : (c * 2 ^ (N - l) : ℝ) ≤ (k : ℝ) :=
      (mul_le_mul_iff_right₀ hden).1 (by simpa [mul_comm] using h)
    exact_mod_cast h'
  · intro h
    have h' : (c * 2 ^ (N - l) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h
    have hm := (mul_le_mul_iff_right₀ hden).2 h'
    simpa [mul_comm] using hm

private lemma dyadic_endpoint_upper_bound_iff {N l c k : ℕ} (hl : l ≤ N) :
    dyadicGridPoint N k < ((c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ l ↔
      k < (c + 1) * 2 ^ (N - l) := by
  have he := dyadic_endpoint_grid_eq (N := N) (l := l) (c := c + 1) hl
  rw [dyadicGridPoint, ← he]
  have hden : 0 < (2 : ℝ) ^ N := by positivity
  rw [div_lt_div_iff₀ hden hden]
  constructor
  · intro h
    have h' : (k : ℝ) < ((c + 1) * 2 ^ (N - l) : ℝ) :=
      (mul_lt_mul_iff_right₀ hden).1 (by simpa [mul_comm] using h)
    exact_mod_cast h'
  · intro h
    have h' : (k : ℝ) < ((c + 1) * 2 ^ (N - l) : ℝ) := by exact_mod_cast h
    have hm := (mul_lt_mul_iff_right₀ hden).2 h'
    simpa [mul_comm] using hm

theorem dyadicGridPoint_mem_realDyadicCell_iff
    (N l c k : ℕ) (hl : l ≤ N) :
    dyadicGridPoint N k ∈ realDyadicCell l c ↔
      dyadicCellContainsAtLevel N l c k := by
  rw [realDyadicCell, Set.mem_Ico]
  rw [dyadic_endpoint_bound_iff hl, dyadic_endpoint_upper_bound_iff hl]
  rfl

theorem dyadicGridPoint_mem_realDyadicCell_iff_contains
    (N : ℕ) (l : Fin N) (c k : ℕ) :
    dyadicGridPoint N k ∈ realDyadicCell l.val c ↔
      dyadicCellContains N l c k := by
  simpa [dyadicCellContainsAtLevel, dyadicCellContains] using
    dyadicGridPoint_mem_realDyadicCell_iff N l.val c k (Nat.le_of_lt l.isLt)

theorem dyadicGridPoint_mem_realDyadicLeftHalf_iff
    (N : ℕ) (l : Fin N) (c k : ℕ) :
    dyadicGridPoint N k ∈ realDyadicLeftHalf l.val c ↔
      dyadicLeftHalfContains N l c k := by
  rw [realDyadicLeftHalf, Set.mem_Ico]
  have hl : l.val + 1 ≤ N := Nat.succ_le_of_lt l.isLt
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · exact (dyadic_endpoint_bound_iff (N := N) (l := l.val + 1)
        (c := 2 * c) (k := k) hl).mp hlo
    · exact (dyadic_endpoint_upper_bound_iff (N := N) (l := l.val + 1)
        (c := 2 * c) (k := k) hl).mp hhi
  · rintro ⟨hlo, hhi⟩
    constructor
    · exact (dyadic_endpoint_bound_iff (N := N) (l := l.val + 1)
        (c := 2 * c) (k := k) hl).mpr hlo
    · exact (dyadic_endpoint_upper_bound_iff (N := N) (l := l.val + 1)
        (c := 2 * c) (k := k) hl).mpr hhi

theorem dyadicGridPoint_mem_realDyadicRightHalf_iff
    (N : ℕ) (l : Fin N) (c k : ℕ) :
    dyadicGridPoint N k ∈ realDyadicRightHalf l.val c ↔
      dyadicRightHalfContains N l c k := by
  rw [realDyadicRightHalf, Set.mem_Ico]
  have hl : l.val + 1 ≤ N := Nat.succ_le_of_lt l.isLt
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · exact (dyadic_endpoint_bound_iff (N := N) (l := l.val + 1)
        (c := 2 * c + 1) (k := k) hl).mp hlo
    · exact (dyadic_endpoint_upper_bound_iff (N := N) (l := l.val + 1)
        (c := 2 * c + 1) (k := k) hl).mp hhi
  · rintro ⟨hlo, hhi⟩
    constructor
    · exact (dyadic_endpoint_bound_iff (N := N) (l := l.val + 1)
        (c := 2 * c + 1) (k := k) hl).mpr hlo
    · exact (dyadic_endpoint_upper_bound_iff (N := N) (l := l.val + 1)
        (c := 2 * c + 1) (k := k) hl).mpr hhi

theorem realDyadicHaar_eq_dyadicHaarFromHalfIntervals
    (N : ℕ) (l : Fin N) (c k : ℕ) :
    realDyadicHaar l.val c (dyadicGridPoint N k) =
      dyadicHaarFromHalfIntervals N l c k := by
  unfold realDyadicHaar dyadicHaarFromHalfIntervals
  rw [dyadicGridPoint_mem_realDyadicRightHalf_iff,
    dyadicGridPoint_mem_realDyadicLeftHalf_iff]
  rfl

theorem realDyadicCell_volumeReal (l c : ℕ) :
    volume.real (realDyadicCell l c) = ((2 : ℝ) ^ l)⁻¹ := by
  rw [realDyadicCell, Real.volume_real_Ico_of_le]
  · field_simp
    push_cast
    ring
  · apply (div_le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ l)
      (by positivity : 0 < (2 : ℝ) ^ l)).2
    exact mul_le_mul_of_nonneg_right (by norm_cast; omega)
      (by positivity : 0 ≤ (2 : ℝ) ^ l)

end HaarQuarter
