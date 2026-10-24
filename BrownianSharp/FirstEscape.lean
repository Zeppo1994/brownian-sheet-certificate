import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Basic.Real.Basic

/-!
# Exact first escape

Source: unrestricted quarter-gain proof, Section 5, Lemma A1.

This file checks the combinatorial partition for arbitrary dimensions and
arbitrary finite families of interactions. Prefix measurability and the
probability estimates are separate obligations.
-/

open scoped BigOperators

namespace HaarQuarter

abbrev Profile (D : ℕ) := Fin D → ℕ

def grade {D : ℕ} (v : Profile D) : ℕ := ∑ a, v a

/-- The least coordinate at which the source profile exceeds the target. -/
def IsFirstEscape {D : ℕ} (v t : Profile D) (h : Fin D) : Prop :=
  t h < v h ∧ ∀ a : Fin D, a < h → v a ≤ t a

instance {D : ℕ} (v t : Profile D) (h : Fin D) : Decidable (IsFirstEscape v t h) :=
  inferInstanceAs (Decidable (t h < v h ∧ ∀ a : Fin D, a < h → v a ≤ t a))

theorem not_isFirstEscape_self {D : ℕ} (v : Profile D) (h : Fin D) :
    ¬ IsFirstEscape v v h := by
  intro hh
  exact (Nat.lt_irrefl (v h)) hh.1

theorem firstEscape_unique {D : ℕ} {v t : Profile D} {h k : Fin D}
    (hh : IsFirstEscape v t h) (hk : IsFirstEscape v t k) : h = k := by
  rcases lt_trichotomy h k with hhk | heq | hkh
  · exact False.elim ((not_lt_of_ge (hk.2 h hhk)) hh.1)
  · exact heq
  · exact False.elim ((not_lt_of_ge (hh.2 k hkh)) hk.1)

/-- Every non-diagonal interaction of critical-or-lower target grade escapes. -/
theorem exists_firstEscape {D : ℕ} {v t : Profile D}
    (hgrade : grade t ≤ grade v) (hne : v ≠ t) :
    ∃ h : Fin D, IsFirstEscape v t h := by
  classical
  have hsome : ∃ h : Fin D, t h < v h := by
    by_contra hnone
    have hle : ∀ h : Fin D, v h ≤ t h := by
      intro h
      exact Nat.le_of_not_gt (fun hh => hnone ⟨h, hh⟩)
    have hneqsome : ∃ h : Fin D, v h ≠ t h := by
      by_contra hnoneq
      apply hne
      funext a
      by_contra hneq
      exact hnoneq ⟨a, hneq⟩
    obtain ⟨h, hh⟩ := hneqsome
    have hstrict : grade v < grade t := by
      apply Finset.sum_lt_sum
      · intro a ha
        exact hle a
      · exact ⟨h, Finset.mem_univ h, lt_of_le_of_ne (hle h) hh⟩
    exact (not_lt_of_ge hgrade) hstrict
  let escapes : Finset (Fin D) := Finset.univ.filter (fun h => t h < v h)
  have hn : escapes.Nonempty := by
    obtain ⟨h, hh⟩ := hsome
    exact ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_univ h, hh⟩⟩
  refine ⟨escapes.min' hn, ?_⟩
  constructor
  · exact (Finset.mem_filter.mp (Finset.min'_mem escapes hn)).2
  · intro a ha
    by_contra hnot
    have hlt : t a < v a := Nat.lt_of_not_ge hnot
    have haS : a ∈ escapes := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hlt⟩
    have hmin : escapes.min' hn ≤ a := Finset.min'_le escapes a haS
    exact (not_lt_of_ge hmin) ha

noncomputable def escapeMask {D : ℕ} (v t : Profile D) (h : Fin D) : ℝ := by
  classical
  exact if IsFirstEscape v t h then 1 else 0

/-- The masks partition the off-diagonal exactly; there is no counting loss. -/
theorem sum_escapeMask {D : ℕ} (v t : Profile D)
    (hgrade : grade t ≤ grade v) :
    (∑ h, escapeMask v t h) = if v = t then 0 else 1 := by
  classical
  by_cases heq : v = t
  · subst t
    simp [escapeMask, not_isFirstEscape_self]
  · obtain ⟨h, hh⟩ := exists_firstEscape hgrade heq
    rw [ite_eq_right heq, Finset.sum_eq_single h]
    · simp [escapeMask, hh]
    · intro k hk hkh
      have hnot : ¬ IsFirstEscape v t k := by
        intro hkfirst
        exact hkh (firstEscape_unique hkfirst hh)
      simp [escapeMask, hnot]
    · simp

theorem weighted_escape_partition {D : ℕ} (v t : Profile D)
    (hgrade : grade t ≤ grade v) (z : ℝ) :
    (∑ h, escapeMask v t h * z) = if v = t then 0 else z := by
  classical
  rw [← Finset.sum_mul, sum_escapeMask v t hgrade]
  split_ifs <;> simp

/-- Exact regrouping of any finite collection of interactions by escape axis. -/
theorem partition_offDiagonal {D : ℕ} {ι : Type*} [Fintype ι]
    (v t : ι → Profile D) (hgrade : ∀ j, grade (t j) ≤ grade (v j))
    (term : ι → ℝ) :
    (∑ j, if v j = t j then 0 else term j) =
      ∑ h, ∑ j, escapeMask (v j) (t j) h * term j := by
  classical
  calc
    _ = ∑ j, ∑ h, escapeMask (v j) (t j) h * term j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (weighted_escape_partition (v j) (t j) (hgrade j) (term j)).symm
    _ = _ := Finset.sum_comm

end HaarQuarter
