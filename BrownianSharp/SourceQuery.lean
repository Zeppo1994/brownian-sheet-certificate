import BrownianSharp.SignCube
import Mathlib.Tactic.Ring

/-!
# The source/query identity of Lemma A1

An arbitrary finite index type represents the admissible triples `(l, v, t)`.
The only geometric hypothesis is that each target grade is at most its source
grade. Legal source and target coefficients are needed for the fresh-sign
invariance, not for the algebraic identity itself.
-/

open scoped BigOperators

namespace HaarQuarter

def interaction {D N : ℕ} (Ω β : SignCube D N → ℝ)
    (v t : BoundedProfile D N) (x : SignCube D N) : ℝ :=
  Ω x * β x * profileWord x v * profileWord x t

noncomputable def diagonalTerm {D N : ℕ} (Ω β : SignCube D N → ℝ)
    (v t : BoundedProfile D N) (x : SignCube D N) : ℝ := by
  classical
  exact if v = t then Ω x * β x else 0

theorem interaction_factor {D N : ℕ} (Ω β : SignCube D N → ℝ)
    (v t : BoundedProfile D N) (h : Fin D) (x : SignCube D N) :
    interaction Ω β v t x = digit x h (v h) * escapingCoefficient Ω β v t h x := by
  unfold interaction escapingCoefficient
  rw [profileWord_factor x v h]
  ring

theorem interaction_self {D N : ℕ} (Ω β : SignCube D N → ℝ)
    (v : BoundedProfile D N) (x : SignCube D N) :
    interaction Ω β v v x = Ω x * β x := by
  unfold interaction
  calc
    Ω x * β x * profileWord x v * profileWord x v =
        Ω x * β x * (profileWord x v * profileWord x v) := by ring
    _ = Ω x * β x := by rw [profileWord_sq, mul_one]

theorem interaction_offDiagonal {D N : ℕ} (Ω β : SignCube D N → ℝ)
    (v t : BoundedProfile D N)
    (hgrade : grade (naturalProfile t) ≤ grade (naturalProfile v))
    (x : SignCube D N) :
    interaction Ω β v t x - diagonalTerm Ω β v t x =
      ∑ h, escapeMask (naturalProfile v) (naturalProfile t) h *
        (digit x h (v h) * escapingCoefficient Ω β v t h x) := by
  classical
  have hw := weighted_escape_partition (naturalProfile v) (naturalProfile t)
    hgrade (interaction Ω β v t x)
  have heq : naturalProfile v = naturalProfile t ↔ v = t :=
    naturalProfile_injective.eq_iff
  simp only [heq] at hw
  calc
    _ = if v = t then 0 else interaction Ω β v t x := by
      by_cases hv : v = t
      · subst t
        simp [diagonalTerm, interaction_self]
      · simp [diagonalTerm, hv]
    _ = ∑ h, escapeMask (naturalProfile v) (naturalProfile t) h *
        interaction Ω β v t x := hw.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      rw [interaction_factor Ω β v t h x]

noncomputable def escapedCoefficientAt {D N : ℕ} {ι : Type*} [Fintype ι]
    (Ω β : ι → SignCube D N → ℝ) (v t : ι → BoundedProfile D N)
    (h : Fin D) (u : Fin N) (x : SignCube D N) : ℝ := by
  classical
  exact ∑ j, if IsFirstEscape (naturalProfile (v j)) (naturalProfile (t j)) h ∧
      v j h = u then escapingCoefficient (Ω j) (β j) (v j) (t j) h x else 0

theorem regroup_escape_depth {D N : ℕ} {ι : Type*} [Fintype ι]
    (Ω β : ι → SignCube D N → ℝ) (v t : ι → BoundedProfile D N)
    (h : Fin D) (x : SignCube D N) :
    (∑ j, escapeMask (naturalProfile (v j)) (naturalProfile (t j)) h *
        (digit x h (v j h) * escapingCoefficient (Ω j) (β j) (v j) (t j) h x)) =
      ∑ u, digit x h u * escapedCoefficientAt Ω β v t h u x := by
  classical
  calc
    _ = ∑ j, ∑ u, digit x h u *
        (if IsFirstEscape (naturalProfile (v j)) (naturalProfile (t j)) h ∧
          v j h = u then escapingCoefficient (Ω j) (β j) (v j) (t j) h x else 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hf : IsFirstEscape (naturalProfile (v j)) (naturalProfile (t j)) h
      · rw [Finset.sum_eq_single (v j h)]
        · simp [escapeMask, hf]
        · intro u hu hune
          simp [hf, Ne.symm hune]
        · simp
      · simp [escapeMask, hf]
    _ = ∑ u, ∑ j, digit x h u *
        (if IsFirstEscape (naturalProfile (v j)) (naturalProfile (t j)) h ∧
          v j h = u then escapingCoefficient (Ω j) (β j) (v j) (t j) h x else 0) :=
      Finset.sum_comm
    _ = _ := by simp [escapedCoefficientAt, Finset.mul_sum]

/-- Exact raw-minus-diagonal identity, grouped by one fresh axis and depth. -/
theorem sourceQuery_firstEscape {D N : ℕ} {ι : Type*} [Fintype ι]
    (Ω β : ι → SignCube D N → ℝ) (v t : ι → BoundedProfile D N)
    (hgrade : ∀ j, grade (naturalProfile (t j)) ≤ grade (naturalProfile (v j)))
    (x : SignCube D N) :
    (∑ j, interaction (Ω j) (β j) (v j) (t j) x) -
        (∑ j, diagonalTerm (Ω j) (β j) (v j) (t j) x) =
      ∑ h, ∑ u, digit x h u * escapedCoefficientAt Ω β v t h u x := by
  classical
  calc
    _ = ∑ j, (interaction (Ω j) (β j) (v j) (t j) x -
        diagonalTerm (Ω j) (β j) (v j) (t j) x) := by rw [Finset.sum_sub_distrib]
    _ = ∑ j, ∑ h, escapeMask (naturalProfile (v j)) (naturalProfile (t j)) h *
        (digit x h (v j h) * escapingCoefficient (Ω j) (β j) (v j) (t j) h x) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact interaction_offDiagonal (Ω j) (β j) (v j) (t j) (hgrade j) x
    _ = ∑ h, ∑ j, escapeMask (naturalProfile (v j)) (naturalProfile (t j)) h *
        (digit x h (v j h) * escapingCoefficient (Ω j) (β j) (v j) (t j) h x) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro h hh
      exact regroup_escape_depth Ω β v t h x

/-- Every grouped coefficient is unchanged when its putative fresh sign flips. -/
theorem escapedCoefficientAt_flip {D N : ℕ} {ι : Type*} [Fintype ι]
    (l : ι → ℕ) (Ω β : ι → SignCube D N → ℝ) (v t : ι → BoundedProfile D N)
    (hΩ : ∀ j, LegalCoefficient (l j) (naturalProfile (v j)) (Ω j))
    (hβ : ∀ j, LegalCoefficient (l j) (naturalProfile (t j)) (β j))
    (h : Fin D) (u : Fin N) (x : SignCube D N) :
    escapedCoefficientAt Ω β v t h u (flip x h u) =
      escapedCoefficientAt Ω β v t h u x := by
  classical
  unfold escapedCoefficientAt
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hs : IsFirstEscape (naturalProfile (v j)) (naturalProfile (t j)) h ∧ v j h = u
  · simp only [ite_eq_left hs]
    rw [← hs.2]
    exact escapingCoefficient_flip (l j) (Ω j) (β j) (v j) (t j) h
      (hΩ j) (hβ j) hs.1 x
  · simp [hs]

/-- The grouped coefficient reads only the past of its escaping axis. -/
theorem escapedCoefficientAt_readsAxisPast {D N : ℕ} {ι : Type*} [Fintype ι]
    (l : ι → ℕ) (Ω β : ι → SignCube D N → ℝ) (v t : ι → BoundedProfile D N)
    (hΩ : ∀ j, LegalCoefficient (l j) (naturalProfile (v j)) (Ω j))
    (hβ : ∀ j, LegalCoefficient (l j) (naturalProfile (t j)) (β j))
    (h : Fin D) (u : Fin N) :
    ReadsAxisPast h u (escapedCoefficientAt Ω β v t h u) := by
  classical
  intro x y hxy
  unfold escapedCoefficientAt
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hs : IsFirstEscape (naturalProfile (v j)) (naturalProfile (t j)) h ∧ v j h = u
  · simp only [ite_eq_left hs]
    have hreads := escapingCoefficient_readsAxisPast (l j) (Ω j) (β j)
      (v j) (t j) h (hΩ j) (hβ j) hs.1
    rw [hs.2] at hreads
    exact hreads x y hxy
  · simp [hs]

end HaarQuarter
