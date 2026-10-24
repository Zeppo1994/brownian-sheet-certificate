import BrownianSharp.F1Stop
import BrownianSharp.F1Score

/-!
# Complete critical-plus-coarser queries

This connects the finite target's critical coefficients and every admitted
coarser field to the predictable query rows used by the actual F1 score law.
Normalization is by the full critical-plus-drift norm, with all coarser terms
retained. `InputRecovery` proves norm positivity from positive critical mass.
-/

open scoped BigOperators

namespace HaarQuarter

def IsQueryProfile {D N : ℕ} (l : Fin N) (v : BoundedProfile D N) : Prop :=
  l.val + grade (naturalProfile v) ≤ N - 1

instance {D N : ℕ} (l : Fin N) (v : BoundedProfile D N) : Decidable (IsQueryProfile l v) :=
  inferInstanceAs (Decidable (l.val + grade (naturalProfile v) ≤ N - 1))

def QueryFieldLegal {D N : ℕ} (β : CoefficientField D N) : Prop :=
  ∀ l v, IsQueryProfile l v → LegalCoefficient l.val (naturalProfile v) (β l v)

noncomputable def queryLevel {D N : ℕ} (β : CoefficientField D N)
    (l : Fin N) (x : SignCube D N) : ℝ := by
  classical
  exact ∑ v, if IsQueryProfile l v then β l v x * profileWord x v else 0

theorem queryLevel_firstPast {D N : ℕ} (β : CoefficientField D N)
    (hβ : QueryFieldLegal β) (l : Fin N) : ReadsFirstPast l.val (queryLevel β l) := by
  classical
  intro x y hxy
  unfold queryLevel
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hvq : IsQueryProfile l v
  · simp only [ite_eq_left hvq]
    rw [hβ l v hvq x y (firstPastAgreement_prefix hxy _), profileWord_transverse_eq hxy.1]
  · simp [hvq]

noncomputable def combinedField {D N : ℕ} (α b : CoefficientField D N) : CoefficientField D N := by
  classical
  exact fun l v x => if IsCriticalProfile l v then α l v x else
    if IsCoarseProfile l v then b l v x else 0

theorem combinedField_queryLegal {D N : ℕ} (α b : CoefficientField D N)
    (hα : CriticalFieldLegal α) (hb : CoarseFieldLegal b) : QueryFieldLegal (combinedField α b) := by
  classical
  intro l v hv x y hxy
  by_cases hc : IsCriticalProfile l v
  · simpa [combinedField, hc] using hα l v hc x y hxy
  · have hcoarse : IsCoarseProfile l v := lt_of_le_of_ne hv hc
    simpa [combinedField, hc, hcoarse] using hb l v hcoarse x y hxy

theorem combinedField_query_term {D N : ℕ} (α b : CoefficientField D N)
    (l : Fin N) (v : BoundedProfile D N) (x : SignCube D N) :
    firstDigit x l * (if IsQueryProfile l v then combinedField α b l v x * profileWord x v else 0) =
      (if IsCriticalProfile l v then α l v x * firstDigit x l * profileWord x v else 0) +
      (if IsCoarseProfile l v then b l v x * firstDigit x l * profileWord x v else 0) := by
  classical
  by_cases hc : IsCriticalProfile l v
  · have hquery : IsQueryProfile l v := le_of_eq hc
    have hncoarse : ¬ IsCoarseProfile l v := not_lt_of_ge (le_of_eq hc.symm)
    simp [combinedField, hc, hquery, hncoarse]
    ring
  · by_cases hcoarse : IsCoarseProfile l v
    · have hquery : IsQueryProfile l v := le_of_lt hcoarse
      simp [combinedField, hc, hcoarse, hquery]
      ring
    · have hnquery : ¬ IsQueryProfile l v := fun hq => hcoarse (lt_of_le_of_ne hq hc)
      simp [hc, hcoarse, hnquery]

theorem combinedField_signal {D N : ℕ} (α b : CoefficientField D N)
    (b₀ : ℝ) (x : SignCube D N) :
    rowPolynomial b₀ (queryLevel (combinedField α b)) x =
      criticalPolynomial α x + coarsePolynomial b₀ b x := by
  classical
  unfold rowPolynomial queryLevel criticalPolynomial coarsePolynomial
  simp_rw [Finset.mul_sum, combinedField_query_term, Finset.sum_add_distrib]
  ring

noncomputable def normalizedField {D N : ℕ} (β : CoefficientField D N) (K : ℝ) :
    CoefficientField D N := fun l v x => β l v x / K

theorem normalizedField_queryLegal {D N : ℕ} (β : CoefficientField D N)
    (hβ : QueryFieldLegal β) (K : ℝ) : QueryFieldLegal (normalizedField β K) := by
  intro l v hv x y hxy
  change β l v x / K = β l v y / K
  rw [hβ l v hv x y hxy]

theorem queryLevel_normalized {D N : ℕ} (β : CoefficientField D N)
    (K : ℝ) (l : Fin N) (x : SignCube D N) :
    queryLevel (normalizedField β K) l x = queryLevel β l x / K := by
  classical
  unfold queryLevel normalizedField
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hq : IsQueryProfile l v
  · simp only [ite_eq_left hq]
    ring
  · simp [hq]

theorem normalizedField_signal {D N : ℕ} (α b : CoefficientField D N)
    (b₀ K : ℝ) (x : SignCube D N) :
    rowPolynomial (b₀ / K) (queryLevel (normalizedField (combinedField α b) K)) x =
      (criticalPolynomial α x + coarsePolynomial b₀ b x) / K := by
  rw [← combinedField_signal α b b₀ x]
  unfold rowPolynomial
  simp_rw [queryLevel_normalized]
  conv_rhs => rw [add_div, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  ring

theorem normalizedField_query_bound {D N : ℕ} (α b : CoefficientField D N)
    (b₀ : ℝ)
    (hK : 0 < cubeSupNorm (fun x => criticalPolynomial α x + coarsePolynomial b₀ b x))
    (x : SignCube D N) :
    |rowPolynomial
        (b₀ / cubeSupNorm (fun y => criticalPolynomial α y + coarsePolynomial b₀ b y))
        (queryLevel (normalizedField (combinedField α b)
          (cubeSupNorm (fun y => criticalPolynomial α y + coarsePolynomial b₀ b y)))) x| ≤ 1 := by
  rw [normalizedField_signal]
  exact normalizedQuery_bound _ hK x

end HaarQuarter
