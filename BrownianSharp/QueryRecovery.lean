import BrownianSharp.QueryRows
import BrownianSharp.TensorRecovery
import Mathlib.Algebra.BigOperators.Fin

/-!
# Coefficient recovery for complete first/transverse queries

The original first coordinate becomes one more tensor coordinate. An unused
dummy first coordinate permits reuse of the local tensor recovery theorem.
All strictly coarser profiles and the scalar are retained in the polynomial.
-/

open scoped BigOperators

namespace HaarQuarter

def unpackFullCube {D N : ℕ} (z : SignCube (D + 1) N) : SignCube D N :=
  ⟨z.transverse 0, fun a => z.transverse a.succ⟩

def packFullCube {D N : ℕ} (x : SignCube D N) : SignCube (D + 1) N :=
  ⟨fun _ => false, Fin.cons x.first x.transverse⟩

theorem unpack_packFullCube {D N : ℕ} (x : SignCube D N) :
    unpackFullCube (packFullCube x) = x := by
  cases x
  simp [unpackFullCube, packFullCube]

theorem fullTensor_word {D N : ℕ} (z : SignCube (D + 1) N)
    (l : Fin N) (v : BoundedProfile D N) :
    profileWord z (Fin.cons l v) =
      firstDigit (unpackFullCube z) l * profileWord (unpackFullCube z) v := by
  simp [profileWord, Fin.prod_univ_succ, digit, firstDigit, unpackFullCube]

theorem sum_fullProfiles {D N : ℕ} (f : BoundedProfile (D + 1) N → ℝ) :
    (∑ v, f v) = ∑ l : Fin N, ∑ v : BoundedProfile D N, f (Fin.cons l v) := by
  classical
  calc
    _ = ∑ p : Fin N × BoundedProfile D N, f (Fin.cons p.1 p.2) :=
      ((Fin.consEquiv (fun _ : Fin (D + 1) => Fin N)).sum_comp f).symm
    _ = _ := Fintype.sum_prod_type _

noncomputable def fullTensorField {D N : ℕ} (β : CoefficientField D N)
    (v : BoundedProfile (D + 1) N) (z : SignCube (D + 1) N) : ℝ :=
  if IsQueryProfile (v 0) (Fin.tail v) then
    β (v 0) (Fin.tail v) (unpackFullCube z) else 0

theorem fullTensorField_legal {D N : ℕ} (β : CoefficientField D N)
    (hβ : QueryFieldLegal β) (v : BoundedProfile (D + 1) N) :
    LegalCoefficient 0 (naturalProfile v) (fullTensorField β v) := by
  intro x y hxy
  by_cases hq : IsQueryProfile (v 0) (Fin.tail v)
  · simp only [fullTensorField, ite_eq_left hq]
    apply hβ (v 0) (Fin.tail v) hq
    constructor
    · intro k hk
      exact hxy.2 0 k hk
    · intro a k hk
      exact hxy.2 a.succ k hk
  · simp [fullTensorField, hq]

theorem fullTensor_signal {D N : ℕ} (β : CoefficientField D N)
    (c₀ : ℝ) (z : SignCube (D + 1) N) :
    tensorPolynomial c₀ (fullTensorField β) z =
      rowPolynomial c₀ (queryLevel β) (unpackFullCube z) := by
  classical
  unfold tensorPolynomial rowPolynomial queryLevel
  rw [sum_fullProfiles]
  congr 1
  apply Finset.sum_congr rfl
  intro l hl
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hq : IsQueryProfile l v
  · simp only [fullTensorField, Fin.cons_zero, Fin.tail_cons, ite_eq_left hq, fullTensor_word]
    ring
  · simp [fullTensorField, hq]

theorem query_coefficient_bound {D N : ℕ} (β : CoefficientField D N)
    (hβ : QueryFieldLegal β) (c₀ K : ℝ)
    (hbound : ∀ x, |rowPolynomial c₀ (queryLevel β) x| ≤ K)
    (l : Fin N) (v : BoundedProfile D N) (hq : IsQueryProfile l v)
    (x : SignCube D N) : |β l v x| ≤ K := by
  have h := tensor_coefficient_bound (Nat.succ_pos D) c₀ K (fullTensorField β)
    (fullTensorField_legal β hβ)
    (fun z => by rw [fullTensor_signal]; exact hbound (unpackFullCube z))
    (Fin.cons l v) (packFullCube x)
  simpa [fullTensorField, hq, unpack_packFullCube] using h

theorem critical_coefficient_bound {D N : ℕ} (α b : CoefficientField D N)
    (hα : CriticalFieldLegal α) (hb : CoarseFieldLegal b) (c₀ : ℝ)
    (l : Fin N) (v : BoundedProfile D N) (hc : IsCriticalProfile l v)
    (x : SignCube D N) :
    |α l v x| ≤ cubeSupNorm (fun y => criticalPolynomial α y + coarsePolynomial c₀ b y) := by
  have h := query_coefficient_bound (combinedField α b)
    (combinedField_queryLegal α b hα hb) c₀
    (cubeSupNorm (fun y => criticalPolynomial α y + coarsePolynomial c₀ b y))
    (fun y => by
      rw [combinedField_signal]
      exact cubeSupNorm_pointwise (fun z => criticalPolynomial α z + coarsePolynomial c₀ b z) y)
    l v (le_of_eq hc) x
  simpa [combinedField, hc] using h

theorem coarse_coefficient_bound {D N : ℕ} (α b : CoefficientField D N)
    (hα : CriticalFieldLegal α) (hb : CoarseFieldLegal b) (c₀ : ℝ)
    (l : Fin N) (v : BoundedProfile D N) (hc : IsCoarseProfile l v)
    (x : SignCube D N) :
    |b l v x| ≤ cubeSupNorm (fun y => criticalPolynomial α y + coarsePolynomial c₀ b y) := by
  have hnc : ¬ IsCriticalProfile l v := ne_of_lt hc
  have h := query_coefficient_bound (combinedField α b)
    (combinedField_queryLegal α b hα hb) c₀
    (cubeSupNorm (fun y => criticalPolynomial α y + coarsePolynomial c₀ b y))
    (fun y => by
      rw [combinedField_signal]
      exact cubeSupNorm_pointwise (fun z => criticalPolynomial α z + coarsePolynomial c₀ b z) y)
    l v (le_of_lt hc) x
  simpa [combinedField, hnc, hc] using h

end HaarQuarter
