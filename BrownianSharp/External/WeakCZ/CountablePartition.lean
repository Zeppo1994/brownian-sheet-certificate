import Mathlib.MeasureTheory.Integral.Prod

/-!
A reserved-core partition indexed by an arbitrary encodable type. This allows
countable Whitney centers to remain in their natural subtype; the natural code
orders the overlap assignment without introducing repeated centers.
-/

noncomputable section

open Set MeasureTheory

namespace BrownianSharp.External.WeakCZ

variable {α : Type*} [MeasurableSpace α]
variable {ι : Type*} [Encodable ι]

def rankedCoreExpandedPiece (C D : ι → Set α) (i : ι) : Set α :=
  C i ∪ (D i \ ((⋃ j, C j) ∪ ⋃ j : {j : ι // Encodable.encode j < Encodable.encode i}, D j.1))

theorem rankedCoreExpandedPiece_core_subset (C D : ι → Set α) (i : ι) :
    C i ⊆ rankedCoreExpandedPiece C D i := subset_union_left

theorem rankedCoreExpandedPiece_subset (C D : ι → Set α) (i : ι)
    (hCD : ∀ i, C i ⊆ D i) : rankedCoreExpandedPiece C D i ⊆ D i := by
  intro x hx
  rcases hx with hx | hx
  · exact hCD i hx
  · exact hx.1

theorem rankedCoreExpandedPiece_pairwiseDisjoint (C D : ι → Set α)
    (hCD : ∀ i, C i ⊆ D i)
    (hC : Pairwise (fun i j => Disjoint (C i) (C j))) :
    Pairwise (fun i j => Disjoint (rankedCoreExpandedPiece C D i)
      (rankedCoreExpandedPiece C D j)) := by
  classical
  intro i j hij
  have hcode : Encodable.encode i ≠ Encodable.encode j := by
    intro h
    exact hij (Encodable.encode_injective h)
  rw [disjoint_left]
  intro x hxi hxj
  rcases lt_or_gt_of_ne hcode with hlt | hgt
  · rcases hxi with hci | ⟨hdi, hxi⟩ <;> rcases hxj with hcj | ⟨hdj, hxj⟩
    · exact (disjoint_left.mp (hC hij) hci) hcj
    · exact hxj (Or.inr (mem_iUnion.mpr ⟨(⟨i, hlt⟩ : {k : ι // Encodable.encode k < Encodable.encode j}), hCD i hci⟩))
    · exact hxi (Or.inl (mem_iUnion.mpr ⟨j, hcj⟩))
    · exact hxj (Or.inr (mem_iUnion.mpr ⟨(⟨i, hlt⟩ : {k : ι // Encodable.encode k < Encodable.encode j}), hdi⟩))
  · rcases hxi with hci | ⟨hdi, hxi⟩ <;> rcases hxj with hcj | ⟨hdj, hxj⟩
    · exact (disjoint_left.mp (hC hij) hci) hcj
    · exact hxj (Or.inl (mem_iUnion.mpr ⟨i, hci⟩))
    · exact hxi (Or.inr (mem_iUnion.mpr ⟨(⟨j, hgt⟩ : {k : ι // Encodable.encode k < Encodable.encode i}), hCD j hcj⟩))
    · exact hxi (Or.inr (mem_iUnion.mpr ⟨(⟨j, hgt⟩ : {k : ι // Encodable.encode k < Encodable.encode i}), hdj⟩))

theorem iUnion_rankedCoreExpandedPiece_eq (C D : ι → Set α)
    (hCD : ∀ i, C i ⊆ D i) :
    (⋃ i, rankedCoreExpandedPiece C D i) = ⋃ i, D i := by
  classical
  ext x
  constructor
  · intro h
    rcases mem_iUnion.mp h with ⟨i, hi⟩
    exact mem_iUnion.mpr ⟨i, rankedCoreExpandedPiece_subset C D i hCD hi⟩
  · intro hx
    by_cases hcore : x ∈ ⋃ i, C i
    · rcases mem_iUnion.mp hcore with ⟨i, hi⟩
      exact mem_iUnion.mpr ⟨i, rankedCoreExpandedPiece_core_subset C D i hi⟩
    · rcases mem_iUnion.mp hx with ⟨i₀, hi₀⟩
      have hex : ∃ n : ℕ, ∃ i : ι, Encodable.encode i = n ∧ x ∈ D i :=
        ⟨Encodable.encode i₀, i₀, rfl, hi₀⟩
      obtain ⟨i, hcode, hDi⟩ := Nat.find_spec hex
      have hbefore : ∀ j : ι, Encodable.encode j < Encodable.encode i → x ∉ D j := by
        intro j hj hDj
        have hnot := Nat.find_min hex (by rw [← hcode]; exact hj)
        exact hnot ⟨j, rfl, hDj⟩
      have hnotcore : x ∉ ⋃ j, C j := hcore
      have hnotbefore : x ∉ ⋃ j : {j : ι // Encodable.encode j < Encodable.encode i}, D j.1 := by
        intro h
        rcases mem_iUnion.mp h with ⟨j, hj⟩
        exact hbefore j j.2 hj
      exact mem_iUnion.mpr ⟨i, Or.inr ⟨hDi, not_or.mpr ⟨hnotcore, hnotbefore⟩⟩⟩

theorem measurableSet_rankedCoreExpandedPiece (C D : ι → Set α) (i : ι)
    (hC : ∀ i, MeasurableSet (C i)) (hD : ∀ i, MeasurableSet (D i)) :
    MeasurableSet (rankedCoreExpandedPiece C D i) := by
  unfold rankedCoreExpandedPiece
  exact (hC i).union ((hD i).diff ((MeasurableSet.iUnion hC).union
    (MeasurableSet.iUnion fun j : {j : ι // Encodable.encode j < Encodable.encode i} => hD j.1)))

end BrownianSharp.External.WeakCZ
