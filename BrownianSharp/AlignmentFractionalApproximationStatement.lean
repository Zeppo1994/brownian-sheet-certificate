import BrownianSharp.AlignmentFractionalApproximationRates

/-! The sharp upper approximation-number rate with the manuscript's arbitrary
coordinate indexing and explicit minimum multiplicity. -/
noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentFractionalApproximationStatement
open AlignmentFractionalApproximationNumbers AlignmentFractionalTensorOperator

def FractionalApproximationUpperStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ (α : Fin d → ℝ) (hα : ∀ i, 1/2 < α i)
    (r : ℝ) (ν : ℕ), 2 ≤ ν → Latest.minimumMultiplicity α r ν →
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      approximationNumber (fractionalTensorRL α hα) k ≤
        ENNReal.ofReal (C*logarithmicIndexRate (r-1/2) (r*((ν-1:ℕ):ℝ)) k)

theorem fractionalApproximation_upper_certified : FractionalApproximationUpperStatement := by
  intro d hd α hα r ν hν hm
  classical
  have hpos : 0 < (Finset.univ.filter (fun i : Fin d => α i=r)).card := by
    rw [hm.2]
    omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hpos
  have hir : α i=r := (Finset.mem_filter.mp hi).2
  have hr : 1/2 < r := hir ▸ hα i
  have hνd : ν ≤ d := by
    calc
      ν = (Finset.univ.filter (fun i : Fin d => α i=r)).card := hm.2.symm
      _ ≤ (Finset.univ : Finset (Fin d)).card := Finset.card_filter_le _ _
      _ = d := by simp
  obtain ⟨e,he⟩ := Nat.exists_eq_add_of_le hνd
  subst d
  obtain ⟨A,hA,C,hC,k₀,hk₀,h⟩ :=
    AlignmentFractionalApproximationRates.polynomial_fractional_tensor_RL_approximation_number_upper
      hν hr α hα hm
  refine ⟨C,hC,k₀,?_,h⟩
  omega

end BrownianSharp.AlignmentFractionalApproximationStatement
