import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.Module.Basic

open scoped RealInnerProductSpace
open InnerProductSpace
namespace HaarQuarter

variable {ι H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Equal Gram matrices define a canonical isometry on the closed linear
span, including dependent generating families. -/
theorem exists_closedSpan_isometry_of_gram
    (v : ι → H) (w : ι → K)
    (hGram : ∀ i j, ⟪w i,w j⟫ = ⟪v i,v j⟫) :
    ∃ T : (Submodule.span ℝ (Set.range v)).topologicalClosure →ₗᵢ[ℝ] K,
      ∀ i, T ⟨v i, (Submodule.span ℝ (Set.range v)).le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self i))⟩ = w i := by
  classical
  let f₀ := Finsupp.linearCombination ℝ v
  let g := Finsupp.linearCombination ℝ w
  let R := Submodule.span ℝ (Set.range v)
  let S := R.topologicalClosure
  have hspan : LinearMap.range f₀ = R := Finsupp.range_linearCombination ℝ
  let f : (ι →₀ ℝ) →ₗ[ℝ] R := f₀.codRestrict R (by
    intro c
    rw [← hspan]
    exact LinearMap.mem_range_self f₀ c)
  let inc : R →ₗ[ℝ] S := Submodule.inclusion R.le_topologicalClosure
  let e : (ι →₀ ℝ) →ₗ[ℝ] S := inc.comp f
  have hi : DenseRange inc := by
    apply (denseRange_inclusion_iff R.le_topologicalClosure).2
    simpa only [Submodule.topologicalClosure_coe] using
      (Set.Subset.rfl : closure (R : Set H) ⊆ closure (R : Set H))
  have hiCont : Continuous inc := by
    change Continuous (fun x : R => (⟨(x:H), R.le_topologicalClosure x.property⟩ : S))
    exact continuous_subtype_val.subtype_mk _
  have hfSurj : Function.Surjective f := by
    rintro ⟨x, hx⟩
    rw [← hspan] at hx
    rcases hx with ⟨c,hc⟩
    exact ⟨c, Subtype.ext hc⟩
  have he : DenseRange e := hi.comp hfSurj.denseRange hiCont
  have hinner (c d : ι →₀ ℝ) : ⟪g c,g d⟫ = ⟪f₀ c,f₀ d⟫ := by
    simp only [g, f₀, Finsupp.linearCombination_apply,
      Finsupp.sum_inner, Finsupp.inner_sum, real_inner_smul_left,
      real_inner_smul_right, hGram]
  have hnorm (c : ι →₀ ℝ) : ‖g c‖ = ‖e c‖ := by
    have hsq := hinner c c
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hsq
    change ‖g c‖ = ‖f₀ c‖
    nlinarith [norm_nonneg (g c), norm_nonneg (f₀ c)]
  let T : S →ₗᵢ[ℝ] K := g.extendOfIsometry he hnorm
  refine ⟨T, ?_⟩
  intro i
  have h := LinearMap.extendOfIsometry_eq (f := g) he hnorm (Finsupp.single i 1)
  have hgen : e (Finsupp.single i 1) =
      (⟨v i, R.le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self i))⟩ : S) := by
    apply Subtype.ext
    change f₀ (Finsupp.single i 1) = v i
    simp [f₀]
  have ht : T (e (Finsupp.single i 1)) = w i := by simpa [T,g] using h
  rw [hgen] at ht
  exact ht


/-- A continuous isometry fixed on generators maps their closed span into
the closed span of the image generators. -/
theorem closedSpan_isometry_image_mem [CompleteSpace H]
    (v : ι → H) (w : ι → K)
    (T : (Submodule.span ℝ (Set.range v)).topologicalClosure →ₗᵢ[ℝ] K)
    (hT : ∀ i, T ⟨v i, (Submodule.span ℝ (Set.range v)).le_topologicalClosure
      (Submodule.subset_span (Set.mem_range_self i))⟩ = w i)
    (x : (Submodule.span ℝ (Set.range v)).topologicalClosure) :
    T x ∈ (Submodule.span ℝ (Set.range w)).topologicalClosure := by
  let V := Submodule.span ℝ (Set.range v)
  let S := V.topologicalClosure
  let U := (Submodule.span ℝ (Set.range w)).topologicalClosure
  let L : H →L[ℝ] K := T.toContinuousLinearMap.comp S.orthogonalProjectionOnto
  let Q : Submodule ℝ H := U.comap L.toLinearMap
  have hgen (i : ι) : L (v i) = w i := by
    change T (S.orthogonalProjectionOnto
      (⟨v i, V.le_topologicalClosure (Submodule.subset_span (Set.mem_range_self i))⟩ : S)) = w i
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
    exact hT i
  have hV : V ≤ Q := by
    apply Submodule.span_le.mpr
    rintro y ⟨i,rfl⟩
    change L (v i) ∈ U
    rw [hgen]
    exact (Submodule.span ℝ (Set.range w)).le_topologicalClosure
      (Submodule.subset_span (Set.mem_range_self i))
  have hQ : IsClosed (Q : Set H) :=
    (Submodule.isClosed_topologicalClosure _).preimage L.continuous
  have hSQ : S ≤ Q := Submodule.topologicalClosure_minimal V hV hQ
  have hx : L (x:H) ∈ U := hSQ x.property
  have heq : L (x:H) = T x := by
    dsimp [L]
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rw [heq] at hx
  exact hx

end HaarQuarter
