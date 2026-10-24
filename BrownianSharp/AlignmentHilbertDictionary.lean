import BrownianSharp.GaussianDictionaryApproximation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
open scoped BigOperators RealInnerProductSpace ENNReal
namespace BrownianSharp.AlignmentHilbertDictionary

/-- Finite Gaussian dictionary approximation applies to vectors in any real
Hilbert space: only their finite-dimensional span is needed. -/
theorem hilbert_dictionary_approximation
    {H G : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype G]
    (m : ℕ) (v : G → H) (R : ℝ) (hR : 0 ≤ R) (hv : ∀ g, ‖v g‖ ≤ R) :
    ∃ W : Submodule ℝ (G → ℝ), Module.rank ℝ W ≤ (m : Cardinal) ∧
      ∀ x : H, ‖x‖ ≤ 1 → ∃ y ∈ W,
        ‖(fun g => ⟪x, v g⟫) - y‖ ≤
          10000 * R * Real.sqrt
            (Real.log (2 * (Fintype.card G : ℝ) + 2) / ((m : ℝ) + 1)) := by
  classical
  let V : Submodule ℝ H := Submodule.span ℝ (Set.range v)
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  let b := stdOrthonormalBasis ℝ V
  let w : G → EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    fun g => b.repr ⟨v g, Submodule.subset_span (Set.mem_range_self g)⟩
  obtain ⟨W, hW, happ⟩ := dictionary_approximation_of_fin_dictionary
    GaussianRIP.finDictionaryApproximation_gaussian m w R hR
    (fun g => by simpa [w] using hv g)
  refine ⟨W, hW, ?_⟩
  intro x hx
  obtain ⟨y, hy, herr⟩ := happ (b.repr (V.orthogonalProjectionOnto x)) (by
    rw [b.repr.norm_map]
    exact (V.norm_orthogonalProjectionOnto_apply_le x).trans hx)
  refine ⟨y, hy, ?_⟩
  have heq : finiteRowLinear w (b.repr (V.orthogonalProjectionOnto x)) =
      (fun g => ⟪x, v g⟫) := by
    funext g
    change ⟪b.repr (V.orthogonalProjectionOnto x),
      b.repr ⟨v g, Submodule.subset_span (Set.mem_range_self g)⟩⟫ = _
    rw [b.repr.inner_map_map]
    exact V.inner_orthogonalProjectionOnto_eq_of_mem_right _ _
  simpa only [heq] using herr

end BrownianSharp.AlignmentHilbertDictionary
