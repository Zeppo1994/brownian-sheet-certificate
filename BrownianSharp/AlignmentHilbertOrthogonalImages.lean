import BrownianSharp.AlignmentHilbertTraceApproximation

/-! Finite source bases diagonalizing the output inner product. -/
noncomputable section
open scoped RealInnerProductSpace
namespace BrownianSharp.AlignmentHilbertOrthogonalImages
open AlignmentHilbertTraceApproximation

theorem exists_orthogonal_image_basis
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E,
      ∀ i j, i ≠ j → ⟪T (b i), T (b j)⟫ = 0 := by
  let hG := gram_isPositive T
  let b := hG.isSymmetric.eigenvectorBasis (n:=Module.finrank ℝ E) rfl
  refine ⟨b,?_⟩
  intro i j hij
  have heigen : gram T (b j) = hG.isSymmetric.eigenvalues rfl j • b j :=
    hG.isSymmetric.apply_eigenvectorBasis rfl j
  calc
    ⟪T (b i), T (b j)⟫ = ⟪b i, gram T (b j)⟫ := by
      simpa only [gram,ContinuousLinearMap.comp_apply] using
        (T.adjoint_inner_right (b i) (T (b j))).symm
    _ = 0 := by
      rw [heigen,inner_smul_right,b.orthonormal.inner_eq_zero hij,mul_zero]

theorem exists_orthogonal_image_basis_of_lower
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (σ : ℝ)
    (hlower : ∀ x : E, ‖x‖ = 1 → σ ≤ ‖T x‖) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E,
      (∀ i j, i ≠ j → ⟪T (b i), T (b j)⟫ = 0) ∧
      ∀ i, σ ≤ ‖T (b i)‖ := by
  obtain ⟨b,hb⟩ := exists_orthogonal_image_basis T
  exact ⟨b,hb,fun i => hlower (b i) (b.orthonormal.norm_eq_one i)⟩

end BrownianSharp.AlignmentHilbertOrthogonalImages
