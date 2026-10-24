import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.Dimension.LinearMap
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

/-! Finite-source Hilbert trace and low-rank approximation utilities. -/

noncomputable section
open scoped InnerProductSpace

namespace BrownianSharp.AlignmentHilbertTraceApproximation

/-- The Gram operator of a continuous linear map. -/
def gram {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) : E →L[ℝ] E := T.adjoint ∘L T

/-- The Gram operator is positive. -/
theorem gram_isPositive {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) : (gram T).IsPositive := by
  simpa [gram] using (ContinuousLinearMap.isPositive_adjoint_comp_self T)

/-- The trace of `T†T` is the sum of the squared images of its Gram eigenbasis. -/
theorem gram_eigenvalues_sum_eq_norm_sq_sum {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) :
    (∑ i : Fin (Module.finrank ℝ E),
      (gram_isPositive T).isSymmetric.eigenvalues rfl i) =
    ∑ i : Fin (Module.finrank ℝ E),
      ‖T ((gram_isPositive T).isSymmetric.eigenvectorBasis rfl i)‖ ^ 2 := by
  let hG := gram_isPositive T
  let b := hG.isSymmetric.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  have htrace := hG.isSymmetric.trace_eq_sum_eigenvalues (n := Module.finrank ℝ E) rfl
  have htrace' := LinearMap.trace_eq_sum_inner (gram T).toLinearMap b
  calc
    (∑ i : Fin (Module.finrank ℝ E), hG.isSymmetric.eigenvalues rfl i) =
        LinearMap.trace ℝ E (gram T).toLinearMap := by
          rw [hG.isSymmetric.trace_eq_sum_eigenvalues (n := Module.finrank ℝ E) rfl]
          simp
    _ = ∑ i, ⟪b i, (gram T) (b i)⟫_ℝ := htrace'
    _ = ∑ i, ‖T (b i)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      change ⟪b i, T.adjoint (T (b i))⟫_ℝ = _
      rw [T.adjoint_inner_right]
      rw [real_inner_self_eq_norm_sq]
    _ = ∑ i : Fin (Module.finrank ℝ E),
        ‖T (hG.isSymmetric.eigenvectorBasis rfl i)‖ ^ 2 := by rfl

/-- The `(k+1)`-st Gram eigenvalue is bounded by the trace divided by `k+1`. -/
theorem gram_eigenvalue_le_trace_div {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) (k : ℕ) (hk : k < Module.finrank ℝ E) :
    (gram_isPositive T).isSymmetric.eigenvalues rfl ⟨k, hk⟩ ≤
      (∑ i : Fin (Module.finrank ℝ E),
        (gram_isPositive T).isSymmetric.eigenvalues rfl i) / (k + 1 : ℝ) := by
  let evals := (gram_isPositive T).isSymmetric.eigenvalues (n := Module.finrank ℝ E) rfl
  let s : Finset (Fin (Module.finrank ℝ E)) := Finset.Iic ⟨k, hk⟩
  have hmono : Antitone evals := (gram_isPositive T).isSymmetric.eigenvalues_antitone rfl
  have hnonneg : ∀ i, 0 ≤ evals i := by
    intro i
    exact (gram_isPositive T).toLinearMap.nonneg_eigenvalues rfl i
  have hcard : s.card = k + 1 := by
    simp [s]
  have hpartial : (k + 1 : ℝ) * evals ⟨k, hk⟩ ≤ ∑ i ∈ s, evals i := by
    calc
      (k + 1 : ℝ) * evals ⟨k, hk⟩ = ∑ i ∈ s, evals ⟨k, hk⟩ := by simp [hcard]
      _ ≤ ∑ i ∈ s, evals i := by
        apply Finset.sum_le_sum
        intro i hi
        exact hmono (Finset.mem_Iic.mp hi)
  have hfull : (∑ i ∈ s, evals i) ≤ ∑ i : Fin (Module.finrank ℝ E), evals i := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      simp
    · intro i hi hnot
      exact hnonneg i
  have hmul : (k + 1 : ℝ) * evals ⟨k, hk⟩ ≤ ∑ i : Fin (Module.finrank ℝ E), evals i :=
    le_trans hpartial hfull
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < k + 1)).2 (by nlinarith)

/-- The leading Gram eigenspaces define a source subspace of dimension at most `k`. -/
def leadingSubspace {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F] (T : E →L[ℝ] F) (k : ℕ)
    (hk : k < Module.finrank ℝ E) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range fun i : Fin k =>
    (gram_isPositive T).isSymmetric.eigenvectorBasis rfl
      ⟨i.val, Nat.lt_trans i.isLt hk⟩)

/-- Projection through the first `k` Gram eigenvectors gives a genuine
rank-at-most-`k` approximant (the norm estimate is supplied below). -/
theorem exists_leading_rank_approximation {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) (k : ℕ) (hk : k < Module.finrank ℝ E) :
    ∃ A : E →L[ℝ] F,
      Module.finrank ℝ A.toLinearMap.range ≤ k ∧
      A = T ∘L (leadingSubspace T k hk).starProjection := by
  let U := leadingSubspace T k hk
  have hU : Module.finrank ℝ U ≤ k := by
    dsimp [U, leadingSubspace]
    calc
      Module.finrank ℝ (Submodule.span ℝ (Set.range fun i : Fin k =>
          (gram_isPositive T).isSymmetric.eigenvectorBasis rfl
            ⟨i.val, Nat.lt_trans i.isLt hk⟩)) ≤ Fintype.card (Fin k) :=
        finrank_range_le_card _
      _ = k := Fintype.card_fin k
  refine ⟨T ∘L U.starProjection, ?_, rfl⟩
  change Module.finrank ℝ (LinearMap.range (T.toLinearMap.comp U.starProjection.toLinearMap)) ≤ k
  rw [LinearMap.range_comp, Submodule.range_starProjection]
  exact (Submodule.finrank_map_le T.toLinearMap U).trans hU

/-- The quadratic form of the Gram operator is diagonal in its eigenbasis. -/
theorem gram_quadratic_eq_eigen_sum {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) (y : E) :
    ‖T y‖ ^ 2 = ∑ i : Fin (Module.finrank ℝ E),
      (gram_isPositive T).isSymmetric.eigenvalues rfl i *
        ⟪(gram_isPositive T).isSymmetric.eigenvectorBasis rfl i, y⟫_ℝ ^ 2 := by
  let hG := gram_isPositive T
  let b := hG.isSymmetric.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  let evals := hG.isSymmetric.eigenvalues (n := Module.finrank ℝ E) rfl
  have hdiag : (b.repr ((gram T) y)).ofLp =
      fun i => evals i * (b.repr y).ofLp i := by
    funext i
    exact hG.isSymmetric.eigenvectorBasis_apply_self_apply rfl y i
  calc
    ‖T y‖ ^ 2 = ⟪T y, T y⟫_ℝ := by rw [real_inner_self_eq_norm_sq]
    _ = ⟪y, (gram T) y⟫_ℝ := by
      simp only [gram, ContinuousLinearMap.comp_apply]
      rw [T.adjoint_inner_right]
    _ = ⟪b.repr y, b.repr ((gram T) y)⟫_ℝ := by
      symm
      exact b.repr.inner_map_map y ((gram T) y)
    _ = ∑ i : Fin (Module.finrank ℝ E), evals i * (b.repr y i) ^ 2 := by
      have hcoord : ∀ i, (b.repr ((gram T) y)) i = evals i * (b.repr y) i := by
        intro i
        simpa using congrFun hdiag i
      rw [PiLp.inner_apply]
      simp only [hcoord]
      apply Finset.sum_congr rfl
      intro i hi
      have hs (x a : ℝ) : ⟪x, a * x⟫_ℝ = a * x ^ 2 := by
        calc
          ⟪x, a * x⟫_ℝ = a * ⟪x, x⟫_ℝ := by
            simpa only [smul_eq_mul] using (real_inner_smul_right x x a)
          _ = a * x ^ 2 := by simp [Real.norm_eq_abs]
      exact hs _ _
    _ = ∑ i : Fin (Module.finrank ℝ E), evals i * ⟪b i, y⟫_ℝ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      simp [b.repr_apply_apply]

/-- On the orthogonal complement of the first `k` Gram eigenvectors, the
quadratic form is bounded by the `k`-th eigenvalue. -/
theorem gram_norm_sq_le_eigenvalue_of_mem_orthogonal {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) (k : ℕ) (hk : k < Module.finrank ℝ E) (y : E)
    (hy : y ∈ (leadingSubspace T k hk)ᗮ) :
    ‖T y‖ ^ 2 ≤
      (gram_isPositive T).isSymmetric.eigenvalues rfl ⟨k, hk⟩ * ‖y‖ ^ 2 := by
  let hG := gram_isPositive T
  let b := hG.isSymmetric.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  let evals := hG.isSymmetric.eigenvalues (n := Module.finrank ℝ E) rfl
  have hzero (i : Fin k) : ⟪b ⟨i.val, Nat.lt_trans i.isLt hk⟩, y⟫_ℝ = 0 := by
    have hiU : b ⟨i.val, Nat.lt_trans i.isLt hk⟩ ∈ leadingSubspace T k hk := by
      apply Submodule.subset_span
      exact ⟨i, rfl⟩
    have hinner := (Submodule.mem_orthogonal' (leadingSubspace T k hk) y).1 hy _ hiU
    simpa [real_inner_comm] using hinner
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      evals i * ⟪b i, y⟫_ℝ ^ 2 ≤ evals ⟨k, hk⟩ * ⟪b i, y⟫_ℝ ^ 2 := by
    intro i
    by_cases hi : i.val < k
    · have hz : ⟪b i, y⟫_ℝ = 0 := by
        let j : Fin k := ⟨i.val, hi⟩
        simpa [j] using hzero j
      simp [hz]
    · have hki : (⟨k, hk⟩ : Fin (Module.finrank ℝ E)) ≤ i :=
        Fin.le_iff_val_le_val.mpr (Nat.le_of_not_lt hi)
      exact mul_le_mul_of_nonneg_right
        ((hG.isSymmetric.eigenvalues_antitone rfl) hki) (sq_nonneg _)
  calc
    ‖T y‖ ^ 2 = ∑ i : Fin (Module.finrank ℝ E), evals i * ⟪b i, y⟫_ℝ ^ 2 := by
      simpa [b, evals, hG] using gram_quadratic_eq_eigen_sum T y
    _ ≤ ∑ i : Fin (Module.finrank ℝ E), evals ⟨k, hk⟩ * ⟪b i, y⟫_ℝ ^ 2 :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = evals ⟨k, hk⟩ * ‖y‖ ^ 2 := by
      rw [← Finset.mul_sum]
      congr 1
      rw [← b.sum_sq_inner_right y]
    _ = (gram_isPositive T).isSymmetric.eigenvalues rfl ⟨k, hk⟩ * ‖y‖ ^ 2 := rfl

/-- The leading spectral projection has operator error at most the square root
of the first omitted Gram eigenvalue. -/
theorem leading_projection_error_le_sqrt_eigenvalue {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) (k : ℕ) (hk : k < Module.finrank ℝ E) :
    ‖T - T ∘L (leadingSubspace T k hk).starProjection‖ ≤
      Real.sqrt ((gram_isPositive T).isSymmetric.eigenvalues rfl ⟨k, hk⟩) := by
  let U := leadingSubspace T k hk
  let hG := gram_isPositive T
  have hEigNonneg : 0 ≤ hG.isSymmetric.eigenvalues rfl ⟨k, hk⟩ :=
    hG.toLinearMap.nonneg_eigenvalues rfl ⟨k, hk⟩
  apply (T - T ∘L U.starProjection).opNorm_le_bound (Real.sqrt_nonneg _)
  intro x
  let y := x - U.starProjection x
  have hy : y ∈ Uᗮ := by
    dsimp [y, U]
    exact Submodule.sub_starProjection_mem_orthogonal x
  have hysq := gram_norm_sq_le_eigenvalue_of_mem_orthogonal T k hk y (by simpa [U] using hy)
  have hyNorm : ‖y‖ ≤ ‖x‖ := by
    calc
      ‖y‖ = ‖(Uᗮ).starProjection x‖ := by
        dsimp [y]
        rw [U.starProjection_orthogonal]
        simp
      _ ≤ ‖x‖ := (Uᗮ).norm_starProjection_apply_le x
  have hnorm : ‖T y‖ ≤ Real.sqrt (hG.isSymmetric.eigenvalues rfl ⟨k, hk⟩) * ‖y‖ := by
    have hleft : 0 ≤ ‖T y‖ := norm_nonneg _
    have hright : 0 ≤ Real.sqrt (hG.isSymmetric.eigenvalues rfl ⟨k, hk⟩) * ‖y‖ :=
      mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    nlinarith [Real.sq_sqrt hEigNonneg]
  calc
    ‖(T - T ∘L U.starProjection) x‖ = ‖T y‖ := by
      simp [y, ContinuousLinearMap.comp_apply, map_sub]
    _ ≤ Real.sqrt (hG.isSymmetric.eigenvalues rfl ⟨k, hk⟩) * ‖y‖ := hnorm
    _ ≤ Real.sqrt (hG.isSymmetric.eigenvalues rfl ⟨k, hk⟩) * ‖x‖ :=
      mul_le_mul_of_nonneg_left hyNorm (Real.sqrt_nonneg _)

/-- A finite-source Hilbert operator admits a rank-`k` approximation with the
Hilbert--Schmidt trace bound `sqrt(trace(T†T)/(k+1))`. -/
theorem exists_rank_k_approximation_of_trace {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]
    (T : E →L[ℝ] F) (k : ℕ) :
    ∃ A : E →L[ℝ] F,
      Module.finrank ℝ A.toLinearMap.range ≤ k ∧
      ‖T - A‖ ≤ Real.sqrt
        ((∑ i : Fin (Module.finrank ℝ E),
          ‖T ((gram_isPositive T).isSymmetric.eigenvectorBasis rfl i)‖ ^ 2) /
          (k + 1 : ℝ)) := by
  let n := Module.finrank ℝ E
  by_cases hk : k < n
  · obtain ⟨A, hA, rfl⟩ := exists_leading_rank_approximation T k hk
    refine ⟨T ∘L (leadingSubspace T k hk).starProjection, hA, ?_⟩
    have heig := gram_eigenvalue_le_trace_div T k hk
    have herr := leading_projection_error_le_sqrt_eigenvalue T k hk
    have htrace := gram_eigenvalues_sum_eq_norm_sq_sum T
    rw [htrace] at heig
    exact herr.trans (Real.sqrt_le_sqrt heig)
  · have hnk : n ≤ k := Nat.le_of_not_gt hk
    refine ⟨T, ?_, ?_⟩
    · exact (LinearMap.finrank_range_le T.toLinearMap).trans hnk
    · simp

end BrownianSharp.AlignmentHilbertTraceApproximation
