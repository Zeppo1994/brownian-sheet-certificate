import BrownianSharp.AlignmentHilbertOrthogonalEnergy
import Mathlib.Tactic

/-! A finite orthonormal source frame with orthogonal, uniformly nondegenerate
images gives a lower bound on its entire span. -/

noncomputable section
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentFiniteOrthonormalSpanLower

open BrownianSharp.AlignmentHilbertOrthogonalEnergy

theorem norm_lower_on_orthonormal_span
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) {ι : Type*} [Fintype ι]
    (e : ι → E) (σ : ℝ)
    (he : Orthonormal ℝ e)
    (horth : ∀ (i j : ι), i ≠ j → inner ℝ (T (e i)) (T (e j)) = 0)
    (hlower : ∀ (i : ι), σ ≤ ‖T (e i)‖) (hσ : 0 ≤ σ) :
    ∀ x ∈ Submodule.span ℝ (Set.range e), σ * ‖x‖ ≤ ‖T x‖ := by
  classical
  let s : Finset ι := Finset.univ
  let U : Submodule ℝ E := Submodule.span ℝ (s.image e : Set E)
  have hset : (s.image e : Set E) = Set.range e := by
    ext x
    simp [s]
  have hU : U = Submodule.span ℝ (Set.range e) := by
    simp [U, hset]
  let b : OrthonormalBasis (↥s) ℝ U := OrthonormalBasis.span he s
  let T' : U →L[ℝ] F := T.comp U.subtypeₗᵢ.toContinuousLinearMap
  have horth' : ∀ (i j : ↥s), i ≠ j → inner ℝ (T' (b i)) (T' (b j)) = 0 := by
    intro i j hij
    have hi : ((b i : U) : E) = e i := by
      change (OrthonormalBasis.span he s i : E) = e i
      exact OrthonormalBasis.span_apply he s i
    have hj : ((b j : U) : E) = e j := by
      change (OrthonormalBasis.span he s j : E) = e j
      exact OrthonormalBasis.span_apply he s j
    have hij' : (i : ι) ≠ (j : ι) := by
      intro heq
      exact hij (Subtype.ext heq)
    simpa [T', hi, hj] using horth i j hij'
  have hlower' : ∀ i : ↥s, σ ≤ ‖T' (b i)‖ := by
    intro i
    have hi : ((b i : U) : E) = e i := by
      change (OrthonormalBasis.span he s i : E) = e i
      exact OrthonormalBasis.span_apply he s i
    simpa [T', hi] using hlower i
  intro x hx
  have hxU : x ∈ U := by
    rw [hU]
    exact hx
  let xU : U := ⟨x, hxU⟩
  have hbound := norm_lower_of_orthogonal_basis_images T' b σ horth' hlower' hσ xU
  simpa [T', xU] using hbound

end BrownianSharp.AlignmentFiniteOrthonormalSpanLower
