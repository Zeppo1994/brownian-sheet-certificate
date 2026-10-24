import BrownianSharp.AlignmentHilbertOrthogonalImages
import Mathlib.Tactic

/-! Select a prescribed finite number of orthogonal-image singular directions
from a finite-dimensional source with a uniform lower norm bound. -/

noncomputable section
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentFiniteOrthogonalImageSubframe

open BrownianSharp.AlignmentHilbertOrthogonalImages

/-- A uniform lower bound on the unit sphere of a finite-dimensional source
gives any requested number of orthonormal vectors with pairwise orthogonal
images and the same lower bound. -/
theorem exists_orthogonal_image_subframe
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) {n : ℕ}
    (hn : n ≤ Module.finrank ℝ E) (σ : ℝ)
    (hlower : ∀ x : E, ‖x‖ = 1 → σ ≤ ‖T x‖) :
    ∃ e : Fin n → E,
      Orthonormal ℝ e ∧
      (∀ i j, i ≠ j → inner ℝ (T (e i)) (T (e j)) = 0) ∧
      ∀ i, σ ≤ ‖T (e i)‖ := by
  classical
  obtain ⟨b, horth, hlowerb⟩ := exists_orthogonal_image_basis_of_lower T σ hlower
  let c : Fin n → Fin (Module.finrank ℝ E) := Fin.castLE hn
  have hc : Function.Injective c := by
    intro i j h
    exact Fin.castLE_injective hn h
  refine ⟨fun i => b (c i), ?_, ?_, ?_⟩
  · exact b.orthonormal.comp c hc
  · intro i j hij
    exact horth (c i) (c j) (by
      intro h
      apply hij
      exact hc h)
  · intro i
    exact hlowerb (c i)

end BrownianSharp.AlignmentFiniteOrthogonalImageSubframe
