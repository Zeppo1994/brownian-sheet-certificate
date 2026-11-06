import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Generic orthogonal increments for nested finite-dimensional subspaces of
an actual Hilbert space. These lemmas are intended for polynomial and other
piecewise-finite approximation spaces. -/

noncomputable section
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentNestedProjectionBasis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The new directions added between two consecutive nested subspaces. -/
def increment (U : ℕ → Submodule ℝ E) (n : ℕ) : Submodule ℝ E :=
  U (n+1) ⊓ (U n)ᗮ

/-- A finite-dimensional ambient successor gives a finite-dimensional
orthogonal increment, so mathlib's canonical finite orthonormal basis applies. -/
instance increment_finiteDimensional (U : ℕ → Submodule ℝ E) (n : ℕ)
    [FiniteDimensional ℝ ↥(U (n+1))] :
    FiniteDimensional ℝ ↥(increment U n) :=
  FiniteDimensional.of_injective
    (Submodule.inclusion (inf_le_left : increment U n ≤ U (n+1)))
    (Submodule.inclusion_injective _)

noncomputable def incrementBasis (U : ℕ → Submodule ℝ E) (n : ℕ)
    [FiniteDimensional ℝ ↥(U (n+1))] :
    OrthonormalBasis (Fin (Module.finrank ℝ ↥(increment U n))) ℝ ↥(increment U n) :=
  stdOrthonormalBasis ℝ (increment U n)

/-- A nested finite-dimensional subspace splits into its previous part and
the orthogonal increment. -/
theorem succ_eq_sup_increment (U : ℕ → Submodule ℝ E) (n : ℕ)
    [FiniteDimensional ℝ ↥(U n)]
    (hnested : U n ≤ U (n+1)) :
    U (n+1) = U n ⊔ increment U n := by
  let V := increment U n
  apply le_antisymm
  · intro x hx
    let p := (U n).starProjection x
    have hp : p ∈ U n := (U n).starProjection_apply_mem x
    have hres : x-p ∈ V := by
      change x-p ∈ U (n+1) ⊓ (U n)ᗮ
      constructor
      · exact sub_mem hx (hnested hp)
      · exact (U n).sub_starProjection_mem_orthogonal x
    exact (Submodule.mem_sup.mpr ⟨p,hp,x-p,hres,by simp [p]⟩)
  · intro x hx
    rcases (Submodule.mem_sup.mp hx) with ⟨u,hu,v,hv,rfl⟩
    exact add_mem (hnested hu) hv.1

end BrownianSharp.AlignmentNestedProjectionBasis
