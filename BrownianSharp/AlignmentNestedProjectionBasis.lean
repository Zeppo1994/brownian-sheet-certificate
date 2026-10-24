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

/-- Orthogonal projections add across the nested-space decomposition. -/
theorem starProjection_succ_eq_add_increment (U : ℕ → Submodule ℝ E) (n : ℕ)
    [FiniteDimensional ℝ ↥(U n)]
    [FiniteDimensional ℝ ↥(U (n+1))]
    [FiniteDimensional ℝ ↥(increment U n)]
    (hnested : U n ≤ U (n+1)) (x : E) :
    (U (n+1)).starProjection x =
      (U n).starProjection x + (increment U n).starProjection x := by
  let V := increment U n
  have hdecomp := succ_eq_sup_increment U n hnested
  have horth : V ≤ (U n)ᗮ := by
    intro y hy
    exact hy.2
  let p := (U n).starProjection x
  let q := V.starProjection x
  have hp : p ∈ U n := (U n).starProjection_apply_mem x
  have hq : q ∈ V := V.starProjection_apply_mem x
  have hsum : p+q ∈ U n ⊔ V := Submodule.add_mem_sup hp hq
  have hres : x-(p+q) ∈ (U n ⊔ V)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    rcases (Submodule.mem_sup.mp hw) with ⟨u,hu,v,hv,rfl⟩
    have hpu : ⟪x-p,u⟫ = 0 :=
      (Submodule.mem_orthogonal' (U n) (x-p)).mp
        ((U n).sub_starProjection_mem_orthogonal x) u hu
    have hqv : ⟪x-q,v⟫ = 0 :=
      (Submodule.mem_orthogonal' V (x-q)).mp
        (V.sub_starProjection_mem_orthogonal x) v hv
    have hqu : ⟪q,u⟫ = 0 :=
      (Submodule.mem_orthogonal' (U n) q).mp (horth hq) u hu
    have hpv' : ⟪v,p⟫ = 0 :=
      (Submodule.mem_orthogonal' (U n) v).mp (horth hv) p hp
    have hpv : ⟪p,v⟫ = 0 := by rw [real_inner_comm]; exact hpv'
    have hleft : ⟪x-p-q,u⟫ = 0 := by
      rw [inner_sub_left, hpu, hqu]
      simp
    have hright : ⟪x-p-q,v⟫ = 0 := by
      rw [inner_sub_left] at hqv
      rw [inner_sub_left, inner_sub_left]
      nlinarith
    have hxform : x-(p+q) = x-p-q := by abel
    have hleft' : ⟪x-(p+q),u⟫ = 0 := by rw [hxform]; exact hleft
    have hright' : ⟪x-(p+q),v⟫ = 0 := by rw [hxform]; exact hright
    rw [inner_add_right, hleft', hright']
    simp
  have hproj := (U n ⊔ V).eq_starProjection_of_mem_orthogonal hsum hres
  simpa [p,q,V,hdecomp] using hproj

end BrownianSharp.AlignmentNestedProjectionBasis
