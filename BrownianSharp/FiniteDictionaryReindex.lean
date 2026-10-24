import BrownianSharp.FiniteCoordinateLayers
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.LinearAlgebra.Dimension.Basic

/-! Reindex finite Euclidean dictionaries and finite sup-norm grids without
changing approximation dimensions or errors. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace ENNReal
namespace BrownianSharp

/-- The finite `Fin`-indexed dictionary approximation interface. -/
def FinDictionaryApproximation (C : ℝ) : Prop :=
  ∀ N M m : ℕ, ∀ v : Fin M → EuclideanSpace ℝ (Fin N), ∀ R : ℝ,
    0 ≤ R → (∀ i,‖v i‖≤R) →
    ∃ V : Submodule ℝ (PiLp ∞ (fun _ : Fin M => ℝ)),
      Module.rank ℝ V≤(m:Cardinal) ∧
      ∀ x : EuclideanSpace ℝ (Fin N), ‖x‖≤1 → ∃ y ∈ V,
        ‖(WithLp.toLp ∞ (fun i => ⟪x,v i⟫))-y‖≤
          C*R*Real.sqrt (Real.log (2*(M:ℝ)+2)/((m:ℝ)+1))

variable {I G : Type} [Fintype I] [Fintype G]

def finiteEuclideanReindex : EuclideanSpace ℝ I ≃ₗᵢ[ℝ]
    EuclideanSpace ℝ (Fin (Fintype.card I)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin I)

def finiteSupReindex : PiLp ∞ (fun _ : Fin (Fintype.card G) => ℝ) ≃ₗᵢ[ℝ] (G → ℝ) :=
  (LinearIsometryEquiv.piLpCongrLeft ∞ ℝ ℝ (Fintype.equivFin G).symm).trans
    (PiLp.equivₗᵢ (𝕜:=ℝ) (fun _ : G => ℝ))

/-- The ordinary function sup norm is exactly the `PiLp ∞` norm used in the
finite Gaussian-matrix construction. -/
theorem finiteSupReindex_rows (v : G → EuclideanSpace ℝ I) (x : EuclideanSpace ℝ I) :
    finiteSupReindex (G:=G)
      (WithLp.toLp ∞ (fun i : Fin (Fintype.card G) =>
        ⟪finiteEuclideanReindex x,
          finiteEuclideanReindex (v ((Fintype.equivFin G).symm i))⟫)) =
      finiteRowLinear v x := by
  funext g
  change ⟪finiteEuclideanReindex x,
    finiteEuclideanReindex (v ((Fintype.equivFin G).symm ((Fintype.equivFin G) g)))⟫=⟪x,v g⟫
  rw [Equiv.symm_apply_apply]
  exact LinearIsometryEquiv.inner_map_map _ _ _

theorem dictionary_approximation_of_fin_dictionary {C : ℝ}
    (hfin : FinDictionaryApproximation C) (m : ℕ)
    (v : G → EuclideanSpace ℝ I) (R : ℝ) (hR : 0≤R) (hv : ∀ g,‖v g‖≤R) :
    ∃ V : Submodule ℝ (G → ℝ), Module.rank ℝ V≤(m:Cardinal) ∧
      ∀ x : EuclideanSpace ℝ I, ‖x‖≤1 → ∃ y ∈ V,
        ‖finiteRowLinear v x-y‖≤C*R*
          Real.sqrt (Real.log (2*(Fintype.card G:ℝ)+2)/((m:ℝ)+1)) := by
  let E := finiteEuclideanReindex (I:=I)
  let F := finiteSupReindex (G:=G)
  let w : Fin (Fintype.card G) → EuclideanSpace ℝ (Fin (Fintype.card I)) :=
    fun i => E (v ((Fintype.equivFin G).symm i))
  obtain ⟨V,hV,happrox⟩ := hfin (Fintype.card I) (Fintype.card G) m w R hR
    (fun i => by simpa [w,E] using hv ((Fintype.equivFin G).symm i))
  refine ⟨V.map F.toLinearEquiv.toLinearMap,(rank_map_le _ _).trans hV,?_⟩
  intro x hx
  obtain ⟨y,hy,herr⟩ := happrox (E x) (by simpa [E] using hx)
  refine ⟨F y,Submodule.mem_map.mpr ⟨y,hy,rfl⟩,?_⟩
  have heq : F (WithLp.toLp ∞ (fun i => ⟪E x,w i⟫))=finiteRowLinear v x :=
    finiteSupReindex_rows v x
  rw [← heq,← map_sub,F.norm_map]
  exact herr

end BrownianSharp
