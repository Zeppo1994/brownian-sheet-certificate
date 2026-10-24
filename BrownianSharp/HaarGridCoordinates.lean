import BrownianSharp.FiniteHaarGridSpan
import BrownianSharp.FiniteHaarLayerEnergy
import BrownianSharp.FiniteCoordinateLayers

/-! Actual endpoint-grid integration in finite, orthonormal Haar coordinates. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp
open HaarQuarter CameronMartin

abbrev HaarGridCoordinateSpace (d N : ℕ) := EuclideanSpace ℝ (FiniteHaarIndex d N)

theorem finiteHaarIndex_card_grid (d N : ℕ) :
    Fintype.card (FiniteHaarIndex d N)=(2^N)^d := by
  simpa [pow_mul] using finiteHaarIndex_card d N

def haarGridRows (d N : ℕ) (j : CubeDyadicGrid d N) : HaarGridCoordinateSpace d N :=
  WithLp.toLp 2 (fun a => ⟪finiteHaarVector a,featureVector (cubeDyadicAnchor j)⟫)

def haarGridCoordinates (d N : ℕ) : AmbientL2 d →ₗ[ℝ] HaarGridCoordinateSpace d N :=
  finiteOrthonormalCoordinates (fun a => (finiteHaarVector a : AmbientL2 d))

theorem haarGridCoordinates_norm_le (d N : ℕ) (g : AmbientL2 d) :
    ‖haarGridCoordinates d N g‖≤‖g‖ := by
  apply finiteOrthonormalCoordinates_norm_le
  apply orthonormal_iff_ite.mpr
  intro a b
  exact finiteHaarVector_orthonormal a b

/-- The full original integration path agrees exactly with its finite
coordinate row map at every grid point. -/
theorem haarGridCoordinates_evaluation (d N : ℕ) (g : AmbientL2 d) :
    finiteRowLinear (haarGridRows d N) (haarGridCoordinates d N g)=
      fun j => anchoredIntegrationPath g (cubeDyadicAnchor j) := by
  funext j
  rw [anchoredIntegrationPath_grid_eq_haar_sum (finiteHaarIndex_card_grid d N)]
  change ⟪haarGridCoordinates d N g,haarGridRows d N j⟫= _
  simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,
    haarGridCoordinates,finiteOrthonormalCoordinates,haarGridRows,PiLp.toLp_apply]
  apply Finset.sum_congr rfl
  intro a ha
  change ⟪finiteHaarVector a,featureVector (cubeDyadicAnchor j)⟫ *
    ⟪g,(finiteHaarVector a : AmbientL2 d)⟫ =
    ⟪g,(finiteHaarVector a : AmbientL2 d)⟫ *
    ⟪finiteHaarVector a,featureVector (cubeDyadicAnchor j)⟫
  ring

/-- Any finite-coordinate row approximation applies to the original ambient
L² unit ball with the same error. -/
theorem haarGrid_unitBall_approximation_transfer (d N : ℕ)
    (V : Submodule ℝ (CubeDyadicGrid d N → ℝ)) {ε : ℝ}
    (happrox : ∀ x : HaarGridCoordinateSpace d N, ‖x‖≤1 →
      ∃ v ∈ V, ‖finiteRowLinear (haarGridRows d N) x-v‖≤ε) :
    ∀ g : AmbientL2 d, ‖g‖≤1 → ∃ v ∈ V,
      ‖(fun j => anchoredIntegrationPath g (cubeDyadicAnchor j))-v‖≤ε := by
  intro g hg
  obtain ⟨v,hv,herr⟩ := happrox (haarGridCoordinates d N g)
    ((haarGridCoordinates_norm_le d N g).trans hg)
  rw [haarGridCoordinates_evaluation] at herr
  exact ⟨v,hv,herr⟩

end BrownianSharp
