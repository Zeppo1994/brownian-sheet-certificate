import BrownianSharp.CubeSamplingExtension
import BrownianSharp.CameronMartinDKLLApprox
import Mathlib.LinearAlgebra.Dimension.Basic

/-! Finite-grid approximating subspaces lift to the actual continuous-path
Cameron–Martin ball without increasing dimension or finite-grid error. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp
open HaarQuarter CameronMartin

def cubeGridEvaluationLinear (d N : ℕ) : AmbientL2 d →ₗ[ℝ] (CubeDyadicGrid d N → ℝ) where
  toFun g j := anchoredIntegrationPath g (cubeDyadicAnchor j)
  map_add' g h := by
    funext j
    change ⟪g+h,(featureVector (cubeDyadicAnchor j) : AmbientL2 d)⟫ = _
    simp [anchoredIntegrationPath,inner_add_left]
  map_smul' a g := by
    funext j
    simp [anchoredIntegrationPath,real_inner_smul_left]

/-- This reduction concerns the actual restricted-cube integration unit ball. -/
theorem KdUnitCube_width_le_of_grid_approximation
    (d N m : ℕ) (W : Submodule ℝ (CubeDyadicGrid d N → ℝ))
    (hW : Module.rank ℝ W ≤ (m:Cardinal)) {η : ℝ}
    (happrox : ∀ g : AmbientL2 d, ‖g‖ ≤ 1 →
      ∃ w ∈ W, ‖cubeGridEvaluationLinear d N g-w‖ ≤ η) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth (KdUnitCube d) m ≤
      ENNReal.ofReal (Real.sqrt ((d:ℝ)*(2*((2:ℝ)^N)⁻¹))+η) := by
  obtain ⟨E,hE,hres⟩ := exists_cube_sampling_extension d N
  let V : Submodule ℝ C(BrownianCubeAnchor d,ℝ) := W.map E
  have hV : Module.rank ℝ V ≤ (m:Cardinal) := (rank_map_le E W).trans hW
  apply kolmogorovWidth_KdUnitCube_le_of_uniform_approximation d m V hV
  intro g hg
  obtain ⟨w,hw,herr⟩ := happrox g hg
  refine ⟨⟨E w,Submodule.mem_map.mpr ⟨w,hw,rfl⟩⟩,?_⟩
  have hsplit : anchoredIntegrationPath g-E w =
      (anchoredIntegrationPath g-E (cubeGridEvaluationLinear d N g))+
        E (cubeGridEvaluationLinear d N g-w) := by
    rw [map_sub]
    abel
  rw [hsplit]
  exact (norm_add_le _ _).trans (add_le_add (hres g hg) ((hE _).trans herr))

end BrownianSharp
