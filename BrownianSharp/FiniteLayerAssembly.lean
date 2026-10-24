import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-! Finite orthogonal-layer approximation: the component errors combine in
quadrature when their source energies have sum at most one. The range of the
sum of approximating subspaces has dimension at most the sum of dimensions. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp

variable {ι H Y : Type} [Fintype ι]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A homogeneous map inherits a relative approximation estimate from its
unit-ball estimate. The witness remains in the same linear subspace. -/
theorem linear_approximation_of_unit_ball (T : H →ₗ[ℝ] Y)
    (V : Submodule ℝ Y) {ε : ℝ} (hε : 0 ≤ ε)
    (happrox : ∀ x : H, ‖x‖ ≤ 1 → ∃ v ∈ V, ‖T x-v‖ ≤ ε) (x : H) :
    ∃ v ∈ V, ‖T x-v‖ ≤ ε*‖x‖ := by
  by_cases hx : x = 0
  · subst x
    exact ⟨0,V.zero_mem,by simp⟩
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨v,hv,herr⟩ := happrox (‖x‖⁻¹ • x) (by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hn)]
    exact le_of_eq (inv_mul_cancel₀ (ne_of_gt hn)))
  refine ⟨‖x‖ • v,V.smul_mem _ hv,?_⟩
  have hsplit : T x-‖x‖ • v = ‖x‖ • (T (‖x‖⁻¹ • x)-v) := by
    rw [smul_sub,map_smul,smul_smul,mul_inv_cancel₀ (ne_of_gt hn),one_smul]
  rw [hsplit,norm_smul,Real.norm_eq_abs,abs_of_pos hn]
  nlinarith

/-- The finite sum map explicitly supplies the approximating subspace. -/
def finiteLayerSumMap (V : ι → Submodule ℝ Y) : (∀ i,V i) →ₗ[ℝ] Y where
  toFun v := ∑ i,(v i : Y)
  map_add' v w := by simp [Finset.sum_add_distrib]
  map_smul' a v := by simp [Finset.smul_sum]

theorem finiteLayerSumMap_rank (V : ι → Submodule ℝ Y)
    [∀ i,FiniteDimensional ℝ (V i)] (m : ι → ℕ)
    (hm : ∀ i,Module.finrank ℝ (V i) ≤ m i) :
    Module.rank ℝ (LinearMap.range (finiteLayerSumMap V)) ≤
      ((∑ i,m i : ℕ) : Cardinal) := by
  apply (rank_range_le (finiteLayerSumMap V)).trans
  rw [← Module.finrank_eq_rank,Module.finrank_pi_fintype]
  exact_mod_cast Finset.sum_le_sum (fun i _ => hm i)

/-- Cauchy--Schwarz is applied across the source layers, retaining the sharp
square-summed error rather than losing a factor from the number of layers. -/
theorem exists_finite_layer_approximation
    (T : ι → H →ₗ[ℝ] Y) (V : ι → Submodule ℝ Y)
    (ε : ι → ℝ) (hε : ∀ i,0 ≤ ε i)
    (happrox : ∀ i x, ‖x‖ ≤ 1 → ∃ v ∈ V i, ‖T i x-v‖ ≤ ε i)
    (x : ι → H) (henergy : ∑ i,‖x i‖^2 ≤ 1) :
    ∃ v ∈ LinearMap.range (finiteLayerSumMap V),
      ‖(∑ i,T i (x i))-v‖ ≤ Real.sqrt (∑ i,(ε i)^2) := by
  classical
  have hh : ∀ i,∃ v ∈ V i,‖T i (x i)-v‖ ≤ ε i*‖x i‖ :=
    fun i => linear_approximation_of_unit_ball (T i) (V i) (hε i) (happrox i) (x i)
  choose v hv herr using hh
  refine ⟨∑ i,v i,⟨fun i => ⟨v i,hv i⟩,rfl⟩,?_⟩
  calc
    ‖(∑ i,T i (x i))-∑ i,v i‖ = ‖∑ i,(T i (x i)-v i)‖ := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i,‖T i (x i)-v i‖ := norm_sum_le _ _
    _ ≤ ∑ i,ε i*‖x i‖ := Finset.sum_le_sum (fun i _ => herr i)
    _ ≤ Real.sqrt (∑ i,(ε i)^2)*Real.sqrt (∑ i,‖x i‖^2) := by
      simpa using Real.sum_mul_le_sqrt_mul_sqrt Finset.univ ε (fun i => ‖x i‖)
    _ ≤ Real.sqrt (∑ i,(ε i)^2)*1 := by
      exact mul_le_mul_of_nonneg_left (by simpa using Real.sqrt_le_sqrt henergy)
        (Real.sqrt_nonneg _)
    _ = _ := mul_one _

end BrownianSharp
