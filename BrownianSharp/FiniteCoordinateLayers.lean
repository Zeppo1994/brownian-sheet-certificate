import BrownianSharp.FiniteLayerAssembly
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Orthogonal finite coordinate layers, including the exact energy identity.
This is the deterministic source splitting used by the multilevel width proof. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp
variable {I J G : Type} [Fintype I] [Fintype J] [Fintype G] [DecidableEq J]

def coordinateLayerMask (σ : I → J) (j : J) :
    EuclideanSpace ℝ I →ₗ[ℝ] EuclideanSpace ℝ I where
  toFun x := WithLp.toLp 2 (fun i => if σ i=j then x i else 0)
  map_add' x y := by
    ext i
    simp only [PiLp.toLp_apply,PiLp.add_apply]
    split_ifs <;> simp_all
  map_smul' a x := by
    ext i
    simp only [PiLp.toLp_apply,PiLp.smul_apply,smul_eq_mul]
    split_ifs <;> simp_all

@[simp] theorem coordinateLayerMask_apply (σ : I → J) (j : J)
    (x : EuclideanSpace ℝ I) (i : I) :
    coordinateLayerMask σ j x i = if σ i=j then x i else 0 := rfl

@[simp] theorem coordinateLayerMask_idempotent (σ : I → J) (j : J)
    (x : EuclideanSpace ℝ I) :
    coordinateLayerMask σ j (coordinateLayerMask σ j x)=coordinateLayerMask σ j x := by
  classical
  ext i
  simp only [coordinateLayerMask_apply]
  split_ifs <;> rfl

theorem coordinateLayerMask_sum (σ : I → J) (x : EuclideanSpace ℝ I) :
    ∑ j,coordinateLayerMask σ j x=x := by
  classical
  ext i
  simp [coordinateLayerMask,eq_comm]

theorem coordinateLayerMask_energy (σ : I → J) (x : EuclideanSpace ℝ I) :
    ∑ j,‖coordinateLayerMask σ j x‖^2=‖x‖^2 := by
  classical
  simp only [EuclideanSpace.norm_sq_eq,coordinateLayerMask_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [eq_comm]

/-- Row representation of a finite-grid integration map, with the ordinary
sup norm on its target. -/
def finiteRowLinear (v : G → EuclideanSpace ℝ I) :
    EuclideanSpace ℝ I →ₗ[ℝ] (G → ℝ) where
  toFun x j := ⟪x,v j⟫
  map_add' x y := by ext j; simp [inner_add_left]
  map_smul' a x := by ext j; simp [real_inner_smul_left]

theorem inner_coordinateLayerMask (σ : I → J) (j : J)
    (x y : EuclideanSpace ℝ I) :
    ⟪x,coordinateLayerMask σ j y⟫=⟪coordinateLayerMask σ j x,y⟫ := by
  classical
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct,star_trivial,
    coordinateLayerMask_apply]
  apply Finset.sum_congr rfl
  intro i hi
  split_ifs <;> simp

def finiteRowLayerLinear (σ : I → J) (v : G → EuclideanSpace ℝ I) (j : J) :
    EuclideanSpace ℝ I →ₗ[ℝ] (G → ℝ) :=
  finiteRowLinear (fun g => coordinateLayerMask σ j (v g))

theorem finiteRowLayerLinear_eq_comp (σ : I → J) (v : G → EuclideanSpace ℝ I) (j : J) :
    finiteRowLayerLinear σ v j=(finiteRowLinear v).comp (coordinateLayerMask σ j) := by
  ext x g
  exact inner_coordinateLayerMask σ j x (v g)

theorem finiteRowLayerLinear_sum (σ : I → J) (v : G → EuclideanSpace ℝ I)
    (x : EuclideanSpace ℝ I) :
    ∑ j,finiteRowLayerLinear σ v j (coordinateLayerMask σ j x)=finiteRowLinear v x := by
  simp_rw [finiteRowLayerLinear_eq_comp,LinearMap.comp_apply,coordinateLayerMask_idempotent]
  rw [← map_sum,coordinateLayerMask_sum]

/-- Local approximating subspaces for the rows restricted to each coordinate
layer assemble into a single finite-grid approximating subspace. -/
theorem finiteRow_unitBall_approximation
    (σ : I → J) (v : G → EuclideanSpace ℝ I)
    (V : J → Submodule ℝ (G → ℝ)) [∀ j,FiniteDimensional ℝ (V j)]
    (m : J → ℕ) (hm : ∀ j,Module.finrank ℝ (V j)≤m j)
    (ε : J → ℝ) (hε : ∀ j,0≤ε j)
    (happrox : ∀ j x,‖x‖≤1 → ∃ y ∈ V j,‖finiteRowLayerLinear σ v j x-y‖≤ε j) :
    ∃ W : Submodule ℝ (G → ℝ), Module.rank ℝ W≤((∑ j,m j : ℕ):Cardinal) ∧
      ∀ x : EuclideanSpace ℝ I, ‖x‖≤1 → ∃ y ∈ W,
        ‖finiteRowLinear v x-y‖≤Real.sqrt (∑ j,(ε j)^2) := by
  refine ⟨LinearMap.range (finiteLayerSumMap V),finiteLayerSumMap_rank V m hm,?_⟩
  intro x hx
  have henergy : ∑ j,‖coordinateLayerMask σ j x‖^2≤1 := by
    rw [coordinateLayerMask_energy]
    nlinarith [norm_nonneg x]
  obtain ⟨y,hy,herr⟩ := exists_finite_layer_approximation
    (finiteRowLayerLinear σ v) V ε hε happrox (fun j => coordinateLayerMask σ j x) henergy
  exact ⟨y,hy,by simpa only [finiteRowLayerLinear_sum] using herr⟩

end BrownianSharp
