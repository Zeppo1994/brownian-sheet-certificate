import BrownianSharp.Projection
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Exact finite orthonormal coordinates and their unit-ball contraction.
These statements require no completeness or infinite-basis expansion. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp
variable {ι H : Type} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def finiteProjectionLinear (e : ι → H) : H →ₗ[ℝ] H where
  toFun x := finiteOrthonormalProjection e x
  map_add' x y := by simp [finiteOrthonormalProjection,inner_add_left,add_smul,Finset.sum_add_distrib]
  map_smul' a x := by simp [finiteOrthonormalProjection,real_inner_smul_left,mul_smul,Finset.smul_sum]

theorem finiteProjectionLinear_eq_of_mem_span (e : ι → H) (he : Orthonormal ℝ e)
    {x : H} (hx : x ∈ Submodule.span ℝ (Set.range e)) :
    finiteOrthonormalProjection e x=x := by
  classical
  have hb : Set.EqOn (finiteProjectionLinear e) (LinearMap.id : H →ₗ[ℝ] H) (Set.range e) := by
    rintro _ ⟨i,rfl⟩
    simp [finiteProjectionLinear,finiteOrthonormalProjection,orthonormal_iff_ite.mp he]
  exact LinearMap.eqOn_span hb hx

def finiteOrthonormalCoordinates (e : ι → H) : H →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (fun i => ⟪x,e i⟫)
  map_add' x y := by ext i; simp [inner_add_left]
  map_smul' a x := by ext i; simp [real_inner_smul_left]

theorem finiteOrthonormalCoordinates_norm_sq (e : ι → H) (x : H) :
    ‖finiteOrthonormalCoordinates e x‖^2=∑ i,⟪x,e i⟫^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [finiteOrthonormalCoordinates,Real.norm_eq_abs,sq_abs]

theorem finiteOrthonormalCoordinates_norm_le (e : ι → H) (he : Orthonormal ℝ e) (x : H) :
    ‖finiteOrthonormalCoordinates e x‖≤‖x‖ := by
  have h := he.sum_inner_products_le (s:=Finset.univ) x
  simp only [Finset.mem_univ,Finset.sum_const_zero,Finset.sum_const_zero,Finset.sum_ite_irrel,
    ↓reduceIte,Real.norm_eq_abs,sq_abs] at h
  have heq : (∑ i,⟪x,e i⟫^2)=(∑ i,⟪e i,x⟫^2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
  rw [← heq,← finiteOrthonormalCoordinates_norm_sq] at h
  nlinarith [norm_nonneg (finiteOrthonormalCoordinates e x),norm_nonneg x]

end BrownianSharp
