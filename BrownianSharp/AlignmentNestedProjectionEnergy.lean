import BrownianSharp.AlignmentNestedProjectionFrame
import BrownianSharp.FiniteOrthogonalCoordinates

/-! Gradewise Bessel and rank bounds for nested finite-dimensional projections. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentNestedProjectionEnergy

open BrownianSharp.AlignmentNestedProjectionBasis
open BrownianSharp.AlignmentNestedProjectionFrame

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- The father-space coefficients obey Bessel's inequality. -/
theorem father_coefficient_energy_le_norm_sq
    (U : ℕ → Submodule ℝ E) [FiniteDimensional ℝ ↥(U 0)] (x : E) :
    (∑ i : Fin (Module.finrank ℝ ↥(U 0)),
      ⟪x, (stdOrthonormalBasis ℝ (U 0) i : E)⟫ ^ 2) ≤ ‖x‖ ^ 2 := by
  classical
  let v : Fin (Module.finrank ℝ ↥(U 0)) → E :=
    fun i => (stdOrthonormalBasis ℝ (U 0) i : E)
  have hv : Orthonormal ℝ v := by
    change Orthonormal ℝ
      (fun i : Fin (Module.finrank ℝ ↥(U 0)) =>
        (stdOrthonormalBasis ℝ (U 0) i : E))
    exact (stdOrthonormalBasis ℝ (U 0)).orthonormal
  have hb := hv.sum_inner_products_le (s := Finset.univ) x
  have hsum : (∑ i : Fin (Module.finrank ℝ ↥(U 0)), ⟪x,v i⟫ ^ 2) =
      ∑ i : Fin (Module.finrank ℝ ↥(U 0)), ⟪v i,x⟫ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
  calc
    (∑ i : Fin (Module.finrank ℝ ↥(U 0)), ⟪x,v i⟫ ^ 2) =
        ∑ i : Fin (Module.finrank ℝ ↥(U 0)), ⟪v i,x⟫ ^ 2 := hsum
    _ ≤ ‖x‖ ^ 2 := by simpa [Real.norm_eq_abs, sq_abs] using hb

/-- The coefficient energy in the new orthogonal directions at level `n` is
bounded by the squared error left after projection onto the preceding space. -/
theorem increment_coefficient_energy_le_projection_residual
    (U : ℕ → Submodule ℝ E)
    [∀ n, FiniteDimensional ℝ ↥(U n)] (n : ℕ) (x : E) :
    (∑ i : Fin (Module.finrank ℝ ↥(increment U n)),
      ⟪x, (incrementBasis U n i : E)⟫ ^ 2) ≤
      ‖x - (U n).starProjection x‖ ^ 2 := by
  classical
  let v : Fin (Module.finrank ℝ ↥(increment U n)) → E :=
    fun i => (incrementBasis U n i : E)
  have hv : Orthonormal ℝ v := by
    change Orthonormal ℝ (fun i => (stdOrthonormalBasis ℝ (increment U n) i : E))
    exact (incrementBasis U n).orthonormal
  have hres : x - (U n).starProjection x ∈ (U n)ᗮ :=
    (U n).sub_starProjection_mem_orthogonal x
  have hzero (i : Fin (Module.finrank ℝ ↥(increment U n))) :
      ⟪(U n).starProjection x, v i⟫ = 0 := by
    have hp : (U n).starProjection x ∈ U n := (U n).starProjection_apply_mem x
    have hi : v i ∈ (U n)ᗮ := by
      simpa [v] using (incrementBasis U n i).property.2
    rw [real_inner_comm]
    exact (Submodule.mem_orthogonal' (U n) (v i)).mp hi
      ((U n).starProjection x) hp
  have hcoeff (i : Fin (Module.finrank ℝ ↥(increment U n))) :
      ⟪x, v i⟫ = ⟪x - (U n).starProjection x, v i⟫ := by
    rw [inner_sub_left, hzero i]
    simp
  have hb := hv.sum_inner_products_le (s := Finset.univ)
    (x - (U n).starProjection x)
  have hsum :
      (∑ i : Fin (Module.finrank ℝ ↥(increment U n)), ⟪x, v i⟫ ^ 2) =
      ∑ i : Fin (Module.finrank ℝ ↥(increment U n)),
        ⟪v i, x - (U n).starProjection x⟫ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoeff i, real_inner_comm]
  calc
    (∑ i : Fin (Module.finrank ℝ ↥(increment U n)), ⟪x, v i⟫ ^ 2) =
        ∑ i : Fin (Module.finrank ℝ ↥(increment U n)),
          ⟪v i, x - (U n).starProjection x⟫ ^ 2 := hsum
    _ ≤ ‖x - (U n).starProjection x‖ ^ 2 := by
      simpa [Real.norm_eq_abs, sq_abs] using hb

/-- Each increment's dimension is at most the dimension of the next space. -/
theorem increment_finrank_le_succ (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ ↥(U n))
    (hnested : ∀ n, U n ≤ U (n+1)) (n : ℕ) :
    Module.finrank ℝ ↥(increment U n) ≤ Module.finrank ℝ ↥(U (n+1)) := by
  have hrec := increment_finrank_recurrence U hfinite hnested n
  omega

/-- A dimension growth estimate for the filtration immediately bounds every
grade's number of new orthogonal coordinates. -/
theorem increment_finrank_le_of_growth (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ ↥(U n))
    (hnested : ∀ n, U n ≤ U (n+1)) {A : ℕ}
    (hgrowth : ∀ n, Module.finrank ℝ ↥(U n) ≤ A * 2 ^ n)
    (n : ℕ) :
    Module.finrank ℝ ↥(increment U n) ≤ A * 2 ^ (n+1) := by
  exact (increment_finrank_le_succ U hfinite hnested n).trans (hgrowth (n+1))

end BrownianSharp.AlignmentNestedProjectionEnergy
