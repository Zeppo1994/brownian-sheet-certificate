import BrownianSharp.AlignmentNestedProjectionDecay

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentNestedProjectionDecayFromOne
open AlignmentNestedProjectionBasis AlignmentNestedProjectionGrades
open AlignmentNestedProjectionDecay
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem projection_residual_norm_le (U : Submodule ℝ E)
    [U.HasOrthogonalProjection] (x : E) : ‖x-U.starProjection x‖ ≤ ‖x‖ := by
  have h := Uᗮ.norm_starProjection_apply_le x
  simpa only [Submodule.starProjection_orthogonal, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply] using h

theorem gradeFamily_energy_le_geometric_from_one (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n)) (x : E)
    (C₀ C q : ℝ) (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C) (hq : 0 < q)
    (hfather : ‖x‖^2 ≤ C₀)
    (hres : ∀ n, 1 ≤ n → ‖x-(U n).starProjection x‖^2 ≤ C*q^n) (g : ℕ) :
    (∑ i : GradeIndex U g, ⟪x,gradeFamily U hfinite g i⟫^2) ≤
      (C₀+(C₀+C)/q)*q^g := by
  letI : ∀ n, FiniteDimensional ℝ (U n) := hfinite
  apply gradeFamily_energy_le_geometric U hfinite x C₀ (C₀+C) q
    hC₀ (add_nonneg hC₀ hC) hq hfather
  intro n
  cases n with
  | zero =>
      simp only [pow_zero,mul_one]
      exact (pow_le_pow_left₀ (norm_nonneg _) (projection_residual_norm_le (U 0) x) 2).trans
        (hfather.trans (le_add_of_nonneg_right hC))
  | succ n =>
      exact (hres (n+1) (by omega)).trans
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₀) (pow_nonneg hq.le _))

end BrownianSharp.AlignmentNestedProjectionDecayFromOne
