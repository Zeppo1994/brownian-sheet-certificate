import BrownianSharp.AlignmentNestedProjectionGrades

/-! Uniform decay envelopes for the actual orthogonal increment coefficients. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentNestedProjectionDecay
open AlignmentNestedProjectionBasis AlignmentNestedProjectionGrades
open AlignmentNestedProjectionEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem gradeFamily_energy_le (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n)) (x : E)
    (A q : ℝ) (hfather : ‖x‖^2 ≤ A)
    (hres : ∀ n, ‖x-(U n).starProjection x‖^2 ≤ A*q^(n+1)) (g : ℕ) :
    (∑ i : GradeIndex U g, ⟪x,gradeFamily U hfinite g i⟫^2) ≤ A*q^g := by
  letI : ∀ n, FiniteDimensional ℝ (U n) := hfinite
  cases g with
  | zero =>
      simpa [GradeIndex,gradeFamily] using
        (father_coefficient_energy_le_norm_sq U x).trans hfather
  | succ n =>
      exact (increment_coefficient_energy_le_projection_residual U n x).trans (hres n)

theorem gradeFamily_energy_le_geometric (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n)) (x : E)
    (C₀ C q : ℝ) (hC₀ : 0 ≤ C₀) (hC : 0 ≤ C) (hq : 0 < q)
    (hfather : ‖x‖^2 ≤ C₀)
    (hres : ∀ n, ‖x-(U n).starProjection x‖^2 ≤ C*q^n) (g : ℕ) :
    (∑ i : GradeIndex U g, ⟪x,gradeFamily U hfinite g i⟫^2) ≤
      (C₀+C/q)*q^g := by
  apply gradeFamily_energy_le U hfinite x (C₀+C/q) q
  · exact hfather.trans (le_add_of_nonneg_right (div_nonneg hC hq.le))
  · intro n
    calc
      _ ≤ C*q^n := hres n
      _ = (C/q)*q^(n+1) := by rw [pow_succ]; field_simp
      _ ≤ (C₀+C/q)*q^(n+1) := by gcongr; linarith

end BrownianSharp.AlignmentNestedProjectionDecay
