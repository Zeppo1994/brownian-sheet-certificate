import BrownianSharp.AlignmentNestedProjectionDecay

/-! Generic finite graded frames and grade-energy bounds for a nested
finite-dimensional Hilbert filtration. This module only packages the existing
orthogonal-increment construction; the analytic input is a uniform projection
residual estimate. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperGenericGradedHilbert

open AlignmentNestedProjectionGrades AlignmentNestedProjectionDecay
open AlignmentNestedProjectionBasis AlignmentNestedProjectionEnergy

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- Convert a geometric bound for the actual Hilbert projection residual into
an energy bound for every orthogonal grade. In particular, the grade estimate
is derived from nested projections and Bessel's inequality; it is not an
assumed coefficient profile. -/
theorem grade_energy_le_of_uniform_projection_residual
    (U : ℕ → Submodule ℝ E)
    (hfinite : ∀ n, FiniteDimensional ℝ (U n))
    {ι : Type*} (K : ι → E) (A C r : ℝ)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hr : 0 < r)
    (hfather : ∀ i, ‖K i‖^2 ≤ A)
    (hres : ∀ i n, ‖K i - (U n).starProjection (K i)‖ ≤ C*r^n) :
    ∀ i g,
      (∑ j : GradeIndex U g,
        ⟪K i, gradeFamily U hfinite g j⟫^2) ≤
        (A + C^2/(r^2)) * (r^2)^g := by
  intro i g
  have hresSq : ∀ n,
      ‖K i - (U n).starProjection (K i)‖^2 ≤ C^2*(r^2)^n := by
    intro n
    have hnonneg : 0 ≤ ‖K i - (U n).starProjection (K i)‖ := norm_nonneg _
    have hbound : 0 ≤ C*r^n := mul_nonneg hC (pow_nonneg hr.le n)
    have hsquare : ‖K i - (U n).starProjection (K i)‖^2 ≤ (C*r^n)^2 :=
      (sq_le_sq₀ hnonneg hbound).mpr (hres i n)
    calc
      _ ≤ (C*r^n)^2 := hsquare
      _ = C^2*(r^2)^n := by
        rw [mul_pow]
        congr 1
        calc
          (r^n)^2 = r^(n*2) := by rw [← pow_mul]
          _ = r^(2*n) := by rw [Nat.mul_comm]
          _ = (r^2)^n := by rw [pow_mul]
  have hq : 0 < r^2 := sq_pos_of_pos hr
  have hC2 : 0 ≤ C^2 := sq_nonneg C
  exact gradeFamily_energy_le_geometric U hfinite (K i)
    A (C^2) (r^2) hA hC2 hq (hfather i) hresSq g

end BrownianSharp.AlignmentPaperGenericGradedHilbert
