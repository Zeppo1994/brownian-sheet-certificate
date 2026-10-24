import BrownianSharp.AlignmentFractionalPolynomialProjectionRate
import BrownianSharp.AlignmentFractionalTranslation
import BrownianSharp.AlignmentNestedProjectionDecayFromOne

/-! Sharp scalar polynomial projection and orthogonal grade envelopes, with
constants uniform in the source level and evaluation point. -/
noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalPolynomialBands
open AlignmentFractionalL2 AlignmentFractionalTranslation
open AlignmentFractionalPolynomialSpaces AlignmentFractionalPolynomialProjectionRate
open AlignmentNestedProjectionGrades AlignmentNestedProjectionDecayFromOne

theorem inverse_dyadic_rpow (β : ℝ) (n : ℕ) :
    (1/(2:ℝ)^n)^β = ((2:ℝ)^(-β))^n := by
  have hbase : 1/(2:ℝ)^n = (2:ℝ)^(-(n:ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]
    simp [one_div]
  rw [hbase,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  rw [show -(n:ℝ)*β=(-β)*(n:ℝ) by ring,
    Real.rpow_mul (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]

theorem kernelVector_norm_sq_le_full (α : ℝ) (hα : 1/2 < α)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖kernelVector α t hα ht0 ht1‖^2 ≤ ‖fullKernelVector α hα‖^2 := by
  have hnorm : ‖kernelVector α t hα ht0 ht1‖ ≤ ‖fullKernelVector α hα‖ := by
    rw [← translatedUnitKernelFamily_eq_kernelVector α t hα ht0 ht1]
    exact translatedUnitKernelFamily_norm_le α hα ⟨t,⟨ht0,ht1⟩⟩
  exact pow_le_pow_left₀ (norm_nonneg _) hnorm 2

theorem polynomialProjection_residual_geometric {α : ℝ} {q : ℕ}
    (hq : 0 < q) (hα : 1/2 < α) (horder : α-1+1/2 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ t : ℝ, (ht0 : 0 ≤ t) →
      (ht1 : t ≤ 1) →
      ‖kernelVector α t hα ht0 ht1 -
        polynomialProjection q n (kernelVector α t hα ht0 ht1)‖^2 ≤
          C * ((2:ℝ)^(-(2*α-1)))^n := by
  obtain ⟨C,hC,hrate⟩ :=
    causalKernel_polynomialProjection_residual_sq_le_dyadic_rate hq hα horder
  let C₀ := ‖fullKernelVector α hα‖^2
  have hC₀ : 0 ≤ C₀ := sq_nonneg _
  let A := C₀+C+1
  refine ⟨A,by dsimp [A]; positivity,?_⟩
  intro n t ht0 ht1
  cases n with
  | zero =>
      simp only [pow_zero,mul_one]
      have hmin : ‖kernelVector α t hα ht0 ht1 -
          polynomialProjection q 0 (kernelVector α t hα ht0 ht1)‖ ≤
          ‖kernelVector α t hα ht0 ht1‖ :=
        projection_residual_norm_le (piecewisePolynomials q 0) _
      have hsq := (pow_le_pow_left₀ (norm_nonneg _) hmin 2).trans
        (kernelVector_norm_sq_le_full α hα t ht0 ht1)
      dsimp [A,C₀] at *
      linarith
  | succ n =>
      have h := hrate (n+1) (by omega) t ht0 ht1
      have h' : ‖kernelVector α t hα ht0 ht1 -
          polynomialProjection q (n+1) (kernelVector α t hα ht0 ht1)‖^2 ≤
          C * ((2:ℝ)^(-(2*α-1)))^(n+1) := by
        simpa only [causalKernelUnitVector,kernelVector,inverse_dyadic_rpow] using h
      exact h'.trans (mul_le_mul_of_nonneg_right
        (by dsimp [A]; linarith) (by positivity))

theorem polynomialGrade_kernel_energy {α : ℝ} {q : ℕ}
    (hq : 0 < q) (hα : 1/2 < α) (horder : α-1+1/2 < q) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, (ht0 : 0 ≤ t) → (ht1 : t ≤ 1) →
      ∀ g : ℕ,
      (∑ i : GradeIndex (piecewisePolynomials q) g,
        ⟪kernelVector α t hα ht0 ht1,
          gradeFamily (piecewisePolynomials q) (fun n => inferInstance) g i⟫^2) ≤
        A * ((2:ℝ)^(-(2*α-1)))^g := by
  obtain ⟨C,hC,hrate⟩ := polynomialProjection_residual_geometric hq hα horder
  let C₀ := ‖fullKernelVector α hα‖^2
  let ρ := (2:ℝ)^(-(2*α-1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  let A := C₀+C/ρ+1
  have hC₀ : 0 ≤ C₀ := sq_nonneg _
  refine ⟨A,by dsimp [A]; positivity,?_⟩
  intro t ht0 ht1 g
  have hbase := AlignmentNestedProjectionDecay.gradeFamily_energy_le_geometric
    (piecewisePolynomials q) (fun n => inferInstance)
    (kernelVector α t hα ht0 ht1) C₀ C ρ hC₀ hC.le hρ
    (kernelVector_norm_sq_le_full α hα t ht0 ht1)
    (fun n => hrate n t ht0 ht1) g
  exact hbase.trans (mul_le_mul_of_nonneg_right
    (by dsimp [A]; linarith) (pow_nonneg hρ.le _))

end BrownianSharp.AlignmentFractionalPolynomialBands
