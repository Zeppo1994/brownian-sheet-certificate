import BrownianSharp.AlignmentFractionalPolynomialWitness
import BrownianSharp.AlignmentFractionalHaarBand

/-! Uniform convergence of polynomial source projections follows already
from their inclusion of the dyadic piecewise constants. -/
noncomputable section
open MeasureTheory
namespace BrownianSharp.AlignmentFractionalPolynomialConvergence
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalPolynomialWitness
open BrownianSharp.AlignmentFractionalDyadicProjection
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalHaarBand
abbrev SourceL2 := BrownianSharp.AlignmentFractionalL2.UnitL2

theorem cellMonomial_zero_eq_indicator (n : ℕ) (j : Fin (2^n)) :
    cellMonomial n j 0 = sourceDyadicCellIndicator n j := by
  apply Lp.ext
  filter_upwards [cellMonomial_coeFn n j 0, sourceDyadicCellIndicator_coeFn n j]
    with x hx hy
  rw [hx,hy]
  simp [cellMonomialFunction]

theorem piecewiseConstants_le_polynomials {q : ℕ} (hq : 0 < q) (n : ℕ) :
    sourceDyadicPiecewiseConstants n ≤ piecewisePolynomials q n := by
  apply Submodule.span_le.2
  rintro x ⟨j,rfl⟩
  rw [← cellMonomial_zero_eq_indicator]
  exact Submodule.subset_span ⟨(j,⟨0,hq⟩),rfl⟩

theorem polynomialProjection_residual_le_dyadic {q : ℕ} (hq : 0 < q)
    (n : ℕ) (x : SourceL2) :
    ‖x-polynomialProjection q n x‖ ≤ ‖x-sourceDyadicOrthogonalProjection n x‖ := by
  apply polynomialProjection_residual_le
  apply piecewiseConstants_le_polynomials hq n
  exact Submodule.starProjection_apply_mem _ _

theorem polynomialProjection_error_norm_sq_le_coarse
    {q : ℕ} (hq : 0 < q) {α t : ℝ}
    (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖kernelVector α t hα ht0 ht1 -
      polynomialProjection q n (kernelVector α t hα ht0 ht1)‖^2 ≤
      ((Real.Gamma α)⁻¹)^2 * (2 + 2^(2*α-1)/(2*α-1)) *
        (1/(2:ℝ)^n)^(min (2*α-1) 1) := by
  exact (pow_le_pow_left₀ (norm_nonneg _)
    (polynomialProjection_residual_le_dyadic hq n _) 2).trans
    (causalKernelVector_starProjection_error_norm_sq_le_rate hα ht0 ht1 hn)

end BrownianSharp.AlignmentFractionalPolynomialConvergence
