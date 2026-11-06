import BrownianSharp.AlignmentGaussianFractionalHaar

noncomputable section

namespace BrownianSharp.AlignmentFractionalHaarBand

open BrownianSharp.AlignmentFractionalDyadicProjection
open BrownianSharp.AlignmentGaussianFractionalHaar
open BrownianSharp.AlignmentFractionalL2

/-- The actual RL feature's literal cell-average projection error is uniformly
bounded with squared rate `h ^ min (2α-1) 1`. This estimate saturates at the
first-order cell scale when `α ≥ 1`; it is a projection-approximation bound,
not the manuscript's sharp entropy asymptotic. -/
theorem causalKernelVector_cellAverage_error_norm_sq_le_rate
    {α t : ℝ} (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖kernelVector α t hα ht0 ht1 -
      sourceDyadicCellAverageApproximation n
        (fun x => (kernelVector α t hα ht0 ht1) x)‖^2 ≤
      ((Real.Gamma α)⁻¹)^2 *
        (2 + 2^(2*α-1)/(2*α-1)) *
        (1/(2:ℝ)^n)^(min (2*α-1) 1) := by
  rw [causalKernelVector_cellAverage_error_norm_sq]
  have hsum := Fin.sum_univ_eq_sum_range
    (fun j => causalKernelCellError α t (1/(2:ℝ)^n) j) (2^n)
  calc
    _ = ∑ j ∈ Finset.range (2^n),
        causalKernelCellError α t (1/(2:ℝ)^n) j := hsum
    _ ≤ _ := causalKernel_dyadic_unit_cell_error_sum_le_rate
      (α := α) (t := t) (h := 1/(2:ℝ)^n) (M := 2^n) hα ht0 ht1
      (by positivity) (by
        simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn)
      (by
        have hcast : ((2^n:ℕ):ℝ) = (2:ℝ)^n := by norm_cast
        rw [hcast]
        field_simp)

/-- The orthogonal projection onto dyadic source piecewise constants has no
larger L² residual than the literal cell-average candidate, hence inherits
the same actual-kernel rate. -/
theorem causalKernelVector_starProjection_error_norm_sq_le_rate
    {α t : ℝ} (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖kernelVector α t hα ht0 ht1 -
      sourceDyadicOrthogonalProjection n (kernelVector α t hα ht0 ht1)‖^2 ≤
      ((Real.Gamma α)⁻¹)^2 *
        (2 + 2^(2*α-1)/(2*α-1)) *
        (1/(2:ℝ)^n)^(min (2*α-1) 1) := by
  have hmin := sourceDyadicOrthogonalProjection_le_cellAverageApproximation n
    (kernelVector α t hα ht0 ht1)
  have hrate := causalKernelVector_cellAverage_error_norm_sq_le_rate
    hα ht0 ht1 hn
  have hsq :
      ‖kernelVector α t hα ht0 ht1 -
          sourceDyadicOrthogonalProjection n (kernelVector α t hα ht0 ht1)‖^2 ≤
        ‖kernelVector α t hα ht0 ht1 -
          sourceDyadicCellAverageApproximation n
            (fun x => (kernelVector α t hα ht0 ht1) x)‖^2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hmin)
      (add_nonneg
        (norm_nonneg (kernelVector α t hα ht0 ht1 -
          sourceDyadicOrthogonalProjection n (kernelVector α t hα ht0 ht1)))
        (norm_nonneg (kernelVector α t hα ht0 ht1 -
          sourceDyadicCellAverageApproximation n
            (fun x => (kernelVector α t hα ht0 ht1) x))))
    nlinarith [hprod]
  exact le_trans hsq hrate

end BrownianSharp.AlignmentFractionalHaarBand
