import BrownianSharp.AlignmentGaussianFractionalHaar

noncomputable section

namespace BrownianSharp.AlignmentFractionalHaarBand

open BrownianSharp.AlignmentFractionalDyadicProjection
open BrownianSharp.AlignmentGaussianFractionalHaar
open BrownianSharp.AlignmentFractionalL2

/-- The actual RL kernel has a uniformly bounded dyadic Haar energy band.
This packages the scalar moving-boundary estimate with the genuine L² Haar
vectors; no coefficient regularity or abstract rate premise is assumed. -/
theorem causalKernelVector_haar_level_energy_le_rate
    {α t : ℝ} (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    (∑ j : Fin (2^n),
      (inner ℝ (sourceDyadicHaarMother n j)
        (kernelVector α t hα ht0 ht1))^2) ≤
      ((Real.Gamma α)⁻¹)^2 *
        (2 + 2^(2*α-1)/(2*α-1)) *
        (1/(2:ℝ)^n)^(min (2*α-1) 1) := by
  have hMnat : 2 ≤ 2^n := by
    simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
  have hh : 0 < (1/(2:ℝ)^n) := by positivity
  have hgrid : ((2^n:ℕ):ℝ) * (1/(2:ℝ)^n) = 1 := by
    have hcast : ((2^n:ℕ):ℝ) = (2:ℝ)^n := by norm_cast
    rw [hcast]
    field_simp
  have hsum := Fin.sum_univ_eq_sum_range
    (fun j => causalKernelCellError α t (1/(2:ℝ)^n) j) (2^n)
  calc
    (∑ j : Fin (2^n),
      (inner ℝ (sourceDyadicHaarMother n j)
        (kernelVector α t hα ht0 ht1))^2) ≤
      ∑ j : Fin (2^n),
        causalKernelCellError α t (1/(2:ℝ)^n) j :=
          causalKernelVector_haar_level_energy_le_cell_errors hα ht0 ht1 n
    _ = ∑ j ∈ Finset.range (2^n),
        causalKernelCellError α t (1/(2:ℝ)^n) j := by
      exact hsum
    _ ≤ ((Real.Gamma α)⁻¹)^2 *
        (2 + 2^(2*α-1)/(2*α-1)) *
          (1/(2:ℝ)^n)^(min (2*α-1) 1) := by
      exact causalKernel_dyadic_unit_cell_error_sum_le_rate
        (α := α) (t := t) (h := 1/(2:ℝ)^n) (M := 2^n)
        hα ht0 ht1 hh hMnat hgrid

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

/-- Every finite Haar coefficient tail of the actual RL kernel has the
geometric decay dictated by its proved one-level projection estimate. -/
theorem causalKernelVector_haar_tail_energy_le_rate
    {α t : ℝ} (hα : 1/2 < α) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (n M : ℕ) (hn : 1 ≤ n) :
    (∑ r ∈ Finset.Ico n M,
      ∑ j : Fin (2^r),
        (inner ℝ (sourceDyadicHaarMother r j)
          (kernelVector α t hα ht0 ht1))^2) ≤
      (((Real.Gamma α)⁻¹)^2 *
        (2 + 2^(2*α-1)/(2*α-1))) *
          ((2:ℝ)^(-(min (2*α-1) 1)))^n /
            (1-(2:ℝ)^(-(min (2*α-1) 1))) := by
  let β : ℝ := min (2*α-1) 1
  let C : ℝ := ((Real.Gamma α)⁻¹)^2 *
        (2 + 2^(2*α-1)/(2*α-1))
  let q : ℝ := (2:ℝ)^(-β)
  have hβ0 : 0 < β := by
    dsimp [β]
    exact lt_min (by linarith) (by norm_num)
  have hβ1 : β ≤ 1 := by dsimp [β]; exact min_le_right _ _
  have hC : 0 ≤ C := by
    have hp : 0 < 2*α-1 := by linarith
    have hden : 0 ≤ 2^(2*α-1)/(2*α-1) :=
      div_nonneg (Real.rpow_nonneg (by norm_num) _) hp.le
    dsimp [C]
    exact mul_nonneg (sq_nonneg _) (by linarith)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hpow (r : ℕ) : (1/(2:ℝ)^r)^β = q^r := by
    dsimp [q]
    have hbase : 1/(2:ℝ)^r = (2:ℝ)^(-(r:ℝ)) := by
      calc
        1/(2:ℝ)^r = ((2:ℝ)^(r:ℝ))⁻¹ := by
          rw [Real.rpow_natCast]
          simp [one_div]
        _ = (2:ℝ)^(-(r:ℝ)) := by
          rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    rw [hbase]
    calc
      ((2:ℝ)^(-(r:ℝ)))^β = (2:ℝ)^((-(r:ℝ))*β) :=
        (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
      _ = (2:ℝ)^((-β)*(r:ℝ)) := by congr 1 <;> ring
      _ = ((2:ℝ)^(-β))^(r:ℝ) :=
        Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _
      _ = ((2:ℝ)^(-β))^r := Real.rpow_natCast _ _
  calc
    (∑ r ∈ Finset.Ico n M,
      ∑ j : Fin (2^r),
        (inner ℝ (sourceDyadicHaarMother r j)
          (kernelVector α t hα ht0 ht1))^2) ≤
      ∑ r ∈ Finset.Ico n M, C*q^r := by
        apply Finset.sum_le_sum
        intro r hr
        have hrn : 1 ≤ r := le_trans hn (Finset.mem_Ico.mp hr).1
        have hlevel := causalKernelVector_haar_level_energy_le_rate
          hα ht0 ht1 hrn
        have hgeom := hpow r
        have hgeom' : ((2:ℝ)^r)⁻¹^β = q^r := by
          simpa [one_div] using hgeom
        simpa [C, β, q, hgeom', mul_assoc] using hlevel
    _ = C * (∑ r ∈ Finset.Ico n M, q^r) := by rw [Finset.mul_sum]
    _ ≤ C*(q^n/(1-q)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact geom_sum_Ico_le_of_lt_one hq0 hq1
    _ = C*q^n/(1-q) := by
      field_simp [ne_of_gt (sub_pos.mpr hq1)]

end BrownianSharp.AlignmentFractionalHaarBand
