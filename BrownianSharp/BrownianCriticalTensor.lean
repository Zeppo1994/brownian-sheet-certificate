import BrownianSharp.BrownianCriticalProjection
import BrownianSharp.BrownianHaarCovariance

/-! Tensorization interface for the critical one-dimensional vectors from
Section 7.  The coordinate integrability hypotheses are explicit so this
module does not conceal any stochastic assumption. -/

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace HaarQuarter

/-- Tensor product of one-axis critical vectors, as a pointwise function on
the finite-dimensional Brownian-sheet integrand space. -/
noncomputable def criticalDyadicETensor {d : ℕ}
    (profile cells : Fin d → ℕ) (x : Fin d → ℝ) : ℝ :=
  ∏ i, criticalDyadicE (profile i) (cells i) (x i)

private theorem measurable_realDyadicHaar (r c : ℕ) :
    Measurable (realDyadicHaar r c) := by
  classical
  unfold realDyadicHaar
  apply Measurable.sub
  · exact Measurable.ite measurableSet_Ico measurable_const measurable_const
  · exact Measurable.ite measurableSet_Ico measurable_const measurable_const

private theorem measurable_criticalDyadicE (r c : ℕ) :
    Measurable (criticalDyadicE r c) := by
  unfold criticalDyadicE
  apply Measurable.div
  · exact (measurable_realDyadicHaar (r + 1) (2 * c)).sub
      (measurable_realDyadicHaar (r + 1) (2 * c + 1))
  · exact measurable_const

/-- The scalar critical vectors are orthogonal across different depths. -/
theorem criticalDyadicE_inner_zero_of_depth_ne {r s c d : ℕ}
    (hrs : r ≠ s) :
    ∫ x, criticalDyadicE r c x * criticalDyadicE s d x ∂volume = 0 := by
  rcases lt_or_gt_of_ne hrs with hlt | hgt
  · exact criticalDyadicE_inner_of_depth_ne hlt
  · have hrev := criticalDyadicE_inner_of_depth_ne
      (r := s) (s := r) (c := d) (d := c) hgt
    calc
      ∫ x, criticalDyadicE r c x * criticalDyadicE s d x ∂volume =
          ∫ x, criticalDyadicE s d x * criticalDyadicE r c x ∂volume := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = 0 := hrev

/-- The scalar critical vectors are orthogonal whenever either their depths
or their cell indices differ. -/
theorem criticalDyadicE_inner_zero_of_ne {r s c d : ℕ}
    (h : r ≠ s ∨ c ≠ d) :
    ∫ x, criticalDyadicE r c x * criticalDyadicE s d x ∂volume = 0 := by
  rcases h with hrs | hcd
  · exact criticalDyadicE_inner_zero_of_depth_ne hrs
  · by_cases hrs : r = s
    · subst s
      exact criticalDyadicE_inner_same_level_of_ne hcd
    · exact criticalDyadicE_inner_zero_of_depth_ne hrs

/-- The raw finite-product integral factors into the one-dimensional inner
products.  This algebraic/Fubini statement is the base step for proving that
the manuscript's tensor critical vectors are orthonormal. -/
theorem criticalDyadicETensor_inner_eq_prod {d : ℕ}
    (profile cells profile' cells' : Fin d → ℕ) :
    ∫ x : Fin d → ℝ,
      criticalDyadicETensor profile cells x *
        criticalDyadicETensor profile' cells' x ∂
          (Measure.pi fun _ : Fin d => volume) =
      ∏ i, ∫ x : ℝ,
        criticalDyadicE (profile i) (cells i) x *
          criticalDyadicE (profile' i) (cells' i) x ∂volume := by
  have hpoint : (fun x : Fin d → ℝ =>
      criticalDyadicETensor profile cells x *
        criticalDyadicETensor profile' cells' x) =
      fun x => ∏ i,
        (criticalDyadicE (profile i) (cells i) (x i) *
          criticalDyadicE (profile' i) (cells' i) (x i)) := by
    funext x
    simp [criticalDyadicETensor, ← Finset.prod_mul_distrib]
  rw [hpoint]
  exact integral_fintype_prod_eq_prod
    (f := fun i x => criticalDyadicE (profile i) (cells i) x *
      criticalDyadicE (profile' i) (cells' i) x)
    (μ := fun _ : Fin d => (volume : Measure ℝ))

/-- Distinct profile-cell indices give orthogonal tensor critical vectors.
This is the continuous tensor orthogonality assertion needed for the
independent Gaussian projection family. -/
theorem criticalDyadicETensor_inner_zero_of_coordinate_ne {d : ℕ}
    (profile cells profile' cells' : Fin d → ℕ) (i : Fin d)
    (hneq : profile i ≠ profile' i ∨ cells i ≠ cells' i) :
    ∫ x : Fin d → ℝ,
      criticalDyadicETensor profile cells x *
        criticalDyadicETensor profile' cells' x ∂
          (Measure.pi fun _ : Fin d => volume) = 0 := by
  rw [criticalDyadicETensor_inner_eq_prod profile cells profile' cells']
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact criticalDyadicE_inner_zero_of_ne hneq

/-- Equal profile-cell indices give unit norm in the product integrand
space. -/
theorem criticalDyadicETensor_inner_self {d : ℕ}
    (profile cells : Fin d → ℕ) :
    ∫ x : Fin d → ℝ,
      criticalDyadicETensor profile cells x ^ 2 ∂
          (Measure.pi fun _ : Fin d => volume) = 1 := by
  have hprod : (fun x : Fin d → ℝ =>
      criticalDyadicETensor profile cells x ^ 2) =
      fun x => ∏ i, (criticalDyadicE (profile i) (cells i) (x i)) ^ 2 := by
    funext x
    simp [criticalDyadicETensor, Finset.prod_pow]
  rw [hprod, integral_fintype_prod_eq_prod
    (f := fun i x => (criticalDyadicE (profile i) (cells i) x) ^ 2)
    (μ := fun _ : Fin d => (volume : Measure ℝ))]
  simp_rw [criticalDyadicE_integral_sq_eq_one]
  simp

/-- The tensor critical function belongs to the Brownian-sheet integrand
space `L²([0,1]^d)`. Its square is a finite product of integrable
one-dimensional squares. -/
theorem criticalDyadicETensor_memLp_two {d : ℕ}
    (profile cells : Fin d → ℕ) :
    MemLp (criticalDyadicETensor profile cells) 2
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
  have hprod : Integrable (fun x : Fin d → ℝ =>
      ∏ i, (criticalDyadicE (profile i) (cells i) (x i)) ^ 2)
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
    exact Integrable.fintype_prod
      (μ := fun _ : Fin d => (volume : Measure ℝ))
      (f := fun i x => (criticalDyadicE (profile i) (cells i) x) ^ 2)
      (fun i => criticalDyadicE_sq_integrable (profile i) (cells i))
  have hpoint : (fun x : Fin d → ℝ =>
      criticalDyadicETensor profile cells x ^ 2) =
      fun x => ∏ i, (criticalDyadicE (profile i) (cells i) (x i)) ^ 2 := by
    funext x
    simp [criticalDyadicETensor, Finset.prod_pow]
  have hsq : Integrable
      (fun x : Fin d → ℝ => criticalDyadicETensor profile cells x ^ 2)
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
    rw [hpoint]
    exact hprod
  have hmeas : Measurable (criticalDyadicETensor profile cells) := by
    unfold criticalDyadicETensor
    exact Finset.univ.measurable_fun_prod (fun i hi =>
      (measurable_criticalDyadicE (profile i) (cells i)).comp
        (measurable_pi_apply i))
  exact (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hsq

/-- Actual `L²` vector represented by the tensor product of critical Haar
differences. -/
noncomputable def criticalDyadicETensorLp {d : ℕ}
    (profile cells : Fin d → ℕ) :
    Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
  (criticalDyadicETensor_memLp_two profile cells).toLp
    (criticalDyadicETensor profile cells)

/-- Hilbert inner product of two critical tensor vectors as an integral of
their pointwise representatives. -/
theorem criticalDyadicETensorLp_inner_eq_integral {d : ℕ}
    (profile cells profile' cells' : Fin d → ℕ) :
    ⟪criticalDyadicETensorLp profile cells,
      criticalDyadicETensorLp profile' cells'⟫ =
      ∫ x : Fin d → ℝ,
        criticalDyadicETensor profile cells x *
          criticalDyadicETensor profile' cells' x ∂
            (Measure.pi fun _ : Fin d => volume) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    MemLp.coeFn_toLp (criticalDyadicETensor_memLp_two profile cells),
    MemLp.coeFn_toLp (criticalDyadicETensor_memLp_two profile' cells')]
    with x hx hx'
  simp [criticalDyadicETensorLp, hx, hx', mul_comm]

/-- Tensor critical vectors with distinct profile-cell indices are genuinely
orthogonal in the Brownian-sheet integrand Hilbert space. -/
theorem criticalDyadicETensorLp_inner_zero_of_coordinate_ne {d : ℕ}
    (profile cells profile' cells' : Fin d → ℕ) (i : Fin d)
    (hneq : profile i ≠ profile' i ∨ cells i ≠ cells' i) :
    ⟪criticalDyadicETensorLp profile cells,
      criticalDyadicETensorLp profile' cells'⟫ = 0 := by
  rw [criticalDyadicETensorLp_inner_eq_integral]
  exact criticalDyadicETensor_inner_zero_of_coordinate_ne
    profile cells profile' cells' i hneq

/-- Each tensor critical vector has unit Hilbert norm. -/
theorem criticalDyadicETensorLp_inner_self {d : ℕ}
    (profile cells : Fin d → ℕ) :
    ⟪criticalDyadicETensorLp profile cells,
      criticalDyadicETensorLp profile cells⟫ = 1 := by
  rw [criticalDyadicETensorLp_inner_eq_integral]
  convert criticalDyadicETensor_inner_self profile cells using 1
  simp [pow_two]

/-- For every finite set of distinct profile-cell indices, an isonormal
family sends the actual tensor critical vectors to independent standard
Gaussians. This proves the orthonormal Gaussian input, conditional on the
separately constructed isonormal realization. -/
theorem criticalDyadicETensor_isonormal_independent {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω] (P : Measure Ω)
    (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) Ω ι P)
    (profile cells : ι → Fin d → ℕ)
    (hseparate : ∀ i j, i ≠ j → ∃ k,
      profile i k ≠ profile j k ∨ cells i k ≠ cells j k) :
    iIndepFun (fun i ω => W.eval
      (criticalDyadicETensorLp (profile i) (cells i)) ω) P := by
  have horth : ∀ i j, i ≠ j →
      ⟪criticalDyadicETensorLp (profile i) (cells i),
        criticalDyadicETensorLp (profile j) (cells j)⟫ = 0 := by
    intro i j hij
    obtain ⟨k, hk⟩ := hseparate i j hij
    exact criticalDyadicETensorLp_inner_zero_of_coordinate_ne
      (profile i) (cells i) (profile j) (cells j) k hk
  have hind := W.iIndepFun_of_orthogonal
    (fun i => criticalDyadicETensorLp (profile i) (cells i))
    (fun _ => 1) horth
  simpa using hind

/-- The actual isonormal coordinates on tensor critical vectors are standard
normal, by their unit L² norm. -/
theorem criticalDyadicETensor_isonormal_coordinate_law {d : ℕ}
    {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] (P : Measure Ω)
    (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) Ω ι P)
    (profile cells : ι → Fin d → ℕ) (i : ι) :
    P.map (fun ω => W.eval
      (criticalDyadicETensorLp (profile i) (cells i)) ω) =
      gaussianReal 0 1 := by
  have hnorm : ‖criticalDyadicETensorLp (profile i) (cells i)‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]
    exact criticalDyadicETensorLp_inner_self (profile i) (cells i)
  simpa [hnorm] using
    W.coordinate_law
      (fun j => criticalDyadicETensorLp (profile j) (cells j)) i

end HaarQuarter
