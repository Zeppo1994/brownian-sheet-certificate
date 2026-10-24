import BrownianSharp.SheetProjection
import BrownianSharp.FiniteOrthogonalCoordinates
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Metric control for finite Gaussian residuals

For an isonormal Gaussian family, removing any finite orthonormal projection
contracts the canonical Gaussian metric.  This is the Hilbert-space input to
chaining bounds for the actual residual sheet.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianResidualMetric

open HaarQuarter

variable {H Ω K I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [Fintype K] [Nonempty K] [Fintype I] [DecidableEq I]
  [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

private theorem projection_residual_norm_le (e : I → H) (x : H)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0) :
    ‖x - finiteOrthonormalProjection e x‖ ≤ ‖x‖ := by
  classical
  let q := finiteOrthonormalProjection e x
  have hres (i : I) : ⟪x - q, e i⟫ = 0 := by
    exact finiteProjection_residual_orthogonal e x he i
  have horth : ⟪x - q, q⟫ = 0 := by
    dsimp [q, finiteOrthonormalProjection]
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro i hi
    have hr : ⟪x - (∑ j, ⟪x, e j⟫ • e j), e i⟫ = 0 := by
      simpa [q, finiteOrthonormalProjection] using hres i
    rw [inner_smul_right, hr]
    simp
  have hdecomp : x = (x - q) + q := by abel
  have hsq : ‖x‖ ^ 2 = ‖x - q‖ ^ 2 + ‖q‖ ^ 2 := by
    calc
      ‖x‖ ^ 2 = ⟪x, x⟫ := (real_inner_self_eq_norm_sq x).symm
      _ = ⟪(x - q) + q, (x - q) + q⟫ := by rw [← hdecomp]
      _ = ⟪x - q, x - q⟫ + ⟪q, q⟫ := by
        rw [inner_add_left, inner_add_right]
        have hc : ⟪q, x - q⟫ = 0 := by rw [real_inner_comm]; exact horth
        rw [inner_add_right, horth, hc]
        ring
      _ = ‖x - q‖ ^ 2 + ‖q‖ ^ 2 := by
        rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg (‖q‖ : ℝ), norm_nonneg (x - q), norm_nonneg x]

private theorem residualLinear (e : I → H) (x y : H) :
    (x - finiteOrthonormalProjection e x) -
      (y - finiteOrthonormalProjection e y) =
      (x-y) - finiteOrthonormalProjection e (x-y) := by
  simp only [finiteOrthonormalProjection, inner_sub_left, sub_smul]
  rw [Finset.sum_sub_distrib]
  abel

private theorem finset_prod_sub_le_sum_sub {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℝ)
    (hab : ∀ i ∈ s, 0 ≤ b i ∧ b i ≤ a i ∧ a i ≤ 1) :
    (∏ i ∈ s, a i) - (∏ i ∈ s, b i) ≤ ∑ i ∈ s, (a i - b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hia := hab i (Finset.mem_insert_self _ _)
      have hrest : ∀ j ∈ s, 0 ≤ b j ∧ b j ≤ a j ∧ a j ≤ 1 := by
        intro j hj
        exact hab j (Finset.mem_insert_of_mem hj)
      have hprodB0 : 0 ≤ ∏ j ∈ s, b j :=
        Finset.prod_nonneg (fun j hj => (hrest j hj).1)
      have hprodA0 : 0 ≤ ∏ j ∈ s, a j :=
        Finset.prod_nonneg (fun j hj =>
          ((hrest j hj).1).trans (hrest j hj).2.1)
      have hprodAle : ∏ j ∈ s, a j ≤ 1 := by
        exact Finset.prod_le_one₀
          (fun j hj => ((hrest j hj).1).trans (hrest j hj).2.1)
          (fun j hj => (hrest j hj).2.2)
      have hprodB_le : ∏ j ∈ s, b j ≤ ∏ j ∈ s, a j := by
        exact Finset.prod_le_prod₀
          (fun j hj => (hrest j hj).1)
          (fun j hj => (hrest j hj).2.1)
      rw [Finset.prod_insert hi, Finset.prod_insert hi,
        Finset.sum_insert hi]
      have hcalc : a i * (∏ j ∈ s, a j) - b i * (∏ j ∈ s, b j) =
          (a i - b i) * (∏ j ∈ s, a j) +
            b i * ((∏ j ∈ s, a j) - (∏ j ∈ s, b j)) := by ring
      rw [hcalc]
      have ih' := ih hrest
      have hmul₁ : (a i - b i) * (∏ j ∈ s, a j) ≤ a i - b i :=
        mul_le_of_le_one_right (sub_nonneg.mpr hia.2.1) hprodAle
      have hdiff0 : 0 ≤ (∏ j ∈ s, a j) - (∏ j ∈ s, b j) :=
        sub_nonneg.mpr hprodB_le
      have hbi1 : b i ≤ 1 := hia.2.1.trans hia.2.2
      have hmul₂ : b i * ((∏ j ∈ s, a j) - (∏ j ∈ s, b j)) ≤
          ∑ j ∈ s, (a j - b j) := by
        calc
          b i * ((∏ j ∈ s, a j) - (∏ j ∈ s, b j)) ≤
              (∏ j ∈ s, a j) - (∏ j ∈ s, b j) :=
            mul_le_of_le_one_left hdiff0 hbi1
          _ ≤ ∑ j ∈ s, (a j - b j) := ih'
      nlinarith

/-- The Brownian box-feature canonical metric is bounded by the coordinate
`L¹` distance. -/
theorem brownianSheet_boxFeature_metric_sq_le_sum_abs {d : ℕ}
    (x y : BrownianCubeAnchor d) :
    ‖brownianSheetBoxIndicatorLp x.val -
      brownianSheetBoxIndicatorLp y.val‖ ^ 2 ≤
      ∑ i : Fin d, |x.val i - y.val i| := by
  have hx (i : Fin d) : 0 ≤ x.val i ∧ x.val i ≤ 1 := x.property i
  have hy (i : Fin d) : 0 ≤ y.val i ∧ y.val i ≤ 1 := y.property i
  let z : Fin d → ℝ := fun i => min (x.val i) (y.val i)
  have hzx : ∀ i, 0 ≤ z i ∧ z i ≤ x.val i ∧ x.val i ≤ 1 := by
    intro i
    simp [z, hx i, hy i]
  have hzy : ∀ i, 0 ≤ z i ∧ z i ≤ y.val i ∧ y.val i ≤ 1 := by
    intro i
    simp [z, hx i, hy i]
  have hprodX := finset_prod_sub_le_sum_sub Finset.univ x.val z
    (by intro i hi; exact hzx i)
  have hprodY := finset_prod_sub_le_sum_sub Finset.univ y.val z
    (by intro i hi; exact hzy i)
  have hsum : (∑ i : Fin d, (x.val i - z i)) +
      (∑ i : Fin d, (y.val i - z i)) =
      ∑ i : Fin d, |x.val i - y.val i| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [z]
    by_cases h : x.val i ≤ y.val i
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · have h' : y.val i ≤ x.val i := le_of_not_ge h
      rw [min_eq_right h', abs_of_nonneg (sub_nonneg.mpr h')]
      ring
  have hnorm : ‖brownianSheetBoxIndicatorLp x.val -
      brownianSheetBoxIndicatorLp y.val‖^2 =
      (∏ i, x.val i) + (∏ i, y.val i) -
        2 * ∏ i, min (x.val i) (y.val i) := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
      inner_sub_right,
      brownianSheetBoxIndicatorLp_inner x.val x.val
        (fun i => (x.property i).1) (fun i => (x.property i).1),
      brownianSheetBoxIndicatorLp_inner x.val y.val
        (fun i => (x.property i).1) (fun i => (y.property i).1),
      brownianSheetBoxIndicatorLp_inner y.val x.val
        (fun i => (y.property i).1) (fun i => (x.property i).1),
      brownianSheetBoxIndicatorLp_inner y.val y.val
        (fun i => (y.property i).1) (fun i => (y.property i).1)]
    have hmin : (∏ i : Fin d, min (y.val i) (x.val i)) =
        ∏ i : Fin d, min (x.val i) (y.val i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [min_comm]
    simp only [min_self]
    rw [hmin]
    ring
  rw [hnorm]
  have halg : (∏ i, x.val i) + (∏ i, y.val i) -
      2 * ∏ i, z i =
      ((∏ i, x.val i) - ∏ i, z i) +
        ((∏ i, y.val i) - ∏ i, z i) := by ring
  rw [halg]
  have hprodX' : (∏ i : Fin d, x.val i) - (∏ i : Fin d, z i) ≤
      ∑ i : Fin d, (x.val i - z i) := hprodX
  have hprodY' : (∏ i : Fin d, y.val i) - (∏ i : Fin d, z i) ≤
      ∑ i : Fin d, (y.val i - z i) := hprodY
  rw [← hsum]
  exact add_le_add hprodX' hprodY'

/-- The residual coordinates have covariance equal to the inner product of
their projected-away source vectors. -/
theorem residual_covariance
    (W : IsonormalGaussianFamily H Ω K P) (e : I → H)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0) (x y : H) :
    cov[fun ω => W.eval (x - finiteOrthonormalProjection e x) ω,
        fun ω => W.eval (y - finiteOrthonormalProjection e y) ω; P] =
      ⟪x - finiteOrthonormalProjection e x,
        y - finiteOrthonormalProjection e y⟫ := by
  exact W.covariance_eq_inner _ _

/-- Removing a finite orthonormal layer cannot increase the canonical
Gaussian distance between two residual coordinates. -/
theorem residual_canonicalMetric_le
    (W : IsonormalGaussianFamily H Ω K P) (e : I → H)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0) (x y : H) :
    ‖(x - finiteOrthonormalProjection e x) -
        (y - finiteOrthonormalProjection e y)‖ ≤ ‖x-y‖ := by
  rw [residualLinear]
  exact projection_residual_norm_le e (x-y) he

/-- Pointwise residual variance is bounded by the original feature variance.
The exact variance identity follows from isonormality; the inequality is
Bessel's contraction estimate. -/
theorem residual_variance_le
    (W : IsonormalGaussianFamily H Ω K P) (e : I → H)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0) (x : H) :
    Var[fun ω => W.eval (x - finiteOrthonormalProjection e x) ω; P] ≤
      ‖x‖ ^ 2 := by
  have hgauss := W.coordinate_law
    (fun _ : K => x - finiteOrthonormalProjection e x) (Classical.choice ‹Nonempty K›)
  have hmem : MemLp (fun ω => W.eval (x - finiteOrthonormalProjection e x) ω) 2 P :=
    (W.jointlyGaussian (fun _ : K => x - finiteOrthonormalProjection e x)).eval
      (Classical.choice ‹Nonempty K›) |>.memLp_two
  have hvar : Var[fun ω => W.eval (x - finiteOrthonormalProjection e x) ω; P] =
      ‖x - finiteOrthonormalProjection e x‖ ^ 2 := by
    rw [← covariance_self (W.measurable_eval _).aemeasurable,
      W.covariance_eq_inner, real_inner_self_eq_norm_sq]
  rw [hvar]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    (projection_residual_norm_le e x he)

/-- The continuous Brownian-sheet sample-path covariance is represented by
the actual anchored-box feature vectors in the isonormal source Hilbert space.
This identifies the abstract metric contraction with the sheet itself. -/
theorem brownianSheet_eval_covariance_eq_boxFeature_inner
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) (x y : BrownianCubeAnchor d) :
    cov[B.eval x, B.eval y; P] =
      ⟪brownianSheetBoxIndicatorLp x.val,
        brownianSheetBoxIndicatorLp y.val⟫ := by
  rw [B.eval_covariance, brownianSheetBoxIndicatorLp_inner]
  · intro i
    exact (x.property i).1
  · intro i
    exact (y.property i).1

end BrownianSharp.AlignmentGaussianResidualMetric
