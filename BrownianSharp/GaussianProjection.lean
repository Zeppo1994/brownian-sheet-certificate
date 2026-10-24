import BrownianSharp.BrownianHaarCovariance
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Tactic

/-!
Finite native projection of a Gaussian isonormal family. The coefficient and
evaluation index sets may differ. The proof reuses the existing isonormal
Gaussian interface and derives residual independence from orthogonality.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.GaussianProjection
open HaarQuarter

noncomputable def projection {H I : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [Fintype I] [DecidableEq I] (e : I → H) (v : H) : H :=
  ∑ i, ⟪e i, v⟫ • e i

/-- Orthogonality of the residual holds for every evaluation vector. -/
theorem cross_residual_zero {H I : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [Fintype I] [DecidableEq I] (e : I → H)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0)
    (v : H) (i : I) : ⟪e i, v - projection e v⟫ = 0 := by
  classical
  simp [projection, inner_sub_right, inner_sum, inner_smul_right, he]

/-- The two finite blocks form one jointly Gaussian vector. -/
theorem blocks_gaussian {H Ω I J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype I] [DecidableEq I] [Fintype J] [MeasurableSpace Ω]
    {P : Measure Ω} (W : IsonormalGaussianFamily H Ω (Sum I J) P)
    (e : I → H) (v : J → H) :
    HasGaussianLaw (fun ω =>
      (fun i => W.eval (e i) ω,
       fun j => W.eval (v j - projection e (v j)) ω)) P := by
  let vectors : Sum I J → H :=
    Sum.elim e (fun j => v j - projection e (v j))
  let split := (LinearEquiv.sumArrowLequivProdArrow I J ℝ ℝ).toContinuousLinearEquiv
  have hmap := (W.jointlyGaussian vectors).map_equiv split
  have heq : (fun ω => split (fun k => W.eval (vectors k) ω)) =
      (fun ω => (fun i => W.eval (e i) ω,
        fun j => W.eval (v j - projection e (v j)) ω)) := by
    funext ω
    apply Prod.ext
    · funext i
      simp [split, vectors]
    · funext j
      simp [split, vectors]
  rw [← heq]
  exact hmap

/-- Independent residuals follow from the exact finite orthogonal projection;
no diagonal cross-Gram restriction between e and v is assumed. -/
theorem coefficients_residual_independent {H Ω I J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype I] [DecidableEq I] [Fintype J] [MeasurableSpace Ω]
    {P : Measure Ω} (W : IsonormalGaussianFamily H Ω (Sum I J) P)
    (e : I → H) (v : J → H)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0) :
    IndepFun (fun ω i => W.eval (e i) ω)
      (fun ω j => W.eval (v j - projection e (v j)) ω) P := by
  apply (blocks_gaussian W e v).indepFun_of_covariance_eval
  intro i j
  rw [W.covariance_eq_inner]
  exact cross_residual_zero e he (v j) i

/-- The selected orthonormal coordinates are mutually independent. -/
theorem coefficients_independent {H Ω I J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype I] [DecidableEq I] [Fintype J] [MeasurableSpace Ω]
    {P : Measure Ω} (W : IsonormalGaussianFamily H Ω (Sum I J) P)
    (e : I → H) (v : J → H)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0) :
    iIndepFun (fun i ω => W.eval (e i) ω) P := by
  apply HasGaussianLaw.iIndepFun_of_covariance_eq_zero (blocks_gaussian W e v).fst
  intro i j hij
  rw [W.covariance_eq_inner, he i j]
  simp [hij]

/-- Every selected coefficient has the standard real Gaussian law. -/
theorem coefficient_standard_normal {H Ω I J : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype I] [DecidableEq I] [Fintype J] [MeasurableSpace Ω]
    {P : Measure Ω} (W : IsonormalGaussianFamily H Ω (Sum I J) P)
    (e : I → H) (v : J → H)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0) (i : I) :
    P.map (W.eval (e i)) = gaussianReal 0 1 := by
  have h := W.coordinate_law (Sum.elim e v) (Sum.inl i)
  change P.map (W.eval (e i)) = gaussianReal 0 (⟪e i, e i⟫).toNNReal at h
  rw [he i i] at h
  simpa using h

end BrownianSharp.GaussianProjection
