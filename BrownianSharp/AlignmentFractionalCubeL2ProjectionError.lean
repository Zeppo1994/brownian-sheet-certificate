import BrownianSharp.AlignmentFractionalTensorL2Semigroup
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Contractivity and actual operator-norm approximation in cube L². -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped ENNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalCubeL2ProjectionError
open AlignmentFractionalTensorL2Semigroup AlignmentFractionalTensorOperator

theorem cubeProfileToL2_norm_le {d : ℕ} (f : C(BrownianCubeAnchor d,ℝ)) :
    ‖cubeProfileToL2 f‖ ≤ ‖f‖ := by
  let μ : Measure (Fin d → ℝ) :=
    (Measure.pi (fun _ : Fin d => (volume:Measure ℝ))).restrict (CameronMartin.unitCubeSet d)
  letI : IsProbabilityMeasure ((volume:Measure ℝ).restrict (Set.Icc (0:ℝ) 1)) :=
    ⟨by simp⟩
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    rw [AlignmentFractionalTensor.unitCube_measure_eq_pi]
    infer_instance
  have hAE : ∀ᵐ x ∂μ, ‖(cubeProfileToL2 f) x‖ ≤ ‖f‖ := by
    filter_upwards [cubeProfileToL2_coe f] with x hx
    rw [hx]
    exact f.norm_coe_le_norm (clipCube x)
  have hh := Lp.norm_le_of_ae_bound (norm_nonneg f) hAE
  simpa [measureUnivNNReal] using hh

theorem fractionalTensorRLToL2_projection_error_bound {d : ℕ}
    (a : Fin d → ℝ) (ha : ∀ i,1/2<a i)
    (U : Submodule ℝ (CameronMartin.UnitCubeL2 d)) [FiniteDimensional ℝ U]
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hres : ∀ t, ‖tensorKernelFamily a ha t -
      U.starProjection (tensorKernelFamily a ha t)‖ ≤ δ) :
    ‖fractionalTensorRLToL2 a ha -
      (fractionalTensorRLToL2 a ha).comp U.starProjection‖ ≤ δ := by
  apply ContinuousLinearMap.opNorm_le_bound _ hδ
  intro g
  change ‖cubeProfileToL2 (fractionalTensorRL a ha g) -
    cubeProfileToL2 (fractionalTensorRL a ha (U.starProjection g))‖ ≤ δ*‖g‖
  rw [← map_sub]
  refine (cubeProfileToL2_norm_le _).trans ?_
  apply (ContinuousMap.norm_le _ (mul_nonneg hδ (norm_nonneg g))).mpr
  intro t
  change ‖⟪tensorKernelFamily a ha t,g⟫ -
    ⟪tensorKernelFamily a ha t,U.starProjection g⟫‖ ≤ δ*‖g‖
  rw [← U.inner_starProjection_left_eq_right,← inner_sub_left]
  exact (norm_inner_le_norm _ g).trans
    (mul_le_mul_of_nonneg_right (hres t) (norm_nonneg g))

end BrownianSharp.AlignmentFractionalCubeL2ProjectionError
