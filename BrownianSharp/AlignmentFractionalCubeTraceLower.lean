import BrownianSharp.AlignmentFiniteOrthonormalSpanLower
import BrownianSharp.AlignmentIntegerTwoTensorApproximationRate
import BrownianSharp.AlignmentFractionalTensorL2Semigroup
import BrownianSharp.AlignmentOperatorKernelTrace
import Mathlib.Tactic

/-! Convert the actual cube-L² norm of an order-two tensor output into the
probability-space trace energy used by the C-valued approximation number. -/

noncomputable section
open MeasureTheory HaarQuarter
open scoped RealInnerProductSpace ENNReal

namespace BrownianSharp.AlignmentFractionalCubeTraceLower

open BrownianSharp.AlignmentFractionalTensorL2Semigroup
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalTensor
open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentIntegerTwoTensorApproximationRate
open BrownianSharp.AlignmentFractionalApproximationNumbers

private def sourceCubeMeasure (d : ℕ) : Measure (Fin d → ℝ) :=
  (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
    (CameronMartin.unitCubeSet d)

private theorem sourceCubeMeasure_probability (d : ℕ) :
    IsProbabilityMeasure (sourceCubeMeasure d) := by
  letI : IsProbabilityMeasure ((volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1)) := ⟨by simp⟩
  dsimp [sourceCubeMeasure]
  rw [AlignmentFractionalTensor.unitCube_measure_eq_pi]
  infer_instance

private def cubeAnchorMeasure (d : ℕ) : Measure (BrownianCubeAnchor d) :=
  Measure.map (clipCube (d:=d)) (sourceCubeMeasure d)

private theorem cubeAnchorMeasure_probability (d : ℕ) :
    IsProbabilityMeasure (cubeAnchorMeasure d) := by
  letI := sourceCubeMeasure_probability d
  dsimp [cubeAnchorMeasure]
  infer_instance

private theorem cubeProfileToL2_norm_sq_integral {d : ℕ}
    (f : C(BrownianCubeAnchor d, ℝ)) :
    ‖cubeProfileToL2 f‖^2 = ∫ t, (f t)^2 ∂cubeAnchorMeasure d := by
  have hinner : ‖cubeProfileToL2 f‖^2 =
      ∫ x, (cubeProfileToL2 f x)^2 ∂sourceCubeMeasure d := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    simp_rw [Real.inner_apply]
    rw [sourceCubeMeasure]
    simp [pow_two]
  calc
    ‖cubeProfileToL2 f‖^2 =
        ∫ x, (cubeProfileToL2 f x)^2 ∂sourceCubeMeasure d := hinner
    _ = ∫ x, (f (clipCube x))^2 ∂sourceCubeMeasure d := by
      apply integral_congr_ae
      filter_upwards [cubeProfileToL2_coe f] with x hx
      simp [hx]
    _ = ∫ t, (f t)^2 ∂cubeAnchorMeasure d := by
      rw [cubeAnchorMeasure]
      symm
      exact integral_map (φ:=clipCube (d:=d)) (μ:=sourceCubeMeasure d)
        (f:=fun t => (f t)^2) clipCube.continuous.aemeasurable
        (f.continuous.pow 2).aestronglyMeasurable


theorem approximationNumber_lower_of_cubeL2_subspace_energy
    {d D k : ℕ}
    (T : CameronMartin.UnitCubeL2 d →L[ℝ] C(BrownianCubeAnchor d,ℝ))
    (V : Submodule ℝ (CameronMartin.UnitCubeL2 d))
    [FiniteDimensional ℝ V] (hD : Module.finrank ℝ V = D)
    (hk : 1 ≤ k) (hkD : k ≤ D) (σ : ℝ) (hσ : 0 ≤ σ)
    (henergy : ∀ v : V, ‖(v : CameronMartin.UnitCubeL2 d)‖ = 1 →
      σ^2 ≤ ‖cubeProfileToL2 (T (v : CameronMartin.UnitCubeL2 d))‖^2) :
    ENNReal.ofReal (σ * Real.sqrt ((D-(k-1):ℕ):ℝ)) ≤ approximationNumber T k := by
  let μ := cubeAnchorMeasure d
  letI : IsProbabilityMeasure μ := cubeAnchorMeasure_probability d
  have henergy' : ∀ v : V, ‖(v : CameronMartin.UnitCubeL2 d)‖ = 1 →
      σ^2 ≤ ∫ t, (T (v : CameronMartin.UnitCubeL2 d) t)^2 ∂μ := by
    intro v hv
    rw [← cubeProfileToL2_norm_sq_integral]
    exact henergy v hv
  exact BrownianSharp.AlignmentOperatorKernelTrace.approximationNumber_lower_of_subspace_trace
    μ T V hD hk hkD σ hσ henergy'

theorem approximationNumber_lower_of_orthonormal_cube_frame
    {d k : ℕ} {ι : Type*} [Fintype ι]
    (T : CameronMartin.UnitCubeL2 d →L[ℝ] C(BrownianCubeAnchor d,ℝ))
    (e : ι → CameronMartin.UnitCubeL2 d) (he : Orthonormal ℝ e)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (horth : ∀ i j, i ≠ j →
      inner ℝ (cubeProfileToL2 (T (e i))) (cubeProfileToL2 (T (e j))) = 0)
    (hlower : ∀ i, σ ≤ ‖cubeProfileToL2 (T (e i))‖)
    (hk : 1 ≤ k) (hkD : k ≤ Fintype.card ι) :
    ENNReal.ofReal (σ * Real.sqrt ((Fintype.card ι-(k-1):ℕ):ℝ)) ≤
      approximationNumber T k := by
  let V := Submodule.span ℝ (Set.range e)
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
  have hD : Module.finrank ℝ V = Fintype.card ι := finrank_span_eq_card he.linearIndependent
  apply approximationNumber_lower_of_cubeL2_subspace_energy T V hD hk hkD σ hσ
  intro v hv
  let S := (cubeProfileToL2 (d:=d)).comp T
  have hbound := AlignmentFiniteOrthonormalSpanLower.norm_lower_on_orthonormal_span
    S e σ he horth hlower hσ (v : CameronMartin.UnitCubeL2 d) v.property
  have hnorm : σ ≤ ‖S (v : CameronMartin.UnitCubeL2 d)‖ := by simpa [hv] using hbound
  exact (sq_le_sq₀ hσ (norm_nonneg _)).2 hnorm

end BrownianSharp.AlignmentFractionalCubeTraceLower
