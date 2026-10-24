import BrownianSharp.AlignmentNestedProjectionTensor
import BrownianSharp.AlignmentFractionalTensorOperator

/-! Tensorized finite source projections of the actual fractional RL kernel.
The approximation is built from arbitrary coordinatewise finite orthonormal
families, with an exact frame expansion and a dimension-free scalar residual
input to the product telescoping estimate. -/

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentNestedProjectionTensorApproximation

open BrownianSharp
open BrownianSharp.AlignmentNestedProjectionTensor
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalTensor
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentL2TensorProduct
open BrownianSharp.AlignmentNestedProjectionFrame
open HaarQuarter
open BrownianSharp.CameronMartin

abbrev AxisL2 := AlignmentFractionalL2.UnitL2

instance axisFrameSpan_finiteDimensional {I : Type*} [Fintype I]
    (e : I → AxisL2) :
    FiniteDimensional ℝ ↥(Submodule.span ℝ (Set.range e)) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range e)

/-- The finite orthogonal projection onto a coordinate source frame's span. -/
def axisFrameProjection {I : Type*} [Fintype I] (e : I → AxisL2) :
    AxisL2 →L[ℝ] AxisL2 := (Submodule.span ℝ (Set.range e)).starProjection

/-- Exact finite expansion of the scalar finite-dimensional projection. -/
theorem axisFrameProjection_eq_sum {I : Type*} [Fintype I]
    (e : I → AxisL2) (he : Orthonormal ℝ e) (x : AxisL2) :
    axisFrameProjection e x = ∑ i, ⟪x,e i⟫ • e i := by
  classical
  let W : Submodule ℝ AxisL2 := Submodule.span ℝ (Set.range e)
  have hmem : (∑ i, ⟪x,e i⟫ • e i) ∈ W := by
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  have hres : x - (∑ i, ⟪x,e i⟫ • e i) ∈ Wᗮ := by
    rw [Submodule.mem_orthogonal']
    intro w hw
    dsimp [W] at hw
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro z ⟨i,rfl⟩
      have h := BrownianSharp.finiteProjection_residual_orthogonal e x
        (orthonormal_iff_ite.mp he) i
      simpa [BrownianSharp.finiteOrthonormalProjection] using h
    · simp
    · intro y z hy hz hpy hpz
      rw [inner_add_right, hpy, hpz]
      simp
    · intro c y hy hpy
      rw [inner_smul_right, hpy]
      simp
  have hp := W.eq_starProjection_of_mem_orthogonal hmem hres
  simpa [axisFrameProjection, W, BrownianSharp.finiteOrthonormalProjection] using hp

/-- When the coordinate frame is the global nested frame, its finite-span
projection is exactly the original projection onto `U n`. -/
theorem axisFrameProjection_nestedFrame_eq
    (U : ℕ → Submodule ℝ AxisL2)
    (hfinite : ∀ n, FiniteDimensional ℝ ↥(U n))
    (hnested : ∀ n, U n ≤ U (n+1)) (n : ℕ) :
    axisFrameProjection (nestedFrame U hfinite n) = (U n).starProjection := by
  ext x
  rw [axisFrameProjection_eq_sum (nestedFrame U hfinite n)
    (nestedFrame_orthonormal U hfinite hnested n) x]
  apply Filter.Eventually.of_forall
  intro t
  exact congrArg (fun z : AxisL2 => z t)
    (starProjection_eq_frame_sum U hfinite hnested n x).symm

/-- Coordinatewise scalar projection of the actual tensor RL kernel. -/
noncomputable def tensorFrameProjectedKernel {d : ℕ} {I : Fin d → Type*}
    [∀ i, Fintype (I i)] (e : ∀ i, I i → AxisL2)
    (α : Fin d → ℝ) (hα : ∀ i, 1/2 < α i) :
    C(BrownianCubeAnchor d, UnitCubeL2 d) := by
  let μ : Fin d → Measure ℝ := fun _ => volume.restrict (Set.Icc (0:ℝ) 1)
  let T := tensorContinuous (μ := μ)
  refine ⟨fun t => productToCube d (T (fun i =>
    axisFrameProjection (e i)
      (translatedUnitKernelFamily (α i) (hα i) (cubeCoordinate i t)))), ?_⟩
  exact (productToCube d).continuous.comp (T.cont.comp (continuous_pi fun i =>
    (axisFrameProjection (e i)).continuous.comp
      ((translatedUnitKernelFamily (α i) (hα i)).continuous.comp
        (cubeCoordinate i).continuous)))

/-- The coordinatewise finite projection is exactly a finite sum over the
tensor frame, with coefficients given by the actual tensor-kernel inner
products. -/
theorem tensorFrameProjectedKernel_eq_sum {d : ℕ} {I : Fin d → Type*}
    [∀ i, Fintype (I i)] (e : ∀ i, I i → AxisL2)
    (he : ∀ i, Orthonormal ℝ (e i))
    (α : Fin d → ℝ) (hα : ∀ i, 1/2 < α i) (t : BrownianCubeAnchor d) :
    tensorFrameProjectedKernel e α hα t =
      ∑ a : (∀ i, I i),
        ⟪tensorKernelFamily α hα t, tensorFrame e a⟫ • tensorFrame e a := by
  classical
  let μ : Fin d → Measure ℝ := fun _ => volume.restrict (Set.Icc (0:ℝ) 1)
  let T := tensorContinuous (μ := μ)
  let v : Fin d → AxisL2 := fun i =>
    translatedUnitKernelFamily (α i) (hα i) (cubeCoordinate i t)
  have hproj (i : Fin d) : axisFrameProjection (e i) (v i) =
      ∑ a : I i, ⟪v i,e i a⟫ • e i a := axisFrameProjection_eq_sum (e i) (he i) (v i)
  have hsum : T (fun i => axisFrameProjection (e i) (v i)) =
      ∑ a : (∀ i, I i),
        (∏ i : Fin d, ⟪v i,e i (a i)⟫) •
          productVector (fun i => e i (a i)) := by
    calc
      T (fun i => axisFrameProjection (e i) (v i)) =
          T (fun i => ∑ a : I i, ⟪v i,e i a⟫ • e i a) := by
            congr 1
            funext i
            exact hproj i
      _ = ∑ a : (∀ i, I i),
          T (fun i => ⟪v i,e i (a i)⟫ • e i (a i)) := by
            exact T.map_sum (fun i a => ⟪v i,e i a⟫ • e i a)
      _ = ∑ a : (∀ i, I i),
          (∏ i : Fin d, ⟪v i,e i (a i)⟫) •
            productVector (fun i => e i (a i)) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [T.map_smul_univ]
            simp only [T, tensorContinuous_apply]
  have hactual : tensorKernelFamily α hα t = productToCube d (T v) := by
    simp [tensorKernelFamily, productKernelFamily, T, v, cubeCoordinate,
      tensorContinuous_apply]
  have hprojected : tensorFrameProjectedKernel e α hα t =
      productToCube d (T (fun i => axisFrameProjection (e i) (v i))) := rfl
  rw [hprojected, hsum, hactual]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_smul]
  congr 1
  rw [← hactual, tensorKernel_inner_frame]
  apply Finset.prod_congr rfl
  intro i hi
  have hkernel : v i = kernelVector (α i) (t.val i) (hα i)
      (Set.mem_Icc.mp (t.property i)).1 (Set.mem_Icc.mp (t.property i)).2 := by
    dsimp [v, cubeCoordinate]
    exact translatedUnitKernelFamily_eq_kernelVector (α i) (t.val i) (hα i)
      (Set.mem_Icc.mp (t.property i)).1 (Set.mem_Icc.mp (t.property i)).2
  rw [hkernel]

/-- Generic product residual bound. If every coordinate kernel is bounded by
`B` and its projection residual by `δ i`, the tensor feature error is at most
`d * B^(d-1) * ∑ δ i`. -/
theorem tensorKernel_frameProjection_error_le
    {d : ℕ} (hd : 0 < d) {I : Fin d → Type*} [∀ i, Fintype (I i)]
    (e : ∀ i, I i → AxisL2) (he : ∀ i, Orthonormal ℝ (e i))
    (α : Fin d → ℝ) (hα : ∀ i, 1/2 < α i)
    {B : ℝ} (hB : 0 ≤ B) (δ : Fin d → ℝ) (hδ : ∀ i, 0 ≤ δ i)
    (hnorm : ∀ i (t : BrownianCubeAnchor d),
      ‖translatedUnitKernelFamily (α i) (hα i) (cubeCoordinate i t)‖ ≤ B)
    (herror : ∀ i (t : BrownianCubeAnchor d),
      ‖translatedUnitKernelFamily (α i) (hα i) (cubeCoordinate i t) -
        axisFrameProjection (e i)
          (translatedUnitKernelFamily (α i) (hα i) (cubeCoordinate i t))‖ ≤ δ i)
    (t : BrownianCubeAnchor d) :
    ‖tensorKernelFamily α hα t - tensorFrameProjectedKernel e α hα t‖ ≤
      (d : ℝ) * B^(d-1) * ∑ i : Fin d, δ i := by
  classical
  let μ : Fin d → Measure ℝ := fun _ => volume.restrict (Set.Icc (0:ℝ) 1)
  let T := tensorContinuous (μ := μ)
  let v : Fin d → AxisL2 := fun i =>
    translatedUnitKernelFamily (α i) (hα i) (cubeCoordinate i t)
  let w : Fin d → AxisL2 := fun i => axisFrameProjection (e i) (v i)
  have hprojOp (i : Fin d) : ‖axisFrameProjection (e i)‖ ≤ 1 :=
    (Submodule.span ℝ (Set.range (e i))).starProjection_norm_le
  have hnormv (i : Fin d) : ‖v i‖ ≤ B := hnorm i t
  have hnormw (i : Fin d) : ‖w i‖ ≤ B := by
    calc
      ‖w i‖ ≤ ‖axisFrameProjection (e i)‖ * ‖v i‖ :=
        (axisFrameProjection (e i)).le_opNorm (v i)
      _ ≤ 1 * B := by
        exact mul_le_mul (hprojOp i) (hnormv i) (norm_nonneg _) (by norm_num)
      _ = B := one_mul _
  have hmaxv : ‖v‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).2
    intro i
    exact hnormv i
  have hmaxw : ‖w‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).2
    intro i
    exact hnormw i
  have hdiff : ‖v-w‖ ≤ ∑ i : Fin d, δ i := by
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i hi => hδ i)).2
    intro i
    have hi := herror i t
    dsimp [v,w]
    calc
      ‖translatedUnitKernelFamily (α i) (hα i) (cubeCoordinate i t) -
        axisFrameProjection (e i)
          (translatedUnitKernelFamily (α i) (hα i) (cubeCoordinate i t))‖ ≤ δ i := hi
      _ ≤ ∑ j : Fin d, δ j := Finset.single_le_sum
        (f:=δ) (s:=Finset.univ) (fun j hj => hδ j) (Finset.mem_univ i)
  have hTbound : ‖T‖ ≤ 1 := by
    dsimp [T, tensorContinuous]
    exact MultilinearMap.mkContinuous_norm_le
      (tensorMultilinear (μ := μ)) (by norm_num)
      (fun _ => by simp [tensorMultilinear, productVector_norm])
  have hmult := T.norm_image_sub_le v w
  have hmult' : ‖T v - T w‖ ≤
      (d : ℝ) * B^(d-1) * (∑ i : Fin d, δ i) := by
    calc
      ‖T v - T w‖ ≤ ‖T‖ * (d:ℝ) * max ‖v‖ ‖w‖^(d-1) * ‖v-w‖ := by
        simpa [Fintype.card_fin] using hmult
      _ ≤ 1 * (d:ℝ) * B^(d-1) * (∑ i : Fin d, δ i) := by
        have hdR : 0 ≤ (d:ℝ) := by positivity
        have hpowB : 0 ≤ B^(d-1) := pow_nonneg hB _
        have hsumδ : 0 ≤ ∑ i : Fin d, δ i := Finset.sum_nonneg fun i hi => hδ i
        have hmax : max ‖v‖ ‖w‖ ≤ B := max_le hmaxv hmaxw
        gcongr
      _ = (d:ℝ) * B^(d-1) * (∑ i : Fin d, δ i) := by ring
  have hactual : tensorKernelFamily α hα t = productToCube d (T v) := by
    simp [tensorKernelFamily, productKernelFamily, T, v, cubeCoordinate,
      tensorContinuous_apply]
  have hprojected : tensorFrameProjectedKernel e α hα t = productToCube d (T w) := rfl
  rw [hactual, hprojected]
  calc
    ‖productToCube d (T v) - productToCube d (T w)‖ ≤ ‖T v - T w‖ := by
      rw [← map_sub]
      exact productToCube_norm_le d _
    _ ≤ (d:ℝ) * B^(d-1) * ∑ i : Fin d, δ i := hmult'

end BrownianSharp.AlignmentNestedProjectionTensorApproximation
