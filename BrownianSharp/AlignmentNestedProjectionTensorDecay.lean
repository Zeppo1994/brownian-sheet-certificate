import BrownianSharp.AlignmentNestedProjectionTensor
import BrownianSharp.AlignmentNestedProjectionGrades
import BrownianSharp.AlignmentNestedProjectionDecay
import Mathlib.Tactic

/-! Exact product-profile energy bounds for tensor products of arbitrary
finite nested one-dimensional frames. The scalar decay input is supplied by
the actual one-coordinate projection residual estimate, while this module
performs only the tensorization. -/

noncomputable section
set_option maxHeartbeats 500000
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentNestedProjectionTensorDecay

open BrownianSharp
open HaarQuarter
open BrownianSharp.AlignmentNestedProjectionTensor
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentNestedProjectionFrame
open BrownianSharp.AlignmentNestedProjectionBasis
open BrownianSharp.AlignmentNestedProjectionDecay
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalTensorHaar
open BrownianSharp.AlignmentFractionalL2

theorem tensorKernel_gradeProfile_energy_le {d M : ℕ}
    (U : Fin d → ℕ → Submodule ℝ AlignmentNestedProjectionTensor.AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1))
    (α : Fin d → ℝ) (hα : ∀ i, 1/2 < α i)
    (t : BrownianCubeAnchor d)
    (C q : Fin d → ℝ) (hC : ∀ i, 0 ≤ C i) (hq : ∀ i, 0 ≤ q i)
    (haxis : ∀ i (g : ℕ),
      (∑ j : GradeIndex (U i) g,
        ⟪kernelVector (α i) (t.val i) (hα i)
          (Set.mem_Icc.mp (t.property i)).1
          (Set.mem_Icc.mp (t.property i)).2,
          gradeFamily (U i) (hfinite i) g j⟫ ^ 2) ≤ C i * q i ^ g)
    (s : Fin d → Fin (M+1)) :
    (∑ a : (∀ i, GradeIndex (U i) (s i).val),
      ⟪tensorKernelFamily α hα t,
        tensorFrame
          (fun i => gradedFrame (U i) (hfinite i) M)
          (fun i => (⟨s i, a i⟩ : GradedFrameIndex (U i) M))⟫ ^ 2) ≤
      ∏ i : Fin d, C i * q i ^ (s i).val := by
  classical
  let I : Fin d → Type := fun i => GradedFrameIndex (U i) M
  let J : Fin d → Type := fun i => GradeIndex (U i) (s i).val
  let emb : ∀ i, J i → I i := fun i j => ⟨s i, j⟩
  let frame : ∀ i, I i → AlignmentNestedProjectionTensor.AxisL2 :=
    fun i a => gradedFrame (U i) (hfinite i) M a
  have hfactor := tensorKernel_profile_energy_eq_product
    (embed := emb) (e := frame) α hα t
  change (∑ a : (∀ i, J i),
      ⟪tensorKernelFamily α hα t,
        tensorFrame frame (fun i => emb i (a i))⟫ ^ 2) ≤ _
  rw [hfactor]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.sum_nonneg fun j hj => sq_nonneg
      (⟪kernelVector (α i) (t.val i) (hα i)
        (Set.mem_Icc.mp (t.property i)).1
        (Set.mem_Icc.mp (t.property i)).2,
        frame i (emb i j)⟫)
  · intro i hi
    simpa [J, emb, frame, gradedFrame] using haxis i (s i).val

/-- Actual tensor-kernel profile energy from coordinatewise projection-tail
estimates. The one-dimensional geometric envelopes are derived from the
father norm and the residual of the genuine nested orthogonal projections;
they are not assumptions on the tensor kernel itself. -/
theorem tensorKernel_gradeProfile_energy_le_of_projection_residual
    {d M : ℕ}
    (U : Fin d → ℕ → Submodule ℝ AlignmentNestedProjectionTensor.AxisL2)
    (hfinite : ∀ i n, FiniteDimensional ℝ ↥(U i n))
    (hnested : ∀ i n, U i n ≤ U i (n+1))
    (α : Fin d → ℝ) (hα : ∀ i, 1/2 < α i)
    (t : BrownianCubeAnchor d)
    (C₀ C q : Fin d → ℝ)
    (hC₀ : ∀ i, 0 ≤ C₀ i) (hC : ∀ i, 0 ≤ C i)
    (hq : ∀ i, 0 < q i)
    (hfather : ∀ i,
      ‖kernelVector (α i) (t.val i) (hα i)
        (Set.mem_Icc.mp (t.property i)).1
        (Set.mem_Icc.mp (t.property i)).2‖ ^ 2 ≤ C₀ i)
    (hres : ∀ i n,
      ‖kernelVector (α i) (t.val i) (hα i)
          (Set.mem_Icc.mp (t.property i)).1
          (Set.mem_Icc.mp (t.property i)).2 -
        (U i n).starProjection
          (kernelVector (α i) (t.val i) (hα i)
            (Set.mem_Icc.mp (t.property i)).1
            (Set.mem_Icc.mp (t.property i)).2)‖ ^ 2 ≤ C i * q i ^ n)
    (s : Fin d → Fin (M+1)) :
    (∑ a : (∀ i, GradeIndex (U i) (s i).val),
      ⟪tensorKernelFamily α hα t,
        tensorFrame
          (fun i => gradedFrame (U i) (hfinite i) M)
          (fun i => (⟨s i, a i⟩ : GradedFrameIndex (U i) M))⟫ ^ 2) ≤
      ∏ i : Fin d, (C₀ i + C i / q i) * q i ^ (s i).val := by
  classical
  apply tensorKernel_gradeProfile_energy_le U hfinite hnested α hα t
    (fun i => C₀ i + C i / q i) q
  · intro i
    exact add_nonneg (hC₀ i) (div_nonneg (hC i) (hq i).le)
  · intro i
    exact (hq i).le
  · intro i g
    have hscalar := gradeFamily_energy_le_geometric
      (U i) (hfinite i) (kernelVector (α i) (t.val i) (hα i)
        (Set.mem_Icc.mp (t.property i)).1
        (Set.mem_Icc.mp (t.property i)).2)
      (C₀ i) (C i) (q i) (hC₀ i) (hC i) (hq i)
      (hfather i) (hres i)
    simpa using hscalar g

end BrownianSharp.AlignmentNestedProjectionTensorDecay
