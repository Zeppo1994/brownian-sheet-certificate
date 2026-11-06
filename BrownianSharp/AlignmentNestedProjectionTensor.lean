import BrownianSharp.AlignmentNestedProjectionEnergy
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentFractionalTensorHaar
import Mathlib.Tactic

/-! Tensor products of arbitrary finite source frames for the fractional
Riemann--Liouville operator. This generalizes the concrete Haar tensor proofs
to coordinate-dependent orthonormal families. -/

noncomputable section
open MeasureTheory
open HaarQuarter
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentNestedProjectionTensor

open BrownianSharp
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentL2TensorProduct
open BrownianSharp.AlignmentFractionalTensorHaar
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalTensor
open BrownianSharp.CameronMartin
open BrownianSharp.AlignmentNestedProjectionBasis
open BrownianSharp.AlignmentNestedProjectionFrame

abbrev AxisL2 := AlignmentFractionalL2.UnitL2

/-- The tensor of arbitrary coordinate source vectors in the actual cube
source space used by the manuscript. -/
def tensorSource {d : ℕ} (v : Fin d → AxisL2) : UnitCubeL2 d :=
  productToCube d (productVector v)

/-- Tensor a coordinate-dependent family of finite source vectors. -/
def tensorFrame {d : ℕ} {I : Fin d → Type*} [∀ i, Fintype (I i)]
    (e : ∀ i, I i → AxisL2) (a : ∀ i, I i) : UnitCubeL2 d :=
  tensorSource (fun i => e i (a i))

instance tensorFrame_span_finiteDimensional {d : ℕ} {I : Fin d → Type*}
    [∀ i, Fintype (I i)] (e : ∀ i, I i → AxisL2) :
    FiniteDimensional ℝ ↥(Submodule.span ℝ (Set.range (tensorFrame e))) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range (tensorFrame e))

/-- The actual cube-source inner product of elementary tensors factors into
the product of the one-dimensional inner products. -/
theorem tensorSource_inner {d : ℕ} (v w : Fin d → AxisL2) :
    ⟪tensorSource v, tensorSource w⟫ = ∏ i : Fin d, ⟪v i, w i⟫ := by
  classical
  rw [MeasureTheory.L2.inner_def]
  have haeA := cube_productVector_ae v
  have haeB := cube_productVector_ae w
  have hprod := MeasureTheory.integral_fintype_prod_eq_prod
    (μ := fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))
    (fun i u => v i u * w i u)
  have hfun : (fun u : Fin d → ℝ =>
      (∏ i : Fin d, v i (u i)) * (∏ i : Fin d, w i (u i))) =
      fun u => ∏ i : Fin d, v i (u i) * w i (u i) := by
    funext u
    rw [← Finset.prod_mul_distrib]
  calc
    _ = ∫ u, (∏ i : Fin d, v i (u i)) * (∏ i : Fin d, w i (u i))
          ∂((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
            (CameronMartin.unitCubeSet d)) := by
      apply integral_congr_ae
      filter_upwards [haeA, haeB] with u hu hw
      simp [tensorSource, hu, hw]
      ring
    _ = ∫ u, ∏ i : Fin d, v i (u i) * w i (u i)
          ∂Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1)) := by
      rw [hfun, unitCube_measure_eq_pi]
    _ = ∏ i : Fin d, ∫ u, v i u * w i u
          ∂volume.restrict (Set.Icc (0:ℝ) 1) := hprod
    _ = ∏ i : Fin d, ⟪v i, w i⟫ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards with u
      rw [Real.inner_apply]

theorem tensorFrame_inner {d : ℕ} {I : Fin d → Type*} [∀ i, Fintype (I i)]
    (e : ∀ i, I i → AxisL2) (a b : ∀ i, I i) :
    ⟪tensorFrame e a, tensorFrame e b⟫ =
      ∏ i : Fin d, ⟪e i (a i), e i (b i)⟫ := by
  exact tensorSource_inner _ _

/-- Coordinatewise orthonormal families tensorize in the exact cube source
Hilbert space. -/
theorem tensorFrame_orthonormal {d : ℕ} {I : Fin d → Type*}
    [∀ i, Fintype (I i)] (e : ∀ i, I i → AxisL2)
    (he : ∀ i, Orthonormal ℝ (e i)) :
    Orthonormal ℝ (tensorFrame e) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  rw [tensorFrame_inner]
  have hcoord (i : Fin d) :
      ⟪e i (a i), e i (b i)⟫ = if a i = b i then 1 else 0 :=
    (orthonormal_iff_ite.mp (he i)) (a i) (b i)
  simp_rw [hcoord]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    have hne : ∃ i : Fin d, a i ≠ b i := by
      by_contra hn
      push_neg at hn
      apply hab
      funext i
      exact hn i
    obtain ⟨i, hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Exact scalar coefficient factorization for the actual tensor RL kernel and
an arbitrary product source vector. -/
theorem tensorKernel_inner_source {d : ℕ} (α : Fin d → ℝ)
    (hα : ∀ i, 1/2 < α i) (t : BrownianCubeAnchor d)
    (v : Fin d → AxisL2) :
    ⟪tensorKernelFamily α hα t, tensorSource v⟫ =
      ∏ i : Fin d,
        ⟪kernelVector (α i) (t.val i) (hα i)
          (Set.mem_Icc.mp (t.property i)).1
          (Set.mem_Icc.mp (t.property i)).2, v i⟫ := by
  classical
  change fractionalTensorRL α hα (productToCube d (productVector v)) t = _
  rw [fractionalTensorRL_product α hα v t]
  apply Finset.prod_congr rfl
  intro i hi
  simpa [cubeCoordinate, Set.mem_Icc] using
    (fractionalRL_eq_kernel_inner (α i) (hα i) (v i) (cubeCoordinate i t))

theorem tensorKernel_inner_frame {d : ℕ} {I : Fin d → Type*}
    [∀ i, Fintype (I i)] (α : Fin d → ℝ) (hα : ∀ i, 1/2 < α i)
    (t : BrownianCubeAnchor d) (e : ∀ i, I i → AxisL2)
    (a : ∀ i, I i) :
    ⟪tensorKernelFamily α hα t, tensorFrame e a⟫ =
      ∏ i : Fin d,
        ⟪kernelVector (α i) (t.val i) (hα i)
          (Set.mem_Icc.mp (t.property i)).1
          (Set.mem_Icc.mp (t.property i)).2, e i (a i)⟫ := by
  exact tensorKernel_inner_source α hα t (fun i => e i (a i))

/-- Finite sums over product-profile fibers factor exactly. This is the
coordinatewise grade-energy identity used with nested polynomial increments. -/
theorem sum_pi_prod_sq {d : ℕ} (J : Fin d → Type*) [∀ i, Fintype (J i)]
    (c : ∀ i, J i → ℝ) :
    (∑ x : (∀ i, J i), (∏ i, c i (x i)) ^ 2) =
      ∏ i : Fin d, ∑ j : J i, c i j ^ 2 := by
  classical
  have hpow (x : (∀ i, J i)) :
      (∏ i : Fin d, c i (x i)) ^ 2 = ∏ i : Fin d, c i (x i) ^ 2 := by
    simpa using (Finset.prod_pow (Finset.univ : Finset (Fin d)) 2
      (fun i => c i (x i))).symm
  simp_rw [hpow]
  simpa using (Finset.prod_univ_sum
    (fun i => (Finset.univ : Finset (J i))) (fun i j => c i j ^ 2)).symm

/-- Exact product-profile energy for the actual RL kernel coefficients of a
coordinatewise tensor frame. The `J i` types can be exact-grade fibers. -/
theorem tensorKernel_profile_energy_eq_product {d : ℕ}
    {I J : Fin d → Type*} [∀ i, Fintype (I i)] [∀ i, Fintype (J i)]
    (embed : ∀ i, J i → I i) (e : ∀ i, I i → AxisL2)
    (α : Fin d → ℝ) (hα : ∀ i, 1/2 < α i) (t : BrownianCubeAnchor d) :
    (∑ x : (∀ i, J i),
      ⟪tensorKernelFamily α hα t,
        tensorFrame e (fun i => embed i (x i))⟫ ^ 2) =
      ∏ i : Fin d, ∑ j : J i,
        ⟪kernelVector (α i) (t.val i) (hα i)
          (Set.mem_Icc.mp (t.property i)).1
          (Set.mem_Icc.mp (t.property i)).2,
          e i (embed i j)⟫ ^ 2 := by
  classical
  calc
    _ = ∑ x : (∀ i, J i),
        (∏ i : Fin d,
          ⟪kernelVector (α i) (t.val i) (hα i)
            (Set.mem_Icc.mp (t.property i)).1
            (Set.mem_Icc.mp (t.property i)).2, e i (embed i (x i))⟫) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [tensorKernel_inner_frame]
    _ = ∏ i : Fin d, ∑ j : J i,
        ⟪kernelVector (α i) (t.val i) (hα i)
          (Set.mem_Icc.mp (t.property i)).1
          (Set.mem_Icc.mp (t.property i)).2, e i (embed i j)⟫ ^ 2 :=
          sum_pi_prod_sq J (fun i j =>
            ⟪kernelVector (α i) (t.val i) (hα i)
              (Set.mem_Icc.mp (t.property i)).1
              (Set.mem_Icc.mp (t.property i)).2, e i (embed i j)⟫)

end BrownianSharp.AlignmentNestedProjectionTensor
