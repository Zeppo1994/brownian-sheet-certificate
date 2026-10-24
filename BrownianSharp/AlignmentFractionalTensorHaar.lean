import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentGaussianFractionalHaar
import BrownianSharp.AlignmentFractionalHaarProjection
import BrownianSharp.FiniteHaarGeometry
import BrownianSharp.FiniteHaarGradeEnergy
import Mathlib.Tactic

/-! Actual tensor RL coefficients against finite tensor-Haar source vectors.
The finite index carries one father or one normalized mother in each source
coordinate.  This file starts from the actual L² kernel and scalar Haar
features; it does not postulate a tensor coefficient envelope. -/

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
open HaarQuarter
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalTensorHaar

open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentL2TensorProduct
open BrownianSharp.AlignmentGaussianFractionalHaar
open BrownianSharp.AlignmentFractionalHaarProjection
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.CameronMartin
open BrownianSharp

abbrev AxisL2 := AlignmentGaussianFractionalHaar.SourceL2

noncomputable def tensorHaarAxis {N : ℕ} (a : FiniteHaarAxis N) : AxisL2 :=
  sourceHaarFamily N a

noncomputable def tensorHaarSource {d N : ℕ} (a : FiniteHaarIndex d N) : UnitCubeL2 d :=
  productToCube d (productVector (fun i => tensorHaarAxis (a i)))

noncomputable def tensorHaarCoefficient {d N : ℕ}
    (α : Fin d → ℝ) (hα : ∀ i, 1/2 < α i)
    (t : BrownianCubeAnchor d) (a : FiniteHaarIndex d N) : ℝ :=
  inner ℝ (tensorKernelFamily α hα t) (tensorHaarSource a)

private noncomputable def tensorProfileEquiv {d N n : ℕ} (r : Fin d → ℕ)
    (hr : ∑ i : Fin d, r i = n) :
    FiniteHaarProfileFiber (N := N) r ≃
      ((i : Fin d) → {a : FiniteHaarAxis N // finiteHaarAxisGrade a = r i}) where
  toFun a i := ⟨a.1 i, a.2 i⟩
  invFun f := ⟨fun i => (f i).1, fun i => (f i).2⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv f := by
    funext i
    apply Subtype.ext
    rfl

private theorem sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (f : ∀ i, α i → ℝ) :
    (∑ x : (∀ i, α i), ∏ i, f i (x i)) =
      ∏ i, ∑ a : α i, f i a := by
  classical
  simpa using (Finset.prod_univ_sum
    (fun i => (Finset.univ : Finset (α i))) f).symm

theorem fractionalRL_eq_kernel_inner (α : ℝ) (hα : 1/2 < α)
    (g : AxisL2) (t : UnitInterval) :
    fractionalRL α hα g t =
      inner ℝ (kernelVector α t.1 hα
        (Set.mem_Icc.mp t.2).1 (Set.mem_Icc.mp t.2).2) g := by
  change fractionalEvaluation α t.1 hα
    (Set.mem_Icc.mp t.2).1 (Set.mem_Icc.mp t.2).2 g = _
  rw [fractionalEvaluation, evaluationFunctional, innerSL_apply_apply]

/-- Coefficients of the actual tensor RL kernel against a product of the
one-dimensional father/mother Haar sources factor into the scalar RL
coefficients. -/
theorem tensorKernel_inner_tensorHaarSource {d N : ℕ}
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i)
    (t : BrownianCubeAnchor d) (h : FiniteHaarIndex d N) :
    inner ℝ (tensorKernelFamily a ha t) (tensorHaarSource h) =
      ∏ i : Fin d,
        inner ℝ (kernelVector (a i) (t.val i) (ha i)
          (t.property i).1 (t.property i).2) (tensorHaarAxis (h i)) := by
  classical
  change fractionalTensorRL a ha (tensorHaarSource h) t = _
  calc
    fractionalTensorRL a ha (tensorHaarSource h) t =
        ∏ i : Fin d, fractionalRL (a i) (ha i) (tensorHaarAxis (h i))
          (cubeCoordinate i t) := by
      simpa [tensorHaarSource] using
        (fractionalTensorRL_product a ha (fun i => tensorHaarAxis (h i)) t)
    _ = ∏ i : Fin d,
        inner ℝ (kernelVector (a i) (t.val i) (ha i)
          (Set.mem_Icc.mp (t.property i)).1 (Set.mem_Icc.mp (t.property i)).2)
          (tensorHaarAxis (h i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      simpa [fractionalRL_eq_kernel_inner, cubeCoordinate,
        Set.mem_Icc] using
        (fractionalRL_eq_kernel_inner (a i) (ha i) (tensorHaarAxis (h i))
          (cubeCoordinate i t))

/-- In a fixed shifted-grade profile, the sum of squared coefficients of the
actual tensor RL feature factors into the product of the scalar address-band
energies. -/
theorem tensorHaarProfile_energy_eq_product {d N n : ℕ}
    (α : Fin d → ℝ) (hα : ∀ i, 1/2 < α i)
    (t : BrownianCubeAnchor d) (r : Fin d → ℕ)
    (hr : ∑ i : Fin d, r i = n) :
    (∑ a : FiniteHaarProfileFiber (N := N) r,
      tensorHaarCoefficient α hα t a.1 ^ 2) =
      ∏ i : Fin d,
        ∑ a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = r i},
          (inner ℝ (kernelVector (α i) (t.val i) (hα i)
            (Set.mem_Icc.mp (t.property i)).1 (Set.mem_Icc.mp (t.property i)).2)
            (tensorHaarAxis a.1)) ^ 2 := by
  classical
  rw [Fintype.sum_equiv (tensorProfileEquiv r hr)
    (fun a => tensorHaarCoefficient α hα t a.1 ^ 2)
    (fun f => (∏ i : Fin d,
      inner ℝ (kernelVector (α i) (t.val i) (hα i)
        (Set.mem_Icc.mp (t.property i)).1 (Set.mem_Icc.mp (t.property i)).2)
        (tensorHaarAxis (f i).1)) ^ 2)
    (by intro a
        simp [tensorHaarCoefficient, tensorKernel_inner_tensorHaarSource,
          tensorProfileEquiv])]
  have hpow (x : (i : Fin d) → {a : FiniteHaarAxis N // finiteHaarAxisGrade a = r i}) :
      (∏ i : Fin d,
        inner ℝ (kernelVector (α i) (t.val i) (hα i)
          (Set.mem_Icc.mp (t.property i)).1 (Set.mem_Icc.mp (t.property i)).2)
          (tensorHaarAxis (x i).1)) ^ 2 =
      ∏ i : Fin d,
        (inner ℝ (kernelVector (α i) (t.val i) (hα i)
          (Set.mem_Icc.mp (t.property i)).1 (Set.mem_Icc.mp (t.property i)).2)
          (tensorHaarAxis (x i).1)) ^ 2 := by
    simpa using (Finset.prod_pow (Finset.univ : Finset (Fin d)) 2
      (fun i => inner ℝ (kernelVector (α i) (t.val i) (hα i)
        (Set.mem_Icc.mp (t.property i)).1 (Set.mem_Icc.mp (t.property i)).2)
        (tensorHaarAxis (x i).1))).symm
  simp_rw [hpow]
  exact sum_pi_prod (fun (i : Fin d)
      (a : {a : FiniteHaarAxis N // finiteHaarAxisGrade a = r i}) =>
    (inner ℝ (kernelVector (α i) (t.val i) (hα i)
      (Set.mem_Icc.mp (t.property i)).1 (Set.mem_Icc.mp (t.property i)).2)
      (tensorHaarAxis a.1)) ^ 2)

end BrownianSharp.AlignmentFractionalTensorHaar
