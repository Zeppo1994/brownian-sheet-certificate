import BrownianSharp.AlignmentFractionalTensorHaar
import BrownianSharp.AlignmentFractionalTensor
import BrownianSharp.AlignmentFractionalHaarProjection
import Mathlib.Tactic

/-! Orthogonality of the actual tensor Haar family in the cube source L². -/

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalTensorOrthogonal

open BrownianSharp
open BrownianSharp.AlignmentFractionalTensorHaar
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentL2TensorProduct
open BrownianSharp.AlignmentFractionalHaarProjection

/-- The product source Haar family remains orthonormal after identifying the
product interval with the manuscript's unit-cube source measure. -/
theorem tensorHaarSource_inner {d N : ℕ}
    (a b : FiniteHaarIndex d N) :
    ⟪tensorHaarSource a, tensorHaarSource b⟫ =
      ∏ i : Fin d, ⟪tensorHaarAxis (a i), tensorHaarAxis (b i)⟫ := by
  classical
  rw [MeasureTheory.L2.inner_def]
  let va : Fin d → AxisL2 := fun i => tensorHaarAxis (a i)
  let vb : Fin d → AxisL2 := fun i => tensorHaarAxis (b i)
  have haeA : productToCube d (productVector va) =ᵐ[
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet d)]
      (fun u => ∏ i, va i (u i)) := by
    have hPV := productVector_ae va
    have hPV' : productVector va =ᵐ[
        (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
          (CameronMartin.unitCubeSet d)] (fun u => ∏ i, va i (u i)) := by
      simpa only [BrownianSharp.AlignmentFractionalTensor.unitCube_measure_eq_pi]
        using hPV
    exact (productToCube_ae (productVector va)).trans hPV'
  have haeB : productToCube d (productVector vb) =ᵐ[
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet d)]
      (fun u => ∏ i, vb i (u i)) := by
    have hPV := productVector_ae vb
    have hPV' : productVector vb =ᵐ[
        (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
          (CameronMartin.unitCubeSet d)] (fun u => ∏ i, vb i (u i)) := by
      simpa only [BrownianSharp.AlignmentFractionalTensor.unitCube_measure_eq_pi]
        using hPV
    exact (productToCube_ae (productVector vb)).trans hPV'
  have hprod := MeasureTheory.integral_fintype_prod_eq_prod
    (μ := fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1))
    (fun i u => va i u * vb i u)
  have hfun : (fun u : Fin d → ℝ =>
      (∏ i : Fin d, va i (u i)) * (∏ i : Fin d, vb i (u i))) =
      fun u => ∏ i : Fin d, va i (u i) * vb i (u i) := by
    funext u
    rw [← Finset.prod_mul_distrib]
  calc
    _ = ∫ u, (∏ i : Fin d, va i (u i)) * (∏ i : Fin d, vb i (u i))
          ∂((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
            (CameronMartin.unitCubeSet d)) := by
      apply integral_congr_ae
      filter_upwards [haeA, haeB] with u hu hv
      simp [tensorHaarSource, va, vb, hu, hv]
      ring
    _ = ∫ u, ∏ i : Fin d, va i (u i) * vb i (u i)
          ∂Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1)) := by
      rw [hfun, BrownianSharp.AlignmentFractionalTensor.unitCube_measure_eq_pi]
    _ = ∏ i : Fin d, ∫ u, va i u * vb i u
          ∂volume.restrict (Set.Icc (0:ℝ) 1) := hprod
    _ = ∏ i : Fin d, ⟪va i, vb i⟫ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards with u
      rw [Real.inner_apply]

/-- The tensor Haar feature family is orthonormal in the exact source space
used by the fractional Riemann--Liouville operator. -/
theorem tensorHaarSource_orthonormal {d N : ℕ} :
    Orthonormal ℝ (tensorHaarSource (d:=d) (N:=N)) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  rw [tensorHaarSource_inner]
  have haxis := sourceHaarFamily_orthonormal N
  have hcoord (i : Fin d) :
      ⟪tensorHaarAxis (a i), tensorHaarAxis (b i)⟫ =
        if a i = b i then 1 else 0 := by
    simpa [tensorHaarAxis, sourceHaarFamily]
      using (orthonormal_iff_ite.mp haxis) (a i) (b i)
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

end BrownianSharp.AlignmentFractionalTensorOrthogonal
