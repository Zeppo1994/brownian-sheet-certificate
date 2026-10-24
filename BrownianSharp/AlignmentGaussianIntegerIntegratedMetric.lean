import BrownianSharp.AlignmentFractionalTensorHolder
import BrownianSharp.AlignmentGaussianHilbertFeature
import BrownianSharp.AlignmentFractionalPolynomialWeightedEnergy
import BrownianSharp.AlignmentGaussianGradedFeatureVariance
import BrownianSharp.AlignmentGaussianGradedBudgets
import BrownianSharp.AlignmentFractionalWeightedHaarCounts

/-! Actual feature metric estimates for integer integrated sheets. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianIntegerIntegratedMetric

open HaarQuarter
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalTensorHolder
open BrownianSharp.AlignmentGaussianHilbertFeature
open BrownianSharp.AlignmentGaussianGradedFeatureVariance
open BrownianSharp.AlignmentGaussianDiagonalCoordinates
open BrownianSharp.AlignmentFractionalPolynomialWeightedEnergy
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentNestedProjectionFrame
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalWeightedGrades
open BrownianSharp.AlignmentFractionalWeightedHaarCounts
open BrownianSharp.AlignmentNestedProjectionTensor

private def polynomialFiltration {d : ℕ} (degree : Fin d → ℕ) :
    Fin d → ℕ → Submodule ℝ AlignmentFractionalL2.UnitL2 :=
  fun i n => AlignmentFractionalPolynomialSpaces.piecewisePolynomials (degree i) n

private theorem polynomialFiltration_finite {d : ℕ} (degree : Fin d → ℕ) :
    ∀ i n, FiniteDimensional ℝ ↥(polynomialFiltration degree i n) := by
  intro i n
  exact piecewisePolynomials_finiteDimensional (degree i) n

private theorem polynomialFiltration_nested {d : ℕ} (degree : Fin d → ℕ) :
    ∀ i n, polynomialFiltration degree i n ≤ polynomialFiltration degree i (n+1) := by
  intro i n
  exact piecewisePolynomials_le_succ (degree i) n

theorem polynomialTensor_frame_orthonormal {d M : ℕ}
    (degree : Fin d → ℕ) :
    Orthonormal ℝ (fun a : (∀ i, GradedFrameIndex
      (polynomialFiltration degree i) M) =>
      tensorFrame (fun i => gradedFrame (polynomialFiltration degree i)
        (polynomialFiltration_finite degree i) M) a) := by
  apply tensorFrame_orthonormal
  intro i
  exact gradedFrame_orthonormal (polynomialFiltration degree i)
    (polynomialFiltration_finite degree i)
    (polynomialFiltration_nested degree i) M

/-- For integer integrated orders, the actual tensor feature has squared
L² increments bounded linearly by the anchor distance.  This is the metric
input used by the Gaussian chaining estimate. -/
theorem integerTensorKernel_squared_holder {d : ℕ} (hd : 0 < d)
    (m : Fin d → ℕ) :
    ∃ R : ℝ, 0 < R ∧ ∀ x y : BrownianCubeAnchor d,
      ‖(tensorKernelFamily (fun i => (m i : ℝ) + 1)
          (by intro i; have hm0 : (0:ℝ) ≤ (m i : ℝ) := Nat.cast_nonneg _; linarith)) x -
        (tensorKernelFamily (fun i => (m i : ℝ) + 1)
          (by intro i; have hm0 : (0:ℝ) ≤ (m i : ℝ) := Nat.cast_nonneg _; linarith)) y‖^2 ≤
        R * dist x y := by
  have horders : ∀ i : Fin d, 1/2 < (m i : ℝ) + 1 := by
    intro i
    have hm0 : (0:ℝ) ≤ (m i : ℝ) := Nat.cast_nonneg _
    linarith
  let K := tensorKernelFamily (fun i => (m i : ℝ) + 1) horders
  obtain ⟨C,hC,hholder⟩ := tensorKernelFamily_holder hd
    (fun i => (m i : ℝ)+1) horders 1 (by norm_num)
    (by intro i; have hm0 : (0:ℝ) ≤ (m i : ℝ) := Nat.cast_nonneg _; linarith)
  refine ⟨C^2, by positivity, ?_⟩
  intro x y
  have hdist : 0 ≤ dist x y := dist_nonneg
  have hmod := hholder x y
  have hexp : tensorHolderExponent 1 = (1/2:ℝ) := by
    norm_num [tensorHolderExponent]
  rw [hexp] at hmod
  change ‖K x-K y‖ ≤ C * dist x y ^ (1/2:ℝ) at hmod
  have hnorm : 0 ≤ ‖K x-K y‖ := norm_nonneg _
  have hsqrt : 0 ≤ C * (dist x y)^(1/2:ℝ) := by positivity
  have hroot : ((dist x y)^(1/2:ℝ))^2 = dist x y := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdist]
    norm_num
  have hsq := (sq_le_sq₀ hnorm hsqrt).2 hmod
  rw [mul_pow, hroot] at hsq
  simpa [K] using hsq

/-- The actual polynomially graded tensor coordinates of a tensor RL feature
have the uniform contracted variance bound required by Gaussian chaining.
The coordinate energy and all constants are independent of the depth, grade,
and anchor. -/
theorem polynomialTensor_contracted_variance_bound
    {ν e : ℕ} (hν : 0 < ν) (r : ℝ) (hr : 1/2 < r)
    (α : Fin (ν+e) → ℝ) (hα : ∀ i, 1/2 < α i)
    (hm : Latest.minimumMultiplicity α r ν) :
    ∃ ep : Fin (ν+e) ≃ Fin (ν+e), ∃ w : Fin e → ℝ,
    ∃ degree : Fin (ν+e) → ℕ, ∃ A : Fin (ν+e) → ℝ,
      (∀ j, 1 < w j) ∧ (∀ i, 0 < degree i) ∧ (∀ i, 0 < A i) ∧
      ∃ q C : ℝ, q = Real.rpow 2 (-(2*r-1)) ∧ 0 < q ∧ q < 1 ∧ 0 < C ∧
      ∀ (M N : ℕ) (t : BrownianCubeAnchor (ν+e)) (η : ℝ), η^2=q/2 →
      ∑ a : (∀ i, GradedFrameIndex (polynomialFiltration degree i) M),
        (contractionScale η N
          (weightedProfileGrade α r (profileNat (fun i => (a i).1))) *
          ⟪tensorKernelFamily α hα t,
            tensorFrame (fun i => gradedFrame (polynomialFiltration degree i)
              (polynomialFiltration_finite degree i) M) a⟫)^2 ≤
        C*q^N*((N+1:ℕ):ℝ)^(ν-1) *
          (AlignmentGeometricRanks.polynomialBudget (1/2) 0 +
            AlignmentGeometricRanks.polynomialBudget q (ν-1)) := by
  classical
  obtain ⟨ep,w,degree,A,hw,hactive,hinactive,hdegree,hA,henergy⟩ :=
    polynomialTensor_weightedGrade_energy_le hν r hr α hα hm
  let q : ℝ := Real.rpow 2 (-(2*r-1))
  let inactiveFactor : ℝ :=
    ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹
  let Aprod : ℝ := ∏ i : Fin (ν+e), A i
  let C : ℝ := Aprod * inactiveFactor
  have hq0 : 0 < q := by
    dsimp [q]
    exact Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _
  have hq1 : q < 1 := by
    dsimp [q]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have : 0 < 2*r-1 := by linarith
    linarith
  have hfactor (j : Fin e) : 0 < (1-Real.rpow 2 (-(w j-1)))⁻¹ := by
    have hwneg : -(w j-1) < 0 := by linarith [hw j]
    have hpowpos : 0 < Real.rpow 2 (-(w j-1)) :=
      Real.rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _
    have hpowlt : Real.rpow 2 (-(w j-1)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hwneg
    apply inv_pos.mpr
    linarith
  have hAprod : 0 < Aprod := by
    dsimp [Aprod]
    exact Finset.prod_pos fun i hi => hA i
  have hC : 0 < C := by
    dsimp [C, inactiveFactor]
    exact mul_pos hAprod (Finset.prod_pos fun j hj => hfactor j)
  refine ⟨ep,w,degree,A,hw,hdegree,hA,q,C,rfl,hq0,hq1,hC,?_⟩
  intro M N t η hη
  let U : Fin (ν+e) → ℕ → Submodule ℝ AlignmentFractionalL2.UnitL2 :=
    polynomialFiltration degree
  let I : Type := ∀ i, GradedFrameIndex (U i) M
  let grade : I → ℕ := fun a =>
    weightedProfileGrade α r (profileNat (fun i => (a i).1))
  let frame : I → CameronMartin.UnitCubeL2 (ν+e) := fun a =>
    tensorFrame (fun i => gradedFrame (U i)
      (polynomialFiltration_finite degree i) M) a
  let coeff : I → ℝ := fun a => ⟪tensorKernelFamily α hα t, frame a⟫
  have henergy' (g : ℕ) :
      (∑ a : {a : I // grade a = g}, (coeff a.val)^2) ≤
        C * (((g+1:ℕ):ℝ)^(ν-1)) * q^g := by
    have h := henergy M g t
    have hqpow : q^g = Real.rpow 2 (-(2*r-1)*(g:ℝ)) := by
      dsimp [q]
      calc
        (Real.rpow 2 (-(2*r-1)))^g =
            (Real.rpow 2 (-(2*r-1)))^(g:ℝ) := (Real.rpow_natCast _ _).symm
        _ = Real.rpow 2 (-(2*r-1)*(g:ℝ)) :=
          (Real.rpow_mul (by norm_num : (0:ℝ)≤2) _ _).symm
    have hfactor_nonneg : 0 ≤ inactiveFactor := le_of_lt (Finset.prod_pos
      fun j hj => hfactor j)
    have hAprod_nonneg : 0 ≤ Aprod := le_of_lt hAprod
    have hpoly : 0 ≤ (((g+1:ℕ):ℝ)^(ν-1)) := by positivity
    have hqpow_nonneg : 0 ≤ q^g := pow_nonneg hq0.le _
    have hrewrite :
        Aprod * (Real.rpow 2 (-(2*r-1)*(g:ℝ)) *
          ((((g+1:ℕ):ℝ)^(ν-1)) * inactiveFactor)) =
        C * (((g+1:ℕ):ℝ)^(ν-1)) * q^g := by
      dsimp [C]
      calc
        Aprod * ((2:ℝ)^(-(2*r-1)*(g:ℝ)) *
            ((((g+1:ℕ):ℝ)^(ν-1)) * inactiveFactor)) =
          Aprod * (Real.rpow 2 (-(2*r-1)*(g:ℝ)) *
            ((((g+1:ℕ):ℝ)^(ν-1)) * inactiveFactor)) := by rfl
        _ = Aprod * (q^g *
            ((((g+1:ℕ):ℝ)^(ν-1)) * inactiveFactor)) := by rw [← hqpow]
        _ = Aprod * inactiveFactor * (((g+1:ℕ):ℝ)^(ν-1)) * q^g := by ring
    calc
      _ = (∑ a : {a : ∀ i, GradedFrameIndex
            (polynomialFiltration degree i) M //
            weightedProfileGrade α r (profileNat (fun i => (a i).1)) = g},
          ⟪tensorKernelFamily α hα t,
            tensorFrame (fun i => gradedFrame (polynomialFiltration degree i)
              (polynomialFiltration_finite degree i) M) a.1⟫^2) := by
            simp [I, U, grade, coeff, frame]
      _ ≤ Aprod * (Real.rpow 2 (-(2*r-1)*g) *
            ((((g+1:ℕ):ℝ)^(ν-1)) * inactiveFactor)) := h
      _ = C * (((g+1:ℕ):ℝ)^(ν-1)) * q^g := hrewrite
  have hvar := graded_contracted_square_sum_le_uniform
    grade coeff hq0 hq1 hη (le_of_lt hC) (ν-1) N henergy'
  simpa [I, grade, coeff, frame, U, mul_assoc, mul_left_comm, mul_comm] using hvar

end BrownianSharp.AlignmentGaussianIntegerIntegratedMetric
