import BrownianSharp.AlignmentGaussianIntegerIntegratedMetric
import BrownianSharp.AlignmentGaussianGradedHalfMass
import BrownianSharp.AlignmentGaussianGradedDilationCost
import BrownianSharp.AlignmentFractionalGradedPolynomialFeature
import BrownianSharp.AlignmentGaussianIntegratedSourceModel
import Mathlib.Tactic

/-! Finite-grid reverse small-ball bounds for actual integer-integrated sheets. -/

noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianIntegratedHalfMass

open HaarQuarter
open BrownianSharp.AlignmentGaussianIntegerIntegratedMetric
open BrownianSharp.AlignmentGaussianHilbertFeature
open BrownianSharp.AlignmentGaussianGradedHalfMass
open BrownianSharp.AlignmentGaussianGradedDilationCost
open BrownianSharp.AlignmentGaussianDiagonalCoordinates
open BrownianSharp.AlignmentGaussianIntegratedSourceModel
open BrownianSharp.AlignmentGaussianFiniteFeature
open BrownianSharp.AlignmentFractionalGradedPolynomialFeature
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentNestedProjectionFrame
open BrownianSharp.AlignmentNestedProjectionTensor
open BrownianSharp.AlignmentFractionalTensorHolder
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalWeightedGrades
open BrownianSharp.AlignmentFractionalWeightedHaarCounts
open BrownianSharp.CameronMartin

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

private def polynomialTensorFrame {d M : ℕ} (degree : Fin d → ℕ) :
    (∀ i, GradedFrameIndex (polynomialFiltration degree i) M) → UnitCubeL2 d :=
  fun a => tensorFrame (fun i => gradedFrame (polynomialFiltration degree i)
    (polynomialFiltration_finite degree i) M) a

private theorem polynomialTensorFrame_orthonormal {d M : ℕ}
    (degree : Fin d → ℕ) :
    Orthonormal ℝ (polynomialTensorFrame (d:=d) (M:=M) degree) := by
  apply tensorFrame_orthonormal
  intro i
  exact gradedFrame_orthonormal (polynomialFiltration degree i)
    (polynomialFiltration_finite degree i)
    (polynomialFiltration_nested degree i) M

private theorem rpow_dyadic_rate_sq (β : ℝ) (N : ℕ) :
    (Real.rpow 2 (-β * (N : ℝ) / 2))^2 =
      (Real.rpow 2 (-β))^N := by
  calc
    (Real.rpow 2 (-β * (N : ℝ) / 2))^2 =
        Real.rpow 2 ((-β * (N : ℝ) / 2) * 2) := by
          calc
            _ = Real.rpow (Real.rpow 2 (-β * (N : ℝ) / 2)) (2:ℝ) :=
              (Real.rpow_natCast _ _).symm
            _ = _ := (Real.rpow_mul (by norm_num : (0:ℝ)≤2)
              (-β*(N:ℝ)/2) 2).symm
    _ = Real.rpow 2 (-β * (N : ℝ)) := by congr 1 <;> ring
    _ = (Real.rpow 2 (-β))^N := by
      calc
        Real.rpow 2 (-β*(N:ℝ)) = Real.rpow (Real.rpow 2 (-β)) (N:ℝ) :=
          Real.rpow_mul (by norm_num : (0:ℝ)≤2) (-β) (N:ℝ)
        _ = (Real.rpow 2 (-β))^N := Real.rpow_natCast _ _

/-- The diagonal contraction of the actual integrated RL feature has a
uniform half-mass bound.  The source frame is the genuine tensor polynomial
frame, and the constants are independent of its truncation depth. -/
theorem integerIntegrated_polynomial_frame_half_mass
    {ν e : ℕ} (hν : 0 < ν) (m₀ : ℕ)
    (m : Fin (ν+e) → ℕ)
    (hm : Latest.minimumMultiplicity (fun i => (m i : ℝ) + 1)
      ((m₀ : ℝ) + 1) ν) :
    ∃ degree : Fin (ν+e) → ℕ, ∃ C A : ℝ,
      (∀ i, 0 < degree i) ∧ 0 < C ∧ 0 < A ∧
      ∀ (M N : ℕ),
        let d := ν+e
        let α : Fin d → ℝ := fun i => (m i : ℝ)+1
        let r : ℝ := (m₀:ℝ)+1
        let β : ℝ := 2*r-1
        let q : ℝ := Real.rpow 2 (-β)
        let U := polynomialFiltration degree
        let I := ∀ i : Fin d, GradedFrameIndex (U i) M
        let frame : I → UnitCubeL2 d := polynomialTensorFrame (d:=d) (M:=M) degree
        let grade : I → ℕ := fun a =>
          weightedProfileGrade α r (profileNat (fun i => (a i).1))
        let K : C(BrownianCubeAnchor d, UnitCubeL2 d) :=
          tensorKernelFamily α (by
            intro i
            have hm0 : (0:ℝ) ≤ (m i:ℝ) := Nat.cast_nonneg _
            dsimp [α]
            linarith)
        (1/2:ℝ≥0∞) ≤ productStandardGaussian I
          {z | ‖finiteGaussianFeaturePath
            (diagonalFeature K frame (fun a => contractionScale
              (Real.sqrt (q/2)) N (grade a))) z‖ ≤
            A * Real.rpow 2 (-β*(N:ℝ)/2) *
              Real.sqrt (((N+1:ℕ):ℝ)^ν)} := by
  classical
  let d : ℕ := ν+e
  let α : Fin d → ℝ := fun i => (m i : ℝ)+1
  let r : ℝ := (m₀:ℝ)+1
  let β : ℝ := 2*r-1
  let q : ℝ := Real.rpow 2 (-β)
  have hr : 1/2 < r := by
    dsimp [r]
    have hm0 : (0:ℝ)≤(m₀:ℝ) := Nat.cast_nonneg _
    linarith
  have hβ : 0 < β := by
    dsimp [β,r]
    have hm0 : (0:ℝ)≤(m₀:ℝ) := Nat.cast_nonneg _
    linarith
  have hα : ∀ i, 1/2 < α i := by
    intro i
    dsimp [α]
    have hm0 : (0:ℝ) ≤ (m i:ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨ep,w,degree,A₀,hw,hdegree,hA₀,q₀,C₀,hqdef,hq0,hq1,hC₀,hvar⟩ :=
    polynomialTensor_contracted_variance_bound hν r hr α hα hm
  have hq : q = q₀ := by
    change Real.rpow 2 (-(2*r-1)) = q₀
    exact hqdef.symm
  let Budget := AlignmentGeometricRanks.polynomialBudget (1/2) 0 +
      AlignmentGeometricRanks.polynomialBudget q₀ (ν-1)
  let Cmetric := C₀ * (Budget+1)
  have hCmetric : 0 < Cmetric := by
    dsimp [Cmetric, Budget]
    have hbudget0 : 0 ≤ AlignmentGeometricRanks.polynomialBudget (1/2) 0 :=
      AlignmentGeometricRanks.polynomialBudget_nonneg (by norm_num) 0
    have hbudgetq : 0 ≤ AlignmentGeometricRanks.polynomialBudget q₀ (ν-1) :=
      AlignmentGeometricRanks.polynomialBudget_nonneg hq0.le _
    exact mul_pos hC₀ (by linarith)
  let βval := β
  let R := Classical.choose (integerTensorKernel_squared_holder (by omega) m)
  have hR : 0 < R := (Classical.choose_spec
    (integerTensorKernel_squared_holder (by omega) m)).1
  obtain ⟨A,hA,hhalf⟩ := finiteGaussianFeaturePath_half_mass_of_graded_variance
    (d:=d) βval Cmetric R (ν-1) hβ hCmetric.le hR.le
  refine ⟨degree,Cmetric,A,hdegree,hCmetric,hA,?_⟩
  intro M N
  let U : Fin d → ℕ → Submodule ℝ AlignmentFractionalL2.UnitL2 :=
    polynomialFiltration degree
  let I : Type := ∀ i : Fin d, GradedFrameIndex (U i) M
  let frame : I → UnitCubeL2 d := polynomialTensorFrame (d:=d) (M:=M) degree
  let grade : I → ℕ := fun a =>
    weightedProfileGrade α r (profileNat (fun i => (a i).1))
  let scale : I → ℝ := fun a => contractionScale (Real.sqrt (q₀/2)) N (grade a)
  let K : C(BrownianCubeAnchor d, UnitCubeL2 d) := tensorKernelFamily α hα
  have hη0 : 0 ≤ Real.sqrt (q₀/2) := Real.sqrt_nonneg _
  have hη1 : Real.sqrt (q₀/2) ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    have hqdiv : q₀/2 < 1 := by linarith [hq1]
    linarith
  have hscale : ∀ a : I, |scale a| ≤ 1 := by
    intro a
    exact contractionScale_abs_le_one hη0 hη1 N (grade a)
  have hmetric : ∀ x y : BrownianCubeAnchor d, ‖K x-K y‖^2 ≤ R*dist x y := by
    intro x y
    exact (Classical.choose_spec
      (integerTensorKernel_squared_holder (by omega) m)).2 x y
  let rate : ℝ := Real.rpow 2 (-βval*(N:ℝ)/2)
  have hrate_sq : rate^2 = q₀^N := by
    change (Real.rpow 2 (-βval*(N:ℝ)/2))^2 = q₀^N
    rw [rpow_dyadic_rate_sq βval N, hqdef]
  have hvar' : ∀ x : BrownianCubeAnchor d,
      ∑ a : I, (diagonalFeature K frame scale a x)^2 ≤
        Cmetric * rate^2 * (((N+1:ℕ):ℝ)^(ν-1)) := by
    intro x
    have h := hvar M N x (Real.sqrt (q₀/2))
      (Real.sq_sqrt (show 0 ≤ q₀/2 by positivity))
    rw [hrate_sq]
    have hbudget0 : 0 ≤ AlignmentGeometricRanks.polynomialBudget (1/2) 0 :=
      AlignmentGeometricRanks.polynomialBudget_nonneg (by norm_num) 0
    have hbudgetq : 0 ≤ AlignmentGeometricRanks.polynomialBudget q₀ (ν-1) :=
      AlignmentGeometricRanks.polynomialBudget_nonneg hq0.le _
    have hB : 0 ≤ Budget := by dsimp [Budget]; linarith
    have hbase : 0 ≤ (((N+1:ℕ):ℝ)^(ν-1)) := by positivity
    have hbound :
        C₀*q₀^N*(((N+1:ℕ):ℝ)^(ν-1))*Budget ≤
          Cmetric*q₀^N*(((N+1:ℕ):ℝ)^(ν-1)) := by
      have hqpow : 0 ≤ q₀^N := pow_nonneg hq0.le _
      calc
        C₀*q₀^N*(((N+1:ℕ):ℝ)^(ν-1))*Budget ≤
            C₀*q₀^N*(((N+1:ℕ):ℝ)^(ν-1))*(Budget+1) := by
              have hcoef : 0 ≤ C₀*q₀^N*(((N+1:ℕ):ℝ)^(ν-1)) := by positivity
              exact mul_le_mul_of_nonneg_left (by linarith) hcoef
        _ = Cmetric*q₀^N*(((N+1:ℕ):ℝ)^(ν-1)) := by
              dsimp [Cmetric]
              ring
    have h' : ‖diagonalCoordinates frame scale (K x)‖^2 ≤
        Cmetric*q₀^N*(((N+1:ℕ):ℝ)^(ν-1)) := by
      rw [← diagonalFeature_square_sum]
      exact h.trans hbound
    simpa only [diagonalFeature_square_sum, Cmetric, Budget] using h'
  have hincrement : ∀ x y : BrownianCubeAnchor d,
      ∑ a : I, (diagonalFeature K frame scale a x-
        diagonalFeature K frame scale a y)^2 ≤ R*dist x y := by
    intro x y
    exact diagonalFeature_increment_square_sum_le K frame
      (polynomialTensorFrame_orthonormal degree) scale hscale R hmetric x y
  have hh := hhalf (ι:=I) N (diagonalFeature K frame scale) hvar' hincrement
  have hpow : (ν-1)+1=ν := by omega
  dsimp [scale] at hh
  rw [hqdef] at hh
  simpa [I,U,frame,grade,scale,K,polynomialTensorFrame,polynomialFiltration,
    βval,rate,hpow,β,r,α,d] using hh

end BrownianSharp.AlignmentGaussianIntegratedHalfMass
