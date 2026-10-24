import BrownianSharp.AlignmentFractionalApproximationNumbers
import BrownianSharp.AlignmentFractionalGradedPolynomialWidth
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.CameronMartinFeatureModulus
import BrownianSharp.AlignmentNestedProjectionGrades
import BrownianSharp.AlignmentFractionalWeightedHaarCounts
import BrownianSharp.AlignmentGeometricRanks

/-! Actual finite-frame approximation-number upper bounds for fractional
Riemann--Liouville tensor operators. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
open scoped BigOperators RealInnerProductSpace ENNReal

namespace BrownianSharp.AlignmentFractionalApproximationUpper

open BrownianSharp
open BrownianSharp.AlignmentFractionalApproximationNumbers
open BrownianSharp.AlignmentFractionalGradedPolynomialWidth
open BrownianSharp.AlignmentFractionalGradedPolynomialFeature
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalSharpBudgets
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentFractionalWeightedHaarCounts
open BrownianSharp.AlignmentGeometricRanks
open HaarQuarter.TheoremD.Width
open HaarQuarter

/-! The remaining wrapper will choose the depth and simplify the profile to a
dyadic rate. This first theorem is already unconditional in the actual
operator once finite-depth projection and grade-energy data are provided. -/

/-- Every explicit finite polynomial frame gives a true strict-rank linear
approximation to the actual fractional RL operator. The error is its uniform
rectangular residual plus the square root of the omitted finite-frame energy. -/
theorem fractionalTensorRL_approximationNumber_le_of_polynomial_frame
    {ν e : ℕ} (hν : 2 ≤ ν) {r : ℝ} (hr : 1/2 < r)
    (α : Fin (ν+e) → ℝ) (hα : ∀ i, 1/2 < α i)
    (hm : Latest.minimumMultiplicity α r ν)
    (qdegree : Fin (ν+e) → ℕ) (hqdegree : ∀ i, 0 < qdegree i)
    {M n k : ℕ} {τ Cenergy : ℝ}
    (hτ : 0 ≤ τ) (hCenergy : 0 ≤ Cenergy)
    (hres : ∀ t : BrownianCubeAnchor (ν+e),
      ‖tensorKernelFamily α hα t -
        gradedPolynomialTensorProjectedKernel qdegree M α hα t‖ ≤ τ)
    (henergy : ∀ g : ℕ, ∀ t : BrownianCubeAnchor (ν+e),
      (∑ z : {z : (∀ i : Fin (ν+e), GradedFrameIndex (fun m =>
        piecewisePolynomials (qdegree i) m) M) //
          weightedProfileGrade α r (profileNat (fun i => (z i).1)) = g},
        ⟪tensorKernelFamily α hα t,
          polynomialTensorGradedFrame qdegree M z.1⟫^2) ≤
        Cenergy * (((g+1:ℕ):ℝ)^(ν-1)) *
          (Real.rpow 2 (-(2*r-1)))^g)
    (hcount : Fintype.card {z : (∀ i : Fin (ν+e), GradedFrameIndex (fun m =>
      piecewisePolynomials (qdegree i) m) M) //
        weightedProfileGrade α r (profileNat (fun i => (z i).1)) ≤ n} < k)
    (hgradeMax : ∃ L : ℕ, ∀ z : (∀ i : Fin (ν+e), GradedFrameIndex (fun m =>
      piecewisePolynomials (qdegree i) m) M),
        weightedProfileGrade α r (profileNat (fun i => (z i).1)) < L) :
    approximationNumber (fractionalTensorRL α hα) k ≤
      ENNReal.ofReal (τ + Real.sqrt
        (Cenergy * (Real.rpow 2 (-(2*r-1)))^n *
          ((n+1:ℕ):ℝ)^(ν-1) *
          polynomialBudget (Real.rpow 2 (-(2*r-1))) (ν-1))) := by
  classical
  let d := ν+e
  let I := ∀ i : Fin d, GradedFrameIndex (fun m => piecewisePolynomials (qdegree i) m) M
  let v : C(BrownianCubeAnchor d, CameronMartin.UnitCubeL2 d) := tensorKernelFamily α hα
  let frame : I → CameronMartin.UnitCubeL2 d := polynomialTensorGradedFrame qdegree M
  let grade : I → ℕ := fun z => weightedProfileGrade α r (profileNat (fun i => (z i).1))
  have hframe : Orthonormal ℝ frame := polynomialTensorGradedFrame_orthonormal qdegree M
  have hT : ∀ g t, fractionalTensorRL α hα g t = ⟪g,v t⟫ := by
    intro g t
    change inner ℝ (tensorKernelFamily α hα t) g = _
    exact real_inner_comm _ _
  obtain ⟨L,hL⟩ := hgradeMax
  have hprofile : ∀ t,
      (∑ z ∈ Finset.univ.filter (fun z : I => n < grade z),
        ⟪v t,frame z⟫^2) ≤
        Cenergy * (Real.rpow 2 (-(2*r-1)))^n *
          ((n+1:ℕ):ℝ)^(ν-1) *
            polynomialBudget (Real.rpow 2 (-(2*r-1))) (ν-1) := by
    intro t
    have hq0 : 0 < Real.rpow 2 (-(2*r-1)) := Real.rpow_pos_of_pos (by norm_num) _
    have hq1 : Real.rpow 2 (-(2*r-1)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    have htail := finite_grade_profile_tail_le (n:=n) (L:=L) (k:=ν-1) grade
      (fun z : I => ⟪v t,frame z⟫^2)
      (C:=Cenergy) (q:=Real.rpow 2 (-(2*r-1)))
      hCenergy hq0 hq1
      (fun z => hL z)
      (fun z => sq_nonneg _)
      (by
        intro g
        simpa [I, frame, v, grade, d, polynomialTensorGradedFrame] using henergy g t)
    simpa [v, frame, I, grade] using htail
  have hproj (t : BrownianCubeAnchor d) :
      finiteOrthonormalProjection frame (v t) =
        gradedPolynomialTensorProjectedKernel qdegree M α hα t := by
    change (∑ z : (∀ i : Fin (ν+e),
      GradedFrameIndex (fun m => piecewisePolynomials (qdegree i) m) M),
        ⟪tensorKernelFamily α hα t, polynomialTensorGradedFrame qdegree M z⟫ •
          polynomialTensorGradedFrame qdegree M z) = _
    exact (gradedPolynomialTensorProjectedKernel_eq_sum qdegree M α hα t).symm
  have hfull : ∀ t, ‖v t-finiteOrthonormalProjection frame (v t)‖ ≤ τ := by
    intro t
    rw [hproj t]
    simpa [v] using hres t
  let E : ℝ := Cenergy * (Real.rpow 2 (-(2*r-1)))^n *
    ((n+1:ℕ):ℝ)^(ν-1) *
      polynomialBudget (Real.rpow 2 (-(2*r-1))) (ν-1)
  have hE : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCenergy (by positivity)) (by positivity))
      (polynomialBudget_nonneg (by positivity) (ν-1))
  simpa [d, v, frame, grade, E] using
    approximationNumber_le_of_finite_grade_frame
      (fractionalTensorRL α hα) v hT frame hframe grade hcount hτ hE hfull hprofile

/-- Actual anisotropic RL operators have the sharp dyadic upper rate for
bounded-linear approximation numbers. The finite rectangular depth is chosen
after the cutoff so its exact projection residual is no larger than the
geometric high-grade coefficient tail. -/
theorem polynomial_fractional_tensor_RL_approximation_number_dyadic
    {ν e : ℕ} (hν : 2 ≤ ν) {r : ℝ} (hr : 1/2 < r)
    (α : Fin (ν+e) → ℝ) (hα : ∀ i, 1/2 < α i)
    (hm : Latest.minimumMultiplicity α r ν) :
    ∃ A : ℕ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      approximationNumber (fractionalTensorRL α hα)
        (A * Fintype.card (LayerIndex ν n) + 1) ≤
        ENNReal.ofReal (B * Real.sqrt
          ((Real.rpow 2 (-(2*r-1)))^n * ((n+1:ℕ):ℝ)^(ν-1))) := by
  classical
  let d := ν+e
  have hd : 0 < d := by dsimp [d]; omega
  have hrpos : 0 < r := by linarith
  obtain ⟨qdegree,hqdegree,Cenergy,hCenergy,hgradeEnergy⟩ :=
    exists_polynomial_tensor_weighted_grade_energy_data
      (by omega : 0 < ν) r hr α hα hm
  obtain ⟨Cdim,hCdim,hlow⟩ :=
    polynomial_tensor_weightedLowFiber_layer_multiple hν hrpos α qdegree hqdegree hm
  let ρ : ℝ := Real.rpow 2 (-(2*r-1))
  have hρ : 0 < ρ := by dsimp [ρ]; exact Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hbudget : 0 ≤ polynomialBudget ρ (ν-1) :=
    polynomialBudget_nonneg hρ.le (ν-1)
  refine ⟨Cdim, hCdim, 1+Real.sqrt (Cenergy*polynomialBudget ρ (ν-1)), ?_, ?_⟩
  · have hprod : 0 ≤ Cenergy*polynomialBudget ρ (ν-1) :=
      mul_nonneg hCenergy.le hbudget
    positivity
  · intro n
    let target : ℝ := Real.sqrt (ρ^n * ((n+1:ℕ):ℝ)^(ν-1))
    have htarget : 0 < target := by
      dsimp [target]
      apply Real.sqrt_pos.2
      exact mul_pos (pow_pos hρ _) (by positivity)
    obtain ⟨M,hM,hres⟩ :=
      exists_gradedPolynomialTensorProjectedKernel_depth
        hd qdegree hqdegree α hα htarget
    obtain ⟨Acoord,hAcoord⟩ := exists_nat_gt (∑ i : Fin d, α i/r)
    have hαnonneg : ∀ i : Fin d, 0 ≤ α i := by
      intro i
      exact le_trans hrpos.le (hm.1 i)
    have hsum : (∑ i : Fin d, α i/r) < (Acoord:ℝ) := by exact_mod_cast hAcoord
    let L : ℕ := M*Acoord+1
    have hcut : (M:ℝ)*(∑ i : Fin d, α i/r) < L := by
      have hmul : (M:ℝ)*(∑ i : Fin d, α i/r) ≤ (M:ℝ)*(Acoord:ℝ) :=
        mul_le_mul_of_nonneg_left hsum.le (by positivity)
      have hnext : (M:ℝ)*(Acoord:ℝ) < (M*Acoord+1:ℕ) := by
        push_cast
        nlinarith
      dsimp [L]
      exact hmul.trans_lt hnext
    have hgradeMax : ∀ z : (∀ i : Fin d,
        GradedFrameIndex (fun m => piecewisePolynomials (qdegree i) m) M),
        weightedProfileGrade α r (profileNat (fun i => (z i).1)) < L :=
      polynomial_tensor_weightedGrade_lt_cutoff qdegree α r hrpos hαnonneg hcut
    let k : ℕ := Cdim * Fintype.card (LayerIndex ν n) + 1
    have hcount : Fintype.card {z : (∀ i : Fin d,
        GradedFrameIndex (fun m => piecewisePolynomials (qdegree i) m) M) //
          weightedProfileGrade α r (profileNat (fun i => (z i).1)) ≤ n} < k := by
      have hle : Fintype.card {z : (∀ i : Fin d,
          GradedFrameIndex (fun m => piecewisePolynomials (qdegree i) m) M) //
            weightedProfileGrade α r (profileNat (fun i => (z i).1)) ≤ n} ≤
          Cdim * Fintype.card (LayerIndex ν n) := by
        simpa [d] using hlow M n
      dsimp [k]
      exact Nat.lt_succ_of_le hle
    have hgradeEnergy' : ∀ g : ℕ, ∀ t : BrownianCubeAnchor d,
        (∑ z : {z : (∀ i : Fin d,
          GradedFrameIndex (fun m => piecewisePolynomials (qdegree i) m) M) //
            weightedProfileGrade α r (profileNat (fun i => (z i).1)) = g},
          ⟪tensorKernelFamily α hα t,
            polynomialTensorGradedFrame qdegree M z.1⟫^2) ≤
          Cenergy * (((g+1:ℕ):ℝ)^(ν-1)) * ρ^g := by
      intro g t
      simpa [ρ, d, mul_assoc, mul_left_comm, mul_comm] using hgradeEnergy M g t
    have hupper := fractionalTensorRL_approximationNumber_le_of_polynomial_frame
      hν hr α hα hm qdegree hqdegree htarget.le hCenergy.le hres hgradeEnergy'
      hcount ⟨L,hgradeMax⟩
    have hE : 0 ≤ Cenergy * ρ^n * ((n+1:ℕ):ℝ)^(ν-1) *
        polynomialBudget ρ (ν-1) := by positivity
    have hEsq : Cenergy * ρ^n * ((n+1:ℕ):ℝ)^(ν-1) *
        polynomialBudget ρ (ν-1) =
        (Cenergy*polynomialBudget ρ (ν-1))*target^2 := by
      dsimp [target]
      rw [Real.sq_sqrt (by positivity)]
      ring
    have hsqrt : Real.sqrt (Cenergy * ρ^n * ((n+1:ℕ):ℝ)^(ν-1) *
        polynomialBudget ρ (ν-1)) =
        Real.sqrt (Cenergy*polynomialBudget ρ (ν-1))*target := by
      rw [hEsq, Real.sqrt_mul (mul_nonneg hCenergy.le hbudget),
        Real.sqrt_sq_eq_abs, abs_of_pos htarget]
    have hsumerr : target + Real.sqrt (Cenergy * ρ^n *
        ((n+1:ℕ):ℝ)^(ν-1) * polynomialBudget ρ (ν-1)) =
        (1+Real.sqrt (Cenergy*polynomialBudget ρ (ν-1)))*target := by
      rw [hsqrt]
      ring
    rw [hsumerr] at hupper
    simpa [d, k, ρ, target] using hupper

end BrownianSharp.AlignmentFractionalApproximationUpper
