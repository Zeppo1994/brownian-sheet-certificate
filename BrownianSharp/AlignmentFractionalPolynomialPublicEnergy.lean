import BrownianSharp.AlignmentFractionalPolynomialWeightedEnergy
import BrownianSharp.AlignmentFractionalGradedPolynomialFeature
import Mathlib.Tactic

/-! A public-frame adapter for the actual weighted polynomial tensor energy
envelope. -/

noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalPolynomialPublicEnergy

open BrownianSharp.AlignmentFractionalPolynomialWeightedEnergy
open BrownianSharp.AlignmentFractionalGradedPolynomialFeature
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalWeightedGrades
open BrownianSharp.AlignmentFractionalWeightedHaarCounts
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentNestedProjectionTensor
open HaarQuarter
open BrownianSharp.CameronMartin

/-- The arbitrary-order weighted grade-energy estimate, stated directly in
terms of the public graded polynomial frame used by the projection theorem. -/
theorem polynomialTensor_weightedGrade_energy_public_frame_le
    {ν e : ℕ} (hν : 0 < ν) (r : ℝ) (hr : 1/2 < r)
    (α : Fin (ν+e) → ℝ) (hα : ∀ i, 1/2 < α i)
    (hm : Latest.minimumMultiplicity α r ν) :
    ∃ ep : Fin (ν+e) ≃ Fin (ν+e), ∃ w : Fin e → ℝ,
    ∃ degree : Fin (ν+e) → ℕ, ∃ A : Fin (ν+e) → ℝ,
    ∃ Cenergy : ℝ,
      (∀ j : Fin e, 1 < w j) ∧
      (∀ i : Fin ν, α (ep (Fin.castAdd e i)) = r) ∧
      (∀ j : Fin e, α (ep (Fin.natAdd ν j)) = r*w j) ∧
      (∀ i, 0 < degree i) ∧ (∀ i, 0 < A i) ∧ 0 < Cenergy ∧
      ∀ (M n : ℕ) (t : BrownianCubeAnchor (ν+e)),
        (∑ z : {z : (∀ i : Fin (ν+e),
              GradedFrameIndex
                (fun m => piecewisePolynomials (degree i) m) M) //
              weightedProfileGrade α r (profileNat (fun i => (z i).1)) = n},
          ⟪tensorKernelFamily α hα t,
            polynomialTensorGradedFrame degree M z.1⟫ ^ 2) ≤
          Cenergy * (((n+1:ℕ):ℝ)^(ν-1) *
            (Real.rpow 2 (-(2*r-1)))^n) := by
  classical
  obtain ⟨ep,w,degree,A,hw,hactive,hinactive,hdegree,hA,henergy⟩ :=
    polynomialTensor_weightedGrade_energy_le hν r hr α hα hm
  let Aprod : ℝ := ∏ i : Fin (ν+e), A i
  let inactiveFactor : ℝ :=
    ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹
  let Cenergy := Aprod * inactiveFactor
  have hfactor (j : Fin e) :
      0 < (1-Real.rpow 2 (-(w j-1)))⁻¹ := by
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
  have hfactorprod : 0 < inactiveFactor := by
    dsimp [inactiveFactor]
    exact Finset.prod_pos fun j hj => hfactor j
  have hCenergy : 0 < Cenergy := by
    dsimp [Cenergy]
    exact mul_pos hAprod hfactorprod
  refine ⟨ep,w,degree,A,Cenergy,hw,hactive,hinactive,hdegree,hA,hCenergy,?_⟩
  intro M n t
  have h := henergy M n t
  have hpow : (Real.rpow 2 (-(2*r-1)))^n =
      Real.rpow 2 (-(2*r-1)*(n:ℝ)) := by
    calc
      _ = (Real.rpow 2 (-(2*r-1)))^(n:ℝ) :=
        (Real.rpow_natCast _ _).symm
      _ = _ := (Real.rpow_mul (by norm_num : (0:ℝ)≤2)
        (-(2*r-1)) (n:ℝ)).symm
  have hpublic :
      (∑ z : {z : (∀ i : Fin (ν+e), GradedFrameIndex
            (fun m => piecewisePolynomials (degree i) m) M) //
            weightedProfileGrade α r (profileNat (fun i => (z i).1)) = n},
          ⟪tensorKernelFamily α hα t,
            polynomialTensorGradedFrame degree M z.1⟫ ^ 2) ≤
        Aprod * (Real.rpow 2 (-(2*r-1)*n) *
          (((n+1:ℕ):ℝ)^(ν-1) * inactiveFactor)) := by
    convert h using 1 <;> rfl
  have hrewrite :
      (∏ i : Fin (ν+e), A i) *
        (Real.rpow 2 (-(2*r-1)*n) *
          (((n+1:ℕ):ℝ)^(ν-1) *
            ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹)) =
      Cenergy * (((n+1:ℕ):ℝ)^(ν-1) *
        (Real.rpow 2 (-(2*r-1)))^n) := by
    rw [hpow]
    simp only [Aprod, inactiveFactor, Cenergy]
    ring
  calc
    _ ≤ Aprod * (Real.rpow 2 (-(2*r-1)*n) *
        (((n+1:ℕ):ℝ)^(ν-1) * inactiveFactor)) := hpublic
    _ = Cenergy * (((n+1:ℕ):ℝ)^(ν-1) *
        (Real.rpow 2 (-(2*r-1)))^n) := hrewrite

end BrownianSharp.AlignmentFractionalPolynomialPublicEnergy
