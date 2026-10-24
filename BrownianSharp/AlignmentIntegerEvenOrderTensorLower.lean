import BrownianSharp.AlignmentSelectedFrameApproximationLower
import BrownianSharp.AlignmentIntegerEvenOrderUniversalFrame
import BrownianSharp.AlignmentIntegerEvenOrderSigma
import BrownianSharp.AlignmentIntegerTwoIteratePower
import BrownianSharp.AlignmentFractionalIntegerSemigroup
import BrownianSharp.AlignmentFractionalTensorL2Product
import BrownianSharp.AlignmentFractionalTensorOperator
import Mathlib.Tactic

/-! All-index approximation-number lower bounds for isotropic even integer
Riemann--Liouville integration, assembled from the constrained sine blocks. -/

noncomputable section
open scoped ENNReal

namespace BrownianSharp.AlignmentIntegerEvenOrderTensorLower

open BrownianSharp.AlignmentSelectedFrameApproximationLower
open BrownianSharp.AlignmentIntegerEvenOrderUniversalFrame
open BrownianSharp.AlignmentIntegerEvenOrderJetConstraints
open BrownianSharp.AlignmentIntegerEvenOrderSigma
open BrownianSharp.AlignmentIntegerTwoIteratePower
open BrownianSharp.AlignmentFractionalIntegerSemigroup
open BrownianSharp.AlignmentFractionalTensorL2Product
open BrownianSharp.AlignmentFractionalTensorL2Semigroup
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalApproximationNumbers
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentSigmaFiniteL2Tensor
open HaarQuarter

private theorem evenOrderSigmaRate_rpow (m : ℕ) :
    evenOrderSigmaRate m = (2:ℝ)^(-(2*(m:ℝ))) := by
  rw [evenOrderSigmaRate, ← Real.rpow_natCast,
    ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  push_cast
  ring

/-- Actual isotropic order-`2m` tensor RL operator has the sharp
all-index approximation-number lower rate, for every `m≥1` and `d≥2`. -/
theorem evenOrder_tensor_approximation_lower_rate
    {d m : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ m) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c₁ * (k:ℝ)^(-(2*(m:ℝ))+1/2) *
          (Real.log (k:ℝ))^((2*(m:ℝ))*((d-1:ℕ):ℝ))) ≤
          approximationNumber
            (fractionalTensorRL (fun _ : Fin d => 2*(m:ℝ)) (fun _ => by
              have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
              linarith)) k := by
  let r : ℝ := 2*(m:ℝ)
  have hr : 1/2 < r := by
    dsimp [r]
    have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
    linarith
  obtain ⟨F, hF, hrest⟩ :=
    exists_evenOrder_universal_sigma_frame m hm
  rcases hrest with ⟨himageIter, hnormIter⟩
  let A : UnitL2 →L[ℝ] UnitL2 := scalarRLOnL2 r hr
  let T : CameronMartin.UnitCubeL2 d →L[ℝ] C(BrownianCubeAnchor d,ℝ) :=
    fractionalTensorRL (fun _ : Fin d => r) (fun _ => hr)
  have hfactor : ∀ v : Fin d → UnitL2,
      cubeProfileToL2 (T (productToCube d (productVector v))) =
        productToCube d (productVector (fun i => A (v i))) := by
    intro v
    simpa [T, A, r, tensorRLOnL2, fractionalTensorRLToL2] using
      (fractionalTensorRLToL2_product r hr v)
  have himage : ∀ x y : EvenOrderSelectedIndex, x ≠ y →
      inner ℝ (A (F x)) (A (F y)) = 0 := by
    intro x y hxy
    have h := himageIter x y hxy
    rw [integerTwoL2Iterate_eq_actual_even_RL hm,
      integerTwoL2Iterate_eq_actual_even_RL hm] at h
    simpa [A, r] using h
  have hc : 0 < evenOrderSigmaConst m := evenOrderSigmaConst_pos m
  have hlower : ∀ s : ℕ, ∀ j : Fin (2^s),
      evenOrderSigmaConst m * ((2:ℝ)^(-r))^s ≤
        ‖A (F ⟨s,j⟩)‖ := by
    intro s j
    have hblock := evenOrder_block_sigma_lower m s
    have hrate := congrArg (fun x : ℝ => x^s) (evenOrderSigmaRate_rpow m)
    have hidx := hnormIter ⟨s,j⟩
    have hactual : ‖A (F ⟨s,j⟩)‖ =
        ‖integerTwoL2Iterate m (F ⟨s,j⟩)‖ := by
      rw [integerTwoL2Iterate_eq_actual_even_RL hm]
    rw [hactual]
    calc
      evenOrderSigmaConst m * ((2:ℝ)^(-r))^s =
          evenOrderSigmaConst m * evenOrderSigmaRate m^s := by
            rw [← hrate]
      _ ≤ ‖integerTwoL2Iterate m (F ⟨s,j⟩)‖ := hblock.trans hidx
  have hmain := tensor_approximation_lower_rate_of_scalar_frame
    hd r hr F hF A T hfactor himage (evenOrderSigmaConst m) hc hlower
  simpa [r, T] using hmain

end BrownianSharp.AlignmentIntegerEvenOrderTensorLower
