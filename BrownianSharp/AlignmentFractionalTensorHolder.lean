import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentFractionalHolder
import Mathlib.Tactic

/-! Quantitative Holder regularity of the actual Gamma-normalized tensor
Riemann--Liouville kernel as a map into the cube-source L² space. -/

noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalTensorHolder

open AlignmentFractionalTensorOperator AlignmentL2TensorProduct
open AlignmentFractionalTranslation AlignmentFractionalHolder AlignmentFractionalL2

noncomputable def tensorHolderExponent (r : ℝ) : ℝ := min (r - 1/2) (1/2)

private noncomputable def scalarHolderSquareConstant (α : ℝ) : ℝ :=
  max (((Real.Gamma α)⁻¹)^2 *
    (4 / (2*(α-1)+1) + (1/2:ℝ)^(2*(α-1))))
    (3*((Real.Gamma α)⁻¹)^2)

private noncomputable def scalarHolderConstant (α : ℝ) : ℝ :=
  1 + Real.sqrt (scalarHolderSquareConstant α)

private theorem scalarHolderSquareConstant_nonneg {α : ℝ} (hα : 1/2 < α) :
    0 ≤ scalarHolderSquareConstant α := by
  unfold scalarHolderSquareConstant
  apply le_max_of_le_right
  positivity

private theorem scalarHolderSquareConstant_le_sq {α : ℝ} (hα : 1/2 < α) :
    scalarHolderSquareConstant α ≤ scalarHolderConstant α ^ 2 := by
  have hK := scalarHolderSquareConstant_nonneg hα
  unfold scalarHolderConstant
  rw [add_sq, Real.sq_sqrt hK]
  nlinarith [Real.sqrt_nonneg (scalarHolderSquareConstant α)]

private theorem translatedUnitKernelFamily_norm_sub_le_holder
    {α β : ℝ} (hα : 1/2 < α) (hβ : 0 < β)
    (hβα : β ≤ holderExponent α) (s t : UnitInterval) :
    ‖translatedUnitKernelFamily α hα t - translatedUnitKernelFamily α hα s‖ ≤
      scalarHolderConstant α * (|t.val-s.val|)^β := by
  let δ : ℝ := |t.val-s.val|
  have hδ0 : 0 ≤ δ := abs_nonneg _
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    rcases t.property with ⟨ht0, ht1⟩
    rcases s.property with ⟨hs0, hs1⟩
    rw [abs_le]
    constructor <;> linarith
  have hpowβ : 0 ≤ δ^β := Real.rpow_nonneg hδ0 _
  have hpowSq : (δ^β)^2 = δ^(2*β) := by
    calc
      (δ^β)^2 = (δ^β)^(2:ℝ) := (Real.rpow_natCast _ 2).symm
      _ = δ^(β*2) := (Real.rpow_mul hδ0 β 2).symm
      _ = δ^(2*β) := by rw [mul_comm]
  have hExponent : 2*β ≤ 2*holderExponent α := by nlinarith
  have hpowOrder := Real.rpow_le_rpow_of_exponent_ge'
    hδ0 hδ1 (by positivity : 0 ≤ 2*β) hExponent
  have hK : 0 ≤ scalarHolderSquareConstant α := scalarHolderSquareConstant_nonneg hα
  have hKle : scalarHolderSquareConstant α ≤ scalarHolderConstant α ^ 2 :=
    scalarHolderSquareConstant_le_sq hα
  have hsq :
      ‖translatedUnitKernelFamily α hα t - translatedUnitKernelFamily α hα s‖^2 ≤
        scalarHolderSquareConstant α * δ^(2*holderExponent α) := by
    by_cases hst : s.val ≤ t.val
    · have h := translatedUnitKernelFamily_increment_sq_norm_le_holder
        hα s.property.1 hst t.property.2
      simpa [scalarHolderSquareConstant, δ, abs_of_nonneg (sub_nonneg.mpr hst)] using h
    · have hts : t.val ≤ s.val := le_of_not_ge hst
      have h := translatedUnitKernelFamily_increment_sq_norm_le_holder
        hα t.property.1 hts s.property.2
      have hrev :
          ‖translatedUnitKernelFamily α hα t - translatedUnitKernelFamily α hα s‖ =
            ‖translatedUnitKernelFamily α hα s - translatedUnitKernelFamily α hα t‖ := by
        rw [norm_sub_rev]
      rw [hrev]
      simpa [scalarHolderSquareConstant, δ, abs_of_nonpos (sub_nonpos.mpr hts)] using h
  have hsq' :
      ‖translatedUnitKernelFamily α hα t - translatedUnitKernelFamily α hα s‖^2 ≤
        scalarHolderConstant α ^ 2 * δ^(2*β) := by
    calc
      _ ≤ scalarHolderSquareConstant α * δ^(2*holderExponent α) := hsq
      _ ≤ scalarHolderSquareConstant α * δ^(2*β) :=
        mul_le_mul_of_nonneg_left hpowOrder hK
      _ ≤ scalarHolderConstant α ^ 2 * δ^(2*β) :=
        mul_le_mul_of_nonneg_right hKle (by positivity)
  have hsq'' :
      ‖translatedUnitKernelFamily α hα t - translatedUnitKernelFamily α hα s‖^2 ≤
        (scalarHolderConstant α * δ^β)^2 := by
    rw [mul_pow, hpowSq]
    exact hsq'
  have hL : 0 ≤ scalarHolderConstant α * δ^β := by
    apply mul_nonneg
    · unfold scalarHolderConstant
      positivity
    · exact hpowβ
  nlinarith [sq_nonneg
    (‖translatedUnitKernelFamily α hα t - translatedUnitKernelFamily α hα s‖ -
      scalarHolderConstant α * δ^β)]

/-- The actual tensor RL evaluation feature is Holder continuous in the
source L² norm, with any exponent up to the least coordinate regularity
`min_i (a_i-1/2,1/2)`. -/
theorem tensorKernelFamily_holder {d : ℕ} (hd : 0 < d)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i)
    (r : ℝ) (hr : 1/2 < r) (hra : ∀ i, r ≤ a i) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : BrownianCubeAnchor d,
        ‖tensorKernelFamily a ha x - tensorKernelFamily a ha y‖ ≤
          C * (dist x y)^(tensorHolderExponent r) := by
  classical
  let β := tensorHolderExponent r
  let μ : Fin d → Measure ℝ := fun _ => volume.restrict (Set.Icc (0:ℝ) 1)
  let T := tensorContinuous (μ := μ)
  let v : BrownianCubeAnchor d → Fin d → UnitL2 := fun x i =>
    translatedUnitKernelFamily (a i) (ha i) (cubeCoordinate i x)
  let M : ℝ := 1 + ∑ i : Fin d, ‖fullKernelVector (a i) (ha i)‖
  let L : ℝ := ∑ i : Fin d, scalarHolderConstant (a i)
  let C : ℝ := 1 + (d:ℝ) * M^(d-1) * L
  have hβ : 0 < β := by
    dsimp [β, tensorHolderExponent]
    exact lt_min (by linarith) (by norm_num)
  have hβa (i : Fin d) : β ≤ holderExponent (a i) := by
    apply le_min
    · exact (min_le_left _ _).trans (sub_le_sub_right (hra i) _)
    · exact min_le_right _ _
  have hMnonneg : 0 ≤ M := by
    dsimp [M]
    positivity
  have hLnonneg : 0 ≤ L := by
    dsimp [L]
    apply Finset.sum_nonneg
    intro i hi
    unfold scalarHolderConstant
    positivity
  have hC : 0 < C := by
    dsimp [C]
    have hMpow : 0 ≤ M^(d-1) := by positivity
    positivity
  have hTnorm : ‖T‖ ≤ 1 := by
    dsimp [T, tensorContinuous]
    exact MultilinearMap.mkContinuous_norm_le (tensorMultilinear (μ := μ))
      (by norm_num) (by intro w; simp [tensorMultilinear, productVector_norm])
  refine ⟨C, hC, ?_⟩
  intro x y
  have hcoord (i : Fin d) : |x.val i - y.val i| ≤ dist x y := by
    change |x.val i - y.val i| ≤ ‖x.val-y.val‖
    simpa using norm_le_pi_norm (x.val-y.val) i
  have hcoordinate (i : Fin d) :
      ‖v x i - v y i‖ ≤ scalarHolderConstant (a i) * (dist x y)^β := by
    have hs := translatedUnitKernelFamily_norm_sub_le_holder
      (ha i) hβ (hβa i) (cubeCoordinate i y) (cubeCoordinate i x)
    dsimp [v, cubeCoordinate] at hs ⊢
    have hp : (|x.val i-y.val i|)^β ≤ (dist x y)^β :=
      Real.rpow_le_rpow (abs_nonneg _) (hcoord i) hβ.le
    exact hs.trans (mul_le_mul_of_nonneg_left hp (by
      unfold scalarHolderConstant
      positivity))
  let vx : Fin d → UnitL2 := v x
  let vy : Fin d → UnitL2 := v y
  have hMcoord (z : BrownianCubeAnchor d) (i : Fin d) :
      ‖v z i‖ ≤ M := by
    have hnorm := translatedUnitKernelFamily_norm_le (a i) (ha i) (cubeCoordinate i z)
    have hsum : ‖fullKernelVector (a i) (ha i)‖ ≤
        ∑ j : Fin d, ‖fullKernelVector (a j) (ha j)‖ := by
      exact Finset.single_le_sum (f := fun j : Fin d =>
        ‖fullKernelVector (a j) (ha j)‖) (s := Finset.univ)
        (fun j hj => norm_nonneg _) (Finset.mem_univ i)
    change ‖translatedUnitKernelFamily (a i) (ha i) (cubeCoordinate i z)‖ ≤ M
    dsimp [M]
    exact hnorm.trans (by linarith [hsum])
  have hMpi (z : BrownianCubeAnchor d) : ‖v z‖ ≤ M := by
    apply (pi_norm_le_iff_of_nonneg hMnonneg).2
    intro i
    exact hMcoord z i
  have hLsum (i : Fin d) : scalarHolderConstant (a i) ≤ L := by
    dsimp [L]
    exact Finset.single_le_sum (f := fun j : Fin d => scalarHolderConstant (a j))
      (s := Finset.univ) (fun j hj => by unfold scalarHolderConstant; positivity)
      (Finset.mem_univ i)
  have hVdiff : ‖vx-vy‖ ≤ L * (dist x y)^β := by
    have hpow : 0 ≤ (dist x y)^β := Real.rpow_nonneg (dist_nonneg) _
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    calc
      ‖vx i-vy i‖ ≤ scalarHolderConstant (a i) * (dist x y)^β := hcoordinate i
      _ ≤ L * (dist x y)^β := mul_le_mul_of_nonneg_right (hLsum i) hpow
  have hmult := T.norm_image_sub_le vx vy
  have hmult' : ‖T vx-T vy‖ ≤
      (d:ℝ) * M^(d-1) * (L * (dist x y)^β) := by
    have hmult0 : ‖T vx-T vy‖ ≤
        ‖T‖ * (d:ℝ) * max ‖vx‖ ‖vy‖^(d-1) * ‖vx-vy‖ := by
      simpa using hmult
    calc
      ‖T vx-T vy‖ ≤ ‖T‖ * (d:ℝ) * max ‖vx‖ ‖vy‖^(d-1) * ‖vx-vy‖ := hmult0
      _ ≤ 1 * (d:ℝ) * M^(d-1) * (L * (dist x y)^β) := by
        have hmax : max ‖vx‖ ‖vy‖ ≤ M := max_le (hMpi x) (hMpi y)
        have hD : 0 ≤ (d:ℝ) := by positivity
        have hP : 0 ≤ M^(d-1) := by positivity
        have hR : 0 ≤ L * (dist x y)^β := mul_nonneg hLnonneg (Real.rpow_nonneg dist_nonneg _)
        gcongr
      _ = (d:ℝ) * M^(d-1) * (L * (dist x y)^β) := by ring
  have hcontract :
      ‖tensorKernelFamily a ha x - tensorKernelFamily a ha y‖ ≤ ‖T vx-T vy‖ := by
    change ‖productToCube d (productKernelFamily a ha x) -
      productToCube d (productKernelFamily a ha y)‖ ≤ _
    have hprodX : productKernelFamily a ha x = T vx := rfl
    have hprodY : productKernelFamily a ha y = T vy := rfl
    rw [hprodX, hprodY, ← map_sub]
    exact productToCube_norm_le d _
  calc
    ‖tensorKernelFamily a ha x - tensorKernelFamily a ha y‖ ≤
        (d:ℝ) * M^(d-1) * (L * (dist x y)^β) := hcontract.trans hmult'
    _ ≤ C * (dist x y)^β := by
      dsimp [C]
      have hpow : 0 ≤ (dist x y)^β := Real.rpow_nonneg dist_nonneg _
      have hcoef : (d:ℝ) * M^(d-1) * L ≤ 1+(d:ℝ)*M^(d-1)*L := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hcoef hpow]

end BrownianSharp.AlignmentFractionalTensorHolder
