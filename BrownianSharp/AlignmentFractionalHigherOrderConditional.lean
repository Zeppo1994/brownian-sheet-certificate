import BrownianSharp.AlignmentFractionalHigherOrderComposition
import BrownianSharp.AlignmentIntegerEvenOrderTensorLower
import BrownianSharp.AlignmentFractionalTensorL2Semigroup
import BrownianSharp.AlignmentFractionalTensorL2ApproximationAllIndex
import BrownianSharp.AlignmentFractionalAnisotropicRateTransfer
import BrownianSharp.AlignmentFractionalApproximationStatement
import BrownianSharp.AlignmentFractionalLinearWidthGap
import BrownianSharp.AlignmentLatestStatements
import Mathlib.Tactic

/-! A transparent conditional closure for all smoothness orders. Its sole
analytic premise is the family of actual isotropic C-valued approximation
lower bounds at even integer orders. -/

noncomputable section
open scoped ENNReal

namespace BrownianSharp.AlignmentFractionalHigherOrderConditional

open BrownianSharp
open BrownianSharp.AlignmentFractionalHigherOrderComposition
open BrownianSharp.AlignmentIntegerEvenOrderTensorLower
open BrownianSharp.AlignmentFractionalTensorL2ApproximationAllIndex
open BrownianSharp.AlignmentFractionalAnisotropicRateTransfer
open BrownianSharp.AlignmentFractionalApproximationStatement
open BrownianSharp.AlignmentFractionalApproximationNumbers
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalTensorL2Semigroup
open BrownianSharp.AlignmentFractionalLinearWidthGap

/-- Required actual C-output lower rates at all even orders, in each
dimension. This is an explicit hypothesis, not a claimed completed theorem. -/
def EvenOrderIsotropicApproximationLower : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ m : ℕ,
    ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c*logarithmicIndexRate
          (((2*(m+1):ℕ):ℝ)-1/2)
          (((2*(m+1):ℕ):ℝ)*((d-1:ℕ):ℝ)) k) ≤
          approximationNumber
            (fractionalTensorRL (fun _ : Fin d => ((2*(m+1):ℕ):ℝ))
              (fun _ => by
                norm_num [Nat.cast_mul, Nat.cast_add]
                have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _
                nlinarith [hm0])) k

/-- All-order anisotropic approximation rates and the literal width quotient. -/
def FractionalHigherOrderStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i),
  ∀ r : ℝ, 1/2 < r → ∀ ν : ℕ, 2 ≤ ν →
    Latest.minimumMultiplicity a r ν →
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c*logarithmicIndexRate (r-1/2)
          (r*((ν-1:ℕ):ℝ)) k) ≤ approximationNumber (fractionalTensorRL a ha) k ∧
        approximationNumber (fractionalTensorRL a ha) k ≤
          ENNReal.ofReal (C*logarithmicIndexRate (r-1/2)
            (r*((ν-1:ℕ):ℝ)) k)) ∧
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        0 < fractionalOperatorWidth a k ∧ fractionalOperatorWidth a k < ⊤ ∧
        ENNReal.ofReal (c*AlignmentBrownianLinearWidthGap.brownianGapFactor k) ≤
          approximationNumber (fractionalTensorRL a ha) k /
            fractionalOperatorWidth a k ∧
        approximationNumber (fractionalTensorRL a ha) k /
            fractionalOperatorWidth a k ≤
          ENNReal.ofReal (C*AlignmentBrownianLinearWidthGap.brownianGapFactor k))

/-- The reusable composition step takes only the even-order lower family.
Its conclusion is shared with the unconditional public theorem. -/
def FractionalHigherOrderConditionalStatement : Prop :=
  EvenOrderIsotropicApproximationLower → FractionalHigherOrderStatement

theorem fractional_higher_order_conditional_certified :
    FractionalHigherOrderConditionalStatement := by
  intro hEven d hd a ha r hr ν hν hm
  obtain ⟨m,hmr⟩ := exists_nat_gt r
  let M : ℝ := (2*(m+1:ℕ):ℕ)
  have hM : r+(1/2:ℝ) < M := by
    dsimp [M]
    have hm' : (r:ℝ) < (m:ℝ) := hmr
    norm_num
    linarith
  have hMhalf : 1/2 < M-r := by linarith
  have hEven' : ∀ d : ℕ, 2 ≤ d → ∀ m : ℕ,
      ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
        ∀ k : ℕ, k₀ ≤ k →
          ENNReal.ofReal (c*logarithmicIndexRate
            (((2*(m+1):ℕ):ℝ)-1/2)
            (((2*(m+1):ℕ):ℝ)*((d-1:ℕ):ℝ)) k) ≤
            approximationNumber
              (fractionalTensorRL (fun _ : Fin d => ((2*(m+1):ℕ):ℝ))
                (fun _ => by
                  norm_num [Nat.cast_mul, Nat.cast_add]
                  have hm0 : (0:ℝ) ≤ (m:ℝ) := Nat.cast_nonneg _
                  nlinarith [hm0])) k := hEven
  obtain ⟨cM,hcM,kM,hkM,hMlower⟩ := hEven' ν hν m
  have hIsoLower : ∃ c : ℝ, 0 < c ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c*logarithmicIndexRate (M-1/2)
          (M*((ν-1:ℕ):ℝ)) k) ≤
          approximationNumber (fractionalTensorRL (fun _ : Fin ν => M)
            (fun _ => by linarith)) k := by
    refine ⟨cM,hcM,kM,hkM,?_⟩
    intro k hk
    have h := hMlower k hk
    simpa [M, logarithmicIndexRate] using h
  obtain ⟨Cup,hCup,kup,hkup,hL2⟩ :=
    fractionalTensorRLToL2_approximationNumber_all_index (d:=ν) hν hMhalf
  have hIsoUpper : ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        approximationNumber (fractionalTensorRLToL2 (d:=ν)
          (fun _ : Fin ν => M-r) (fun _ => by linarith)) k ≤
        ENNReal.ofReal (C*logarithmicIndexRate (M-r)
          ((M-r)*((ν-1:ℕ):ℝ)) k) := by
    refine ⟨Cup,hCup,kup,hkup,?_⟩
    intro k hk
    simpa [logarithmicIndexRate, mul_assoc] using hL2 k hk
  obtain ⟨cIso,hcIso,kIso,hkIso,hIso⟩ :=
    isotropic_fractional_approximation_lower_of_higher_order_and_L2
      hν r M hr hM hIsoLower hIsoUpper
  obtain ⟨ca,hca,ka,hka,hLower⟩ :=
    anisotropic_approximation_lower_of_isotropic_rate hd hν a ha r hr hm
      ⟨cIso,hcIso,kIso,hkIso,hIso⟩
  obtain ⟨CU,hCU,kU,hkU,hUpper⟩ :=
    fractionalApproximation_upper_certified d hd a ha r ν hν hm
  let kApprox := max 2 (max ka kU)
  have hApprox : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c*logarithmicIndexRate (r-1/2)
          (r*((ν-1:ℕ):ℝ)) k) ≤ approximationNumber (fractionalTensorRL a ha) k ∧
        approximationNumber (fractionalTensorRL a ha) k ≤
          ENNReal.ofReal (C*logarithmicIndexRate (r-1/2)
            (r*((ν-1:ℕ):ℝ)) k) := by
    refine ⟨ca,CU,hca,hCU,kApprox,?_,?_⟩
    · dsimp [kApprox]; omega
    · intro k hk
      have hkmax : max ka kU ≤ k := (le_max_right 2 (max ka kU)).trans hk
      have hkA : ka ≤ k := (le_max_left ka kU).trans hkmax
      have hkB : kU ≤ k := (le_max_right ka kU).trans hkmax
      refine ⟨hLower k hkA,?_⟩
      simpa [logarithmicIndexRate, mul_assoc] using hUpper k hkB
  obtain ⟨clo,Clo,hclo,hClo,klo,hklo,hRatio⟩ :=
    fractional_linear_width_gap_of_approximation_lower hd a ha r hν hm
      ⟨ca,hca,ka,hka,hLower⟩
  let kRatio := max 2 klo
  have hRatioPack : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        0 < fractionalOperatorWidth a k ∧ fractionalOperatorWidth a k < ⊤ ∧
        ENNReal.ofReal (c*AlignmentBrownianLinearWidthGap.brownianGapFactor k) ≤
          approximationNumber (fractionalTensorRL a ha) k /
            fractionalOperatorWidth a k ∧
        approximationNumber (fractionalTensorRL a ha) k /
            fractionalOperatorWidth a k ≤
          ENNReal.ofReal (C*AlignmentBrownianLinearWidthGap.brownianGapFactor k) := by
    refine ⟨clo,Clo,hclo,hClo,kRatio,?_,?_⟩
    · dsimp [kRatio]; exact le_max_left _ _
    · intro k hk
      exact hRatio k ((le_max_right _ _).trans hk)
  exact ⟨hApprox,hRatioPack⟩

/-- The manuscript's actual even-order tensor lower theorem discharges the
conditional family, with the index shift ensuring its order is at least two. -/
theorem actual_even_order_lower_family : EvenOrderIsotropicApproximationLower := by
  intro d hd m
  have hm : 1 ≤ m+1 := by omega
  obtain ⟨c,hc,k₀,hk₀,hlower⟩ :=
    evenOrder_tensor_approximation_lower_rate hd hm
  refine ⟨c,hc,k₀,hk₀,?_⟩
  intro k hk
  have h := hlower k hk
  convert h using 1 <;> congr 1 <;>
    simp [logarithmicIndexRate, Nat.cast_mul, Nat.cast_add] <;> ring

/-- Unconditional all-order anisotropic approximation and width-ratio result,
assembled from the actual even-order tensor lower bounds. -/
theorem fractional_higher_order_certified :
    FractionalHigherOrderStatement := by
  exact fractional_higher_order_conditional_certified actual_even_order_lower_family

end BrownianSharp.AlignmentFractionalHigherOrderConditional
