import BrownianSharp.AlignmentOrdinaryTensorLower
import BrownianSharp.AlignmentFractionalApproximationStatement
import BrownianSharp.AlignmentFractionalUnitOrders
import BrownianSharp.AlignmentOperatorCameronMartin
import BrownianSharp.AlignmentOperatorNumbers
import BrownianSharp.AlignmentFractionalApproximationNumbers
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.ExtendedStatements
import Mathlib.Tactic

/-! Actual approximation-number and Kolmogorov-width rates for the Brownian
sheet integration operator, and their linear/nonlinear gap. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
open HaarQuarter BrownianSharp

namespace BrownianSharp.AlignmentBrownianLinearWidthGap

open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalApproximationNumbers
open BrownianSharp.AlignmentOrdinaryTensorLower
open BrownianSharp.AlignmentOperatorNumbers
open BrownianSharp.AlignmentOperatorCameronMartin
open BrownianSharp.AlignmentFractionalUnitOrders
open BrownianSharp.AlignmentFractionalApproximationStatement
open BrownianSharp.AlignmentOperatorStatements

/-- The actual order-one tensor RL operator. -/
noncomputable def brownianIntegrationOperator (d : ℕ) :
    CameronMartin.UnitCubeL2 d →L[ℝ] C(BrownianCubeAnchor d, ℝ) :=
  fractionalTensorRL (fun _ : Fin d => (1:ℝ)) (by intro i; norm_num)

private theorem ordinary_rate_eq {d k : ℕ} (hk : 2 ≤ k) :
    logarithmicIndexRate (1/2) ((d-1:ℕ):ℝ) k =
      (Real.log (k:ℝ))^(d-1) / Real.sqrt (k:ℝ) := by
  unfold logarithmicIndexRate
  have hkpos : 0 ≤ (k:ℝ) := by exact_mod_cast (by omega : 0≤k)
  rw [Real.rpow_neg hkpos, Real.sqrt_eq_rpow]
  rw [Real.rpow_natCast]
  ring

/-- The Brownian integration operator has its sharp all-index approximation
number rate, with constants and threshold depending only on dimension. -/
theorem brownian_approximationNumber_two_sided {d : ℕ} (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c * logarithmicIndexRate (1/2) ((d-1:ℕ):ℝ) k) ≤
          approximationNumber (brownianIntegrationOperator d) k ∧
        approximationNumber (brownianIntegrationOperator d) k ≤
          ENNReal.ofReal (C * logarithmicIndexRate (1/2) ((d-1:ℕ):ℝ) k) := by
  have hmin : Latest.minimumMultiplicity (fun _ : Fin d => (1:ℝ)) 1 d := by
    constructor
    · intro i
      norm_num
    · simp
  obtain ⟨Cup,hCup,kup,hkup,hupper⟩ := fractionalApproximation_upper_certified
    d hd (fun _ : Fin d => (1:ℝ)) (by intro i; norm_num) 1 d (by omega) hmin
  let clow := ordinaryTensorLowerRateConstant d
  have hclow : 0 < clow := ordinaryTensorLowerRateConstant_pos hd
  refine ⟨clow,Cup,hclow,hCup,max 2 kup,le_max_left _ _,?_⟩
  intro k hk
  have hk2 : 2 ≤ k := (le_max_left 2 kup).trans hk
  have hlow := ordinaryTensor_approximationNumber_lower hd hk2
  have hrate := ordinary_rate_eq (d:=d) hk2
  have hlow' : ENNReal.ofReal (clow * logarithmicIndexRate (1/2)
      ((d-1:ℕ):ℝ) k) ≤ approximationNumber (brownianIntegrationOperator d) k := by
    have heq : clow * logarithmicIndexRate (1/2) ((d-1:ℕ):ℝ) k =
        ordinaryTensorLowerRateConstant d * (Real.log (k:ℝ))^(d-1) /
          Real.sqrt (k:ℝ) := by
      rw [hrate]
      dsimp [clow]
      ring
    rw [heq]
    simpa [brownianIntegrationOperator, clow] using hlow
  have hup := hupper k (le_trans (le_max_right 2 kup) hk)
  have hup' : approximationNumber (brownianIntegrationOperator d) k ≤
      ENNReal.ofReal (Cup * logarithmicIndexRate (1/2) ((d-1:ℕ):ℝ) k) := by
    have hexp : (1:ℝ)-1/2 = 1/2 := by norm_num
    have hpoly : (1:ℝ)*((d-1:ℕ):ℝ) = ((d-1:ℕ):ℝ) := by ring
    rw [hexp, hpoly] at hup
    simpa [brownianIntegrationOperator] using hup
  exact ⟨hlow',hup'⟩

/-- The set of outputs of the order-one integration operator on the Hilbert
unit ball is exactly the Cameron--Martin unit cube. -/
theorem brownian_operator_image_eq_Kd {d : ℕ} :
    brownianIntegrationOperator d '' {g : CameronMartin.UnitCubeL2 d | ‖g‖ ≤ 1} =
      CameronMartin.KdUnitCube d := by
  have hunit := fractionalIntegrationBall_one_eq_KdUnitCube d
  have himage := fractionalIntegrationBall_eq_operator_image
      (fun _ : Fin d => (1:ℝ)) (by intro i; norm_num)
  simpa [brownianIntegrationOperator] using himage.symm.trans hunit

/-- The actual Kolmogorov number of the Brownian image ball has its known
sharp width rate. -/
theorem brownian_operator_width_two_sided {d : ℕ} (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c * logarithmicIndexRate 1 ((d:ℝ)-1/2) k) ≤
          operatorKolmogorovNumber
            (brownianIntegrationOperator d '' {g : CameronMartin.UnitCubeL2 d | ‖g‖≤1}) k ∧
        operatorKolmogorovNumber
            (brownianIntegrationOperator d '' {g : CameronMartin.UnitCubeL2 d | ‖g‖≤1}) k ≤
          ENNReal.ofReal (C * logarithmicIndexRate 1 ((d:ℝ)-1/2) k) := by
  obtain ⟨c,C,t₀,hc,hC,ht₀,ht₀small,hcover,hidx⟩ :=
    BrownianSharp.AlignmentOperatorCameronMartin.cameronMartinEntropyWidth_certified d hd
  obtain ⟨k₀,hk₀,h⟩ := hidx
  refine ⟨c,C,hc,hC,k₀,hk₀,?_⟩
  intro k hk
  have hw := h k hk
  rw [brownian_operator_image_eq_Kd.symm] at hw
  simpa only [cmIndexRate] using ⟨hw.2.2.1, hw.2.2.2⟩

/-- The normalized size of the linear-approximation/Kolmogorov-width gap. -/
def brownianGapFactor (k : ℕ) : ℝ :=
  Real.sqrt ((k:ℝ) / Real.log (k:ℝ))

private theorem brownian_gap_rate_identity {d k : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) :
    brownianGapFactor k * logarithmicIndexRate 1 ((d:ℝ)-1/2) k =
      logarithmicIndexRate (1/2) ((d-1:ℕ):ℝ) k := by
  have hx : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hl : 0 < Real.log (k:ℝ) :=
    Real.log_pos (by exact_mod_cast (show (1:ℕ)<k by omega))
  have hexp : ((d:ℝ)-1/2) + (-1/2) = ((d-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1≤d)]
    push_cast
    ring
  have hlogexp : (-1/2:ℝ)+((d:ℝ)-1/2)=((d-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1≤d)]
    push_cast
    ring
  unfold brownianGapFactor logarithmicIndexRate
  rw [Real.sqrt_div (le_of_lt hx), Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [div_eq_mul_inv]
  rw [← Real.rpow_neg (le_of_lt hl) (1/2:ℝ)]
  calc
    _ = (((k:ℝ)^(1/2:ℝ) * (k:ℝ)^(-1:ℝ)) *
        ((Real.log (k:ℝ))^(-1/2:ℝ) *
          (Real.log (k:ℝ))^((d:ℝ)-1/2))) := by ring_nf
    _ = (k:ℝ)^(-(1/2:ℝ)) * (Real.log (k:ℝ))^((d-1:ℕ):ℝ) := by
      rw [← Real.rpow_add hx (1/2:ℝ) (-1:ℝ)]
      rw [← Real.rpow_add hl (-1/2:ℝ) ((d:ℝ)-1/2)]
      rw [show (1/2:ℝ)+(-1:ℝ)=(-1/2:ℝ) by norm_num, hlogexp]
      congr 1 <;> norm_num
    _ = _ := by congr 1 <;> norm_num

/-- Product form of the actual Brownian linear/nonlinear width gap. The
Kolmogorov number is positive and finite at these indices by the width bounds,
so this also gives the literal ratio estimate. -/
theorem brownian_linear_width_gap_product {d : ℕ} (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c * brownianGapFactor k) *
            operatorKolmogorovNumber
              (brownianIntegrationOperator d ''
                {g : CameronMartin.UnitCubeL2 d | ‖g‖≤1}) k ≤
          approximationNumber (brownianIntegrationOperator d) k ∧
        approximationNumber (brownianIntegrationOperator d) k ≤
          ENNReal.ofReal (C * brownianGapFactor k) *
            operatorKolmogorovNumber
              (brownianIntegrationOperator d ''
                {g : CameronMartin.UnitCubeL2 d | ‖g‖≤1}) k := by
  obtain ⟨ca,Ca,hca,hCa,ka,hka,ha⟩ := brownian_approximationNumber_two_sided hd
  obtain ⟨cw,Cw,hcw,hCw,kw,hkw,hw⟩ := brownian_operator_width_two_sided hd
  let c : ℝ := ca/Cw
  let C : ℝ := Ca/cw
  have hc : 0<c := div_pos hca hCw
  have hC : 0<C := div_pos hCa hcw
  refine ⟨c,C,hc,hC,max ka kw,by omega,?_⟩
  intro k hk
  have hk2 : 2≤k := by omega
  have hA := ha k (by omega)
  have hW := hw k (by omega)
  let ra : ℝ := logarithmicIndexRate (1/2) ((d-1:ℕ):ℝ) k
  let rw : ℝ := logarithmicIndexRate 1 ((d:ℝ)-1/2) k
  let g : ℝ := brownianGapFactor k
  have hrate : g*rw=ra := by
    dsimp [g,rw,ra]
    exact brownian_gap_rate_identity hd hk2
  have hg : 0<g := by
    dsimp [g,brownianGapFactor]
    apply Real.sqrt_pos.2
    apply div_pos (by exact_mod_cast (show 0<k by omega))
    exact Real.log_pos (by exact_mod_cast (show (1:ℕ)<k by omega))
  have hrateA : ENNReal.ofReal (ca*ra) ≤
      approximationNumber (brownianIntegrationOperator d) k := by
    simpa [ra] using hA.1
  have hrateWlow : ENNReal.ofReal (cw*rw) ≤
      operatorKolmogorovNumber
        (brownianIntegrationOperator d ''
          {g : CameronMartin.UnitCubeL2 d | ‖g‖≤1}) k := by
    simpa [rw] using hW.1
  have hrateWhigh : operatorKolmogorovNumber
      (brownianIntegrationOperator d ''
        {g : CameronMartin.UnitCubeL2 d | ‖g‖≤1}) k ≤ ENNReal.ofReal (Cw*rw) := by
    simpa [rw] using hW.2
  have hrateAupper : approximationNumber (brownianIntegrationOperator d) k ≤
      ENNReal.ofReal (Ca*ra) := by
    simpa [ra] using hA.2
  have hcg : 0≤c*g := le_of_lt (mul_pos hc hg)
  have hCg : 0≤C*g := le_of_lt (mul_pos hC hg)
  have hlowProduct : ENNReal.ofReal (c*g) * ENNReal.ofReal (Cw*rw) =
      ENNReal.ofReal (ca*ra) := by
    rw [← ENNReal.ofReal_mul hcg]
    congr 1
    calc
      (c*g)*(Cw*rw) = ca*(g*rw) := by
        dsimp [c]
        field_simp
        <;> ring
      _ = ca*ra := by rw [hrate]
  have hhighProduct : ENNReal.ofReal (C*g) * ENNReal.ofReal (cw*rw) =
      ENNReal.ofReal (Ca*ra) := by
    rw [← ENNReal.ofReal_mul hCg]
    congr 1
    calc
      (C*g)*(cw*rw) = Ca*(g*rw) := by
        dsimp [C]
        field_simp
        <;> ring
      _ = Ca*ra := by rw [hrate]
  have hlower : ENNReal.ofReal (c*g) *
      operatorKolmogorovNumber
        (brownianIntegrationOperator d ''
          {g : CameronMartin.UnitCubeL2 d | ‖g‖≤1}) k ≤
      approximationNumber (brownianIntegrationOperator d) k := by
    calc
      _ ≤ ENNReal.ofReal (c*g) * ENNReal.ofReal (Cw*rw) :=
        by simpa [mul_comm] using mul_le_mul_left hrateWhigh (ENNReal.ofReal (c*g))
      _ = ENNReal.ofReal (ca*ra) := hlowProduct
      _ ≤ _ := hrateA
  have hupper : approximationNumber (brownianIntegrationOperator d) k ≤
      ENNReal.ofReal (C*g) * operatorKolmogorovNumber
        (brownianIntegrationOperator d ''
          {g : CameronMartin.UnitCubeL2 d | ‖g‖≤1}) k := by
    calc
      _ ≤ ENNReal.ofReal (Ca*ra) := hrateAupper
      _ = ENNReal.ofReal (C*g) * ENNReal.ofReal (cw*rw) := hhighProduct.symm
      _ ≤ _ := by simpa [mul_comm] using mul_le_mul_left hrateWlow (ENNReal.ofReal (C*g))
  simpa [g] using ⟨hlower,hupper⟩

end BrownianSharp.AlignmentBrownianLinearWidthGap
