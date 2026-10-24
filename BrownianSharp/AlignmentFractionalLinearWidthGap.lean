import BrownianSharp.AlignmentOperatorFractional
import BrownianSharp.AlignmentFractionalApproximationStatement
import BrownianSharp.AlignmentBrownianLinearWidthRatio

/-! The exact general fractional linear/width ratio, conditional only on its
remaining approximation-number lower bound. This is not an unconditional
completion of that still-open lower bound. -/
noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentFractionalLinearWidthGap
open AlignmentFractionalTensorOperator AlignmentFractionalApproximationNumbers
  AlignmentOperatorNumbers AlignmentBrownianLinearWidthGap

def fractionalOperatorWidth {d : ℕ} (a : Fin d → ℝ) (k : ℕ) : ℝ≥0∞ :=
  operatorKolmogorovNumber (Latest.fractionalIntegrationBall a) k

theorem gap_rate_identity (r a : ℝ) {k : ℕ} (hk : 2 ≤ k) :
    brownianGapFactor k * logarithmicIndexRate r (a+1/2) k =
      logarithmicIndexRate (r-1/2) a k := by
  have hx : 0 < (k:ℝ) := by exact_mod_cast (show 0<k by omega)
  have hl : 0 < Real.log (k:ℝ) :=
    Real.log_pos (by exact_mod_cast (show (1:ℕ)<k by omega))
  unfold brownianGapFactor logarithmicIndexRate
  rw [Real.sqrt_div hx.le,Real.sqrt_eq_rpow,Real.sqrt_eq_rpow,div_eq_mul_inv,
    ← Real.rpow_neg hl.le (1/2:ℝ)]
  calc
    _ = (((k:ℝ)^(1/2:ℝ)*(k:ℝ)^(-r))*
        ((Real.log (k:ℝ))^(-1/2:ℝ)*(Real.log (k:ℝ))^(a+1/2))) := by ring
    _ = _ := by
      rw [← Real.rpow_add hx (1/2:ℝ) (-r),
        ← Real.rpow_add hl (-1/2:ℝ) (a+1/2)]
      congr 1 <;> congr 1 <;> ring

/-- Once the sharp lower approximation rate is supplied, the already checked
upper approximation and width rates imply the literal quotient, with a
strictly positive finite width denominator. -/
theorem fractional_linear_width_gap_of_approximation_lower
    {d ν : ℕ} (hd : 2 ≤ d) (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i)
    (r : ℝ) (hν : 2 ≤ ν) (hm : Latest.minimumMultiplicity a r ν)
    (hlower : ∃ ca : ℝ, 0 < ca ∧ ∃ kA : ℕ, 2 ≤ kA ∧
      ∀ k : ℕ, kA ≤ k →
        ENNReal.ofReal (ca*logarithmicIndexRate (r-1/2) (r*((ν-1:ℕ):ℝ)) k) ≤
          approximationNumber (fractionalTensorRL a ha) k) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        0 < fractionalOperatorWidth a k ∧ fractionalOperatorWidth a k < ⊤ ∧
        ENNReal.ofReal (c*brownianGapFactor k) ≤
          approximationNumber (fractionalTensorRL a ha) k / fractionalOperatorWidth a k ∧
        approximationNumber (fractionalTensorRL a ha) k / fractionalOperatorWidth a k ≤
          ENNReal.ofReal (C*brownianGapFactor k) := by
  obtain ⟨ca,hca,kA,hkA,hA⟩ := hlower
  obtain ⟨Ca,hCa,kU,hkU,hU⟩ :=
    AlignmentFractionalApproximationStatement.fractionalApproximation_upper_certified
      d hd a ha r ν hν hm
  obtain ⟨cw,Cw,hcw,hCw,kW,hkW,hW⟩ :=
    AlignmentOperatorFractional.fractionalEntropyWidth_certified d hd a ha r ν hν hm
  let c := ca/Cw
  let C := Ca/cw
  refine ⟨c,C,div_pos hca hCw,div_pos hCa hcw,max kA (max kU kW),by omega,?_⟩
  intro k hk
  have hk2 : 2 ≤ k := by omega
  have hlow := hA k (by omega)
  have hup := hU k (by omega)
  have hw := hW k (by omega)
  let ra := logarithmicIndexRate (r-1/2) (r*((ν-1:ℕ):ℝ)) k
  let rw := logarithmicIndexRate r (r*((ν-1:ℕ):ℝ)+1/2) k
  let g := brownianGapFactor k
  have hrate : g*rw=ra := gap_rate_identity _ _ hk2
  have hrateW : 0 < rw := AlignmentWidthRates.logarithmicIndexRate_pos _ _ hk2
  have hg : 0 < g := by
    dsimp [g,brownianGapFactor]
    apply Real.sqrt_pos.mpr
    exact div_pos (by exact_mod_cast (show 0<k by omega))
      (Real.log_pos (by exact_mod_cast (show (1:ℕ)<k by omega)))
  have hwlo : ENNReal.ofReal (cw*rw) ≤ fractionalOperatorWidth a k := by
    simpa [fractionalOperatorWidth,rw] using hw.2.2.1
  have hwhi : fractionalOperatorWidth a k ≤ ENNReal.ofReal (Cw*rw) := by
    simpa [fractionalOperatorWidth,rw] using hw.2.2.2
  have hwpos : 0 < fractionalOperatorWidth a k :=
    (ENNReal.ofReal_pos.mpr (mul_pos hcw hrateW)).trans_le hwlo
  have hwfin : fractionalOperatorWidth a k < ⊤ := hwhi.trans_lt ENNReal.ofReal_lt_top
  have hloIdentity : (c*g)*(Cw*rw)=ca*ra := by
    rw [← hrate]
    dsimp [c]
    field_simp
    <;> ring
  have hhiIdentity : (C*g)*(cw*rw)=Ca*ra := by
    rw [← hrate]
    dsimp [C]
    field_simp
    <;> ring
  refine ⟨hwpos,hwfin,?_,?_⟩
  · apply (ENNReal.le_div_iff_mul_le (Or.inl hwpos.ne') (Or.inl hwfin.ne)).mpr
    calc
      _ ≤ ENNReal.ofReal (c*g)*ENNReal.ofReal (Cw*rw) := mul_le_mul' le_rfl hwhi
      _ = ENNReal.ofReal (ca*ra) := by
        rw [← ENNReal.ofReal_mul (by dsimp [c]; positivity),hloIdentity]
      _ ≤ _ := hlow
  · apply (ENNReal.div_le_iff hwpos.ne' hwfin.ne).mpr
    calc
      _ ≤ ENNReal.ofReal (Ca*ra) := hup
      _ = ENNReal.ofReal (C*g)*ENNReal.ofReal (cw*rw) := by
        rw [← ENNReal.ofReal_mul (by dsimp [C]; positivity),hhiIdentity]
      _ ≤ _ := mul_le_mul' le_rfl hwlo

end BrownianSharp.AlignmentFractionalLinearWidthGap
