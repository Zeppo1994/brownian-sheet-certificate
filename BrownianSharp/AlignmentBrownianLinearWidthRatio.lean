import BrownianSharp.AlignmentBrownianLinearWidthGap
import BrownianSharp.AlignmentWidthRates

/-! The literal approximation-number / Kolmogorov-number ratio in the
ordinary integration subcase. The denominator is proved positive and finite. -/
noncomputable section
open scoped ENNReal
namespace BrownianSharp.AlignmentBrownianLinearWidthRatio
open AlignmentBrownianLinearWidthGap AlignmentFractionalApproximationNumbers
open AlignmentOperatorNumbers

def brownianOperatorWidth (d k : ℕ) : ℝ≥0∞ :=
  operatorKolmogorovNumber
    (brownianIntegrationOperator d '' {g : CameronMartin.UnitCubeL2 d | ‖g‖≤1}) k

theorem brownian_linear_width_gap_ratio {d : ℕ} (hd : 2 ≤ d) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        0 < brownianOperatorWidth d k ∧ brownianOperatorWidth d k < ⊤ ∧
        ENNReal.ofReal (c*brownianGapFactor k) ≤
          approximationNumber (brownianIntegrationOperator d) k / brownianOperatorWidth d k ∧
        approximationNumber (brownianIntegrationOperator d) k / brownianOperatorWidth d k ≤
          ENNReal.ofReal (C*brownianGapFactor k) := by
  obtain ⟨c,C,hc,hC,kG,hkG,hG⟩ := brownian_linear_width_gap_product hd
  obtain ⟨cw,Cw,hcw,hCw,kW,hkW,hW⟩ := brownian_operator_width_two_sided hd
  refine ⟨c,C,hc,hC,max kG kW,by omega,?_⟩
  intro k hk
  have hk2 : 2 ≤ k := by omega
  have hw := hW k (by omega)
  have hg := hG k (by omega)
  have hr : 0 < logarithmicIndexRate 1 ((d:ℝ)-1/2) k :=
    AlignmentWidthRates.logarithmicIndexRate_pos _ _ hk2
  have hpos : 0 < brownianOperatorWidth d k :=
    (ENNReal.ofReal_pos.mpr (mul_pos hcw hr)).trans_le hw.1
  have hfin : brownianOperatorWidth d k < ⊤ :=
    hw.2.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hpos,hfin,?_,?_⟩
  · exact (ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl hfin.ne)).mpr hg.1
  · exact (ENNReal.div_le_iff hpos.ne' hfin.ne).mpr hg.2


def BrownianLinearWidthGapStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        0 < brownianOperatorWidth d k ∧ brownianOperatorWidth d k < ⊤ ∧
        ENNReal.ofReal (c*brownianGapFactor k) ≤
          approximationNumber (brownianIntegrationOperator d) k / brownianOperatorWidth d k ∧
        approximationNumber (brownianIntegrationOperator d) k / brownianOperatorWidth d k ≤
          ENNReal.ofReal (C*brownianGapFactor k)

theorem brownianLinearWidthGap_certified : BrownianLinearWidthGapStatement :=
  fun _ hd => brownian_linear_width_gap_ratio hd

end BrownianSharp.AlignmentBrownianLinearWidthRatio
