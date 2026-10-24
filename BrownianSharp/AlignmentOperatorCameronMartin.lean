import BrownianSharp.NativeCameronMartinCoverRate
import BrownianSharp.AlignmentOperatorStatements
import BrownianSharp.AlignmentOperatorWidthIndexShift
import Mathlib.Tactic

/-! Assembly of the checked Cameron--Martin covering/entropy/width estimates
into the revised strict-rank operator-number statement. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentOperatorCameronMartin

open BrownianSharp
open BrownianSharp.AlignmentOperatorStatements
open BrownianSharp.AlignmentOperatorNumbers
open BrownianSharp.AlignmentOperatorWidthIndexShift
open HaarQuarter.TheoremD
open HaarQuarter.TheoremD.Width

private theorem cmIndexRate_nonneg {d k : ℕ} (hd : 2 ≤ d) (hk : 2 ≤ k) :
    0 ≤ cmIndexRate d k := by
  unfold cmIndexRate logarithmicIndexRate
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hlog : 0 ≤ Real.log (k:ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ k by omega))
  have ha : 0 ≤ (d:ℝ)-1/2 := by
    have h : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    linarith
  positivity

private theorem cmCoveringRate_nonneg {d : ℕ} (hd : 2 ≤ d)
    {t t₀ : ℝ} (ht : 0 < t) (ht₀ : t₀ < Real.exp (-1)) (htt₀ : t ≤ t₀) :
    0 ≤ cmCoveringRate d t := by
  unfold cmCoveringRate
  have ht₀pos : 0 < t₀ := lt_of_lt_of_le ht htt₀
  have hinv0 : Real.exp 1 < t₀⁻¹ := by
    have h := one_div_lt_one_div_of_lt ht₀pos ht₀
    simpa [one_div, Real.exp_neg] using h
  have hinv : Real.exp 1 < t⁻¹ := by
    have h := one_div_le_one_div_of_le ht htt₀
    exact hinv0.trans_le (by simpa [one_div] using h)
  have hlog : 0 < Real.log t⁻¹ := by
    apply Real.log_pos
    have h1 : (1:ℝ) < Real.exp 1 := by
      have h := Real.add_one_lt_exp (by norm_num : (1:ℝ) ≠ 0)
      linarith
    exact lt_trans h1 hinv
  have ha : 0 ≤ (d:ℝ)-1/2 := by
    have h : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
    linarith
  positivity

/-- The old set-width theorem uses dimension at most `k`; the revised
operator number uses rank strictly below `k`, hence equals the old width at
`k-1`. Antitonicity transfers the lower bound at `k`, while the checked
adjacent-rate comparison transfers the upper bound from `k-1`. -/
theorem cameronMartinEntropyWidth_certified :
    AlignmentOperatorStatements.CameronMartinEntropyWidthStatement := by
  intro d hd
  obtain ⟨c₀,C₀,t₀,hc₀,hC₀,ht₀,ht₀small,hcover,hexists⟩ :=
    BrownianSharp.cameronMartinEntropyWidth_certified d hd
  obtain ⟨kOld,hkOld,hindex⟩ := hexists
  let c : ℝ := c₀
  let C : ℝ := max C₀ (2*C₀)
  have hc : 0 < c := by simpa [c] using hc₀
  have hC : 0 < C := by
    dsimp [C]
    exact lt_of_lt_of_le hC₀ (le_max_left _ _)
  have hk₀ : 2 ≤ max (kOld+1) 3 := by omega
  refine ⟨c,C,t₀,hc,hC,ht₀,ht₀small,?_,⟨max (kOld+1) 3,hk₀,?_⟩⟩
  · intro t ht htt₀
    obtain ⟨hfinite,hlo,hhi⟩ := hcover t ht htt₀
    have hrate := cmCoveringRate_nonneg hd ht ht₀small htt₀
    have hc_le : c ≤ c₀ := by simp [c]
    have hC_ge : C₀ ≤ C := le_max_left _ _
    refine ⟨hfinite,?_,?_⟩
    · exact (mul_le_mul_of_nonneg_right hc_le hrate).trans hlo
    · exact hhi.trans (mul_le_mul_of_nonneg_right hC_ge hrate)
  · intro k hk
    have hk3 : 3 ≤ k := le_trans (le_max_right _ _) hk
    have hkOld' : kOld ≤ k-1 := by
      have hkleft : kOld+1 ≤ max (kOld+1) 3 := le_max_left _ _
      omega
    have hkOldK : kOld ≤ k := by omega
    have hOldK := hindex k hkOldK
    have hOldPred := hindex (k-1) hkOld'
    have hrate := rate_succ_comparable
      (r:=1) (a:=(d:ℝ)-1/2) (by norm_num) (by
        have h : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
        linarith) hk3
    have hratePred : cmIndexRate d (k-1) ≤ 2*cmIndexRate d k := by
      simpa [cmIndexRate, logarithmicIndexRate] using hrate.2
    have hrateNonneg : 0 ≤ cmIndexRate d k := cmIndexRate_nonneg hd (by omega)
    have hC₀le : C₀ ≤ C := le_max_left _ _
    have h2C₀le : 2*C₀ ≤ C := le_max_right _ _
    have hcast : k-1+1=k := Nat.sub_add_cancel (by omega : 1 ≤ k)
    have hwidthLower :
        ENNReal.ofReal (c * cmIndexRate d k) ≤
          operatorKolmogorovNumber (CameronMartin.KdUnitCube d) k := by
      rw [operatorKolmogorovNumber_eq_width_pred
        (CameronMartin.KdUnitCube d) (by omega : 1 ≤ k)]
      have hmono := kolmogorovWidth_antitone
        (CameronMartin.KdUnitCube d) (show k-1 ≤ k by omega)
      exact le_trans (by simpa [c] using hOldK.2.2.1) hmono
    have hwidthUpper :
        operatorKolmogorovNumber (CameronMartin.KdUnitCube d) k ≤
          ENNReal.ofReal (C * cmIndexRate d k) := by
      rw [operatorKolmogorovNumber_eq_width_pred
        (CameronMartin.KdUnitCube d) (by omega : 1 ≤ k)]
      calc
        kolmogorovWidth (CameronMartin.KdUnitCube d) (k-1) ≤
            ENNReal.ofReal (C₀*cmIndexRate d (k-1)) := hOldPred.2.2.2
        _ ≤ ENNReal.ofReal (C*cmIndexRate d k) := by
          apply ENNReal.ofReal_le_ofReal
          have hmul := mul_le_mul_of_nonneg_left hratePred (le_of_lt hC₀)
          have hmul' : C₀*cmIndexRate d (k-1) ≤
              (2*C₀)*cmIndexRate d k := by nlinarith
          exact hmul'.trans (mul_le_mul_of_nonneg_right h2C₀le hrateNonneg)
    have hEntLower : ENNReal.ofReal (c*cmIndexRate d k) ≤
        entropyNumber k (CameronMartin.KdUnitCube d) := by
      simpa [c] using hOldK.1
    have hEntUpper : entropyNumber k (CameronMartin.KdUnitCube d) ≤
        ENNReal.ofReal (C*cmIndexRate d k) := by
      exact le_trans hOldK.2.1
        (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right hC₀le hrateNonneg))
    exact ⟨hEntLower,hEntUpper,hwidthLower,hwidthUpper⟩

end BrownianSharp.AlignmentOperatorCameronMartin
