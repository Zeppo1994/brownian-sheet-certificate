import BrownianSharp.AlignmentOperatorStatements
import BrownianSharp.AlignmentOperatorWidthIndexShift
import BrownianSharp.AlignmentLatestFractionalPolynomialWidth

/-! The actual RL image with the revised manuscript's strict operator index. -/
noncomputable section
open scoped ENNReal

namespace BrownianSharp.AlignmentOperatorFractional
open BrownianSharp
open BrownianSharp.AlignmentOperatorStatements
open BrownianSharp.AlignmentOperatorNumbers
open BrownianSharp.AlignmentOperatorWidthIndexShift
open BrownianSharp.AlignmentWidthRates
open HaarQuarter.TheoremD.Width

theorem fractionalEntropyWidth_certified :
    AlignmentOperatorStatements.FractionalEntropyWidthStatement := by
  intro d hd a ha r ν hν hm
  classical
  have hcount : 0 < (Finset.univ.filter (fun i : Fin d => a i = r)).card := by
    rw [hm.2]
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcount
  have hieq : a i = r := (Finset.mem_filter.mp hi).2
  have hr : 0 < r := by
    have h := ha i
    rw [hieq] at h
    linarith
  let α : ℝ := r * (ν-1:ℕ) + 1/2
  have hα : 0 ≤ α := by dsimp [α]; positivity
  obtain ⟨c₀,C₀,hc₀,hC₀,kOld,hkOld,hindex⟩ :=
    AlignmentLatestFractionalPolynomialWidth.latest_fractional_entropy_width
      d hd a ha r ν hν hm
  let C : ℝ := max C₀ (C₀ * 2^r)
  have hC : 0 < C := hC₀.trans_le (le_max_left _ _)
  refine ⟨c₀,C,hc₀,hC,max (kOld+1) 3,by omega,?_⟩
  intro k hk
  have hk3 : 3 ≤ k := (le_max_right _ _).trans hk
  have hkOld' : kOld ≤ k-1 := by
    have := (le_max_left (kOld+1) 3).trans hk
    omega
  have hkOldK : kOld ≤ k := by omega
  have hK := hindex k hkOldK
  have hPred := hindex (k-1) hkOld'
  have hrate : 0 ≤ logarithmicIndexRate r α k :=
    logarithmicIndexRate_nonneg r α k
  have hpredRate := (rate_succ_comparable hr hα hk3).2
  change logarithmicIndexRate r α (k-1) ≤ 2^r * logarithmicIndexRate r α k at hpredRate
  refine ⟨hK.1,?_,?_,?_⟩
  · exact hK.2.1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left C₀ (C₀*2^r)) hrate))
  · rw [operatorKolmogorovNumber_eq_width_pred
      (Latest.fractionalIntegrationBall a) (by omega : 1 ≤ k)]
    exact hK.2.2.1.trans (kolmogorovWidth_antitone
      (Latest.fractionalIntegrationBall a) (Nat.sub_le k 1))
  · rw [operatorKolmogorovNumber_eq_width_pred
      (Latest.fractionalIntegrationBall a) (by omega : 1 ≤ k)]
    refine hPred.2.2.2.trans (ENNReal.ofReal_le_ofReal ?_)
    have hmul := mul_le_mul_of_nonneg_left hpredRate hc₀.le
    have hmul' := mul_le_mul_of_nonneg_left hpredRate hC₀.le
    calc
      C₀ * logarithmicIndexRate r α (k-1) ≤
          (C₀ * 2^r) * logarithmicIndexRate r α k := by
            simpa only [mul_assoc] using hmul'
      _ ≤ C * logarithmicIndexRate r α k :=
        mul_le_mul_of_nonneg_right (le_max_right C₀ (C₀*2^r)) hrate

end BrownianSharp.AlignmentOperatorFractional
