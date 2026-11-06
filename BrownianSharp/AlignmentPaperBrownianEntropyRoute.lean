import BrownianSharp.AlignmentPaperAnchoredLpLower
import BrownianSharp.AlignmentPaperAnchoredLpOperator
import BrownianSharp.AlignmentFractionalUnitOrders
import BrownianSharp.AlignmentGaussianIntegratedSmallBall
import BrownianSharp.AlignmentGaussianBrownianReverse

/-!
Section 4 of the manuscript: the lower bound of Theorem 1.1 via the entropy
numbers of the Cameron--Martin ball (Theorem 1.2 at `p = 2`) and the
Kuelbs--Li--Linde correspondence (4.1) with `r = 1`, `β = d - 1/2`. The
Cameron--Martin shift inequality for the Brownian sheet law is the case
`m = 0` of the integrated-sheet shift.
-/

noncomputable section
open MeasureTheory HaarQuarter

namespace BrownianSharp.AlignmentPaperBrownianEntropyRoute

open BrownianSharp.AlignmentGaussianIntegratedSmallBall
open BrownianSharp.AlignmentGaussianRates

/-- Theorem 1.1, lower bound, proved as in Section 4: Theorem 1.2 for the
unit ball of `H_B = T_d(L_2)` (`p = 2`, identified with `K_d`), the
Cameron--Martin shift for the sheet law, and the lower implication of (4.1)
with `r = 1`, `β = d - 1/2`. -/
theorem brownian_lowerLog_paperRoute :
    ∀ d : ℕ, 2 ≤ d → ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : BrownianSheetOnCube d Ω P) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        c * sharpRate d ε ≤ -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε}) := by
  intro d hd
  obtain ⟨c₁, hc₁, k₀, -, hE⟩ :=
    AlignmentPaperAnchoredLpLower.anchoredIntegrationLp_entropy_lower_all_p hd 2
      (by norm_num)
  rw [AlignmentPaperAnchoredLpOperator.anchoredIntegrationLpImage_two_eq_KdUnitCube] at hE
  obtain ⟨c, ε₀, hc, hε₀, hε₀e, hU⟩ :=
    AlignmentGaussianEntropySmallBall.uniform_smallBall_probability_upper_of_entropy_lower
      (CameronMartin.KdUnitCube d) 1 ((d : ℝ) - 1 / 2) (by norm_num)
      (by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
          linarith)
      ⟨c₁, hc₁, k₀, hE⟩
  refine ⟨c, ε₀, hc, hε₀, hε₀e, ?_⟩
  intro Ω _ P _ B ε hε hsmall
  have hpath : integrateBrownianSheetPath B (fun _ => 0) = B.path := by
    funext ω
    exact integrateSheetPath_zero (B.path ω)
  have hlaw : integratedSheetLaw B (fun _ => 0) = P.map B.path := by
    rw [integratedSheetLaw, hpath]
  have : IsProbabilityMeasure (P.map B.path) :=
    ⟨by rw [Measure.map_apply B.measurable_path MeasurableSet.univ]; simp⟩
  have hshift : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η → ∀ x ∈ CameronMartin.KdUnitCube d,
      ENNReal.ofReal (Real.exp (-(R ^ 2) / 2)) * (P.map B.path) (Metric.closedBall 0 η) ≤
        (P.map B.path) (Metric.closedBall (R • x) η) := by
    intro R hR η hη x hx
    rw [← hlaw]
    refine integratedSheetLaw_ball_shift_lower B (fun _ => 0) R η hR hη x ?_
    rw [← AlignmentFractionalUnitOrders.fractionalIntegrationBall_one_eq_KdUnitCube] at hx
    simpa using hx
  have hprob := hU _ inferInstance hshift ε hε hsmall
  have hmass : (P.map B.path).real (Metric.closedBall 0 ε) =
      P.real {ω | ‖B.path ω‖ ≤ ε} := by
    rw [Measure.real_def, Measure.map_apply B.measurable_path measurableSet_closedBall,
      Measure.real_def]
    congr 3
  rw [hmass] at hprob
  have hlog := Real.log_le_log (B.smallBall_probability_pos hε) hprob
  rw [Real.log_exp] at hlog
  have hrate : Latest.smallBallRate ((1 : ℝ) - 1 / 2)⁻¹
      (((d : ℝ) - 1 / 2) / (1 - 1 / 2)) ε = sharpRate d ε := by
    have h1 : ((1 : ℝ) - 1 / 2)⁻¹ = 2 := by norm_num
    have h2 : ((d : ℝ) - 1 / 2) / (1 - 1 / 2) = 2 * d - 1 := by ring
    have h3 : (2 * (d : ℝ) - 1) = ((2 * d - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [h1, h2, h3]
    simp only [Latest.smallBallRate, sharpRate, Real.rpow_natCast, Real.rpow_two]
  rw [hrate] at hlog
  linarith

/-- Theorem 1.1 (two-sided), with the lower bound obtained through the
entropy route of Section 4 and the upper bound from the certificate. -/
theorem brownianTwoSided_paperRoute : Latest.BrownianTwoSidedStatement := by
  intro d hd
  obtain ⟨c, ε₀, hc, hε₀, hε₀e, hlow⟩ := brownian_lowerLog_paperRoute d hd
  obtain ⟨c', C, ε₀', hc', hC, hε₀', hε₀e', hboth⟩ :=
    AlignmentGaussianBrownianReverse.latest_brownian_twoSided_certified d hd
  refine ⟨c, C, min ε₀ ε₀', hc, hC, lt_min hε₀ hε₀',
    (min_le_left _ _).trans_lt hε₀e, ?_⟩
  intro Ω _ P _ B ε hε hsmall
  exact ⟨hlow Ω P B ε hε (hsmall.trans (min_le_left _ _)),
    (hboth Ω P B ε hε (hsmall.trans (min_le_right _ _))).2⟩

end BrownianSharp.AlignmentPaperBrownianEntropyRoute
