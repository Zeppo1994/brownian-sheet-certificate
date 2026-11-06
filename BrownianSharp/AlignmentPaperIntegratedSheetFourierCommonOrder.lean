import BrownianSharp.AlignmentPaperIntegratedSemigroupConsumer
import BrownianSharp.AlignmentGaussianIntegratedSmallBall
import BrownianSharp.AlignmentGaussianIntegratedReverse
import BrownianSharp.AlignmentPaperFractionalEntropyRoute
import BrownianSharp.AlignmentPaperFractionalFourierPreimage

/-! Common-order integrated-sheet lower log proof routed through the actual
Fourier scalar atom preimages, the generic entropy route, and the integrated
sheet Cameron--Martin shift theorem. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperIntegratedSheetFourierCommonOrder

open BrownianSharp.AlignmentPaperIntegratedSemigroupConsumer
open BrownianSharp.AlignmentGaussianIntegratedSmallBall
open BrownianSharp.AlignmentGaussianIntegratedReverse
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentPaperFractionalEntropyRoute
open BrownianSharp.AlignmentPaperFractionalFourierPreimage

/-- For a constant integration-order tuple, the integrated-sheet entropy lower rate comes
from the Fourier-derived scalar preimages through the generic native Gaussian
mass and entropy route. -/
theorem commonOrder_integratedSheet_oneSided_lowerLog_of_scalar
    {d : ℕ} (hd : 2 ≤ d) (m : ℕ) (hscalar : ScalarPreimages) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : BrownianSheetOnCube d Ω P) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        c * BrownianSharp.Latest.smallBallRate
          (2 / (2 * (m : ℝ) + 1))
          (((d - 1 : ℕ) : ℝ) + (d : ℝ) / (2 * (m : ℝ) + 1)) ε ≤
          -Real.log (P.real {ω | ‖integrateSheetPath (fun _ : Fin d => m)
            (B.path ω)‖ ≤ ε}) := by
  let r : ℝ := (m : ℝ) + 1
  let b : ℝ := r * ((d - 1 : ℕ) : ℝ) + 1 / 2
  have hr : 1 / 2 < r := by
    dsimp [r]
    have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg _
    linarith
  have hb : 0 ≤ b := by
    dsimp [b, r]
    positivity
  have hEntropy :
      ∃ c' : ℝ, 0 < c' ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c' * BrownianSharp.logarithmicIndexRate r b k) ≤
          HaarQuarter.TheoremD.entropyNumber k
            (BrownianSharp.Latest.fractionalIntegrationBall
              (fun _ : Fin d => (m : ℝ) + 1)) := by
    obtain ⟨c',hc',k₀,hk₀,hE⟩ :=
      AlignmentPaperFractionalEntropyRoute.entropy_lower_of_scalar
        hd hr hscalar
    refine ⟨c',hc',k₀,?_⟩
    intro k hk
    have hh := hE k hk
    simpa [BrownianSharp.logarithmicIndexRate, r, b, mul_assoc] using hh
  obtain ⟨c, ε₀, hc, hε₀, hε₀exp, hUniform⟩ :=
    BrownianSharp.AlignmentGaussianEntropySmallBall.uniform_smallBall_probability_upper_of_entropy_lower
      (BrownianSharp.Latest.fractionalIntegrationBall
        (fun _ : Fin d => (m : ℝ) + 1))
      r b hr hb hEntropy
  refine ⟨c, ε₀, hc, hε₀, hε₀exp, ?_⟩
  intro Ω _ P _ B ε hε hsmall
  let mTuple : Fin d → ℕ := fun _ => m
  let μ := integratedSheetSemigroupLaw B mTuple
  have hμ : μ = integratedSheetLaw B mTuple :=
    integratedSheetSemigroupLaw_eq_integratedSheetLaw B mTuple
  letI : IsProbabilityMeasure μ := by
    rw [hμ]
    change IsProbabilityMeasure (P.map (integrateBrownianSheetPath B mTuple))
    refine ⟨?_⟩
    rw [Measure.map_apply (measurable_integrateBrownianSheetPath B mTuple)
      MeasurableSet.univ]
    simp
  have hshift : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η →
      ∀ x ∈ BrownianSharp.Latest.fractionalIntegrationBall
        (fun _ : Fin d => (m : ℝ) + 1),
        ENNReal.ofReal (Real.exp (-(R ^ 2) / 2)) *
          μ (Metric.closedBall 0 η) ≤ μ (Metric.closedBall (R • x) η) := by
    intro R hR η hη x hx
    exact integratedSheetSemigroupLaw_ball_shift_lower B mTuple R η hR hη x hx
  have hprob := hUniform μ inferInstance hshift ε hε (by simpa [μ] using hsmall)
  have hball : MeasurableSet
      (Metric.closedBall (0 : C(BrownianCubeAnchor d, ℝ)) ε) :=
    measurableSet_closedBall
  have hmass : μ.real (Metric.closedBall 0 ε) =
      P.real {ω | ‖integrateSheetPath mTuple (B.path ω)‖ ≤ ε} := by
    rw [hμ]
    change (P.map (integrateBrownianSheetPath B mTuple)).real
      (Metric.closedBall 0 ε) = _
    rw [Measure.real_def,
      Measure.map_apply (measurable_integrateBrownianSheetPath B mTuple) hball,
      Measure.real_def]
    congr 1
  have hpositive : 0 < P.real
      {ω | ‖integrateSheetPath mTuple (B.path ω)‖ ≤ ε} :=
    BrownianSharp.AlignmentIntegratedNorm.integrated_smallBall_probability_pos
      P B mTuple hε
  have hpositiveμ : 0 < μ.real (Metric.closedBall 0 ε) := by
    rw [hmass]
    exact hpositive
  have hlog := Real.log_le_log hpositiveμ hprob
  rw [Real.log_exp] at hlog
  have hden : (1 + (m : ℝ) * 2) ≠ 0 := by positivity
  have hden' : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  have hden'' : ((m : ℝ) + 1 - 1 / 2) ≠ 0 := by positivity
  have hdenEq : 2 * (m : ℝ) + 1 = 1 + (m : ℝ) * 2 := by ring
  have hrpow : (r - 1 / 2)⁻¹ = 2 / (2 * (m : ℝ) + 1) := by
    dsimp [r]
    rw [show (m : ℝ) + 1 - 1 / 2 = (1 + (m : ℝ) * 2) / 2 by ring]
    rw [inv_div, hdenEq]
  have habeta : b / (r - 1 / 2) =
      ((d - 1 : ℕ) : ℝ) + (d : ℝ) / (2 * (m : ℝ) + 1) := by
    dsimp [b, r]
    have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
    rw [hcast]
    rw [show (m : ℝ) + 1 - 1 / 2 = (1 + (m : ℝ) * 2) / 2 by ring]
    field_simp [hden, hden', hden'']
    <;> ring
  have hrate : BrownianSharp.Latest.smallBallRate (r - 1 / 2)⁻¹
      (b / (r - 1 / 2)) ε =
      BrownianSharp.Latest.smallBallRate
        (2 / (2 * (m : ℝ) + 1))
        (((d - 1 : ℕ) : ℝ) + (d : ℝ) / (2 * (m : ℝ) + 1)) ε := by
    rw [hrpow, habeta]
  rw [hmass, hrate] at hlog
  linarith

/-- Common-order integrated-sheet two-sided estimate. The lower side uses
Fourier scalar preimages through entropy and the actual integrated-sheet
shift; the upper side remains the independent dyadic reverse argument. -/
theorem commonOrder_integratedSheet_certified_of_scalar
    {d : ℕ} (hd : 2 ≤ d) (m : ℕ) (hscalar : ScalarPreimages) :
    ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : BrownianSheetOnCube d Ω P) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        c * BrownianSharp.Latest.smallBallRate
          (2 / (2 * (m : ℝ) + 1))
          (((d - 1 : ℕ) : ℝ) + (d : ℝ) / (2 * (m : ℝ) + 1)) ε ≤
          -Real.log (P.real {ω | ‖integrateSheetPath (fun _ : Fin d => m)
            (B.path ω)‖ ≤ ε}) ∧
        -Real.log (P.real {ω | ‖integrateSheetPath (fun _ : Fin d => m)
            (B.path ω)‖ ≤ ε}) ≤
          C * BrownianSharp.Latest.smallBallRate
            (2 / (2 * (m : ℝ) + 1))
            (((d - 1 : ℕ) : ℝ) + (d : ℝ) / (2 * (m : ℝ) + 1)) ε := by
  let mTuple : Fin d → ℕ := fun _ => m
  have hm : BrownianSharp.Latest.minimumMultiplicity
      (fun i => (mTuple i : ℝ)) (m : ℝ) d := by
    constructor
    · intro i
      exact le_rfl
    · simp [mTuple]
  obtain ⟨c, εc, hc, hεc, hεcsmall, hlower⟩ :=
    commonOrder_integratedSheet_oneSided_lowerLog_of_scalar hd m hscalar
  obtain ⟨C, εC, hC, hεC, hεCsmall, hupper⟩ :=
    AlignmentGaussianIntegratedReverse.integratedSheet_oneSided_upperLog
      hd mTuple m d (by omega) hm
  refine ⟨c, C, min εc εC, hc, hC, lt_min hεc hεC,
    (min_le_left _ _).trans_lt hεcsmall, ?_⟩
  intro Ω _ P _ B ε hε hsmall
  exact ⟨hlower Ω P B ε hε (hsmall.trans (min_le_left _ _)),
    hupper Ω P B ε hε (hsmall.trans (min_le_right _ _))⟩

/-- Concrete theorem: use the compiled Fourier-derived scalar provider, with
all entropy and small-ball constants chosen before the sheet realization. -/
theorem paperIntegratedSheet_commonOrder_fourier_certified :
    ∀ d : ℕ, 2 ≤ d → ∀ m : ℕ,
      ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (B : BrownianSheetOnCube d Ω P) (ε : ℝ), 0 < ε → ε ≤ ε₀ →
          c * BrownianSharp.Latest.smallBallRate
            (2 / (2 * (m : ℝ) + 1))
            (((d - 1 : ℕ) : ℝ) + (d : ℝ) / (2 * (m : ℝ) + 1)) ε ≤
            -Real.log (P.real {ω | ‖integrateSheetPath (fun _ : Fin d => m)
              (B.path ω)‖ ≤ ε}) ∧
          -Real.log (P.real {ω | ‖integrateSheetPath (fun _ : Fin d => m)
              (B.path ω)‖ ≤ ε}) ≤
            C * BrownianSharp.Latest.smallBallRate
              (2 / (2 * (m : ℝ) + 1))
              (((d - 1 : ℕ) : ℝ) + (d : ℝ) / (2 * (m : ℝ) + 1)) ε := by
  intro d hd m
  exact commonOrder_integratedSheet_certified_of_scalar hd m
    (fun α hα =>
      smoothAtom_dyadic_fractional_preimage_fourier hα)

end BrownianSharp.AlignmentPaperIntegratedSheetFourierCommonOrder
