import BrownianSharp.AlignmentFractionalSheetShift
import BrownianSharp.AlignmentGaussianEntropySmallBall
import BrownianSharp.AlignmentGaussianFractionalReverseClosure
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory HaarQuarter
open scoped ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalSheetLowerLog

open BrownianSharp.AlignmentFractionalSheetTensorFeature
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentGaussianGradedKernelReverse
open BrownianSharp.AlignmentGaussianGradedReverseClosure
open BrownianSharp.AlignmentGaussianDiagonalCoordinates
open BrownianSharp.AlignmentExponentialGradedReverseInversion
open GaussianProjection
open HaarQuarter
open BrownianSharp.Latest
open BrownianSharp.AlignmentFractionalSheetEntropy
open BrownianSharp.AlignmentFractionalSheetShift
open BrownianSharp.AlignmentGaussianEntropySmallBall
open BrownianSharp.AlignmentCompactFeatureBall

/-- Lower logarithmic small-ball bound for an actual fractional Brownian
sheet. The strict-positivity premise is explicit because Lean's real logarithm
uses `log 0 = 0`; the companion actual-sheet upper-log theorem supplies this
positivity in the final two-sided application. -/
theorem fractionalSheet_oneSided_lowerLog_of_positive
    {d ν : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (hν : 2 ≤ ν)
    (m₀ : ℝ) (hm : Latest.minimumMultiplicity H m₀ ν) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : FractionalBrownianSheetOnCube d Ω P), B.H = H →
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          0 < P.real {ω | ‖B.path ω‖ ≤ ε} →
          c * Latest.smallBallRate (m₀⁻¹)
            (((ν-1:ℕ):ℝ) + (ν:ℝ)/(2*m₀)) ε ≤
            -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε}) := by
  classical
  let r : ℝ := m₀ + 1/2
  let b : ℝ := r * ((ν-1:ℕ):ℝ) + 1/2
  have hm' : (∀ i, m₀ ≤ H i) ∧
      (Finset.univ.filter (fun i : Fin d => H i = m₀)).card = ν := by
    change (∀ i, m₀ ≤ H i) ∧
      (Finset.univ.filter (fun i : Fin d => H i = m₀)).card = ν at hm
    exact hm
  have hcardpos : 0 < (Finset.univ.filter (fun i : Fin d => H i = m₀)).card := by
    rw [hm'.2]
    omega
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hcardpos
  have hmin : H i = m₀ := (Finset.mem_filter.mp hi).2
  have hmpos : 0 < m₀ := by linarith [(hH i).1]
  have hr : 1/2 < r := by dsimp [r]; linarith
  have hb : 0 ≤ b := by dsimp [b,r]; positivity
  obtain ⟨cE, hcE, k₀, hk₀, hE⟩ :=
    fractionalSheetFeature_entropy_lower hd H hH hν m₀ hm
  have hEntropy : ∃ c : ℝ, 0 < c ∧ ∃ k₁ : ℕ, ∀ k : ℕ, k₁ ≤ k →
      ENNReal.ofReal (c * BrownianSharp.logarithmicIndexRate r b k) ≤
        HaarQuarter.TheoremD.entropyNumber k (featureBall (fractionalSheetFeature H hH)) := by
    refine ⟨cE, hcE, k₀, ?_⟩
    intro k hk
    have h := hE k hk
    simpa [BrownianSharp.logarithmicIndexRate, r, b, mul_assoc] using h
  obtain ⟨c, ε₀, hc, hε₀, hε₀exp, hUpper⟩ :=
    uniform_smallBall_probability_upper_of_entropy_lower
      (featureBall (fractionalSheetFeature H hH)) r b hr hb hEntropy
  refine ⟨c, ε₀, hc, hε₀, hε₀exp, ?_⟩
  intro Ω _ P _ B hBH ε hε hsmall hpositive
  let μ : Measure C(BrownianCubeAnchor d,ℝ) := fractionalSheetLaw B
  have hμ : IsProbabilityMeasure μ := by
    change IsProbabilityMeasure (P.map B.path)
    refine ⟨?_⟩
    rw [Measure.map_apply B.measurable_path MeasurableSet.univ]
    simp
  have hmass : μ.real (Metric.closedBall 0 ε) =
      P.real {ω | ‖B.path ω‖ ≤ ε} := by
    change (P.map B.path).real (Metric.closedBall 0 ε) = _
    rw [Measure.real_def,
      Measure.map_apply B.measurable_path measurableSet_closedBall,
      Measure.real_def]
    congr 1
  have hshift : ∀ R : ℝ, 0 < R → ∀ η : ℝ, 0 < η →
      ∀ x ∈ featureBall (fractionalSheetFeature H hH),
        ENNReal.ofReal (Real.exp (-(R^2)/2)) * μ (Metric.closedBall 0 η) ≤
          μ (Metric.closedBall (R • x) η) := by
    intro R hR η hη x hx
    exact fractionalSheetLaw_ball_shift_lower B H hH hBH R η hR hη x hx
  have hprob := hUpper μ hμ hshift ε hε hsmall
  have hpow : (r - 1/2)⁻¹ = m₀⁻¹ := by
    dsimp [r]
    ring
  have hcast : ((ν-1:ℕ):ℝ) = (ν:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ν)]
    norm_num
  have hlogpow : b/(r-1/2) = ((ν-1:ℕ):ℝ) + (ν:ℝ)/(2*m₀) := by
    dsimp [b,r]
    rw [hcast]
    field_simp [ne_of_gt hmpos]
    <;> ring
  have hmassε : μ.real (Metric.closedBall 0 ε) =
      P.real {ω | ‖B.path ω‖ ≤ ε} := hmass
  have hposμ : 0 < μ.real (Metric.closedBall 0 ε) := by
    rw [hmassε]
    exact hpositive
  have hlog := Real.log_le_log hposμ (by simpa [hmassε] using hprob)
  rw [Real.log_exp] at hlog
  have hpow' : (r - 2⁻¹)⁻¹ = m₀⁻¹ := by simpa using hpow
  have hlogpow' : b / (r - 2⁻¹) = ((ν-1:ℕ):ℝ) + (ν:ℝ)/(2*m₀) := by
    simpa using hlogpow
  rw [hpow', hlogpow'] at hlog
  rw [hmassε] at hlog
  linarith

end BrownianSharp.AlignmentFractionalSheetLowerLog
