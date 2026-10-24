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


/-- Actual fractional-sheet lower-log bound under the same explicit frame
profiles that give the companion upper-log bound. The profile closure provides
the radius-specific positivity needed by the logarithm conversion above. -/
theorem fractionalSheet_oneSided_lowerLog_of_uniform_frame_profiles
    {d : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (ν : ℕ)
    (hν : 2 ≤ ν) (hmin : Latest.minimumMultiplicity H h ν)
    (Cvar Rvar Cdim η : ℝ)
    (hCvar : 0 ≤ Cvar) (hRvar : 0 ≤ Rvar) (hCdim : 0 ≤ Cdim)
    (hη : 0 < η) (hη1 : η ≤ 1)
    (F : ℕ → Type*)
    (hfinite : ∀ M, Fintype (F M))
    (hdecEq : ∀ M, DecidableEq (F M))
    (hnonempty : ∀ M, Nonempty (F M))
    (e : ∀ M, F M → FullProductL2 d)
    (grade : ∀ M, F M → ℕ)
    (horth : ∀ M, letI : Fintype (F M) := hfinite M
      letI : DecidableEq (F M) := hdecEq M
      ∀ i j, ⟪e M i, e M j⟫ = if i = j then 1 else 0)
    (hvar : ∀ (M N : ℕ), letI : Fintype (F M) := hfinite M
      letI : DecidableEq (F M) := hdecEq M
      ∀ z, ∑ i : F M, (contractionScale η N (grade M i) *
          ⟪fractionalSheetFeature H hH z, e M i⟫)^2 ≤
        Cvar * (Real.rpow 2 (-(2*h) * (N : ℝ) / 2))^2 *
          (((N + 1 : ℕ) : ℝ)^((ν-1 : ℕ))))
    (hincrement : ∀ (M N : ℕ), letI : Fintype (F M) := hfinite M
      ∀ z w, ∑ i : F M, (contractionScale η N (grade M i) *
          (⟪fractionalSheetFeature H hH z, e M i⟫ -
            ⟪fractionalSheetFeature H hH w, e M i⟫))^2 ≤
        Rvar * (dist z w)^(2*h))
    (hfiber : ∀ (M N : ℕ), letI : Fintype (F M) := hfinite M
      ∀ g : Fin (N+1),
        (Fintype.card {i : F M // grade M i = g.val} : ℝ) ≤
          Cdim * (2:ℝ)^g.val * (((g.val+1:ℕ):ℝ)^(ν-1)))
    (happrox : ∀ ε, 0 < ε → ∃ M,
      letI : Fintype (F M) := hfinite M
      letI : DecidableEq (F M) := hdecEq M
      ∀ z, ‖fractionalSheetFeature H hH z -
        projection (e M) (fractionalSheetFeature H hH z)‖ ≤ ε) :
    ∃ c ε₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (B : FractionalBrownianSheetOnCube d Ω P), B.H = H →
        ∀ ε, 0 < ε → ε ≤ ε₀ →
          c * Latest.smallBallRate (h⁻¹)
            (((ν-1:ℕ):ℝ) + (ν:ℝ)/(2*h)) ε ≤
            -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε}) := by
  classical
  obtain ⟨cU, εU, hcU, hεU, hεUsmall, hUpper⟩ :=
    BrownianSharp.AlignmentGaussianFractionalReverseClosure.fractionalSheet_upperLog_of_uniform_frame_profiles
      hd H hH h ν hν hmin Cvar Rvar Cdim η hCvar hRvar hCdim hη hη1
      F hfinite hdecEq hnonempty e grade horth hvar hincrement hfiber happrox
  obtain ⟨cL, εL, hcL, hεL, hεLsmall, hLower⟩ :=
    fractionalSheet_oneSided_lowerLog_of_positive hd H hH hν h hmin
  let ε₀ := min εU εL
  refine ⟨cL, ε₀, hcL, lt_min hεU hεL, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) hεLsmall
  · intro Ω _ P _ B hBH ε hε hsmall
    have hsmallU : ε ≤ εU := le_trans hsmall (min_le_left _ _)
    have hpos := (hUpper Ω P B hBH ε hε hsmallU).1
    exact hLower Ω P B hBH ε hε (le_trans hsmall (min_le_right _ _)) hpos

end BrownianSharp.AlignmentFractionalSheetLowerLog
