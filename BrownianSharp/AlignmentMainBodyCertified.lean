import BrownianSharp.AlignmentPaperBrownianEntropyRoute
import BrownianSharp.AlignmentPaperAnchoredLpComplete
import BrownianSharp.AlignmentPaperAnchoredLpClosed
import BrownianSharp.AlignmentPeriodicCutoffCertified
import BrownianSharp.AlignmentPaperPeriodicComplete
import BrownianSharp.AlignmentPaperFullL1PeriodicBesov
import BrownianSharp.AlignmentPaperMeanZeroBesovCutoff
import BrownianSharp.AlignmentPaperFullL1PeriodicEntropy
import BrownianSharp.AlignmentPaperSheetUniverse
import BrownianSharp.AlignmentPaperDeterministicIntegrationRates
import BrownianSharp.AlignmentPaperCarlLemma
import BrownianSharp.AlignmentPaperDeterministicExceptionalSet
import BrownianSharp.AlignmentPaperOneDimensionalFailure
import BrownianSharp.AlignmentPaperConvexTailSharpness
import BrownianSharp.AlignmentPaperFractional
import BrownianSharp.AlignmentPaperMaternNumbersCertified
import BrownianSharp.AlignmentPaperMaternSmallBallUpper
import BrownianSharp.AlignmentPaperQuantizationSheetFinal
import BrownianSharp.AlignmentPaperDeterministicIntegration

/-!
The formal statements of the manuscript, one per numbered result, in the order
of the paper. `mainBodyResults_certified` proves all of them.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal BigOperators

namespace BrownianSharp.AlignmentMainBodyCertified

universe u

open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPaperPeriodic
open BrownianSharp.Torus
open AlignmentPaperContinuumGenericBump AlignmentPaperContinuumGoodRegion AlignmentPaperGenericBumpCertified
open HaarQuarter.TheoremD HaarQuarter.TheoremD.Width

/-- Theorem 1.2: entropy numbers of `T_{d,p}` for every `1 < p < ∞`, Kolmogorov
numbers for `2 ≤ p < ∞`, and compactness of the image ball. -/
def AnchoredLpTheoremStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ p : ℝ, 1 < p →
    twoSidedEntropyRate (AlignmentPaperAnchoredLp.anchoredIntegrationLpImage d p)
      1 ((d:ℝ)-1/2) ∧
    (2 ≤ p → AlignmentOperatorStatements.twoSidedWidthRate
      (AlignmentPaperAnchoredLp.anchoredIntegrationLpImage d p) 1 ((d:ℝ)-1/2)) ∧
    IsCompact (AlignmentPaperAnchoredLp.anchoredIntegrationLpImage d p)

theorem anchoredLpTheorem_certified : AnchoredLpTheoremStatement := by
  intro d hd p hp
  exact ⟨AlignmentPaperAnchoredLpComplete.anchoredIntegrationLp_entropy_equivalent_all_p hd p hp,
    fun hp2 => AlignmentPaperAnchoredLpLower.anchoredIntegrationLp_operatorWidth_equivalent_ge_two hd p hp2,
    AlignmentPaperAnchoredLpClosed.anchoredIntegrationLpImage_isCompact hp⟩

/-- Two-sided entropy in the upper range, with the Sobolev endpoint p=∞
excluded and the Nikolsky endpoint included, for every admissible cutoff. -/
def PeriodicEndpointEntropyStatement : Prop :=
  ∀ (φ : AdmissibleCutoff) (d : ℕ), 2 ≤ d →
    ∀ p : ℝ≥0∞, 2 ≤ p → ∀ r : ℝ, 1 / 2 < r →
      (p ≠ ⊤ → twoSidedEntropyRate
        (Latest.periodicLInfinityImage
          {f : RealPeriodic d | SobolevUnitBall φ p.toReal r f})
        r (r * (d - 1 : ℕ) + 1 / 2)) ∧
      twoSidedEntropyRate
        (Latest.periodicLInfinityImage
          {f : RealPeriodic d | NikolskyUnitBall φ p r f})
        r ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2)

theorem periodicEndpointEntropy_certified : PeriodicEndpointEntropyStatement := by
  intro φ d hd p hp r hr
  exact AlignmentPaperPeriodic.periodic_sobolev_nikolsky_entropy_equivalent
    φ hd hp hr

/-- The full fine-index upper range of the merged periodic theorem. -/
def PeriodicBesovUpperRangeStatement : Prop :=
  ∀ (φ : AdmissibleCutoff) (d : ℕ), 2 ≤ d →
    ∀ p : ℝ≥0∞, 2 ≤ p → ∀ r : ℝ, 1/2 < r → ∀ θ : ℝ≥0∞, 2 ≤ θ →
      twoSidedEntropyRate
        (Latest.periodicLInfinityImage {f : RealPeriodic d | BesovUnitBall φ p r θ f})
        r ((r+1/2-θ.toReal⁻¹)*(d-1:ℕ)+1/2) ∧
      AlignmentOperatorStatements.twoSidedWidthRate
        (Latest.periodicLInfinityImage {f : RealPeriodic d | BesovUnitBall φ p r θ f})
        r ((r+1/2-θ.toReal⁻¹)*(d-1:ℕ)+1/2)

theorem periodicBesovUpperRange_certified : PeriodicBesovUpperRangeStatement := by
  intro φ d hd p hp r hr θ hθ
  exact AlignmentPaperPeriodicComplete.periodicBesov_entropy_width_equivalent φ hd hp hr hθ

/-- The literal full-L1 source class of the merged theorem, including its
continuous-representative identification rather than a smaller surrogate. -/
def FullL1PeriodicBesovUpperRangeStatement : Prop :=
  ∀ (φ : AdmissibleCutoff) (d : ℕ), 2 ≤ d →
    ∀ p : ℝ≥0∞, 2 ≤ p → ∀ r : ℝ, 1/2 < r → ∀ θ : ℝ≥0∞, 2 ≤ θ →
      twoSidedEntropyRate
        (AlignmentPeriodicL1AdmissibleEntropyBoundary.fullL1BesovImage (d := d) φ p r θ)
        r ((r+1/2-θ.toReal⁻¹)*(d-1:ℕ)+1/2) ∧
      AlignmentOperatorStatements.twoSidedWidthRate
        (AlignmentPeriodicL1AdmissibleEntropyBoundary.fullL1BesovImage (d := d) φ p r θ)
        r ((r+1/2-θ.toReal⁻¹)*(d-1:ℕ)+1/2)

theorem fullL1PeriodicBesovUpperRange_certified : FullL1PeriodicBesovUpperRangeStatement := by
  intro φ d hd p hp r hr θ hθ
  exact AlignmentPaperFullL1PeriodicBesov.fullL1_periodic_besov_entropy_width_equivalent
    φ hd hp hr hθ

/-- Remark 3.3: the coordinatewise mean-zero Besov classes, for every admissible
cutoff, in the uniform norm and the finite fine-index range. -/
def MeanZeroBesovEntropyStatement : Prop :=
  ∀ (φ : AdmissibleCutoff) (d : ℕ), 2 ≤ d → ∀ (r : ℝ) (θ p : ℝ≥0∞),
    1/2 < r → θ ≠ ⊤ → 2 ≤ θ.toReal → 2 ≤ p →
      twoSidedEntropyRate
        (Latest.periodicLInfinityImage
          (AlignmentPaperMeanZeroBesovCutoff.MeanZeroBesovCutoffClass (d := d) φ p r θ))
        r ((r+1/2-1/θ.toReal)*(d-1:ℕ)+1/2)

theorem meanZeroBesovEntropy_certified : MeanZeroBesovEntropyStatement := by
  intro φ d hd r θ p hr htop hθ hp
  exact AlignmentPaperMeanZeroBesovCutoff.meanZeroBesovCutoff_entropy_two_sided_LInfinity
    φ hd r θ p hr htop hθ hp

/-- Lemma 3.1: a width upper and an entropy lower bound of the same order
`k^{-s}(log k)^a`, for any real `a`, give both two-sided rates. -/
def CarlLemmaStatement : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [MeasurableSpace X] [BorelSpace X] (K : Set X) (s a : ℝ), 0 < s →
    kolmogorovWidth K 0 ≠ ⊤ →
    (∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      kolmogorovWidth K n ≤ ENNReal.ofReal (C * logarithmicIndexRate s a n)) →
    (∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
      ENNReal.ofReal (c * logarithmicIndexRate s a n) ≤ entropyNumber n K) →
    AlignmentPaperPeriodic.twoSidedEntropyRate K s a ∧ Latest.twoSidedWidthRate K s a

/-- Remark 2.2, (2.7): inequality (2.6) fails only on a set of Gaussian
coefficient vectors of measure `exp(-c''|D_n|)`. -/
def ExceptionalSetStatement : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ ψ : AdmissibleBump,
    ∃ c c'' : ℝ, 0 < c ∧ 0 < c'' ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (G : LayerIndex d n → Ω → ℝ),
        (∀ i, HasLaw (G i) (gaussianReal 0 1) P) → iIndepFun G P →
        P.real {ω | ∃ s : ℝ, (∀ x ∈ cubeSet d, |bumpSynthesis ψ (fun i => G i ω) x| ≤ s) ∧
          (n : ℝ) ^ (((d : ℝ) - 2) / 2) * s < c / 2 ^ n * ∑ i, |G i ω|} ≤
          Real.exp (-c'' * nativeDimension d n)

/-- Remark 2.9: for `d = 1` the confinement probability is at least
`(1 - e^{-a²n/2})^{2^n} = e^{-o(|D_n|)}`, and the `d = 1` form of Theorem 2.1 is false. -/
def OneDimensionalFailureStatement : Prop :=
  ∀ ψ : AdmissibleBump,
    (∀ a : ℝ, 0 < a → ∀ n : ℕ, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (G : LayerIndex 1 n → Ω → ℝ),
      (∀ i, HasLaw (G i) (gaussianReal 0 1) P) → iIndepFun G P →
      (1 - Real.exp (-(a ^ 2 * n / 2))) ^ (2 ^ n) ≤
        P.real {ω | ∀ x ∈ cubeSet 1, |bumpSynthesis ψ (fun i => G i ω) x| ≤
          a * Real.sqrt ((n : ℝ) * hyperbolicCount 1 n)}) ∧
    (∀ a : ℝ, 0 < a → Tendsto (fun n : ℕ =>
      Real.log ((1 - Real.exp (-(a ^ 2 * n / 2))) ^ (2 ^ n)) / nativeDimension 1 n)
      atTop (𝓝 0)) ∧
    ¬ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (G : LayerIndex 1 n → Ω → ℝ),
        (∀ i, HasLaw (G i) (gaussianReal 0 1) P) → iIndepFun G P →
        P.real {ω | ∀ x ∈ cubeSet 1, |bumpSynthesis ψ (fun i => G i ω) x| ≤
          a * Real.sqrt ((n : ℝ) * hyperbolicCount 1 n)} ≤
          Real.exp (-b * nativeDimension 1 n)

open AlignmentPaperConvexTailSharpness in
/-- Remark 2.7: for `f_s(g) = s g_i - s²/2`, `E e^{f_s} = 1`,
`Var e^{f_s} = e^{s²} - 1`, and `-log P{f_s ≤ -t} ∼ t²/(2s²) ∼ t²/(2σ_s²)`. -/
def ConvexTailSharpnessStatement : Prop :=
  ∀ (κ : Type) [Fintype κ] (i : κ),
    (∀ s : ℝ, ∫ x, Real.exp (f s i x) ∂productStandardGaussian κ = 1 ∧
      variance (fun x => Real.exp (f s i x)) (productStandardGaussian κ) =
        Real.exp (s ^ 2) - 1) ∧
    ∀ t : ℝ, 1 < t →
      Tendsto (fun s => -Real.log ((productStandardGaussian κ).real {x | f s i x ≤ -t}) /
        (t ^ 2 / (2 * s ^ 2))) (𝓝[>] 0) (𝓝 1) ∧
      Tendsto (fun s => -Real.log ((productStandardGaussian κ).real {x | f s i x ≤ -t}) /
        (t ^ 2 / (2 * variance (fun x => Real.exp (f s i x)) (productStandardGaussian κ))))
        (𝓝[>] 0) (𝓝 1)

/-- The deterministic at-most-m integration identity for actual centered
continuous Gaussian cube path laws. First moments follow internally from
Mathlib Fernique; no moment or minimax-identity premise remains. -/
def PaperDeterministicIntegrationStatement : Prop :=
  ∀ (d:ℕ), 2≤d →
    ∀ {Ω:Type u} [MeasurableSpace Ω] {P:MeasureTheory.Measure Ω}
      [MeasureTheory.IsProbabilityMeasure P]
      (F:Ω→C(HaarQuarter.BrownianCubeAnchor d,ℝ)) (hF:Measurable F)
      (hG:ProbabilityTheory.IsGaussianProcess (fun x ω=>F ω x) P)
      (hmean:∀x,∫ω,F ω x∂P=0) (m:ℕ) (hm:0<m),
      AlignmentPaperDeterministicIntegration.deterministicIntegrationMinimax (P.map F) m=
        quantizationQ1 (P.map F) m hm

theorem paperDeterministicIntegration_certified : PaperDeterministicIntegrationStatement.{u} := by
  intro d hd Ω hΩ P hP F hF hG hmean m hm
  exact AlignmentPaperDeterministicIntegration.centeredGaussianPath_deterministicIntegration_eq_quantizationQ1
    F hF hG hmean m hm

/-- All results of the manuscript, in the order of the paper. -/
def MainBodyResultsStatement : Prop :=
  AlignmentPaperSheetUniverse.BrownianTwoSidedStatementU.{u} ∧         -- Theorem 1.1
  AnchoredLpTheoremStatement ∧                                         -- Theorem 1.2
  AlignmentPeriodicCutoffCertified.ArbitraryCutoffMainResultsStatement ∧ -- Theorem 1.3
  PeriodicEndpointEntropyStatement ∧                                   -- Theorem 1.3
  PeriodicBesovUpperRangeStatement ∧                                   -- Theorem 1.3
  FullL1PeriodicBesovUpperRangeStatement ∧                             -- Theorem 1.3
  AlignmentPaperFullL1PeriodicEntropy.FullL1PeriodicEndpointEntropyStatement ∧ -- Theorem 1.3
  AdmissibleBumpIidConfinementStatement.{u} ∧                          -- Theorem 2.1
  ExceptionalSetStatement.{u} ∧                                        -- Remark 2.2
  ConvexTailSharpnessStatement ∧                                       -- Remark 2.7
  OneDimensionalFailureStatement.{u} ∧                                 -- Remark 2.9
  CarlLemmaStatement.{u} ∧                                             -- Lemma 3.1
  MeanZeroBesovEntropyStatement ∧                                      -- Remark 3.3
  AlignmentPaperFractional.PaperFractionalTensorStatement ∧            -- Theorem 5.1
  AlignmentPaperSheetUniverse.FractionalSheetStatementU.{u} ∧          -- Theorem 5.2
  AlignmentPaperSheetUniverse.IntegratedSheetStatementU.{u} ∧          -- Theorem 5.2
  AlignmentPaperMaternNumbersCertified.MaternCMNumbersStatement.{u} ∧  -- Corollary 5.3
  AlignmentPaperMaternSmallBallUpper.MaternRawSmallBallStatement.{u} ∧ -- Corollary 5.3
  AlignmentPaperQuantizationSheetFinal.PaperQuantizationResultsStatement.{u} ∧ -- Corollary 5.4
  PaperDeterministicIntegrationStatement.{u} ∧                         -- Section 5.3
  AlignmentPaperDeterministicIntegrationRates.DeterministicIntegrationRatesStatement.{u} -- Section 5.3

theorem mainBodyResults_certified : MainBodyResultsStatement.{u} := by
  refine ⟨AlignmentPaperSheetUniverse.brownianTwoSided_certified,
    anchoredLpTheorem_certified,
    AlignmentPeriodicCutoffCertified.arbitraryCutoffMainResults_certified,
    periodicEndpointEntropy_certified, periodicBesovUpperRange_certified,
    fullL1PeriodicBesovUpperRange_certified,
    AlignmentPaperFullL1PeriodicEntropy.fullL1PeriodicEndpointEntropy_certified,
    admissibleBumpIidConfinement_certified, ?_, ?_, ?_, ?_,
    meanZeroBesovEntropy_certified,
    AlignmentPaperFractional.paperFractionalTensor_certified,
    AlignmentPaperSheetUniverse.fractionalSheet_certified,
    AlignmentPaperSheetUniverse.integratedSheet_certified,
    AlignmentPaperMaternNumbersCertified.maternCMNumbers_certified,
    AlignmentPaperMaternSmallBallUpper.maternRawSmallBall_certified,
    AlignmentPaperQuantizationSheetFinal.paperQuantizationResultsStatement,
    paperDeterministicIntegration_certified,
    AlignmentPaperDeterministicIntegrationRates.deterministicIntegrationRates_certified⟩
  · intro d hd ψ
    exact AlignmentPaperDeterministicExceptionalSet.deterministic_exceptional_set_small hd ψ
  · intro κ _ i
    exact ⟨fun s => ⟨AlignmentPaperConvexTailSharpness.integral_exp_f s i,
        AlignmentPaperConvexTailSharpness.variance_exp_f s i⟩,
      fun _ ht => ⟨AlignmentPaperConvexTailSharpness.tendsto_neg_log_tail i ht,
        AlignmentPaperConvexTailSharpness.tendsto_neg_log_tail_variance i ht⟩⟩
  · intro ψ
    exact ⟨fun _ ha n Ω _ P G hG hI =>
        AlignmentPaperOneDimensionalFailure.oneDimensional_confinement_lower_bound ψ ha n Ω P G hG hI,
      fun _ ha => AlignmentPaperOneDimensionalFailure.log_confinement_lower_bound_isLittleO ha,
      AlignmentPaperOneDimensionalFailure.not_oneDimensional_iid_confinement ψ⟩
  · intro X _ _ _ _ _ K s a hs h0 hW hE
    exact AlignmentPaperCarlLemma.carl_lemma_3_1 K s a hs h0 hW hE

end BrownianSharp.AlignmentMainBodyCertified
