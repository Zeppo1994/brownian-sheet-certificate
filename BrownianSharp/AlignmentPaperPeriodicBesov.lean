import BrownianSharp.AlignmentPaperPeriodic
import BrownianSharp.AlignmentPeriodicCutoffClasses
import BrownianSharp.AlignmentPeriodicCutoffSobolevBridges
import BrownianSharp.AlignmentPeriodicCutoffCertified
import BrownianSharp.AlignmentOperatorWidthIndexShift
import BrownianSharp.AlignmentWidthRates
import BrownianSharp.AlignmentAuditPeriodicBoundedness

/-! The finite endpoint `theta=2` of the periodic Besov entropy theorem.
The spatial-exponent embedding is proved block by block on normalized Haar
measure, and the resulting class inclusion transfers the Sobolev entropy
upper bound to the literal cutoff Besov ball. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperPeriodicBesov

open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicCutoffSobolevBridges
open BrownianSharp.AlignmentPaperPeriodic
open BrownianSharp.AlignmentOperatorStatements
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentOperatorNumbers
open BrownianSharp.AlignmentOperatorWidthIndexShift
open BrownianSharp.AlignmentWidthRates
open BrownianSharp.AlignmentAuditPeriodicBoundedness
open BrownianSharp.AlignmentPeriodicUpperReduction
open BrownianSharp.AlignmentPeriodicScaledClassTransfer
open BrownianSharp.AlignmentScaledSetWidth
open HaarQuarter.TheoremD.Width
open BrownianSharp.Torus
open BrownianSharp.Latest

theorem weightedBlockNorm_mono_exponent {d : ℕ} (φ : AdmissibleCutoff)
    {q p : ℝ≥0∞} (hqp : q ≤ p) (r : ℝ) (s : Fin d → ℕ)
    (f : RealPeriodic d) :
    weightedBlockNorm φ q r s f ≤ weightedBlockNorm φ p r s f := by
  unfold weightedBlockNorm
  gcongr
  exact eLpNorm_le_eLpNorm_of_exponent_le hqp

theorem besovUnitBall_mono_exponent {d : ℕ} (φ : AdmissibleCutoff)
    {q p θ : ℝ≥0∞} (hqp : q ≤ p) (r : ℝ) (f : RealPeriodic d)
    (hf : BesovUnitBall φ p r θ f) : BesovUnitBall φ q r θ f := by
  unfold BesovUnitBall at *
  split_ifs at * with hθ
  · intro s
    exact (weightedBlockNorm_mono_exponent φ hqp r s f).trans (hf s)
  · apply le_trans _ hf
    apply ENNReal.tsum_le_tsum
    intro s
    exact ENNReal.rpow_le_rpow
      (weightedBlockNorm_mono_exponent φ hqp r s f) ENNReal.toReal_nonneg

/-- A periodic Besov ball with spatial exponent at least two and summation
exponent two lies inside the corresponding mixed Sobolev ball of exponent two. -/
theorem besov_two_spatial_exponent_subset_sobolev_two
    {d : ℕ} (φ : AdmissibleCutoff) {p : ℝ≥0∞} (hp : 2 ≤ p)
    (r : ℝ) :
    {f : RealPeriodic d | BesovUnitBall φ p r 2 f} ⊆
      {f : RealPeriodic d | SobolevUnitBall φ 2 r f} := by
  intro f hf
  have hBesov : BesovUnitBall φ 2 r 2 f :=
    besovUnitBall_mono_exponent φ (by exact_mod_cast hp) r f hf
  exact (sobolev_two_iff_besov_two φ r f).2 hBesov

private theorem entropyNumber_mono {X : Type*} [PseudoEMetricSpace X]
    {K J : Set X} (hK : K ⊆ J) (k : ℕ) :
    HaarQuarter.TheoremD.entropyNumber k K ≤ HaarQuarter.TheoremD.entropyNumber k J := by
  unfold HaarQuarter.TheoremD.entropyNumber
  apply le_sInf
  rintro q ⟨ρ, rfl, hcover⟩
  exact sInf_le ⟨ρ, rfl, (Metric.externalCoveringNumber_mono_set hK).trans hcover⟩

private theorem operator_width_rate_of_legacy
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a)
    (hlegacy : Latest.twoSidedWidthRate K r a) :
    AlignmentOperatorStatements.twoSidedWidthRate K r a := by
  obtain ⟨c, C, hc, hC, k₀, hk₀, hwidth⟩ := hlegacy
  let k₁ := max (k₀ + 1) 3
  have hk₁ : 3 ≤ k₁ := by dsimp [k₁]; omega
  have hshiftInput : ∀ k : ℕ, k₁ ≤ k →
      ENNReal.ofReal (c * logarithmicIndexRate r a (k - 1)) ≤
          kolmogorovWidth K (k - 1) ∧
        kolmogorovWidth K (k - 1) ≤
          ENNReal.ofReal (C * logarithmicIndexRate r a (k - 1)) := by
    intro k hk
    have hk0 : k₀ ≤ k - 1 := by dsimp [k₁] at hk; omega
    exact hwidth (k - 1) hk0
  obtain ⟨c', C', hc', hC', hshift⟩ :=
    twoSided_width_index_shift K r a hr ha c C hc hC k₁ hk₁ hshiftInput
  refine ⟨c', C', hc', hC', k₁, by omega, ?_⟩
  intro k hk
  have hEq := operatorKolmogorovNumber_eq_width_pred K (by omega : 1 ≤ k)
  simpa only [hEq] using hshift k hk

/-- The interpolation endpoint `theta=2` also has the sharp strict-index
Kolmogorov width rate. -/
theorem periodic_besov_theta_two_width_certified
    (φ : AdmissibleCutoff) {d : ℕ} (hd : 2 ≤ d)
    {p : ℝ≥0∞} (hp : 2 ≤ p) {r : ℝ} (hr : 1/2 < r) :
    AlignmentOperatorStatements.twoSidedWidthRate
      (Latest.periodicLInfinityImage
        {f : RealPeriodic d | BesovUnitBall φ p r 2 f})
      r (r * (d - 1 : ℕ) + 1 / 2) := by
  have hsub := besov_two_spatial_exponent_subset_sobolev_two
    (d := d) φ hp r
  let K : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    Latest.periodicLInfinityImage {f : RealPeriodic d | BesovUnitBall φ p r 2 f}
  let J : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    Latest.periodicLInfinityImage {f : RealPeriodic d | SobolevUnitBall φ 2 r f}
  have hKJ : K ⊆ J := by
    rintro y ⟨f, hf, rfl⟩
    exact ⟨f, hsub hf, rfl⟩
  have hTransfer :=
    BrownianSharp.AlignmentPeriodicCutoffYoung.cutoffBesovScaleTransfer_certified
      smoothResolutionCutoff φ d (2 : ℝ≥0∞) (by norm_num) r
      (by linarith : 0 ≤ r) (2 : ℝ≥0∞) (by norm_num)
  obtain ⟨cScale, hcScale, hScale⟩ := hTransfer
  let A : ℝ := cScale⁻¹
  have hA : 0 < A := by dsimp [A]; positivity
  let Jfixed : Set (RealPeriodic d) :=
    {f | SmoothResolution.SobolevUnitBall 2 r f}
  have hKfixed : K ⊆ scalarImage A (Latest.periodicLInfinityImage Jfixed) := by
    apply periodicImage_subset_scalarImage
      {f | BesovUnitBall φ p r 2 f} Jfixed A hA
    intro f hf
    have hBesov2 : BesovUnitBall φ 2 r 2 f :=
      besovUnitBall_mono_exponent φ (by exact_mod_cast hp) r f hf
    have hBesovFixed : BesovUnitBall smoothResolutionCutoff 2 r 2
        (cScale • f) := hScale f hBesov2
    have hSobFixed : SobolevUnitBall smoothResolutionCutoff 2 r (cScale • f) :=
      (sobolev_two_iff_besov_two smoothResolutionCutoff r (cScale • f)).2
        hBesovFixed
    simpa [Jfixed, A, BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall_fixed]
      using hSobFixed
  have hwidth0J := sobolev_linf_width_zero_le_of_exponent
    (d := d) (p := (2 : ℝ)) (by norm_num) r hr
  have hwidth0K : kolmogorovWidth K 0 ≤
      ENNReal.ofReal (A * periodicNikolskyRadius d r) := by
    exact kolmogorovWidth_le_of_subset_scalarImage A
      (periodicNikolskyRadius d r) hKfixed 0 hA
      (periodicNikolsky_radius_nonneg (d := d) hr)
      (by simpa [Jfixed] using hwidth0J)
  have hwidthStatement :=
    BrownianSharp.AlignmentPeriodicCutoffCertified.periodic_width_certified
  obtain ⟨hSob, _hNik⟩ := hwidthStatement φ d hd (2 : ℝ≥0∞)
    (by norm_num) r hr
  obtain ⟨cW, CW, hcW, hCW, kW, hkW, hW⟩ := hSob (by norm_num)
  have hupperOp : ∀ k : ℕ, kW ≤ k →
      operatorKolmogorovNumber K k ≤
        ENNReal.ofReal (CW * logarithmicIndexRate r
          (r * (d - 1 : ℕ) + 1 / 2) k) := by
    intro k hk
    have hmono : operatorKolmogorovNumber K k ≤ operatorKolmogorovNumber J k := by
      rw [operatorKolmogorovNumber_eq_width_pred K (by omega : 1 ≤ k),
        operatorKolmogorovNumber_eq_width_pred J (by omega : 1 ≤ k)]
      exact kolmogorovWidth_mono_set hKJ (k - 1)
    exact hmono.trans (hW k hk).2
  obtain ⟨CW', hCW', kU, hkU, hupper⟩ :=
    legacy_width_upper_of_operator_upper K (by linarith : 0 < r)
      (by positivity : 0 ≤ r * (d - 1 : ℕ) + 1 / 2) hCW kW hkW hupperOp
  have hEntropyLow : ∃ cL : ℝ, 0 < cL ∧ ∃ kL : ℕ, ∀ k : ℕ, kL ≤ k →
      ENNReal.ofReal (cL * logarithmicIndexRate r
        (r * (d - 1 : ℕ) + 1 / 2) k) ≤
          HaarQuarter.TheoremD.entropyNumber k K := by
    have hp1 : (1 : ℝ≥0∞) < p := lt_of_lt_of_le (by norm_num) hp
    have hpr : p.toReal⁻¹ < r := by
      by_cases htop : p = ⊤
      · simpa [htop] using (show (0 : ℝ) < r by linarith)
      · have hpR : (2 : ℝ) ≤ p.toReal := by
          have h := (ENNReal.toReal_le_toReal
            (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) htop).2 hp
          simpa only [ENNReal.toReal_ofNat] using h
        have hinv : p.toReal⁻¹ ≤ (1 / 2 : ℝ) := by
          simpa only [one_div] using
            one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpR
        exact hinv.trans_lt hr
    obtain ⟨cL, hcL, kL, hkL, hLow⟩ :=
      BrownianSharp.AlignmentPeriodicCutoffCertified.periodic_mixed_entropy_certified
        φ d hd p hp1 r hpr 2 (by norm_num)
    refine ⟨cL, hcL, kL, ?_⟩
    intro k hk
    have h := (hLow k hk).2.1
    convert h using 1 <;> congr 1 <;> norm_num
  have hlegacy : Latest.twoSidedWidthRate K r
      (r * (d - 1 : ℕ) + 1 / 2) :=
    AlignmentWidthRates.twoSidedWidthRate_of_entropy_lower_and_width_upper
      K r (r * (d - 1 : ℕ) + 1 / 2) (A * periodicNikolskyRadius d r)
      (by linarith) (by positivity)
      (mul_nonneg hA.le (periodicNikolsky_radius_nonneg (d := d) hr))
      hwidth0K hEntropyLow ⟨CW', hCW', kU, hupper⟩
  exact operator_width_rate_of_legacy K r
    (r * (d - 1 : ℕ) + 1 / 2) (by linarith) (by positivity) hlegacy

/-- Two-sided entropy at `theta=2`, including the actual arbitrary-cutoff
Besov class and the paper's logarithmic exponent. -/
theorem periodic_besov_theta_two_entropy_equivalent
    (φ : AdmissibleCutoff) {d : ℕ} (hd : 2 ≤ d)
    {p : ℝ≥0∞} (hp : 2 ≤ p) {r : ℝ} (hr : 1/2 < r) :
    twoSidedEntropyRate
      (Latest.periodicLInfinityImage
        {f : RealPeriodic d | BesovUnitBall φ p r 2 f})
      r (r * (d - 1 : ℕ) + 1 / 2) := by
  have hp1 : (1 : ℝ≥0∞) < p := lt_of_lt_of_le (by norm_num) hp
  have hpr : p.toReal⁻¹ < r := by
    by_cases htop : p = ⊤
    · simpa [htop] using (show (0 : ℝ) < r by linarith)
    · have hpR : (2 : ℝ) ≤ p.toReal := by
        have h := (ENNReal.toReal_le_toReal
          (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) htop).2 hp
        simpa only [ENNReal.toReal_ofNat] using h
      have hinv : p.toReal⁻¹ ≤ (1 / 2 : ℝ) := by
        simpa only [one_div] using
          one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hpR
      exact hinv.trans_lt hr
  obtain ⟨cl, hcl, kl, hkl, hLower⟩ :=
    BrownianSharp.AlignmentPeriodicCutoffCertified.periodic_mixed_entropy_certified
      φ d hd p hp1 r hpr (2 : ℝ≥0∞) (by norm_num)
  obtain ⟨hSob, _hNik⟩ :=
    AlignmentPaperPeriodic.periodic_sobolev_nikolsky_entropy_equivalent
      φ hd (p := (2 : ℝ≥0∞)) (by norm_num) hr
  obtain ⟨_cSob, cu, _hcSob, hcu, ku, hku, hUpper⟩ := hSob (by norm_num)
  let K : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    Latest.periodicLInfinityImage {f : RealPeriodic d | BesovUnitBall φ p r 2 f}
  let J : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
    Latest.periodicLInfinityImage {f : RealPeriodic d | SobolevUnitBall φ 2 r f}
  have hsub : K ⊆ J := by
    rintro y ⟨f, hf, rfl⟩
    exact ⟨f, besov_two_spatial_exponent_subset_sobolev_two φ hp r hf, rfl⟩
  have hrateNonneg : ∀ k : ℕ, 0 ≤ logarithmicIndexRate r
      (r * (d - 1 : ℕ) + 1 / 2) k := by
    intro k
    exact AlignmentWidthRates.logarithmicIndexRate_nonneg _ _ _
  refine ⟨min cl cu, cu, lt_min hcl hcu, hcu, max kl ku,
    hkl.trans (le_max_left _ _), ?_⟩
  intro k hk
  have hkl' : kl ≤ k := (le_max_left kl ku).trans hk
  have hku' : ku ≤ k := (le_max_right kl ku).trans hk
  have hLow := (hLower k hkl').2.1
  have hLowBesov : ENNReal.ofReal
      (cl * logarithmicIndexRate r
        ((r + 1 / 2 - (2 : ℝ≥0∞).toReal⁻¹) * (d - 1 : ℕ) + 1 / 2) k) ≤
      HaarQuarter.TheoremD.entropyNumber k K := by
    simpa [K] using hLow
  have hLowExact : ENNReal.ofReal
      (cl * logarithmicIndexRate r (r * (d - 1 : ℕ) + 1 / 2) k) ≤
      HaarQuarter.TheoremD.entropyNumber k K := by
    convert hLowBesov using 1 <;> congr 1 <;> norm_num
  have hLow' := (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (min_le_left cl cu) (hrateNonneg k))).trans hLowExact
  have hUp := (hUpper k hku').2
  exact ⟨hLow', (entropyNumber_mono hsub k).trans hUp⟩

end BrownianSharp.AlignmentPaperPeriodicBesov
