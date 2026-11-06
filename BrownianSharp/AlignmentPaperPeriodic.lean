import BrownianSharp.AlignmentPeriodicCutoffCertified
import BrownianSharp.AlignmentPeriodicCutoffSobolevWidth
import BrownianSharp.AlignmentPeriodicCutoffNikolskyWidth
import BrownianSharp.AlignmentEndpointDyadicEntropy
import BrownianSharp.AlignmentOperatorNumbers
import BrownianSharp.AlignmentOperatorWidthIndexShift
import BrownianSharp.AlignmentAuditPeriodicBoundedness
import BrownianSharp.AlignmentPeriodicScaledClassTransfer
import BrownianSharp.AlignmentScaledSetWidth
import BrownianSharp.AlignmentWidthRates

/-! Entropy upper rates for the periodic Sobolev and Nikolsky classes.
The upper bounds follow from the already certified sharp width upper bounds
and the Carl covering argument. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperPeriodic

open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffTransferStatement
open BrownianSharp.AlignmentPeriodicCutoffSobolevBridges
open BrownianSharp.AlignmentOperatorStatements
open BrownianSharp.AlignmentOperatorNumbers
open BrownianSharp.AlignmentOperatorWidthIndexShift
open BrownianSharp.AlignmentEndpointDyadicEntropy
open BrownianSharp.AlignmentAuditPeriodicBoundedness
open BrownianSharp.AlignmentPeriodicScaledClassTransfer
open BrownianSharp.AlignmentScaledSetWidth
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.Latest
open HaarQuarter.TheoremD.Width

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) := by
  rw [unitAddCircle_volume_eq_haar]
  infer_instance

private instance (d : ℕ) : MeasurableSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := borel _
private instance (d : ℕ) : BorelSpace
    (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) := ⟨rfl⟩

def twoSidedEntropyRate {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (r a : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
    ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * logarithmicIndexRate r a k) ≤
        HaarQuarter.TheoremD.entropyNumber k K ∧
      HaarQuarter.TheoremD.entropyNumber k K ≤
        ENNReal.ofReal (C * logarithmicIndexRate r a k)

/-- An operator upper rate yields a set-width upper rate (`rank ≤ m`) after shifting
index `n` to strict operator index `n+1`. -/
theorem legacy_width_upper_of_operator_upper
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) {r a C : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (hC : 0 < C)
    (k₀ : ℕ) (hk₀ : 2 ≤ k₀)
    (hupper : ∀ k : ℕ, k₀ ≤ k →
      operatorKolmogorovNumber K k ≤ ENNReal.ofReal (C * logarithmicIndexRate r a k)) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      kolmogorovWidth K n ≤ ENNReal.ofReal (C' * logarithmicIndexRate r a n) := by
  let n₀ := max 2 (k₀ - 1)
  refine ⟨C * 2 ^ a, mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), n₀,
    le_max_left _ _, ?_⟩
  intro n hn
  have hn1 : k₀ ≤ n + 1 := by
    dsimp [n₀] at hn
    have h := (le_max_right 2 (k₀ - 1)).trans hn
    omega
  have hk : 3 ≤ n + 1 := by
    dsimp [n₀] at hn
    have h := (le_max_left 2 (k₀ - 1)).trans hn
    omega
  have hEq := operatorKolmogorovNumber_eq_width_pred K (by omega : 1 ≤ n+1)
  have hrate := rate_succ_comparable hr ha hk
  have hrate' : logarithmicIndexRate r a (n+1) ≤
      2 ^ a * logarithmicIndexRate r a n := by
    have hh := hrate.1
    have hpow : 0 < (2:ℝ)^a := Real.rpow_pos_of_pos (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_left hh (le_of_lt hpow)
    have hfactor : (2:ℝ)^a * 2^(-a) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
      norm_num
    have hmul' : 2 ^ a * (2 ^ (-a) * logarithmicIndexRate r a (n+1)) ≤
        2 ^ a * logarithmicIndexRate r a n := by
      simpa only [Nat.add_sub_cancel] using hmul
    calc
      logarithmicIndexRate r a (n+1) =
          (2 ^ a * 2 ^ (-a)) * logarithmicIndexRate r a (n+1) := by
            rw [hfactor, one_mul]
      _ = 2 ^ a * (2 ^ (-a) * logarithmicIndexRate r a (n+1)) := by ring
      _ ≤ 2 ^ a * logarithmicIndexRate r a n := hmul'
  have hbound := hupper (n+1) hn1
  rw [hEq] at hbound
  have hbound' := hbound.trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hrate' hC.le))
  calc
    kolmogorovWidth K n ≤ ENNReal.ofReal
        (C * (2 ^ a * logarithmicIndexRate r a n)) := by
      simpa only [Nat.add_sub_cancel] using hbound'
    _ = ENNReal.ofReal
        ((C * 2 ^ a) * logarithmicIndexRate r a n) := by
      congr 1
      ring

/-- A certified operator width upper rate gives an all-index entropy upper
rate through the finite-radius Carl theorem. -/
theorem entropy_upper_of_operator_width_upper
    {d : ℕ} (K : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))))
    {r a C R : ℝ} (hr : 0 < r) (ha : 0 ≤ a) (hC : 0 < C) (hR : 0 ≤ R)
    (k₀ : ℕ) (hk₀ : 2 ≤ k₀)
    (hzero : kolmogorovWidth K 0 ≤ ENNReal.ofReal R)
    (hupper : ∀ k : ℕ, k₀ ≤ k →
      operatorKolmogorovNumber K k ≤ ENNReal.ofReal (C * logarithmicIndexRate r a k)) :
    ∃ C' : ℝ, 0 < C' ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧ ∀ n : ℕ, n₀ ≤ n →
      HaarQuarter.TheoremD.entropyNumber n K ≤
        ENNReal.ofReal (C' * logarithmicIndexRate r a n) := by
  obtain ⟨Cw, hCw, nw, hnw, hWidth⟩ :=
    legacy_width_upper_of_operator_upper K hr ha hC k₀ hk₀ hupper
  exact entropy_upper_all_indices_of_width_upper K hr ha hR
    hCw nw hnw hzero hWidth

/-- Arbitrary-cutoff entropy upper rates in the common two-sided-width range.
The Sobolev clause is finite `p`; the Nikolsky clause includes `p=∞`. -/
theorem periodic_entropy_upper_certified :
    ∀ (φ : AdmissibleCutoff) (d : ℕ), 2 ≤ d →
      ∀ p : ℝ≥0∞, 2 ≤ p → ∀ r : ℝ, 1/2 < r →
        (p ≠ ⊤ → ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
          HaarQuarter.TheoremD.entropyNumber k
            (Latest.periodicLInfinityImage
              {f : RealPeriodic d | BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall φ p.toReal r f}) ≤
            ENNReal.ofReal (C * logarithmicIndexRate r
              (r * (d - 1 : ℕ) + 1 / 2) k)) ∧
        (∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
          HaarQuarter.TheoremD.entropyNumber k
            (Latest.periodicLInfinityImage
              {f : RealPeriodic d | BrownianSharp.AlignmentPeriodicCutoffClasses.NikolskyUnitBall φ p r f}) ≤
            ENNReal.ofReal (C * logarithmicIndexRate r
              ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) k)) := by
  intro φ d hd p hp r hr
  have htransfer :=
    BrownianSharp.AlignmentPeriodicCutoffYoung.cutoffBesovScaleTransfer_certified
  have hentropy := BrownianSharp.AlignmentPeriodicCutoffCertified.periodic_mixed_entropy_certified
  have hwidth := BrownianSharp.AlignmentPeriodicCutoffCertified.periodic_width_certified
  have hrpos : 0 < r := by linarith
  constructor
  · intro hptop
    have hw := hwidth φ d hd p hp r hr
    have hwSob := hw.1 hptop
    obtain ⟨c,C,hc,hC,k₀,hk₀,hRate⟩ := hwSob
    let K : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
      Latest.periodicLInfinityImage
        {f : RealPeriodic d | BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall φ p.toReal r f}
    have hpReal : (2:ℝ) ≤ p.toReal := by
      have h := (ENNReal.toReal_le_toReal (by norm_num : (2:ℝ≥0∞) ≠ ⊤) hptop).2 hp
      simpa using h
    have hTransfer := htransfer smoothResolutionCutoff φ d (2:ℝ≥0∞)
      (by norm_num) r (by linarith) (2:ℝ≥0∞) (by norm_num)
    obtain ⟨cScale, hcScale, hScale⟩ := hTransfer
    let A : ℝ := cScale⁻¹
    have hA : 0 < A := by dsimp [A]; positivity
    let K0 : Set (RealPeriodic d) :=
      {f | BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall φ p.toReal r f}
    let J0 : Set (RealPeriodic d) :=
      {f | BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall smoothResolutionCutoff 2 r f}
    have hKimage : K ⊆
        scalarImage A (Latest.periodicLInfinityImage J0) := by
      apply periodicImage_subset_scalarImage K0 J0 A hA
      intro f hf
      have hSob2 : BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall φ 2 r f :=
        sobolev_unitBall_mono φ (by norm_num) hpReal r f hf
      have hBesov : BrownianSharp.AlignmentPeriodicCutoffClasses.BesovUnitBall φ 2 r 2 f :=
        (sobolev_two_iff_besov_two φ r f).1 hSob2
      have hBesovFixed : BrownianSharp.AlignmentPeriodicCutoffClasses.BesovUnitBall
          smoothResolutionCutoff 2 r 2
          (cScale • f) := hScale f hBesov
      have hSobFixed : BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall smoothResolutionCutoff 2 r
          (cScale • f) :=
        (sobolev_two_iff_besov_two smoothResolutionCutoff r
          (cScale • f)).2 hBesovFixed
      simpa [K0, J0, A] using hSobFixed
    have hzeroJ := sobolev_linf_width_zero_le_of_exponent
      (d := d) (p := (2:ℝ)) (by norm_num) r hr
    have hzero := kolmogorovWidth_le_of_subset_scalarImage A
      (periodicNikolskyRadius d r) hKimage 0 hA
      (periodicNikolsky_radius_nonneg (d := d) hr) (by simpa [J0] using hzeroJ)
    have hupper : ∀ k : ℕ, k₀ ≤ k →
        operatorKolmogorovNumber K k ≤
          ENNReal.ofReal (C * logarithmicIndexRate r
            (r * (d - 1 : ℕ) + 1 / 2) k) := by
      intro k hk
      exact (hRate k hk).2
    exact entropy_upper_of_operator_width_upper K hrpos
      (by positivity : 0 ≤ r * (d-1:ℕ)+1/2) hC
      (mul_nonneg hA.le (periodicNikolsky_radius_nonneg (d := d) hr))
      k₀ hk₀ hzero hupper
  · obtain ⟨c,C,hc,hC,k₀,hk₀,hRate⟩ := hwidth φ d hd p hp r hr |>.2
    let K : Set (Lp ℝ ⊤ (volume : Measure (UnitAddTorus (Fin d)))) :=
      Latest.periodicLInfinityImage
        {f : RealPeriodic d | BrownianSharp.AlignmentPeriodicCutoffClasses.NikolskyUnitBall φ p r f}
    have hTransfer := htransfer smoothResolutionCutoff φ d p
      (le_trans (by norm_num : (1:ℝ≥0∞) ≤ 2) hp) r
      (by linarith : 0 ≤ r) ⊤ le_top
    obtain ⟨cScale, hcScale, hScale⟩ := hTransfer
    let A : ℝ := cScale⁻¹
    have hA : 0 < A := by dsimp [A]; positivity
    let K0 : Set (RealPeriodic d) :=
      {f | BrownianSharp.AlignmentPeriodicCutoffClasses.NikolskyUnitBall φ p r f}
    let J0 : Set (RealPeriodic d) :=
      {f | SmoothResolution.NikolskyUnitBall p r f}
    have hKimage : K ⊆
        scalarImage A (Latest.periodicLInfinityImage J0) := by
      apply periodicImage_subset_scalarImage K0 J0 A hA
      intro f hf
      have hh := hScale f hf
      simpa [J0, SmoothResolution.NikolskyUnitBall, A, inv_inv] using hh
    have hzeroJ := nikolsky_linf_width_zero_le_of_exponent (d := d) hp r hr
    have hzero := kolmogorovWidth_le_of_subset_scalarImage A
      (periodicNikolskyRadius d r) hKimage 0 hA
      (periodicNikolsky_radius_nonneg (d := d) hr) (by simpa [J0] using hzeroJ)
    have hupper : ∀ k : ℕ, k₀ ≤ k →
        operatorKolmogorovNumber K k ≤
          ENNReal.ofReal (C * logarithmicIndexRate r
            ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) k) := by
      intro k hk
      exact (hRate k hk).2
    exact entropy_upper_of_operator_width_upper K hrpos
      (by positivity : 0 ≤ (r+1/2)*(d-1:ℕ)+1/2) hC
      (mul_nonneg hA.le (periodicNikolsky_radius_nonneg (d := d) hr))
      k₀ hk₀ hzero hupper

/-- Two-sided entropy rates for the periodic Sobolev and Nikolsky classes,
for every admissible cutoff in the common width range. -/
theorem periodic_sobolev_nikolsky_entropy_equivalent
    (φ : AdmissibleCutoff) {d : ℕ} (hd : 2 ≤ d)
    {p : ℝ≥0∞} (hp : 2 ≤ p) {r : ℝ} (hr : 1/2 < r) :
    (p ≠ ⊤ → twoSidedEntropyRate
      (Latest.periodicLInfinityImage
        {f : RealPeriodic d | BrownianSharp.AlignmentPeriodicCutoffClasses.SobolevUnitBall φ p.toReal r f})
      r (r * (d - 1 : ℕ) + 1 / 2)) ∧
    twoSidedEntropyRate
      (Latest.periodicLInfinityImage
        {f : RealPeriodic d | BrownianSharp.AlignmentPeriodicCutoffClasses.NikolskyUnitBall φ p r f})
      r ((r + 1 / 2) * (d - 1 : ℕ) + 1 / 2) := by
  have hp1 : (1:ℝ≥0∞) < p := lt_of_lt_of_le (by norm_num) hp
  have hpr : p.toReal⁻¹ < r := by
    by_cases htop : p = ⊤
    · simpa [htop] using (show (0:ℝ) < r by linarith)
    · have hpR : (2:ℝ) ≤ p.toReal := by
        have h := (ENNReal.toReal_le_toReal
          (by norm_num : (2:ℝ≥0∞) ≠ ⊤) htop).2 hp
        simpa only [ENNReal.toReal_ofNat] using h
      have hinv : p.toReal⁻¹ ≤ (1/2:ℝ) := by
        simpa only [one_div] using
          one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) hpR
      exact hinv.trans_lt hr
  obtain ⟨cl, hcl, kl, hkl, hLower⟩ :=
    BrownianSharp.AlignmentPeriodicCutoffCertified.periodic_mixed_entropy_certified
      φ d hd p hp1 r hpr ⊤ le_top
  obtain ⟨hSobUpper, hNikUpper⟩ :=
    periodic_entropy_upper_certified φ d hd p hp r hr
  have hrateNonneg : ∀ a : ℝ, ∀ k : ℕ, 0 ≤ logarithmicIndexRate r a k := by
    intro a k
    exact BrownianSharp.AlignmentWidthRates.logarithmicIndexRate_nonneg r a k
  constructor
  · intro hptop
    obtain ⟨cu, hcu, ku, hku, hU⟩ := hSobUpper hptop
    refine ⟨min cl cu, cu, lt_min hcl hcu, hcu, max kl ku,
      hkl.trans (le_max_left _ _), ?_⟩
    intro k hk
    have hkl' : kl ≤ k := (le_max_left kl ku).trans hk
    have hku' : ku ≤ k := (le_max_right kl ku).trans hk
    have hL := (hLower k hkl').1 hptop
    have hL' := (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_left cl cu) (hrateNonneg _ _))).trans hL
    exact ⟨hL', hU k hku'⟩
  · obtain ⟨cu, hcu, ku, hku, hU⟩ := hNikUpper
    refine ⟨min cl cu, cu, lt_min hcl hcu, hcu, max kl ku,
      hkl.trans (le_max_left _ _), ?_⟩
    intro k hk
    have hkl' : kl ≤ k := (le_max_left kl ku).trans hk
    have hku' : ku ≤ k := (le_max_right kl ku).trans hk
    have hL := (hLower k hkl').2.2
    have hL' := (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_left cl cu) (hrateNonneg _ _))).trans hL
    exact ⟨hL', hU k hku'⟩

end BrownianSharp.AlignmentPaperPeriodic
