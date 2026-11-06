import BrownianSharp.AlignmentPaperGaussianPathEnlargement
import BrownianSharp.AlignmentPaperGaussianPathLaws
import BrownianSharp.AlignmentFractionalSheetStatement
import BrownianSharp.AlignmentFractionalSheetTensorFeature
import BrownianSharp.AlignmentFractionalSheetUnitFeature
import BrownianSharp.AlignmentPaperQuantizationLowerCertified
import BrownianSharp.AlignmentPaperQuantizationEmpiricalComparison
import BrownianSharp.AlignmentPaperIntegratedFeatureNonzero
import BrownianSharp.AlignmentGaussianIntegratedReverse
import BrownianSharp.AlignmentGaussianBochner
import BrownianSharp.AlignmentPaperEmpiricalWassersteinMeasurable
import BrownianSharp.AlignmentPaperMomentComparison
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
universe u

namespace BrownianSharp.AlignmentPaperQuantizationSheetUpper

open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentPaperGaussianPathLaws
open BrownianSharp.AlignmentFractionalSheetTensorFeature
open BrownianSharp.AlignmentPaperGaussianPathEnlargement
open BrownianSharp.AlignmentPaperEmpiricalWasserstein
open BrownianSharp.AlignmentPaperEmpiricalWassersteinMeasurable

/-- Convert a finite extended empirical-W₂ expectation bound to the ordinary
real expectation using the checked map/integral identity. -/
theorem ordinary_empirical_integral_le_of_lintegral
    {T : Type*} [MetricSpace T] [CompactSpace T] [Nonempty T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (μ : Measure C(T,ℝ)) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m)
    (hM : (∫⁻ f : C(T,ℝ), edist f 0 ^ (2:ℕ) ∂μ) ≠ ⊤)
    {r : ℝ} (hr : 0 ≤ r)
    (hupper : expectedEmpiricalWassersteinTwo μ m hm ≤ ENNReal.ofReal r) :
    (∫ x : Fin m → C(T,ℝ), empiricalWassersteinReal μ hm x
      ∂iidSampleLaw μ m) ≤ r := by
  have hfinite : expectedEmpiricalWassersteinTwo μ m hm ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hmono := ENNReal.toReal_mono ENNReal.ofReal_ne_top hupper
  have hreal_le : (expectedEmpiricalWassersteinTwo μ m hm).toReal ≤ r := by
    simpa only [ENNReal.toReal_ofReal hr] using hmono
  have hidentity := integral_empiricalWassersteinReal_eq_toReal_lintegral μ 0 hM hm
  have hidentity' :
      (∫ x : Fin m → C(T,ℝ), empiricalWassersteinReal μ hm x
        ∂iidSampleLaw μ m) = (expectedEmpiricalWassersteinTwo μ m hm).toReal := by
    simpa [expectedEmpiricalWassersteinTwo] using hidentity
  rw [hidentity']
  exact hreal_le

/-- A common empirical rate assertion for one fixed path law. -/
def HasEmpiricalPowerlogRate {T : Type*} [MetricSpace T] [MeasurableSpace T]
    [BorelSpace T] [CompactSpace T] [SecondCountableTopology T]
    (μ : Measure C(T, ℝ)) (α β : ℝ) (z : ℝ × ℕ) : Prop :=
  0 < z.1 ∧ 0 < z.2 ∧ ∀ m : ℕ, z.2 ≤ m → ∀ hm : 0 < m,
    expectedEmpiricalWassersteinTwo μ m hm ≤
      ENNReal.ofReal (z.1 * (Real.log (m : ℝ)) ^ (-(1 / α)) *
        (Real.log (Real.log (m : ℝ))) ^ (β / α))

/-- If centered path laws with one covariance are unique, the power-log
empirical upper constants can be selected before the realization. -/
theorem exists_uniform_empirical_powerlog_rate
    {T H : Type*} [MetricSpace T] [MeasurableSpace T] [BorelSpace T]
    [CompactSpace T] [Nonempty T]
    [SecondCountableTopology T] [LocallyCompactSpace T]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : T → T → ℝ) (K : C(T,H)) (a : T) (ha : K a ≠ 0)
    (S : Set (Measure C(T,ℝ)))
    (hunique : ∀ μ ∈ S, ∀ ν ∈ S, μ = ν)
    (hcenter : ∀ μ ∈ S, IsCenteredPathLaw C μ)
    (hcovK : ∀ x y, C x y = inner ℝ (K x) (K y))
    {α β Csb ε₀ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hCsb : 0 < Csb) (hε₀ : 0 < ε₀)
    (hsb : ∀ μ ∈ S, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      -Real.log (μ.real (Metric.closedBall (0 : C(T,ℝ)) ε)) ≤
        Csb * Latest.smallBallRate α β ε) :
    ∃ z : ℝ × ℕ, 0 < z.1 ∧ 0 < z.2 ∧
      ∀ μ ∈ S, HasEmpiricalPowerlogRate μ α β z := by
  classical
  by_cases hSne : S.Nonempty
  · obtain ⟨z, hz⟩ := exists_uniform_of_unique_law S hunique
      (fun μ z => HasEmpiricalPowerlogRate μ α β z) (by
        intro μ hμ
        let hμc := hcenter μ hμ
        letI : IsProbabilityMeasure μ := hμc.1
        obtain ⟨C₁, hC₁, m₀, hm₀, hrate⟩ :=
          expected_empirical_powerlog_rate_of_smallBall
            (P := μ) (F := id) measurable_id hμc.2.1 hμc.2.2.1 K a ha
            (fun x y => (hμc.2.2.2 x y).trans (hcovK x y))
            hα hβ hCsb hε₀ (fun ε hε hεwin => by
              simpa using hsb μ hμ ε hε hεwin)
        refine ⟨(C₁,m₀), hC₁, hm₀, ?_⟩
        simpa [HasEmpiricalPowerlogRate] using hrate)
    obtain ⟨μ, hμ⟩ := hSne
    obtain ⟨hC, hm₀, _⟩ := hz μ hμ
    exact ⟨z, hC, hm₀, hz⟩
  · refine ⟨(1,1), by norm_num, by norm_num, ?_⟩
    intro μ hμ
    exact False.elim (hSne ⟨μ,hμ⟩)

private def fractionalLawSet {d : ℕ} (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) : Set (Measure C(HaarQuarter.BrownianCubeAnchor d,ℝ)) :=
  {μ | IsCenteredPathLaw (fractionalSheetCovariance H) μ}

/-- Sharp empirical upper rate for actual fractional-sheet path laws. The
constants are uniform over all realizations of the covariance law. -/
theorem fractionalSheet_expected_empirical_upper
    {d : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (ν : ℕ)
    (hν : 2 ≤ ν) (hmin : Latest.minimumMultiplicity H h ν) :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, 0 < m₀ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        [IsProbabilityMeasure P]
        (B : FractionalBrownianSheetOnCube d Ω P) (hBH : B.H = H)
        (m : ℕ) (hm : 0 < m), m₀ ≤ m →
        expectedEmpiricalWassersteinTwo (P.map B.path) m hm ≤
          ENNReal.ofReal (C * (Real.log (m : ℝ)) ^ (-h) *
            (Real.log (Real.log (m : ℝ))) ^ (h * ((ν - 1 : ℕ) : ℝ) + ν / 2)) := by
  classical
  obtain ⟨cSB, Csb, ε₀, hcSB, hCsb, hε₀, hεsmall, hsmall⟩ :=
    AlignmentFractionalSheetStatement.latest_fractionalSheet_certified
      d hd H hH h ν hν hmin
  let α : ℝ := h⁻¹
  let β : ℝ := ((ν - 1 : ℕ) : ℝ) + (ν : ℝ) / (2*h)
  have hh : 0 < h := by
    have hνpos : 0 < ν := by omega
    have hcardpos : 0 < (Finset.univ.filter (fun i : Fin d => H i = h)).card := by
      rw [hmin.2]
      exact hνpos
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hcardpos
    rw [← (Finset.mem_filter.mp hi).2]
    exact (hH i).1
  have hα : 0 < α := by dsimp [α]; exact inv_pos.mpr hh
  have hβ : 0 ≤ β := by
    dsimp [β]
    exact add_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) (by positivity))
  let S := fractionalLawSet H hH
  have hunique : ∀ μ ∈ S, ∀ ρ ∈ S, μ = ρ := by
    intro μ hμ ρ hρ
    exact centeredPathLaw_unique hμ hρ
  let K := fractionalSheetFeature H hH
  let a : HaarQuarter.BrownianCubeAnchor d :=
    AlignmentFractionalSheetUnitFeature.cubeOne d
  have ha : K a ≠ 0 := by
    intro hz
    have hnorm : ‖K a‖ = 1 := by
      simpa [a, K] using AlignmentFractionalSheetUnitFeature.fractionalSheetFeature_one_norm H hH
    rw [hz, norm_zero] at hnorm
    norm_num at hnorm
  have hcenter : ∀ μ ∈ S, IsCenteredPathLaw (fractionalSheetCovariance H) μ := by
    intro μ hμ
    exact hμ
  have hsb : ∀ μ ∈ S, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      -Real.log (μ.real (Metric.closedBall (0 : C(HaarQuarter.BrownianCubeAnchor d,ℝ)) ε)) ≤
        Csb * Latest.smallBallRate α β ε := by
    intro μ hμ ε hε hεwin
    letI : IsProbabilityMeasure μ := hμ.1
    let B : FractionalBrownianSheetOnCube d (C(HaarQuarter.BrownianCubeAnchor d,ℝ)) μ := {
      H := H
      hH := hH
      path := id
      measurable_path := measurable_id
      gaussian := hμ.2.1
      mean_zero := hμ.2.2.1
      covariance := by
        intro x y
        exact hμ.2.2.2 x y }
    have hsmall' := (hsmall _ _ B rfl ε hε hεwin).2
    have hevent : Metric.closedBall (0 : C(HaarQuarter.BrownianCubeAnchor d,ℝ)) ε =
        {f | ‖f‖ ≤ ε} := by
      ext f
      simp [Metric.mem_closedBall, dist_eq_norm]
    change -Real.log (μ.real {f | ‖f‖ ≤ ε}) ≤ _ at hsmall'
    have hsmall'' : -Real.log (μ.real (Metric.closedBall
        (0 : C(HaarQuarter.BrownianCubeAnchor d,ℝ)) ε)) ≤
        Csb * Latest.smallBallRate α β ε := by
      rw [← hevent] at hsmall'
      simpa [α, β] using hsmall'
    simpa [α, β] using hsmall''
  have hcovK : ∀ x y, fractionalSheetCovariance H x y = inner ℝ (K x) (K y) := by
    intro x y
    exact (fractionalSheetFeature_gram H hH x y).symm
  obtain ⟨z, hzC, hzM, hz⟩ := exists_uniform_empirical_powerlog_rate
    (fractionalSheetCovariance H) K a ha S hunique hcenter hcovK hα hβ hCsb hε₀ hsb
  refine ⟨z.1, hzC, z.2, hzM, ?_⟩
  intro Ω _ P hP B hBH m hmp hm
  letI : IsProbabilityMeasure P := hP
  have hLaw : P.map B.path ∈ S := by
    exact isCenteredPathLaw_map B.path B.measurable_path B.gaussian B.mean_zero
      (fractionalSheetCovariance H) (by
        intro x y
        rw [B.covariance, hBH])
  rcases hz (P.map B.path) hLaw with ⟨_, _, hrate⟩
  have hrate := hrate m hm hmp
  have hαeq : -(1 / α) = -h := by dsimp [α]; field_simp [ne_of_gt hh]
  have hβeq : β / α = h * ((ν - 1 : ℕ) : ℝ) + ν / 2 := by
    dsimp [α, β]
    rw [Nat.cast_sub (by omega : 1 ≤ ν)]
    field_simp [ne_of_gt hh]
  rw [hαeq, hβeq] at hrate
  exact hrate

private def integratedLawSet {d : ℕ} (orders : Fin d → ℕ) :
    Set (Measure C(HaarQuarter.BrownianCubeAnchor d,ℝ)) :=
  {μ | ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω)
      (hP : IsProbabilityMeasure P)
      (B : @HaarQuarter.BrownianSheetOnCube d Ω mΩ P),
      μ = P.map (fun ω => AlignmentGaussianRates.integrateSheetPath orders (B.path ω))}

/-- The common-integer integrated Brownian sheet has the paper's sharp
expected empirical transport upper rate, uniform over its Brownian
realizations. -/
theorem integrated_common_expected_empirical_upper
    {d : ℕ} (hd : 2 ≤ d) (q : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, 0 < m₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
        [IsProbabilityMeasure P] (B : HaarQuarter.BrownianSheetOnCube d Ω P)
        (m : ℕ) (hm : 0 < m), m₀ ≤ m →
        expectedEmpiricalWassersteinTwo
          (P.map (fun ω => AlignmentGaussianRates.integrateSheetPath
            (fun _ : Fin d => q) (B.path ω))) m hm ≤
          ENNReal.ofReal (C * (Real.log (m : ℝ)) ^ (-((q:ℝ)+(1/2:ℝ))) *
            (Real.log (Real.log (m : ℝ))) ^ (((q+1:ℕ):ℝ)*(d-1:ℕ)+1/2)) := by
  classical
  let orders : Fin d → ℕ := fun _ => q
  have hmin : Latest.minimumMultiplicity (fun i => (orders i : ℝ)) (q:ℝ) d := by
    constructor
    · intro i
      simp [orders]
    · simp [orders, Latest.minimumMultiplicity]
  obtain ⟨cSB, Csb, ε₀, hcSB, hCsb, hε₀, hεsmall, hsmall⟩ :=
    AlignmentGaussianIntegratedReverse.latest_integratedSheet_certified
      d hd orders q d (by omega) hmin
  let α : ℝ := 2 / (2*(q:ℝ)+1)
  let β : ℝ := ((d-1:ℕ):ℝ) + (d:ℝ)/(2*(q:ℝ)+1)
  have hden : 0 < 2*(q:ℝ)+1 := by positivity
  have hα : 0 < α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by
    dsimp [β]
    exact add_nonneg (Nat.cast_nonneg _) (div_nonneg (Nat.cast_nonneg _) (by positivity))
  let Ckernel : HaarQuarter.BrownianCubeAnchor d → HaarQuarter.BrownianCubeAnchor d → ℝ :=
    fun x y => inner ℝ (AlignmentGaussianBochner.integratedFeatureField orders x)
      (AlignmentGaussianBochner.integratedFeatureField orders y)
  let K : C(HaarQuarter.BrownianCubeAnchor d, HaarQuarter.brownianCubeBoxSpan d) :=
    AlignmentGaussianBochner.integratedFeatureField orders
  let a := AlignmentPaperIntegratedFeatureNonzero.cubeCorner d
  have ha : K a ≠ 0 := by
    simpa [K, orders, a] using
      AlignmentPaperIntegratedFeatureNonzero.integratedFeatureField_corner_ne_zero orders
  let S := integratedLawSet orders
  have hunique : ∀ μ ∈ S, ∀ ρ ∈ S, μ = ρ := by
    intro μ hμ ρ hρ
    rcases hμ with ⟨Ω, mΩ, P, hP, B, rfl⟩
    rcases hρ with ⟨Ψ, mΨ, Q, hQ, D, rfl⟩
    letI : MeasurableSpace Ω := mΩ
    letI : IsProbabilityMeasure P := hP
    letI : MeasurableSpace Ψ := mΨ
    letI : IsProbabilityMeasure Q := hQ
    let F : Ω → C(HaarQuarter.BrownianCubeAnchor d,ℝ) := fun ω =>
      AlignmentGaussianRates.integrateSheetPath orders (B.path ω)
    let G : Ψ → C(HaarQuarter.BrownianCubeAnchor d,ℝ) := fun ω =>
      AlignmentGaussianRates.integrateSheetPath orders (D.path ω)
    have hF : Measurable F := AlignmentGaussianRates.measurable_integrateBrownianSheetPath B orders
    have hG : Measurable G := AlignmentGaussianRates.measurable_integrateBrownianSheetPath D orders
    have hXF : IsGaussianProcess (fun x ω => F ω x) P := by
      simpa [F] using AlignmentGaussianBochner.integratedSheetPath_isGaussianProcess B orders
    have hXG : IsGaussianProcess (fun x ω => G ω x) Q := by
      simpa [G] using AlignmentGaussianBochner.integratedSheetPath_isGaussianProcess D orders
    have hmeanF : ∀ x, ∫ ω, F ω x ∂P = 0 := by
      intro x
      obtain ⟨T, W, hW, hpath⟩ :=
        AlignmentGaussianBochner.integratedSheetPath_ae_eq_isonormal B orders
      calc
        _ = ∫ ω, T (AlignmentGaussianBochner.integratedFeatureField orders x) ω ∂P :=
          integral_congr_ae (hpath x)
        _ = ∫ ω, W.eval (AlignmentGaussianBochner.integratedFeatureField orders x) ω ∂P :=
          integral_congr_ae (hW _).symm
        _ = 0 := W.mean_zero _
    have hmeanG : ∀ x, ∫ ω, G ω x ∂Q = 0 := by
      intro x
      obtain ⟨T, W, hW, hpath⟩ :=
        AlignmentGaussianBochner.integratedSheetPath_ae_eq_isonormal D orders
      calc
        _ = ∫ ω, T (AlignmentGaussianBochner.integratedFeatureField orders x) ω ∂Q :=
          integral_congr_ae (hpath x)
        _ = ∫ ω, W.eval (AlignmentGaussianBochner.integratedFeatureField orders x) ω ∂Q :=
          integral_congr_ae (hW _).symm
        _ = 0 := W.mean_zero _
    exact AlignmentPaperGaussianFeatureBridge.continuous_path_law_eq_of_same_covariance
      F G hF hG hXF hXG hmeanF hmeanG
      (fun x y => by
        rw [AlignmentGaussianBochner.integratedSheetPath_covariance,
          AlignmentGaussianBochner.integratedSheetPath_covariance])
  have hcenter : ∀ μ ∈ S, IsCenteredPathLaw Ckernel μ := by
    intro μ hμ
    rcases hμ with ⟨Ω, mΩ, P, hP, B, hEq⟩
    letI : MeasurableSpace Ω := mΩ
    letI : IsProbabilityMeasure P := hP
    let F : Ω → C(HaarQuarter.BrownianCubeAnchor d,ℝ) := fun ω =>
      AlignmentGaussianRates.integrateSheetPath orders (B.path ω)
    have hF : Measurable F := AlignmentGaussianRates.measurable_integrateBrownianSheetPath B orders
    have hXF : IsGaussianProcess (fun x ω => F ω x) P := by
      simpa [F] using AlignmentGaussianBochner.integratedSheetPath_isGaussianProcess B orders
    have hmeanF : ∀ x, ∫ ω, F ω x ∂P = 0 := by
      intro x
      obtain ⟨T, W, hW, hpath⟩ :=
        AlignmentGaussianBochner.integratedSheetPath_ae_eq_isonormal B orders
      calc
        _ = ∫ ω, T (AlignmentGaussianBochner.integratedFeatureField orders x) ω ∂P :=
          integral_congr_ae (hpath x)
        _ = ∫ ω, W.eval (AlignmentGaussianBochner.integratedFeatureField orders x) ω ∂P :=
          integral_congr_ae (hW _).symm
        _ = 0 := W.mean_zero _
    have hcov : ∀ x y, cov[fun ω => F ω x, fun ω => F ω y; P] = Ckernel x y := by
      intro x y
      simpa [F, Ckernel] using AlignmentGaussianBochner.integratedSheetPath_covariance B orders x y
    have hc := isCenteredPathLaw_map F hF hXF hmeanF Ckernel hcov
    rw [hEq]
    exact hc
  have hsb : ∀ μ ∈ S, ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      -Real.log (μ.real (Metric.closedBall (0 : C(HaarQuarter.BrownianCubeAnchor d,ℝ)) ε)) ≤
        Csb * Latest.smallBallRate α β ε := by
    intro μ hμ ε hε hεwin
    rcases hμ with ⟨Ω, mΩ, P, hP, B, hEq⟩
    letI : MeasurableSpace Ω := mΩ
    letI : IsProbabilityMeasure P := hP
    let F : Ω → C(HaarQuarter.BrownianCubeAnchor d,ℝ) := fun ω =>
      AlignmentGaussianRates.integrateSheetPath orders (B.path ω)
    have hF : Measurable F := AlignmentGaussianRates.measurable_integrateBrownianSheetPath B orders
    have hsm := (hsmall Ω P B ε hε hεwin).2
    have hmass : μ.real (Metric.closedBall (0 : C(HaarQuarter.BrownianCubeAnchor d,ℝ)) ε) =
        P.real {ω | ‖F ω‖ ≤ ε} := by
      rw [hEq, Measure.real_def,
        Measure.map_apply hF measurableSet_closedBall, Measure.real_def]
      congr 1
    rw [hmass]
    simpa [α, β, F] using hsm
  have hcovK : ∀ x y, Ckernel x y = inner ℝ (K x) (K y) := by intro x y; rfl
  obtain ⟨z, hzC, hzM, hz⟩ := exists_uniform_empirical_powerlog_rate
    Ckernel K a ha S hunique hcenter hcovK hα hβ hCsb hε₀ hsb
  refine ⟨z.1,hzC,z.2,hzM,?_⟩
  intro Ω _ P hP B m hm hm₀'
  letI : IsProbabilityMeasure P := hP
  let μ : Measure C(HaarQuarter.BrownianCubeAnchor d,ℝ) :=
    P.map (fun ω => AlignmentGaussianRates.integrateSheetPath orders (B.path ω))
  have hLaw : μ ∈ S := ⟨Ω, ‹MeasurableSpace Ω›, P, hP, B, rfl⟩
  rcases hz μ hLaw with ⟨_, _, hrate⟩
  have hrate := hrate m hm₀' hm
  have hαeq : -(1/α) = -((q:ℝ)+(1/2:ℝ)) := by
    dsimp [α]
    field_simp [ne_of_gt hden]
  have hβeq : β/α = ((q+1:ℕ):ℝ)*(d-1:ℕ)+1/2 := by
    dsimp [α, β]
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    push_cast
    field_simp [ne_of_gt hden]
    ring_nf
  rw [hαeq,hβeq] at hrate
  simpa [μ, orders] using hrate

end BrownianSharp.AlignmentPaperQuantizationSheetUpper
