import BrownianSharp.AlignmentPaperQuantizationRates
import BrownianSharp.AlignmentPaperQuantizationAtomicBridge
import BrownianSharp.AlignmentGaussianBrownianReverse
import BrownianSharp.AlignmentFractionalSheetStatement
import BrownianSharp.AlignmentGaussianIntegratedReverse

/-! Quantization lower-rate statements with certified small-ball inputs and
automatic codebook measurability. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperQuantizationLowerCertified

open BrownianSharp
open BrownianSharp.AlignmentPaperQuantizationAtomicBridge
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.Latest

private theorem gaussianQ1_lower_rate_uniform
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [LocallyCompactSpace X] [CompactSpace X]
    {α β c₀ ε₀ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hc₀ : 0 < c₀) (hε₀ : 0 < ε₀) :
    ∃ M : ℕ, ∃ cRate : ℝ, 0 < cRate ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (F : Ω → C(X, ℝ)) (hF : Measurable F)
        (hG : ProbabilityTheory.IsGaussianProcess (fun x ω => F ω x) P)
        (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
        (hlog : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          c₀ * Latest.smallBallRate α β ε ≤
            -Real.log (P.real {ω | ‖F ω‖ ≤ ε}))
        (hmeas : ∀ (m : ℕ) (hm : 0 < m) (c : Fin m → C(X, ℝ)),
          Measurable (fun x => finiteCodebookDistortion hm c x))
        (m : ℕ) (_hM : M ≤ m) (hm : 0 < m),
        ENNReal.ofReal
          (canonicalPowerlogRadius α β cRate (Real.log (m : ℝ))) / 2 ≤
            quantizationQ1 (P.map F) m hm := by
  obtain ⟨cRate, hcRate, Ms, hstrength⟩ :=
    exists_eventual_powerlog_strength_nat hα hβ hc₀
  have hwindow := eventually_powerlog_radius_window_nat
    (α := α) (β := β) (c := cRate) (ε₀ := ε₀) hα hβ hcRate hε₀
  obtain ⟨Mw, hwindow⟩ := Filter.eventually_atTop.1 hwindow
  refine ⟨max Ms Mw, cRate, hcRate, ?_⟩
  intro Ω _ P _ F hF hG hmean hlog hmeas m hM hm
  have hs := hstrength m (le_trans (le_max_left _ _) hM)
  have hw := hwindow m (le_trans (le_max_right _ _) hM)
  let t := canonicalPowerlogRadius α β cRate (Real.log (m : ℝ))
  have ht : 0 < t := by
    dsimp [t, canonicalPowerlogRadius]
    have hx : 0 < Real.log (m : ℝ) := by linarith [hs.1]
    have hL : 0 < Real.log (Real.log (m : ℝ)) := Real.log_pos (by linarith [hs.1])
    positivity
  have hq := centeredGaussian_quantizationQ1_lower_of_powerlog_smallball
    F hF hG hmean hα hβ hc₀ m hm t ht hw
    (by simpa [t, canonicalPowerlogRadius] using hs.2) hlog (hmeas m hm)
  simpa [t] using hq

theorem fractionalSheetQ1_lower_rate
    {d : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (ν : ℕ)
    (hν : 2 ≤ ν) (hmin : Latest.minimumMultiplicity H h ν) :
    ∃ M : ℕ, ∃ cRate : ℝ, 0 < cRate ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
        (B : AlignmentGaussianRates.FractionalBrownianSheetOnCube d Ω P)
        (hBH : B.H = H) [IsProbabilityMeasure P]
        (m : ℕ) (_hM : M ≤ m) (hm : 0 < m),
        ENNReal.ofReal (canonicalPowerlogRadius (h⁻¹)
          (((ν - 1 : ℕ) : ℝ) + (ν : ℝ) / (2 * h)) cRate
          (Real.log (m : ℝ))) / 2 ≤ quantizationQ1 (P.map B.path) m hm := by
  obtain ⟨c₀, _, ε₀, hc₀, _, hε₀, _, hsmall⟩ :=
    AlignmentFractionalSheetStatement.latest_fractionalSheet_certified
      d hd H hH h ν hν hmin
  have ⟨i, hi⟩ : ∃ i, H i = h := by
    have hne : (Finset.univ.filter (fun i : Fin d => H i = h)).Nonempty := by
      apply Finset.card_pos.mp
      rw [hmin.2]
      omega
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, (Finset.mem_filter.mp hi).2⟩
  have hh : 0 < h := by rw [← hi]; exact (hH i).1
  let α : ℝ := h⁻¹
  let β : ℝ := ((ν - 1 : ℕ) : ℝ) + (ν : ℝ) / (2 * h)
  have hα : 0 < α := by dsimp [α]; exact inv_pos.mpr hh
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  obtain ⟨M, cRate, hcRate, hrate⟩ := gaussianQ1_lower_rate_uniform
    (X := HaarQuarter.BrownianCubeAnchor d) hα hβ hc₀ hε₀
  refine ⟨M, cRate, hcRate, ?_⟩
  intro Ω _ P B hBH _ m hM hm
  letI : IsProbabilityMeasure P := B.gaussian.isProbabilityMeasure
  have hlog : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      c₀ * Latest.smallBallRate α β ε ≤
        -Real.log (P.real {ω | ‖B.path ω‖ ≤ ε}) := by
    intro ε hε hεsmall
    exact (hsmall Ω P B hBH ε hε hεsmall).1
  have hmcode : ∀ (n : ℕ) (hn : 0 < n)
      (code : Fin n → C(HaarQuarter.BrownianCubeAnchor d, ℝ)),
      Measurable (fun x => finiteCodebookDistortion hn code x) :=
    fun n hn code => finiteCodebookDistortion_measurable hn code
  have hq := hrate B.path B.measurable_path B.gaussian B.mean_zero hlog hmcode m hM hm
  simpa [α, β] using hq

theorem fractionalSheetQ2_lower_rate
    {d : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (ν : ℕ)
    (hν : 2 ≤ ν) (hmin : Latest.minimumMultiplicity H h ν) :
    ∃ M : ℕ, ∃ cRate : ℝ, 0 < cRate ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
        (B : AlignmentGaussianRates.FractionalBrownianSheetOnCube d Ω P)
        (hBH : B.H = H) [IsProbabilityMeasure P]
        (m : ℕ) (hM : M ≤ m) (hm : 0 < m),
        ENNReal.ofReal (canonicalPowerlogRadius (h⁻¹)
          (((ν - 1 : ℕ) : ℝ) + (ν : ℝ) / (2 * h)) cRate
          (Real.log (m : ℝ))) / 2 ≤ quantizationQ2 (P.map B.path) m hm := by
  obtain ⟨M, cRate, hcRate, hq⟩ := fractionalSheetQ1_lower_rate hd H hH h ν hν hmin
  refine ⟨M, cRate, hcRate, ?_⟩
  intro Ω _ P B hBH hP m hM hm
  letI : IsProbabilityMeasure P := B.gaussian.isProbabilityMeasure
  exact (hq B hBH m hM hm).trans
    (quantizationQ1_le_Q2 (P.map B.path) m hm
      (fun code => finiteCodebookDistortion_measurable hm code))

theorem integratedSheetQ1_lower_rate
    {d : ℕ} (hd : 2 ≤ d) (orders : Fin d → ℕ)
    (m₀ ν : ℕ) (hν : 2 ≤ ν)
    (hmin : Latest.minimumMultiplicity (fun i => (orders i : ℝ))
      (m₀ : ℝ) ν) :
    ∃ M : ℕ, ∃ cRate : ℝ, 0 < cRate ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
        (B : HaarQuarter.BrownianSheetOnCube d Ω P)
        [IsProbabilityMeasure P]
        (m : ℕ) (_hM : M ≤ m) (hm : 0 < m),
        ENNReal.ofReal (canonicalPowerlogRadius (2 / (2 * (m₀ : ℝ) + 1))
          (((ν - 1 : ℕ) : ℝ) + (ν : ℝ) / (2 * (m₀ : ℝ) + 1)) cRate
          (Real.log (m : ℝ))) / 2 ≤
          quantizationQ1 (P.map (fun ω => integrateSheetPath orders (B.path ω))) m hm := by
  obtain ⟨c₀, _, ε₀, hc₀, _, hε₀, _, hsmall⟩ :=
    AlignmentGaussianIntegratedReverse.latest_integratedSheet_certified
      d hd orders m₀ ν hν hmin
  let α : ℝ := 2 / (2 * (m₀ : ℝ) + 1)
  let β : ℝ := ((ν - 1 : ℕ) : ℝ) + (ν : ℝ) / (2 * (m₀ : ℝ) + 1)
  have hα : 0 < α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  obtain ⟨M, cRate, hcRate, hrate⟩ := gaussianQ1_lower_rate_uniform
    (X := HaarQuarter.BrownianCubeAnchor d) hα hβ hc₀ hε₀
  refine ⟨M, cRate, hcRate, ?_⟩
  intro Ω _ P B _ m hM hm
  letI : IsProbabilityMeasure P := B.gaussian.isProbabilityMeasure
  let F : Ω → C(HaarQuarter.BrownianCubeAnchor d, ℝ) := fun ω =>
    integrateSheetPath orders (B.path ω)
  have hF : Measurable F := measurable_integrateBrownianSheetPath B orders
  have hG : ProbabilityTheory.IsGaussianProcess (fun x ω => F ω x) P := by
    simpa [F] using AlignmentGaussianBochner.integratedSheetPath_isGaussianProcess B orders
  have hmean : ∀ x, ∫ ω, F ω x ∂P = 0 := by
    intro x
    obtain ⟨T, W, hW, hpath⟩ :=
      AlignmentGaussianBochner.integratedSheetPath_ae_eq_isonormal B orders
    calc
      _ = ∫ ω, T (AlignmentGaussianBochner.integratedFeatureField orders x) ω ∂P :=
        integral_congr_ae (hpath x)
      _ = ∫ ω, W.eval (AlignmentGaussianBochner.integratedFeatureField orders x) ω ∂P :=
        integral_congr_ae (hW _).symm
      _ = 0 := W.mean_zero _
  have hlog : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      c₀ * Latest.smallBallRate α β ε ≤
        -Real.log (P.real {ω | ‖F ω‖ ≤ ε}) := by
    intro ε hε hεsmall
    exact (hsmall Ω P B ε hε hεsmall).1
  have hmcode : ∀ (n : ℕ) (hn : 0 < n)
      (code : Fin n → C(HaarQuarter.BrownianCubeAnchor d, ℝ)),
      Measurable (fun x => finiteCodebookDistortion hn code x) :=
    fun n hn code => finiteCodebookDistortion_measurable hn code
  have hq := hrate F hF hG hmean hlog hmcode m hM hm
  simpa [α, β, F, integrateSheetPath] using hq

theorem integratedSheetQ2_lower_rate
    {d : ℕ} (hd : 2 ≤ d) (orders : Fin d → ℕ)
    (m₀ ν : ℕ) (hν : 2 ≤ ν)
    (hmin : Latest.minimumMultiplicity (fun i => (orders i : ℝ))
      (m₀ : ℝ) ν) :
    ∃ M : ℕ, ∃ cRate : ℝ, 0 < cRate ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
        (B : HaarQuarter.BrownianSheetOnCube d Ω P)
        [IsProbabilityMeasure P]
        (m : ℕ) (hM : M ≤ m) (hm : 0 < m),
        ENNReal.ofReal (canonicalPowerlogRadius (2 / (2 * (m₀ : ℝ) + 1))
          (((ν - 1 : ℕ) : ℝ) + (ν : ℝ) / (2 * (m₀ : ℝ) + 1)) cRate
          (Real.log (m : ℝ))) / 2 ≤
          quantizationQ2 (P.map (fun ω => integrateSheetPath orders (B.path ω))) m hm := by
  obtain ⟨M, cRate, hcRate, hq⟩ := integratedSheetQ1_lower_rate hd orders m₀ ν hν hmin
  refine ⟨M, cRate, hcRate, ?_⟩
  intro Ω _ P B hP m hM hm
  letI : IsProbabilityMeasure P := B.gaussian.isProbabilityMeasure
  exact (hq B m hM hm).trans
    (quantizationQ1_le_Q2
      (P.map (fun ω => integrateSheetPath orders (B.path ω))) m hm
      (fun code => finiteCodebookDistortion_measurable hm code))

end BrownianSharp.AlignmentPaperQuantizationLowerCertified
