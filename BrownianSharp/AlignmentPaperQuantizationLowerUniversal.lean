import BrownianSharp.AlignmentPaperQuantizationLowerCertified
import BrownianSharp.AlignmentPaperGaussianPathLaws

/-! Universe-polymorphic versions of the certified lower bounds.  They
normalize an arbitrary realization to its continuous-path law, then apply the
already-certified Type 0 result to the identity realization. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperQuantizationLowerUniversal

open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.AlignmentPaperGaussianPathLaws
open BrownianSharp.AlignmentPaperQuantizationLowerCertified
open BrownianSharp.AlignmentPaperQuantizationAtomicBridge
open BrownianSharp.Latest

theorem fractionalSheetQ1_lower_rate
    {d : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (ν : ℕ)
    (hν : 2 ≤ ν) (hmin : Latest.minimumMultiplicity H h ν) :
    ∃ M : ℕ, ∃ cRate : ℝ, 0 < cRate ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        [IsProbabilityMeasure P]
        (B : FractionalBrownianSheetOnCube d Ω P) (hBH : B.H = H)
        (m : ℕ) (hM : M ≤ m) (hm : 0 < m),
        ENNReal.ofReal (canonicalPowerlogRadius (h⁻¹)
          (((ν - 1 : ℕ) : ℝ) + (ν : ℝ) / (2*h)) cRate
          (Real.log (m : ℝ))) / 2 ≤ quantizationQ1 (P.map B.path) m hm := by
  obtain ⟨M,cRate,hc,hq⟩ :=
    AlignmentPaperQuantizationLowerCertified.fractionalSheetQ1_lower_rate
      hd H hH h ν hν hmin
  refine ⟨M,cRate,hc,?_⟩
  intro Ω _ P hP B hBH m hM hm
  letI : IsProbabilityMeasure P := hP
  let μ : Measure C(HaarQuarter.BrownianCubeAnchor d,ℝ) := P.map B.path
  have hμ : IsCenteredPathLaw (fractionalSheetCovariance H) μ :=
    isCenteredPathLaw_map B.path B.measurable_path B.gaussian B.mean_zero
      (fractionalSheetCovariance H) (by simpa [hBH] using B.covariance)
  let B₀ : FractionalBrownianSheetOnCube d
      (C(HaarQuarter.BrownianCubeAnchor d,ℝ)) μ := {
    H := H
    hH := hH
    path := id
    measurable_path := measurable_id
    gaussian := hμ.2.1
    mean_zero := hμ.2.2.1
    covariance := hμ.2.2.2 }
  have hq₀ := hq B₀ rfl m hM hm
  simpa [B₀, μ] using hq₀

theorem fractionalSheetQ2_lower_rate
    {d : ℕ} (hd : 2 ≤ d) (H : Fin d → ℝ)
    (hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (ν : ℕ)
    (hν : 2 ≤ ν) (hmin : Latest.minimumMultiplicity H h ν) :
    ∃ M : ℕ, ∃ cRate : ℝ, 0 < cRate ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        [IsProbabilityMeasure P]
        (B : FractionalBrownianSheetOnCube d Ω P) (hBH : B.H = H)
        (m : ℕ) (hM : M ≤ m) (hm : 0 < m),
        ENNReal.ofReal (canonicalPowerlogRadius (h⁻¹)
          (((ν - 1 : ℕ) : ℝ) + (ν : ℝ) / (2*h)) cRate
          (Real.log (m : ℝ))) / 2 ≤ quantizationQ2 (P.map B.path) m hm := by
  obtain ⟨M,cRate,hc,hq⟩ := fractionalSheetQ1_lower_rate hd H hH h ν hν hmin
  refine ⟨M,cRate,hc,?_⟩
  intro Ω hΩ P hP B hBH m hM hm
  letI : IsProbabilityMeasure P := hP
  exact (hq B hBH m hM hm).trans
    (quantizationQ1_le_Q2 (P.map B.path) m hm
      (fun code => AlignmentPaperQuantizationAtomicBridge.finiteCodebookDistortion_measurable hm code))

theorem integratedSheetQ1_lower_rate
    {d : ℕ} (hd : 2 ≤ d) (orders : Fin d → ℕ)
    (m₀ ν : ℕ) (hν : 2 ≤ ν)
    (hmin : Latest.minimumMultiplicity (fun i => (orders i : ℝ))
      (m₀ : ℝ) ν) :
    ∃ M : ℕ, ∃ cRate : ℝ, 0 < cRate ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        [IsProbabilityMeasure P] (B : HaarQuarter.BrownianSheetOnCube d Ω P)
        (m : ℕ) (hM : M ≤ m) (hm : 0 < m),
        ENNReal.ofReal (canonicalPowerlogRadius (2/(2*(m₀:ℝ)+1))
          (((ν - 1 : ℕ) : ℝ) + (ν : ℝ)/(2*(m₀:ℝ)+1)) cRate
          (Real.log (m : ℝ))) / 2 ≤
          quantizationQ1 (P.map (fun ω => integrateSheetPath orders (B.path ω))) m hm := by
  obtain ⟨M,cRate,hc,hq⟩ :=
    AlignmentPaperQuantizationLowerCertified.integratedSheetQ1_lower_rate
      hd orders m₀ ν hν hmin
  refine ⟨M,cRate,hc,?_⟩
  intro Ω _ P hP B m hM hm
  letI : IsProbabilityMeasure P := hP
  let μ : Measure C(HaarQuarter.BrownianCubeAnchor d,ℝ) := P.map B.path
  have hlaw := isCenteredPathLaw_map B.path B.measurable_path B.gaussian
    B.mean_zero (fun x y => ∏ i, min (x.val i) (y.val i)) B.covariance
  let B₀ : HaarQuarter.BrownianSheetOnCube d
      (C(HaarQuarter.BrownianCubeAnchor d,ℝ)) μ := {
    B with
    path := id
    measurable_path := measurable_id
    gaussian := hlaw.2.1
    mean_zero := hlaw.2.2.1
    covariance := hlaw.2.2.2 }
  have hq₀ := hq B₀ m hM hm
  have hmap : Measurable (fun f : C(HaarQuarter.BrownianCubeAnchor d,ℝ) =>
      integrateSheetPath orders f) := (integrateSheetPath_continuous orders).measurable
  have hq' : ENNReal.ofReal (canonicalPowerlogRadius (2/(2*(m₀:ℝ)+1))
      (((ν - 1 : ℕ) : ℝ) + (ν : ℝ)/(2*(m₀:ℝ)+1)) cRate
      (Real.log (m : ℝ))) / 2 ≤
      quantizationQ1 (μ.map (fun f => integrateSheetPath orders f)) m hm := by
    simpa [B₀] using hq₀
  rw [show μ = P.map B.path from rfl] at hq'
  rw [Measure.map_map hmap B.measurable_path] at hq'
  simpa [Function.comp_def] using hq'

theorem integratedSheetQ2_lower_rate
    {d : ℕ} (hd : 2 ≤ d) (orders : Fin d → ℕ)
    (m₀ ν : ℕ) (hν : 2 ≤ ν)
    (hmin : Latest.minimumMultiplicity (fun i => (orders i : ℝ))
      (m₀ : ℝ) ν) :
    ∃ M : ℕ, ∃ cRate : ℝ, 0 < cRate ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        [IsProbabilityMeasure P] (B : HaarQuarter.BrownianSheetOnCube d Ω P)
        (m : ℕ) (hM : M ≤ m) (hm : 0 < m),
        ENNReal.ofReal (canonicalPowerlogRadius (2/(2*(m₀:ℝ)+1))
          (((ν - 1 : ℕ) : ℝ) + (ν : ℝ)/(2*(m₀:ℝ)+1)) cRate
          (Real.log (m : ℝ))) / 2 ≤
          quantizationQ2 (P.map (fun ω => integrateSheetPath orders (B.path ω))) m hm := by
  obtain ⟨M,c,hc,hq⟩ := integratedSheetQ1_lower_rate hd orders m₀ ν hν hmin
  refine ⟨M,c,hc,?_⟩
  intro Ω hΩ P hP B m hM hm
  letI : IsProbabilityMeasure P := hP
  exact (hq B m hM hm).trans
    (quantizationQ1_le_Q2
      (P.map (fun ω => integrateSheetPath orders (B.path ω))) m hm
      (fun code => AlignmentPaperQuantizationAtomicBridge.finiteCodebookDistortion_measurable hm code))

end BrownianSharp.AlignmentPaperQuantizationLowerUniversal
