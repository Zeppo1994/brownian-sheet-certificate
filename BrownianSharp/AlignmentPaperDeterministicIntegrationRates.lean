import BrownianSharp.AlignmentPaperDeterministicIntegration
import BrownianSharp.AlignmentPaperQuantizationSheetFinal

/-!
# Deterministic integration rates for the sheet laws (Section 5.3)

The minimax error of deterministic integration of 1-Lipschitz functionals against
the Brownian sheet, fractional Brownian sheet and integrated sheet laws, using at
most `m` exact evaluations, satisfies the same two-sided rate (5.18) as `q_{m,1}`.
-/

noncomputable section
universe u
open MeasureTheory ProbabilityTheory
open BrownianSharp.AlignmentPaperQuantizationSheetFinal
open BrownianSharp.AlignmentPaperDeterministicIntegration BrownianSharp.AlignmentGaussianRates

namespace BrownianSharp.AlignmentPaperDeterministicIntegrationRates

/-- Section 5.3, last sentence: the optimal worst-case error of deterministic
integration of 1-Lipschitz functionals against `B`, `B^H` and `R_q^{⊗d} B` has the
rate (5.18). -/
def DeterministicIntegrationRatesStatement : Prop :=
  (∀ {d : ℕ} (_hd : 2 ≤ d),
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ M : ℕ, 0 < M ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        [IsProbabilityMeasure P] (B : HaarQuarter.BrownianSheetOnCube d Ω P)
        (m : ℕ), 0 < m → M ≤ m →
        let μ := P.map B.path
        let r := brownianRate d m
        ENNReal.ofReal (c*r)/2 ≤ deterministicIntegrationMinimax μ m ∧
        deterministicIntegrationMinimax μ m ≤ ENNReal.ofReal (C*r)) ∧
  (∀ {d : ℕ} (_hd : 2 ≤ d) (H : Fin d → ℝ)
    (_hH : ∀ i, 0 < H i ∧ H i < 1) (h : ℝ) (ν : ℕ)
    (_hν : 2 ≤ ν) (_hmin : Latest.minimumMultiplicity H h ν),
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ M : ℕ, 0 < M ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        [IsProbabilityMeasure P] (B : FractionalBrownianSheetOnCube d Ω P)
        (_ : B.H = H) (m : ℕ), 0 < m → M ≤ m →
        let μ := P.map B.path
        let r := fractionalRate h ν m
        ENNReal.ofReal (c*r)/2 ≤ deterministicIntegrationMinimax μ m ∧
        deterministicIntegrationMinimax μ m ≤ ENNReal.ofReal (C*r)) ∧
  (∀ {d : ℕ} (_hd : 2 ≤ d) (q : ℕ),
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ M : ℕ, 0 < M ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
        [IsProbabilityMeasure P] (B : HaarQuarter.BrownianSheetOnCube d Ω P)
        (m : ℕ), 0 < m → M ≤ m →
        let μ := P.map (fun ω => integrateSheetPath (fun _ : Fin d => q) (B.path ω))
        let r := integratedCommonRate q d m
        ENNReal.ofReal (c*r)/2 ≤ deterministicIntegrationMinimax μ m ∧
        deterministicIntegrationMinimax μ m ≤ ENNReal.ofReal (C*r))

theorem deterministicIntegrationRates_certified : DeterministicIntegrationRatesStatement.{u} := by
  obtain ⟨hB, hF, hI⟩ := paperQuantizationResultsStatement.{u}
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨c, _, C, hc, _, hC, M, hM, h⟩ := hB hd
    refine ⟨c, C, hc, hC, M, hM, ?_⟩
    intro Ω _ P hP B m hm hMm
    obtain ⟨h1, -, h12, h2, -⟩ := h B m hm hMm
    have := centeredGaussianPath_deterministicIntegration_eq_quantizationQ1 B.path
      B.measurable_path B.gaussian B.mean_zero m hm
    simp only [this]
    exact ⟨h1, h12.trans h2⟩
  · intro d hd H hH h ν hν hmin
    obtain ⟨c, _, C, hc, _, hC, M, hM, h'⟩ := hF hd H hH h ν hν hmin
    refine ⟨c, C, hc, hC, M, hM, ?_⟩
    intro Ω _ P hP B hBH m hm hMm
    obtain ⟨h1, -, h12, h2, -⟩ := h' B hBH m hm hMm
    have := centeredGaussianPath_deterministicIntegration_eq_quantizationQ1 B.path
      B.measurable_path B.gaussian B.mean_zero m hm
    simp only [this]
    exact ⟨h1, h12.trans h2⟩
  · intro d hd q
    obtain ⟨c, _, C, hc, _, hC, M, hM, h⟩ := hI hd q
    refine ⟨c, C, hc, hC, M, hM, ?_⟩
    intro Ω _ P hP B m hm hMm
    obtain ⟨h1, -, h12, h2, -⟩ := h B m hm hMm
    have hX := AlignmentGaussianBochner.integratedSheetPath_isGaussianProcess B (fun _ : Fin d => q)
    have hmean : ∀ x, ∫ ω, integrateSheetPath (fun _ : Fin d => q) (B.path ω) x ∂P = 0 := by
      intro x
      obtain ⟨T, W, hW, hpath⟩ :=
        AlignmentGaussianBochner.integratedSheetPath_ae_eq_isonormal B (fun _ : Fin d => q)
      calc
        _ = ∫ ω, T (AlignmentGaussianBochner.integratedFeatureField (fun _ : Fin d => q) x) ω ∂P :=
          integral_congr_ae (hpath x)
        _ = ∫ ω, W.eval (AlignmentGaussianBochner.integratedFeatureField (fun _ : Fin d => q) x) ω ∂P :=
          integral_congr_ae (hW _).symm
        _ = 0 := W.mean_zero _
    have := centeredGaussianPath_deterministicIntegration_eq_quantizationQ1
      (fun ω => integrateSheetPath (fun _ : Fin d => q) (B.path ω))
      (measurable_integrateBrownianSheetPath B (fun _ : Fin d => q)) hX hmean m hm
    simp only [this]
    exact ⟨h1, h12.trans h2⟩

end BrownianSharp.AlignmentPaperDeterministicIntegrationRates
