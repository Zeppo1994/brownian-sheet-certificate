import BrownianSharp.AlignmentPaperCodebookTailDistortion

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentPaperEmpiricalGoodTail
open AlignmentPaperEmpiricalCellLift

/-- Combine the actual finite-cell empirical coupling and fourth-moment tail
estimate. The outer integral is the ENNReal integral; measurability of the
Wasserstein error is established separately before using a real expectation. -/
theorem expected_empirical_wassersteinTwo_le_good_tail
    {X : Type*} [MetricSpace X] [Zero X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N)
    (c : Fin N → X) (i₀ : Fin N) (hi₀ : c i₀=0)
    (G : Set X) (hG : MeasurableSet G) (ρ M4 δ D : ℝ≥0∞)
    (hcover : ∀ x ∈ G, ∃ i : Fin N, edist x (c i) ≤ ρ)
    (hM4 : (∫⁻ x, edist x (0:X)^4 ∂μ) ≤ M4)
    (htail : μ Gᶜ ≤ δ)
    (hdiam : ∀ i j, edist (c i) (c j)^2 ≤ D^2) :
    (∫⁻ x : Fin m → X,
      wassersteinTwo μ
        (empiricalMeasure m hm x)
      ∂AlignmentPaperEmpiricalWasserstein.iidSampleLaw μ m) ≤
      ennrealSqrt (3*((2:ℝ≥0∞)*(ρ^2+ennrealSqrt M4*ennrealSqrt δ)+
        D^2*ENNReal.ofReal ((1/2:ℝ)*Real.sqrt ((N:ℝ)/m)))) := by
  have hmass : μ G ≤ 1 := by
    simpa using (measure_mono (Set.subset_univ G) : μ G ≤ μ Set.univ)
  have hdist := AlignmentPaperCodebookTailDistortion.finiteCodebookDistortion_lintegral_le_good_tail μ N hN c i₀ hi₀ G hG ρ M4 hcover hM4
  have hdist' : (∫⁻ x, finiteCodebookDistortion hN c x^2 ∂μ) ≤
      ρ^2+ennrealSqrt M4*ennrealSqrt δ := by
    apply hdist.trans
    calc
      ρ^2*μ G+ennrealSqrt M4*ennrealSqrt (μ Gᶜ) ≤
        ρ^2*1+ennrealSqrt M4*ennrealSqrt δ := by
          gcongr
          exact ENNReal.rpow_le_rpow htail (by norm_num)
      _ = _ := by rw [mul_one]
  apply (AlignmentPaperEmpiricalIntegrals.expected_wassersteinTwo_le_codebook
    μ m hm N hN c D hdiam).trans
  exact ENNReal.rpow_le_rpow (by gcongr) (by norm_num)

end BrownianSharp.AlignmentPaperEmpiricalGoodTail
