import BrownianSharp.Confinement
import BrownianSharp.RootRepair

/-! The complete two-use concentration assembly, conditional only on the
explicit tail properties of the actual power and root statistics. -/
open MeasureTheory ProbabilityTheory
namespace BrownianSharp

/-- The first concentration application pays for the near-zero exceptional
set before taking the p-th root. -/
theorem power_statistic_rare_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → ℝ) (p C D c : ℝ) (hp : 2 ≤ p)
    (hC : 0 < C) (hD : 0 < D) (hc : 0 < c)
    (hmean : ∫ ω, U ω ∂μ = 1)
    (hv : 0 < ProbabilityTheory.variance U μ)
    (hvar : ProbabilityTheory.variance U μ ≤ C * p ^ 2 / D)
    (hsmall : C * p ^ 2 / D ≤ 1 / 16)
    (hpSmall : p ^ 2 ≤ Real.sqrt D)
    (hlarge : 4 * C ≤ (c / 4) * Real.sqrt (Real.sqrt D))
    (htail : VarianceSensitiveLowerTail μ U c) :
    μ.real {ω | U ω < 1 / 2} ≤ 1 / D := by
  have hpPos : 0 < p := by linarith
  have hR : 0 < C * p ^ 2 / D := by positivity
  have hrel : ProbabilityTheory.variance U μ / (∫ ω, U ω ∂μ) ^ 2 ≤
      C * p ^ 2 / D := by simpa [hmean] using hvar
  have h := half_mean_tail_of_relative_variance μ U c (C * p ^ 2 / D)
    hc.le hR hsmall (by simpa [hmean]) hv hrel htail
  rw [hmean] at h
  have hexp : -c / (4 * (C * p ^ 2 / D)) = -(c / 4) * D / (C * p ^ 2) := by
    field_simp
  rw [hexp] at h
  have hweak := h.trans (exponential_remainder_le_inv_dimension hD hpPos
    (by positivity : 0 < c / 4) hC hpSmall hlarge)
  have hsub : {ω | U ω < 1 / 2} ⊆ {ω | U ω ≤ 1 / 2} := by
    intro ω hω
    change U ω ≤ 1 / 2
    exact le_of_lt (show U ω < 1 / 2 from hω)
  exact (MeasureTheory.measureReal_mono hsub).trans hweak

/-- Both applications of PV, the root repair and all denominator factors are
assembled here. The only analytic concentration hypotheses are htailU and
htailRoot; neither is asserted by this module. -/
theorem two_stage_confinement
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → ℝ) (p C D c : ℝ) (hp : 2 ≤ p)
    (hC : 0 < C) (hD : 0 < D) (hc : 0 < c)
    (hU : Measurable U) (hUpos : ∀ ω, 0 ≤ U ω)
    (hULp : MemLp U 2 μ) (hrootLp : MemLp (fun ω => U ω ^ (1 / p)) 2 μ)
    (hmean : ∫ ω, U ω ∂μ = 1)
    (hv : 0 < ProbabilityTheory.variance U μ)
    (hvroot : 0 < ProbabilityTheory.variance (fun ω => U ω ^ (1 / p)) μ)
    (hvar : ProbabilityTheory.variance U μ ≤ C * p ^ 2 / D)
    (hsmall : C * p ^ 2 / D ≤ 1 / 16)
    (hpSmall : p ^ 2 ≤ Real.sqrt D)
    (hlarge : 4 * C ≤ (c / 4) * Real.sqrt (Real.sqrt D))
    (hDlarge : 64 * (4 * C + 1) ≤ D)
    (htailU : VarianceSensitiveLowerTail μ U c)
    (htailRoot : VarianceSensitiveLowerTail μ (fun ω => U ω ^ (1 / p)) c) :
    μ.real {ω | U ω ^ (1 / p) ≤ 1 / 4} ≤
      Real.exp (-(c / (16 * (4 * C + 1))) * D) := by
  have hrare := power_statistic_rare_tail μ U p C D c hp hC hD hc
    hmean hv hvar hsmall hpSmall hlarge htailU
  have hDroot : 4 * (4 * C + 1) ≤ D := by nlinarith
  have hrepair := root_repair_mean_and_relative_variance μ U p C D hp hC hD
    hDroot hU hUpos hULp hrootLp hmean hvar hrare
  have hresult := repaired_root_confinement μ (fun ω => U ω ^ (1 / p)) c
    (4 * (4 * C + 1)) D hc.le (by positivity) hD
    (by nlinarith) hrepair.1 hvroot hrepair.2 htailRoot
  convert hresult using 1 <;> congr 1 <;> ring

end BrownianSharp
