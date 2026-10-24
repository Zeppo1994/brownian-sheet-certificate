import BrownianSharp.TwoStageConfinement

/-! An equivalent two-stage assembly using the exponential remainder directly,
so the proved eventual numerical budgets apply without duplicated estimates. -/
open MeasureTheory ProbabilityTheory
namespace BrownianSharp

theorem two_stage_confinement_of_exponential_remainder
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
    (hremainder : Real.exp (-(c / 4) * D / (C * p ^ 2)) ≤ 1 / D)
    (hDlarge : 64 * (4 * C + 1) ≤ D)
    (htailU : VarianceSensitiveLowerTail μ U c)
    (htailRoot : VarianceSensitiveLowerTail μ (fun ω => U ω ^ (1 / p)) c) :
    μ.real {ω | U ω ^ (1 / p) ≤ 1 / 4} ≤
      Real.exp (-(c / (16 * (4 * C + 1))) * D) := by
  have hpPos : 0 < p := by linarith
  have hR : 0 < C * p ^ 2 / D := div_pos (mul_pos hC (sq_pos_of_pos hpPos)) hD
  have hrel : ProbabilityTheory.variance U μ / (∫ ω, U ω ∂μ) ^ 2 ≤ C * p ^ 2 / D := by
    simpa [hmean] using hvar
  have hhalf := half_mean_tail_of_relative_variance μ U c (C * p ^ 2 / D)
    hc.le hR hsmall (by simpa [hmean]) hv hrel htailU
  rw [hmean] at hhalf
  have hexp : -c / (4 * (C * p ^ 2 / D)) = -(c / 4) * D / (C * p ^ 2) := by field_simp
  rw [hexp] at hhalf
  have hrare : μ.real {ω | U ω < 1 / 2} ≤ 1 / D := by
    exact (measureReal_mono (by intro ω hω; exact le_of_lt (show U ω < 1 / 2 from hω))).trans (hhalf.trans hremainder)
  have hrepair := root_repair_mean_and_relative_variance μ U p C D hp hC hD
    (by nlinarith : 4 * (4 * C + 1) ≤ D) hU hUpos hULp hrootLp hmean hvar hrare
  have hresult := repaired_root_confinement μ (fun ω => U ω ^ (1 / p)) c
    (4 * (4 * C + 1)) D hc.le (by positivity) hD (by nlinarith)
    hrepair.1 hvroot hrepair.2 htailRoot
  convert hresult using 1 <;> congr 1 <;> ring

end BrownianSharp
