import BrownianSharp.RootVariance
import BrownianSharp.TailBudget

/-!
Numerical and measure-theoretic assembly of the two concentration steps.
`VarianceSensitiveLowerTail` is an explicit analytic input, not an axiom or a
proved claim about every Gaussian convex observable. The manuscript's PV
lemma must discharge it for each actual statistic.
-/
open MeasureTheory ProbabilityTheory

namespace BrownianSharp

/-- The relaxed PV conclusion, displayed as a property to be proved for the
actual convex statistic under its actual law. -/
def VarianceSensitiveLowerTail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (c : ℝ) : Prop :=
  ∀ t : ℝ, 2 ≤ t → μ.real {ω | X ω ≤ (∫ ω, X ω ∂μ) -
    t * Real.sqrt (ProbabilityTheory.variance X μ)} ≤ Real.exp (-c * t ^ 2)

/-- A relative-variance bound makes the second PV application a true
exponential bound in reciprocal relative variance. -/
theorem half_mean_tail_of_relative_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (c R : ℝ) (hc : 0 ≤ c) (hR : 0 < R) (hRsmall : R ≤ 1 / 16)
    (hmean : 0 < ∫ ω, X ω ∂μ)
    (hv : 0 < ProbabilityTheory.variance X μ)
    (hrel : ProbabilityTheory.variance X μ / (∫ ω, X ω ∂μ) ^ 2 ≤ R)
    (htail : VarianceSensitiveLowerTail μ X c) :
    μ.real {ω | X ω ≤ (∫ ω, X ω ∂μ) / 2} ≤ Real.exp (-c / (4 * R)) := by
  let m := ∫ ω, X ω ∂μ
  let v := ProbabilityTheory.variance X μ
  let t := m / (2 * Real.sqrt v)
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have htpos : 0 < t := div_pos hmean (by positivity)
  have hvbound : v ≤ R * m ^ 2 := (div_le_iff₀ (sq_pos_of_pos hmean)).mp hrel
  have ht2 : t ^ 2 = m ^ 2 / (4 * v) := by
    dsimp [t]
    rw [div_pow, mul_pow, Real.sq_sqrt hv.le]
    norm_num
    rfl
  have hrecip : 1 / (4 * R) ≤ t ^ 2 := by
    rw [ht2]
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * R) (by positivity : 0 < 4 * v)).2
    nlinarith
  have hfour : 4 ≤ 1 / (4 * R) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * R)).2
    nlinarith
  have ht : 2 ≤ t := by nlinarith
  have hthreshold : m - t * Real.sqrt v = m / 2 := by
    dsimp [t]
    field_simp [hs.ne']
    <;> ring
  have h := htail t ht
  change μ.real {ω | X ω ≤ m - t * Real.sqrt v} ≤ _ at h
  rw [hthreshold] at h
  refine h.trans (Real.exp_le_exp.mpr ?_)
  have hmul := mul_le_mul_of_nonneg_left hrecip hc
  calc
    -c * t ^ 2 ≤ -(c * (1 / (4 * R))) := by simpa only [neg_mul] using neg_le_neg hmul
    _ = -c / (4 * R) := by ring

/-- The second concentration step gives exp(-bD) once the repaired relative
variance is K/D and D is large enough. -/
theorem repaired_root_confinement
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ)
    (c K D : ℝ) (hc : 0 ≤ c) (hK : 0 < K) (hD : 0 < D)
    (hlarge : 16 * K ≤ D) (hmean : 1 / 2 ≤ ∫ ω, Y ω ∂μ)
    (hv : 0 < ProbabilityTheory.variance Y μ)
    (hrel : ProbabilityTheory.variance Y μ / (∫ ω, Y ω ∂μ) ^ 2 ≤ K / D)
    (htail : VarianceSensitiveLowerTail μ Y c) :
    μ.real {ω | Y ω ≤ 1 / 4} ≤ Real.exp (-(c / (4 * K)) * D) := by
  have hRsmall : K / D ≤ 1 / 16 := by
    apply (div_le_iff₀ hD).2
    nlinarith
  have hhalf := half_mean_tail_of_relative_variance μ Y c (K / D) hc
    (div_pos hK hD) hRsmall (by linarith) hv hrel htail
  have hsub : {ω | Y ω ≤ 1 / 4} ⊆ {ω | Y ω ≤ (∫ ω, Y ω ∂μ) / 2} := by
    intro ω hω
    change Y ω ≤ 1 / 4 at hω
    change Y ω ≤ (∫ ω, Y ω ∂μ) / 2
    linarith
  have hmono : μ.real {ω | Y ω ≤ 1 / 4} ≤
      μ.real {ω | Y ω ≤ (∫ ω, Y ω ∂μ) / 2} := by
    exact MeasureTheory.measureReal_mono hsub
  refine hmono.trans (hhalf.trans_eq ?_)
  congr 1
  field_simp

end BrownianSharp
