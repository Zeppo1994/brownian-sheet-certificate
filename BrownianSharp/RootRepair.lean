import BrownianSharp.RootVariance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The actual integral root-error and relative-variance bookkeeping. -/
open MeasureTheory ProbabilityTheory
namespace BrownianSharp

/-- The rare lower tail is used before taking the root. All quantities are
actual integrals or variances under the displayed probability measure. -/
theorem root_error_of_power_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → ℝ) (p C D : ℝ) (hp : 2 ≤ p) (hC : 0 < C) (hD : 0 < D)
    (hU : Measurable U) (hUpos : ∀ ω, 0 ≤ U ω)
    (hULp : MemLp U 2 μ) (hrootLp : MemLp (fun ω => U ω ^ (1 / p)) 2 μ)
    (hmean : ∫ ω, U ω ∂μ = 1)
    (hvar : ProbabilityTheory.variance U μ ≤ C * p ^ 2 / D)
    (hrare : μ.real {ω | U ω < 1 / 2} ≤ 1 / D) :
    (∫ ω, (U ω ^ (1 / p) - 1) ^ 2 ∂μ) ≤ (4 * C + 1) / D := by
  classical
  have hrootError := (hrootLp.sub (memLp_const (1 : ℝ))).integrable_sq
  have hpowerError := (hULp.sub (memLp_const (1 : ℝ))).integrable_sq
  have hset : MeasurableSet {ω | U ω < (1 / 2 : ℝ)} :=
    measurableSet_lt hU measurable_const
  have hind : Integrable (fun ω => if U ω < 1 / 2 then (1 : ℝ) else 0) μ := by
    exact (integrable_const (1 : ℝ)).indicator hset
  have hsplit := integral_pth_root_variance_split μ U p hp hUpos
    hrootError hpowerError hind
  have hvarInt : (∫ ω, (U ω - 1) ^ 2 ∂μ) = ProbabilityTheory.variance U μ := by
    rw [variance_eq_integral hU.aemeasurable, hmean]
  have hindInt : (∫ ω, (if U ω < 1 / 2 then (1 : ℝ) else 0) ∂μ) =
      μ.real {ω | U ω < 1 / 2} := integral_indicator_one hset
  rw [hvarInt, hindInt] at hsplit
  have hpne : p ≠ 0 := by linarith
  have hgood : 4 / p ^ 2 * ProbabilityTheory.variance U μ ≤ 4 * C / D := by
    calc
      _ ≤ 4 / p ^ 2 * (C * p ^ 2 / D) :=
        mul_le_mul_of_nonneg_left hvar (by positivity)
      _ = _ := by field_simp
  calc
    _ ≤ 4 / p ^ 2 * ProbabilityTheory.variance U μ +
        μ.real {ω | U ω < 1 / 2} := hsplit
    _ ≤ 4 * C / D + 1 / D := add_le_add hgood hrare
    _ = _ := by ring

/-- The root repair's output is the actual mean floor and relative variance
used by the second concentration application. -/
theorem root_repair_mean_and_relative_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (U : Ω → ℝ) (p C D : ℝ) (hp : 2 ≤ p) (hC : 0 < C) (hD : 0 < D)
    (hlarge : 4 * (4 * C + 1) ≤ D)
    (hU : Measurable U) (hUpos : ∀ ω, 0 ≤ U ω)
    (hULp : MemLp U 2 μ) (hrootLp : MemLp (fun ω => U ω ^ (1 / p)) 2 μ)
    (hmean : ∫ ω, U ω ∂μ = 1)
    (hvar : ProbabilityTheory.variance U μ ≤ C * p ^ 2 / D)
    (hrare : μ.real {ω | U ω < 1 / 2} ≤ 1 / D) :
    1 / 2 ≤ (∫ ω, U ω ^ (1 / p) ∂μ) ∧
      ProbabilityTheory.variance (fun ω => U ω ^ (1 / p)) μ /
        (∫ ω, U ω ^ (1 / p) ∂μ) ^ 2 ≤ 4 * (4 * C + 1) / D := by
  have herror := root_error_of_power_variance μ U p C D hp hC hD hU hUpos
    hULp hrootLp hmean hvar hrare
  have hsmall : (4 * C + 1) / D ≤ 1 / 4 := by
    apply (div_le_iff₀ hD).2
    nlinarith
  have hrootError := (hrootLp.sub (memLp_const (1 : ℝ))).integrable_sq
  have h := l2_error_to_relative_variance μ (fun ω => U ω ^ (1 / p))
    ((4 * C + 1) / D) (by positivity) hsmall
    (hrootLp.integrable (by norm_num)) hrootError herror
  simpa [mul_div_assoc] using h

end BrownianSharp
