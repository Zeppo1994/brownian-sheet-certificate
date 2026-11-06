import BrownianSharp.GaussianGridStatistics
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance

/-!
Remark 2.7: sharpness in order of the `σ⁻²` dependence of the exponent in (2.30).
For `f_s(g) = s g_i - s²/2` and `G` the product standard Gaussian vector, we prove
`E exp f_s(G) = 1`, `Var exp f_s(G) = exp(s²) - 1 ∼ s²` and, for every fixed `t > 1`,
`-log P{f_s(G) ≤ -t} ∼ t²/(2s²) ∼ t²/(2σ_s²)` as `s ↓ 0`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open BrownianSharp

namespace BrownianSharp.AlignmentPaperConvexTailSharpness

variable {κ : Type*} [Fintype κ]

/-- The function `f_s(g) = s g_i - s²/2` of Remark 2.7. -/
def f (s : ℝ) (i : κ) (x : κ → ℝ) : ℝ := s * x i - s ^ 2 / 2

private lemma hasLaw (i : κ) :
    HasLaw (fun x : κ → ℝ => x i) (gaussianReal 0 1) (productStandardGaussian κ) :=
  ⟨(measurable_pi_apply i).aemeasurable, productStandardGaussian_coordinate_law i⟩

private lemma integrable_exp (i : κ) (a : ℝ) :
    Integrable (fun x : κ → ℝ => Real.exp (a * x i)) (productStandardGaussian κ) :=
  (hasLaw i).integrable_comp (f := fun y : ℝ => Real.exp (a * y))
    (integrable_exp_mul_gaussianReal a)

private lemma integral_exp (i : κ) (a : ℝ) :
    ∫ x, Real.exp (a * x i) ∂productStandardGaussian κ = Real.exp (a ^ 2 / 2) := by
  have := mgf_gaussianReal (hasLaw i) a
  simpa [mgf] using this

omit [Fintype κ] in
private lemma exp_f (s : ℝ) (i : κ) (a : ℝ) (x : κ → ℝ) :
    Real.exp (a * f s i x) = Real.exp (-(a * s ^ 2 / 2)) * Real.exp ((a * s) * x i) := by
  rw [← Real.exp_add]; congr 1; simp only [f]; ring

/-- Remark 2.7: `E exp(f_s(G)) = 1`. -/
theorem integral_exp_f (s : ℝ) (i : κ) :
    ∫ x, Real.exp (f s i x) ∂productStandardGaussian κ = 1 := by
  have := fun x => by simpa using exp_f s i 1 x
  simp_rw [this, integral_const_mul, integral_exp, ← Real.exp_add]
  simp

/-- Remark 2.7: `Var exp(f_s(G)) = exp(s²) - 1`. -/
theorem variance_exp_f (s : ℝ) (i : κ) :
    variance (fun x => Real.exp (f s i x)) (productStandardGaussian κ) = Real.exp (s ^ 2) - 1 := by
  have h2 : ∀ x, Real.exp (f s i x) ^ 2 = Real.exp (-(s ^ 2)) * Real.exp ((2 * s) * x i) := by
    intro x
    rw [← Real.exp_nat_mul]
    simpa using exp_f s i 2 x
  have hint : Integrable (fun x => Real.exp (f s i x) ^ 2) (productStandardGaussian κ) := by
    simp_rw [h2]; exact (integrable_exp i _).const_mul _
  have hmeas : Measurable (fun x : κ → ℝ => Real.exp (f s i x)) := by
    unfold f; fun_prop
  rw [variance_eq_sub ((memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hint)]
  simp only [Pi.pow_apply]
  simp_rw [h2, integral_const_mul, integral_exp, ← Real.exp_add]
  rw [show ∫ x, Real.exp (f s i x) ∂productStandardGaussian κ = 1 from integral_exp_f s i]
  rw [show -s ^ 2 + (2 * s) ^ 2 / 2 = s ^ 2 by ring]; ring

/-- Remark 2.7: `σ_s² = exp(s²) - 1 ∼ s²` as `s ↓ 0`. -/
theorem tendsto_variance_div :
    Tendsto (fun s : ℝ => (Real.exp (s ^ 2) - 1) / s ^ 2) (𝓝[>] 0) (𝓝 1) := by
  have h := (Real.hasDerivAt_exp 0).tendsto_slope_zero_right
  have hsq : Tendsto (fun s : ℝ => s ^ 2) (𝓝[>] 0) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨((continuous_pow 2).tendsto' 0 0 (by simp)).mono_left
      nhdsWithin_le_nhds, eventually_nhdsWithin_of_forall fun s hs => by
        simpa using pow_pos (show (0:ℝ) < s from hs) 2⟩
  simpa [div_eq_inv_mul, Function.comp_def] using h.comp hsq

/-- Gaussian tail bounds: for `x ≥ 0` and `p = P{G_i ≤ -x}`,
`x²/2 ≤ -log p ≤ (x+1)²/2 + log √(2π)`. -/
private lemma tail_bounds (i : κ) {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 / 2 ≤ -Real.log ((productStandardGaussian κ).real {y | y i ≤ -x}) ∧
    -Real.log ((productStandardGaussian κ).real {y | y i ≤ -x}) ≤
      (x + 1) ^ 2 / 2 + Real.log (√(2 * Real.pi)) := by
  set μ := productStandardGaussian κ
  have hreal : μ.real {y | y i ≤ -x} = (gaussianReal 0 1).real (Set.Iic (-x)) := by
    rw [measureReal_def, measureReal_def, ← productStandardGaussian_coordinate_law (κ := κ) i,
      Measure.map_apply (measurable_pi_apply i) measurableSet_Iic]; rfl
  have hup : μ.real {y | y i ≤ -x} ≤ Real.exp (-(x ^ 2 / 2)) := by
    have := measure_le_le_exp_mul_mgf (μ := μ) (X := fun y : κ → ℝ => y i) (-x) (t := -x)
      (by linarith) (by simpa using integrable_exp i (-x))
    have hm : mgf (fun y : κ → ℝ => y i) μ (-x) = Real.exp (x ^ 2 / 2) := by
      simpa [mgf] using integral_exp i (-x)
    rw [hm, ← Real.exp_add] at this
    refine this.trans (le_of_eq (congrArg _ (by ring)))
  have hlow : Real.exp (-((x + 1) ^ 2 / 2)) / √(2 * Real.pi) ≤ μ.real {y | y i ≤ -x} := by
    rw [hreal, measureReal_def, ← ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _),
      gaussianReal_apply 0 one_ne_zero]
    calc ENNReal.ofReal (Real.exp (-((x + 1) ^ 2 / 2)) / √(2 * Real.pi))
        = ∫⁻ _ in Set.Icc (-x - 1) (-x),
            ENNReal.ofReal (Real.exp (-((x + 1) ^ 2 / 2)) / √(2 * Real.pi)) := by
          rw [setLIntegral_const, Real.volume_Icc]; simp
      _ ≤ ∫⁻ y in Set.Icc (-x - 1) (-x), gaussianPDF 0 1 y := by
          refine setLIntegral_mono' measurableSet_Icc fun y hy => ENNReal.ofReal_le_ofReal ?_
          simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
          rw [div_eq_inv_mul]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
          nlinarith [hy.1, hy.2]
      _ ≤ _ := lintegral_mono_set (Set.Icc_subset_Iic_self)
  have hpos : 0 < μ.real {y | y i ≤ -x} := lt_of_lt_of_le (by positivity) hlow
  refine ⟨?_, ?_⟩
  · have := Real.log_le_log hpos hup
    rw [Real.log_exp] at this; linarith
  · have := Real.log_le_log (by positivity) hlow
    rw [Real.log_div (Real.exp_pos _).ne' (by positivity), Real.log_exp] at this; linarith

omit [Fintype κ] in
private lemma set_eq (i : κ) {s : ℝ} (hs : 0 < s) (t : ℝ) :
    {x : κ → ℝ | f s i x ≤ -t} = {x | x i ≤ -((t - s ^ 2 / 2) / s)} := by
  ext x
  simp only [Set.mem_ofPred_eq, f]
  rw [show -((t - s ^ 2 / 2) / s) = (s ^ 2 / 2 - t) / s by ring, le_div_iff₀ hs]
  constructor <;> intro h <;> linarith

/-- Remark 2.7, (2.35): for `t > 1`, `-log P{f_s(G) ≤ -t} ∼ t²/(2s²)` as `s ↓ 0`. -/
theorem tendsto_neg_log_tail (i : κ) {t : ℝ} (ht : 1 < t) :
    Tendsto (fun s : ℝ => -Real.log ((productStandardGaussian κ).real {x | f s i x ≤ -t}) /
      (t ^ 2 / (2 * s ^ 2))) (𝓝[>] 0) (𝓝 1) := by
  have ht0 : 0 < t := by linarith
  set c := Real.log (√(2 * Real.pi))
  have hlo : Tendsto (fun s : ℝ => ((t - s ^ 2 / 2) / t) ^ 2) (𝓝[>] 0) (𝓝 1) := by
    have : Continuous fun s : ℝ => ((t - s ^ 2 / 2) / t) ^ 2 := by fun_prop
    simpa [ht0.ne'] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hhi : Tendsto (fun s : ℝ => ((t - s ^ 2 / 2 + s) ^ 2 + 2 * c * s ^ 2) / t ^ 2)
      (𝓝[>] 0) (𝓝 1) := by
    have : Continuous fun s : ℝ => ((t - s ^ 2 / 2 + s) ^ 2 + 2 * c * s ^ 2) / t ^ 2 := by
      fun_prop
    simpa [ht0.ne'] using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  all_goals filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with s hs
  all_goals
    obtain ⟨hs0, hs1⟩ := hs
    have hx : 0 ≤ (t - s ^ 2 / 2) / s := div_nonneg (by nlinarith) hs0.le
    have hb := tail_bounds i hx
    rw [← set_eq i hs0] at hb
    have hD : 0 < t ^ 2 / (2 * s ^ 2) := by positivity
  · rw [le_div_iff₀ hD]
    refine le_trans (le_of_eq ?_) hb.1
    field_simp
  · rw [div_le_iff₀ hD]
    refine hb.2.trans (le_of_eq ?_)
    field_simp
    ring

/-- Remark 2.7, (2.35): for `t > 1`, `-log P{f_s(G) ≤ -t} ∼ t²/(2σ_s²)` as `s ↓ 0`,
where `σ_s² = Var exp(f_s(G)) = exp(s²) - 1`. -/
theorem tendsto_neg_log_tail_variance (i : κ) {t : ℝ} (ht : 1 < t) :
    Tendsto (fun s : ℝ => -Real.log ((productStandardGaussian κ).real {x | f s i x ≤ -t}) /
      (t ^ 2 / (2 * variance (fun x => Real.exp (f s i x)) (productStandardGaussian κ))))
      (𝓝[>] 0) (𝓝 1) := by
  have := (tendsto_neg_log_tail i ht).mul tendsto_variance_div
  rw [mul_one] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs : 0 < s := hs
  rw [variance_exp_f]
  have : t ^ 2 ≠ 0 := by positivity
  by_cases h : Real.exp (s ^ 2) - 1 = 0
  · simp [h]
  · field_simp

end BrownianSharp.AlignmentPaperConvexTailSharpness
