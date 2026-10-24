import BrownianSharp.BorellApproximation

/-! Explicit probability regularizations for the compact-set limit in Borell's
heat argument. The exterior constants go to zero faster than the interior
constant goes to one, for every pair of positive interpolation weights. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace BrownianSharp
open Concentration

theorem standardGaussianCDF_mem_Ioo (s : ℝ) :
    standardGaussianCDF s ∈ Set.Ioo (0 : ℝ) 1 := by
  have hlo : 0 ≤ standardGaussianCDF (s-1) := ENNReal.toReal_nonneg
  have hhi : standardGaussianCDF (s+1) ≤ 1 := by
    unfold standardGaussianCDF
    calc
      _ ≤ (gaussianReal 0 1).real Set.univ := measureReal_mono (Set.subset_univ _)
      _ = 1 := by simp
  exact ⟨hlo.trans_lt (standardGaussianCDF_strictMono (by linarith)),
    (standardGaussianCDF_strictMono (by linarith)).trans_le hhi⟩

theorem standardGaussianQuantile_CDF (s : ℝ) :
    standardGaussianQuantile (standardGaussianCDF s) = s := by
  apply standardGaussianCDF_strictMono.injective
  exact standardGaussianCDF_standardGaussianQuantile
    (standardGaussianCDF_mem_Ioo s).1 (standardGaussianCDF_mem_Ioo s).2

/-- Linear scales that make both exterior baseline constraints tend to zero. -/
theorem exists_borell_regularization_slopes {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    ∃ c q : ℝ, 0 < c ∧ q < 0 ∧ -c ≤ q ∧ q ≤ 1 ∧
      a - b*c ≤ q ∧ b - a*c ≤ q := by
  let m := min a b
  have hm : 0 < m := lt_min ha hb
  let c := 2 / m
  let q := max (a-b*c) (b-a*c)
  have hc : 0 < c := div_pos (by norm_num) hm
  have ha1 : a < 1 := by linarith
  have hb1 : b < 1 := by linarith
  have hac : 2 ≤ a*c := by
    dsimp [c]
    rw [← mul_div_assoc, le_div_iff₀ hm]
    have hmle : m ≤ a := min_le_left _ _
    linarith
  have hbc : 2 ≤ b*c := by
    dsimp [c]
    rw [← mul_div_assoc, le_div_iff₀ hm]
    have hmle : m ≤ b := min_le_right _ _
    linarith
  have hq : q < 0 := max_lt (by linarith) (by linarith)
  refine ⟨c, q, hc, hq, ?_, hq.le.trans (by norm_num), le_max_left _ _, le_max_right _ _⟩
  apply le_trans (b := a-b*c) _ (le_max_left _ _)
  nlinarith

/-- Exact admissibility of the regularized Gaussian probability endpoints. -/
theorem borell_regularization_endpoints {a b c q t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hc : 0 < c) (hq : q < 0) (hcq : -c ≤ q) (hq1 : q ≤ 1)
    (hbase1 : a-b*c ≤ q) (hbase2 : b-a*c ≤ q) (ht : 0 ≤ t) :
    let δ := standardGaussianCDF (-c*t)
    let α := standardGaussianCDF t
    let β := standardGaussianCDF (q*t)
    0 < δ ∧ α < 1 ∧ δ ≤ α ∧ 0 < β ∧ β ≤ α ∧
      a*standardGaussianQuantile δ + b*standardGaussianQuantile α ≤
        standardGaussianQuantile β ∧
      a*standardGaussianQuantile α + b*standardGaussianQuantile δ ≤
        standardGaussianQuantile β := by
  dsimp only
  have hm := standardGaussianCDF_strictMono.monotone
  refine ⟨(standardGaussianCDF_mem_Ioo _).1, (standardGaussianCDF_mem_Ioo _).2,
    hm (by nlinarith), (standardGaussianCDF_mem_Ioo _).1,
    hm (by simpa using mul_le_mul_of_nonneg_right hq1 ht), ?_, ?_⟩
  · simp only [standardGaussianQuantile_CDF]
    have h := mul_le_mul_of_nonneg_right hbase2 ht
    nlinarith
  · simp only [standardGaussianQuantile_CDF]
    have h := mul_le_mul_of_nonneg_right hbase1 ht
    nlinarith

/-- Removing the explicit endpoint regularization uses continuity only at
interior probability masses. No continuity of the quantile at zero or one is
asserted. -/
theorem borell_regularization_limit {a b c q F G H : ℝ}
    (hc : 0 < c) (hq : q < 0)
    (hF : F ∈ Set.Ioo (0 : ℝ) 1) (hG : G ∈ Set.Ioo (0 : ℝ) 1)
    (hreg : ∀ t : ℝ, 0 ≤ t →
      standardGaussianCDF
        (a * standardGaussianQuantile
          (standardGaussianCDF (-c*t) +
            (standardGaussianCDF t - standardGaussianCDF (-c*t))*F) +
         b * standardGaussianQuantile
          (standardGaussianCDF (-c*t) +
            (standardGaussianCDF t - standardGaussianCDF (-c*t))*G)) ≤
      standardGaussianCDF (q*t) +
        (standardGaussianCDF t - standardGaussianCDF (q*t))*H) :
    standardGaussianCDF (a * standardGaussianQuantile F +
      b * standardGaussianQuantile G) ≤ H := by
  have hδ : Tendsto (fun t : ℝ => standardGaussianCDF (-c*t)) atTop (𝓝 0) :=
    tendsto_standardGaussianCDF_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  have hα := tendsto_standardGaussianCDF_atTop
  have hβ : Tendsto (fun t : ℝ => standardGaussianCDF (q*t)) atTop (𝓝 0) :=
    tendsto_standardGaussianCDF_atBot.comp (tendsto_id.const_mul_atTop_of_neg hq)
  have hFr : Tendsto (fun t : ℝ => standardGaussianCDF (-c*t) +
      (standardGaussianCDF t - standardGaussianCDF (-c*t))*F) atTop (𝓝 F) := by
    simpa using hδ.add ((hα.sub hδ).mul_const F)
  have hGr : Tendsto (fun t : ℝ => standardGaussianCDF (-c*t) +
      (standardGaussianCDF t - standardGaussianCDF (-c*t))*G) atTop (𝓝 G) := by
    simpa using hδ.add ((hα.sub hδ).mul_const G)
  have hHr : Tendsto (fun t : ℝ => standardGaussianCDF (q*t) +
      (standardGaussianCDF t - standardGaussianCDF (q*t))*H) atTop (𝓝 H) := by
    simpa using hβ.add ((hα.sub hβ).mul_const H)
  have hFq := (standardGaussianQuantile_continuousAt hF.1 hF.2).tendsto.comp hFr
  have hGq := (standardGaussianQuantile_continuousAt hG.1 hG.2).tendsto.comp hGr
  have hL := standardGaussianCDF_continuous.continuousAt.tendsto.comp
    ((hFq.const_mul a).add (hGq.const_mul b))
  exact le_of_tendsto_of_tendsto hL hHr (eventually_atTop.2 ⟨0, hreg⟩)

/-- The integral of an affine probability regularization has its literal
expected scalar form. -/
theorem integral_borell_regularization {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] (F : E → ℝ)
    (hF : Integrable F μ) (δ α : ℝ) :
    (∫ x, δ + (α-δ)*F x ∂μ) = δ + (α-δ)*(∫ x, F x ∂μ) := by
  rw [integral_add (integrable_const δ) (hF.const_mul (α-δ)), integral_const_mul]
  simp

/-- It suffices to pass the limit at the original set masses; no endpoint
continuity for the (possibly unit-mass) smooth plateaus is needed. -/
theorem borell_regularization_lower_mass_limit {a b c q A B F G H : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hq : q < 0)
    (hA : A ∈ Set.Ioo (0 : ℝ) 1) (hB : B ∈ Set.Ioo (0 : ℝ) 1)
    (hF : F ∈ Set.Icc (0 : ℝ) 1) (hG : G ∈ Set.Icc (0 : ℝ) 1)
    (hAF : A ≤ F) (hBG : B ≤ G)
    (hreg : ∀ t : ℝ, 0 ≤ t →
      standardGaussianCDF
        (a * standardGaussianQuantile
          (standardGaussianCDF (-c*t) +
            (standardGaussianCDF t - standardGaussianCDF (-c*t))*F) +
         b * standardGaussianQuantile
          (standardGaussianCDF (-c*t) +
            (standardGaussianCDF t - standardGaussianCDF (-c*t))*G)) ≤
      standardGaussianCDF (q*t) +
        (standardGaussianCDF t - standardGaussianCDF (q*t))*H) :
    standardGaussianCDF (a * standardGaussianQuantile A +
      b * standardGaussianQuantile B) ≤ H := by
  apply borell_regularization_limit hc hq hA hB
  intro t ht
  let δ := standardGaussianCDF (-c*t)
  let α := standardGaussianCDF t
  have hδ0 : 0 < δ := (standardGaussianCDF_mem_Ioo _).1
  have hα1 : α < 1 := (standardGaussianCDF_mem_Ioo _).2
  have hδα : δ ≤ α := standardGaussianCDF_strictMono.monotone (by nlinarith)
  have hAr := borell_regularization_mem_Icc ⟨hA.1.le, hA.2.le⟩ hδα
  have hBr := borell_regularization_mem_Icc ⟨hB.1.le, hB.2.le⟩ hδα
  have hFr := borell_regularization_mem_Icc hF hδα
  have hGr := borell_regularization_mem_Icc hG hδα
  have hAQ := gaussianQuantile_mono_Ioo (hδ0.trans_le hAr.1) (hAr.2.trans_lt hα1)
    (hδ0.trans_le hFr.1) (hFr.2.trans_lt hα1)
    (by nlinarith [mul_le_mul_of_nonneg_left hAF (sub_nonneg.mpr hδα)])
  have hBQ := gaussianQuantile_mono_Ioo (hδ0.trans_le hBr.1) (hBr.2.trans_lt hα1)
    (hδ0.trans_le hGr.1) (hGr.2.trans_lt hα1)
    (by nlinarith [mul_le_mul_of_nonneg_left hBG (sub_nonneg.mpr hδα)])
  exact (standardGaussianCDF_strictMono.monotone
    (add_le_add (mul_le_mul_of_nonneg_left hAQ ha.le)
      (mul_le_mul_of_nonneg_left hBQ hb.le))).trans (hreg t ht)

end BrownianSharp
