import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! Tail-integral identities used in the weak-L1/strong-L2 interpolation
argument. These specialize Mathlib's general layer-cake formula. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperLpTailInterpolation

theorem integral_power_density {p a : ℝ} (hp : 0 < p) (_ha : 0 ≤ a) :
    (∫ t in (0 : ℝ)..a, p * t ^ (p-1)) = a ^ p := by
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith : -1 < p-1))]
  rw [show p-1+1 = p by ring, Real.zero_rpow (ne_of_gt hp)]
  field_simp [hp.ne']
  ring

/-- Exact p-th moment as a weighted strict-tail integral. -/
theorem lintegral_rpow_eq_tail {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f : α → ℝ} (hf : AEMeasurable f μ)
    (hfn : 0 ≤ᵐ[μ] f) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal (f x ^ p) ∂μ) =
      ∫⁻ t in Ioi (0 : ℝ), μ {x | t < f x} * ENNReal.ofReal (p * t ^ (p-1)) := by
  have hi : ∀ t > 0,
      IntervalIntegrable (fun u : ℝ => p * u ^ (p-1)) volume 0 t := by
    intro t ht
    exact (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < p-1)).const_mul p
  have hn : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), 0 ≤ p * t ^ (p-1) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg hp.le (Real.rpow_nonneg ht.le _)
  have heq := lintegral_comp_eq_lintegral_meas_lt_mul μ hfn hf hi hn
  rw [← heq]
  apply lintegral_congr_ae
  filter_upwards [hfn] with x hx
  rw [integral_power_density hp hx]

theorem integral_lower_kernel {p a : ℝ} (hp : 1 < p) (_ha : 0 ≤ a) :
    (∫ t in (0 : ℝ)..a, t ^ (p-2)) = a ^ (p-1) / (p-1) := by
  rw [integral_rpow (Or.inl (by linarith : -1 < p-2))]
  rw [show p-2+1 = p-1 by ring, Real.zero_rpow (by linarith : p-1 ≠ 0), sub_zero]

theorem integral_upper_kernel {p a : ℝ} (hp : p < 2) (ha : 0 < a) :
    (∫ t in Ioi a, t ^ (p-3)) = a ^ (p-2) / (2-p) := by
  rw [integral_Ioi_rpow_of_lt (by linarith : p-3 < -1) ha]
  rw [show p-3+1 = p-2 by ring]
  have hd : p-2 ≠ 0 := by linarith
  have he : 2-p ≠ 0 := by linarith
  field_simp [hd, he]
  ring

/-- The high-amplitude truncation kernel integrates to the p-th power. -/
theorem lintegral_lower_kernel {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) :
    (∫⁻ t in Ioo (0 : ℝ) a,
      ENNReal.ofReal a * ENNReal.ofReal (t ^ (p-2))) =
        ENNReal.ofReal (a ^ p / (p-1)) := by
  by_cases haz : a = 0
  · subst a
    simp [Real.zero_rpow (by linarith : p ≠ 0)]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hi : IntegrableOn (fun t : ℝ => t ^ (p-2)) (Ioo 0 a) :=
    ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < p-2)) :
      IntervalIntegrable (fun t : ℝ => t ^ (p-2)) volume 0 a).1.mono_set Ioo_subset_Ioc_self
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) a)] (fun t : ℝ => t ^ (p-2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hi hn]
  have hreal : (∫ t in Ioo (0 : ℝ) a, t ^ (p-2)) = a ^ (p-1) / (p-1) := by
    rw [restrict_Ioo_eq_restrict_Ioc,
      ← intervalIntegral.integral_of_le ha]
    exact integral_lower_kernel hp ha
  rw [hreal, ← ENNReal.ofReal_mul ha]
  congr 1
  rw [← mul_div_assoc]
  congr 1
  calc
    a * a ^ (p-1) = a ^ (1 : ℝ) * a ^ (p-1) := by rw [Real.rpow_one]
    _ = a ^ p := by
      rw [← Real.rpow_add hap]
      congr 1
      ring

/-- The low-amplitude truncation kernel has the complementary factor 2-p. -/
theorem lintegral_upper_kernel {p a : ℝ} (hp0 : 0 < p) (hp : p < 2) (ha : 0 ≤ a) :
    (∫⁻ t in Ioi a,
      ENNReal.ofReal (a ^ (2 : ℝ)) * ENNReal.ofReal (t ^ (p-3))) =
        ENNReal.ofReal (a ^ p / (2-p)) := by
  by_cases haz : a = 0
  · subst a
    simp [Real.zero_rpow hp0.ne']
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have hi : IntegrableOn (fun t : ℝ => t ^ (p-3)) (Ioi a) :=
    (integrableOn_Ioi_rpow_iff hap).2 (by linarith)
  have hn : 0 ≤ᵐ[volume.restrict (Ioi a)] (fun t : ℝ => t ^ (p-3)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hap.trans ht).le _
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← ofReal_integral_eq_lintegral_ofReal hi hn, integral_upper_kernel hp hap,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ha _)]
  congr 1
  rw [← mul_div_assoc, ← Real.rpow_add hap]
  congr 1
  congr 1
  ring

private theorem lintegral_high_cutoff_kernel {a r : ℝ} :
    (∫⁻ t in Ioi (0 : ℝ),
      (if t < a then ENNReal.ofReal a else 0) * ENNReal.ofReal (t ^ r)) =
      ∫⁻ t in Ioo (0 : ℝ) a, ENNReal.ofReal a * ENNReal.ofReal (t ^ r) := by
  have heq : (fun t : ℝ =>
      (if t < a then ENNReal.ofReal a else 0) * ENNReal.ofReal (t ^ r)) =
      (Iio a).indicator (fun t : ℝ => ENNReal.ofReal a * ENNReal.ofReal (t ^ r)) := by
    funext t
    by_cases ht : t < a <;> simp [ht]
  rw [heq, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio]
  rw [show Iio a ∩ Ioi (0 : ℝ) = Ioo 0 a by
    ext t
    simp [and_comm]]

/-- Tonelli evaluates the high-amplitude part of the interpolation bound. -/
theorem lintegral_high_truncation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {f : α → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p : ℝ} (hp : 1 < p) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x, if t < f x then ENNReal.ofReal (f x) else 0 ∂μ) *
        ENNReal.ofReal (t ^ (p-2))) =
      ∫⁻ x, ENNReal.ofReal (f x ^ p / (p-1)) ∂μ := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let J : ℝ → α → ℝ≥0∞ := fun t x =>
    (if t < f x then ENNReal.ofReal (f x) else 0) * ENNReal.ofReal (t ^ (p-2))
  have hJ : Measurable (Function.uncurry J) := by
    dsimp [J, Function.uncurry]
    apply Measurable.mul
    · exact Measurable.ite
        (measurableSet_lt measurable_fst (hf.comp measurable_snd))
        (by fun_prop) measurable_const
    · fun_prop
  calc
    _ = ∫⁻ t, ∫⁻ x, J t x ∂μ ∂ν := by
      apply lintegral_congr_ae
      filter_upwards with t
      exact (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ x, ∫⁻ t, J t x ∂ν ∂μ := lintegral_lintegral_swap hJ.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards with x
      dsimp [J,ν]
      rw [lintegral_high_cutoff_kernel]
      exact lintegral_lower_kernel hp (hfn x)

private theorem lintegral_low_cutoff_kernel {a r : ℝ} (ha : 0 ≤ a) :
    (∫⁻ t in Ioi (0 : ℝ),
      (if a ≤ t then ENNReal.ofReal (a ^ (2 : ℝ)) else 0) * ENNReal.ofReal (t ^ r)) =
      ∫⁻ t in Ioi a, ENNReal.ofReal (a ^ (2 : ℝ)) * ENNReal.ofReal (t ^ r) := by
  by_cases haz : a = 0
  · subst a
    simp
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
  have heq : (fun t : ℝ =>
      (if a ≤ t then ENNReal.ofReal (a ^ (2 : ℝ)) else 0) * ENNReal.ofReal (t ^ r)) =
      (Ici a).indicator (fun t : ℝ => ENNReal.ofReal (a ^ (2 : ℝ)) * ENNReal.ofReal (t ^ r)) := by
    funext t
    by_cases ht : a ≤ t <;> simp [ht]
  rw [heq, lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have hset : Ici a ∩ Ioi (0 : ℝ) = Ici a := by
    ext t
    simp only [mem_inter_iff, mem_Ici, mem_Ioi, and_iff_left_iff_imp]
    intro ht
    exact hap.trans_le ht
  rw [hset, ← restrict_Ioi_eq_restrict_Ici]

/-- Tonelli evaluates the low-amplitude part of the interpolation bound. -/
theorem lintegral_low_truncation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] {f : α → ℝ} (hf : Measurable f)
    (hfn : ∀ x, 0 ≤ f x) {p : ℝ} (hp0 : 0 < p) (hp2 : p < 2) :
    (∫⁻ t in Ioi (0 : ℝ),
      (∫⁻ x, if f x ≤ t then ENNReal.ofReal (f x ^ (2 : ℝ)) else 0 ∂μ) *
        ENNReal.ofReal (t ^ (p-3))) =
      ∫⁻ x, ENNReal.ofReal (f x ^ p / (2-p)) ∂μ := by
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let J : ℝ → α → ℝ≥0∞ := fun t x =>
    (if f x ≤ t then ENNReal.ofReal (f x ^ (2 : ℝ)) else 0) *
      ENNReal.ofReal (t ^ (p-3))
  have hJ : Measurable (Function.uncurry J) := by
    dsimp [J, Function.uncurry]
    apply Measurable.mul
    · exact Measurable.ite
        (measurableSet_le (hf.comp measurable_snd) measurable_fst)
        (by fun_prop) measurable_const
    · fun_prop
  calc
    _ = ∫⁻ t, ∫⁻ x, J t x ∂μ ∂ν := by
      apply lintegral_congr_ae
      filter_upwards with t
      exact (lintegral_mul_const' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ x, ∫⁻ t, J t x ∂ν ∂μ := lintegral_lintegral_swap hJ.aemeasurable
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards with x
      dsimp [J,ν]
      rw [lintegral_low_cutoff_kernel (hfn x)]
      exact lintegral_upper_kernel hp0 hp2 (hfn x)

/-- The tail calculation behind weak-L1/strong-L2 interpolation, with
its exact high/low source integrals and no integrability default. -/
theorem moment_le_of_weighted_truncated_tails
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : Measure β)
    {f : α → ℝ} {g : β → ℝ} (hf : Measurable f) (hg : AEMeasurable g ν)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    {p A B : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (htail : ∀ t > 0,
      ν {y | 2*t < g y} * ENNReal.ofReal (p*t^(p-1)) ≤
        ENNReal.ofReal A *
          ((∫⁻ x, if t < f x then ENNReal.ofReal (f x) else 0 ∂μ) *
            ENNReal.ofReal (t^(p-2))) +
        ENNReal.ofReal B *
          ((∫⁻ x, if f x ≤ t then ENNReal.ofReal (f x ^ (2 : ℝ)) else 0 ∂μ) *
            ENNReal.ofReal (t^(p-3)))) :
    (∫⁻ y, ENNReal.ofReal ((g y/2)^p) ∂ν) ≤
      ENNReal.ofReal A * (∫⁻ x, ENNReal.ofReal (f x^p/(p-1)) ∂μ) +
      ENNReal.ofReal B * (∫⁻ x, ENNReal.ofReal (f x^p/(2-p)) ∂μ) := by
  let H : ℝ → ℝ≥0∞ := fun t => ∫⁻ x,
    if t < f x then ENNReal.ofReal (f x) else 0 ∂μ
  let L : ℝ → ℝ≥0∞ := fun t => ∫⁻ x,
    if f x ≤ t then ENNReal.ofReal (f x ^ (2 : ℝ)) else 0 ∂μ
  have hH : Measurable H := by
    apply Measurable.lintegral_prod_right
    exact Measurable.ite (measurableSet_lt measurable_fst (hf.comp measurable_snd))
      (by fun_prop) measurable_const
  have hL : Measurable L := by
    apply Measurable.lintegral_prod_right
    exact Measurable.ite (measurableSet_le (hf.comp measurable_snd) measurable_fst)
      (by fun_prop) measurable_const
  have hHT : Measurable (fun t : ℝ =>
      ENNReal.ofReal A * (H t * ENNReal.ofReal (t^(p-2)))) := by fun_prop
  have hhalf : 0 ≤ᵐ[ν] (fun y => g y/2) :=
    Filter.Eventually.of_forall fun y => div_nonneg (hgn y) (by norm_num)
  rw [lintegral_rpow_eq_tail ν (hg.div_const 2) hhalf (by linarith : 0 < p)]
  have hevent (t : ℝ) : {y | t < g y/2} = {y | 2*t < g y} := by
    ext y
    simp only [mem_ofPred_eq]
    constructor <;> intro h <;> linarith
  simp_rw [hevent]
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal A * (H t * ENNReal.ofReal (t^(p-2))) +
        ENNReal.ofReal B * (L t * ENNReal.ofReal (t^(p-3))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact htail t ht
    _ = ENNReal.ofReal A * (∫⁻ t in Ioi (0 : ℝ), H t * ENNReal.ofReal (t^(p-2))) +
        ENNReal.ofReal B * (∫⁻ t in Ioi (0 : ℝ), L t * ENNReal.ofReal (t^(p-3))) := by
      rw [lintegral_add_left hHT,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = _ := by
      rw [lintegral_high_truncation μ hf hfn hp1,
        lintegral_low_truncation μ hf hfn (by linarith : 0 < p) hp2]

private theorem truncated_tail_weight {p C t : ℝ} (hp : 0 ≤ p)
    (hC : 0 ≤ C) (ht : 0 < t) (q : ℕ) :
    ENNReal.ofReal (C / t^q) * ENNReal.ofReal (p*t^(p-1)) =
      ENNReal.ofReal (p*C) * ENNReal.ofReal (t^(p-1-(q : ℝ))) := by
  have hreal : (C / t^q) * (p*t^(p-1)) = (p*C) * t^(p-1-(q : ℝ)) := by
    conv_rhs => rw [Real.rpow_sub ht, Real.rpow_natCast]
    ring
  rw [← ENNReal.ofReal_mul (div_nonneg hC (pow_pos ht q).le), hreal,
    ENNReal.ofReal_mul (mul_nonneg hp hC)]

/-- Weak-L1 and strong-L2 truncated tail bounds give an exact p-th moment
bound for every 1<p<2. Source integrals remain explicit and nonnegative. -/
theorem moment_le_of_truncated_tails
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : Measure β)
    {f : α → ℝ} {g : β → ℝ} (hf : Measurable f) (hg : AEMeasurable g ν)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    {p C₁ C₂ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (htail : ∀ t > 0, ν {y | 2*t < g y} ≤
      ENNReal.ofReal (C₁/t) *
        (∫⁻ x, if t < f x then ENNReal.ofReal (f x) else 0 ∂μ) +
      ENNReal.ofReal (C₂/t^2) *
        (∫⁻ x, if f x ≤ t then ENNReal.ofReal (f x ^ (2 : ℝ)) else 0 ∂μ)) :
    (∫⁻ y, ENNReal.ofReal ((g y/2)^p) ∂ν) ≤
      ENNReal.ofReal (p*C₁) * (∫⁻ x, ENNReal.ofReal (f x^p/(p-1)) ∂μ) +
      ENNReal.ofReal (p*C₂) * (∫⁻ x, ENNReal.ofReal (f x^p/(2-p)) ∂μ) := by
  apply moment_le_of_weighted_truncated_tails μ ν hf hg hfn hgn hp1 hp2
  intro t ht
  have h₁ : ENNReal.ofReal (C₁/t) * ENNReal.ofReal (p*t^(p-1)) =
      ENNReal.ofReal (p*C₁) * ENNReal.ofReal (t^(p-2)) := by
    simpa only [pow_one, Nat.cast_one, show p-1-1 = p-2 by ring] using
      truncated_tail_weight (by linarith : 0 ≤ p) hC₁ ht 1
  have h₂ : ENNReal.ofReal (C₂/t^2) * ENNReal.ofReal (p*t^(p-1)) =
      ENNReal.ofReal (p*C₂) * ENNReal.ofReal (t^(p-3)) := by
    simpa only [Nat.cast_ofNat, show p-1-2 = p-3 by ring] using
      truncated_tail_weight (by linarith : 0 ≤ p) hC₂ ht 2
  calc
    _ ≤ (ENNReal.ofReal (C₁/t) *
        (∫⁻ x, if t < f x then ENNReal.ofReal (f x) else 0 ∂μ) +
      ENNReal.ofReal (C₂/t^2) *
        (∫⁻ x, if f x ≤ t then ENNReal.ofReal (f x ^ (2 : ℝ)) else 0 ∂μ)) *
          ENNReal.ofReal (p*t^(p-1)) :=
      by
        gcongr
        exact htail t ht
    _ = (ENNReal.ofReal (C₁/t) * ENNReal.ofReal (p*t^(p-1))) *
        (∫⁻ x, if t < f x then ENNReal.ofReal (f x) else 0 ∂μ) +
      (ENNReal.ofReal (C₂/t^2) * ENNReal.ofReal (p*t^(p-1))) *
        (∫⁻ x, if f x ≤ t then ENNReal.ofReal (f x ^ (2 : ℝ)) else 0 ∂μ) := by ring
    _ = _ := by rw [h₁,h₂]; ring

private theorem lintegral_source_div {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hfn : ∀ x, 0 ≤ f x) (p b : ℝ) :
    (∫⁻ x, ENNReal.ofReal (f x^p/b) ∂μ) =
      (∫⁻ x, ENNReal.ofReal (f x^p) ∂μ) * ENNReal.ofReal b⁻¹ := by
  have heq : (fun x => ENNReal.ofReal (f x^p/b)) =
      (fun x => ENNReal.ofReal (f x^p) * ENNReal.ofReal b⁻¹) := by
    funext x
    rw [div_eq_mul_inv, ENNReal.ofReal_mul (Real.rpow_nonneg (hfn x) p)]
  rw [heq,lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]

/-- A single explicit source-moment constant for the interpolation estimate. -/
theorem half_moment_le_const_mul_source_of_truncated_tails
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [SFinite μ] (ν : Measure β)
    {f : α → ℝ} {g : β → ℝ} (hf : Measurable f) (hg : AEMeasurable g ν)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x)
    {p C₁ C₂ : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (htail : ∀ t > 0, ν {y | 2*t < g y} ≤
      ENNReal.ofReal (C₁/t) *
        (∫⁻ x, if t < f x then ENNReal.ofReal (f x) else 0 ∂μ) +
      ENNReal.ofReal (C₂/t^2) *
        (∫⁻ x, if f x ≤ t then ENNReal.ofReal (f x ^ (2 : ℝ)) else 0 ∂μ)) :
    (∫⁻ y, ENNReal.ofReal ((g y/2)^p) ∂ν) ≤
      ENNReal.ofReal (p*C₁/(p-1) + p*C₂/(2-p)) *
        (∫⁻ x, ENNReal.ofReal (f x^p) ∂μ) := by
  have hp : 0 ≤ p := by linarith
  have h₁ : 0 ≤ p*C₁ := mul_nonneg hp hC₁
  have h₂ : 0 ≤ p*C₂ := mul_nonneg hp hC₂
  have hd₁ : 0 ≤ (p-1)⁻¹ := inv_nonneg.mpr (by linarith)
  have hd₂ : 0 ≤ (2-p)⁻¹ := inv_nonneg.mpr (by linarith)
  apply (moment_le_of_truncated_tails μ ν hf hg hfn hgn hp1 hp2 hC₁ hC₂ htail).trans_eq
  rw [lintegral_source_div μ f hfn p (p-1), lintegral_source_div μ f hfn p (2-p)]
  rw [div_eq_mul_inv, div_eq_mul_inv,
    ENNReal.ofReal_add (mul_nonneg h₁ hd₁) (mul_nonneg h₂ hd₂),
    ENNReal.ofReal_mul h₁, ENNReal.ofReal_mul h₂]
  ring

end BrownianSharp.AlignmentPaperLpTailInterpolation
