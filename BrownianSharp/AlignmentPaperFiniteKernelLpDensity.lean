import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Tactic

/-! Extension of finite continuous-kernel estimates from continuous inputs to
actual Lp classes. Kernel norms enter only convergence of approximants; they
will not enter the final uniform operator constant. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace BrownianSharp.AlignmentPaperFiniteKernelLpDensity
variable {α : Type*} [MetricSpace α] [CompactSpace α]
  [MeasurableSpace α] [BorelSpace α]
  {μ : Measure α} [IsProbabilityMeasure μ]

def applyKernel (K : C(α × α, ℂ)) (f : α → ℂ) (x : α) : ℂ :=
  ∫ y, K (x,y)*f y ∂μ

theorem applyKernel_integrable (K : C(α × α, ℂ)) {f : α → ℂ}
    (hf : Integrable f μ) (x : α) : Integrable (fun y => K (x,y)*f y) μ := by
  have hK : AEStronglyMeasurable (fun y => K (x,y)) μ := by fun_prop
  have hb : ∀ᵐ y ∂μ, ‖K (x,y)‖ ≤ ‖K‖ :=
    ae_of_all _ (fun y => ContinuousMap.norm_coe_le_norm K (x,y))
  exact hf.bdd_mul hK hb

theorem applyKernel_norm_le_integral (K : C(α × α, ℂ)) {f : α → ℂ}
    (hf : Integrable f μ) (x : α) :
    ‖applyKernel (μ := μ) K f x‖ ≤ ‖K‖ * ∫ y, ‖f y‖ ∂μ := by
  apply (norm_integral_le_integral_norm _).trans
  rw [← integral_const_mul]
  apply integral_mono (applyKernel_integrable K hf x).norm (hf.norm.const_mul ‖K‖)
  intro y
  dsimp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm K (x,y)) (norm_nonneg _)

theorem applyKernel_congr_ae (K : C(α × α, ℂ)) {f g : α → ℂ}
    (h : f =ᵐ[μ] g) (x : α) :
    applyKernel (μ := μ) K f x = applyKernel (μ := μ) K g x := by
  apply integral_congr_ae
  filter_upwards [h] with y hy
  rw [hy]

theorem applyKernel_continuous (K : C(α × α, ℂ)) {f : α → ℂ}
    (hf : Integrable f μ) : Continuous (applyKernel (μ := μ) K f) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hm : ∀ᶠ t : α in 𝓝 x,
      AEStronglyMeasurable (fun y => K (t,y)*f y) μ :=
    Eventually.of_forall (fun t => (applyKernel_integrable K hf t).aestronglyMeasurable)
  have hb : ∀ᶠ t : α in 𝓝 x,
      ∀ᵐ y ∂μ, ‖K (t,y)*f y‖ ≤ ‖K‖*‖f y‖ := by
    apply Eventually.of_forall
    intro t
    exact ae_of_all _ (fun y => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ContinuousMap.norm_coe_le_norm K (t,y)) (norm_nonneg _))
  have ht : ∀ᵐ y ∂μ, Tendsto (fun t => K (t,y)*f y) (𝓝 x) (𝓝 (K (x,y)*f y)) := by
    exact ae_of_all _ (fun y =>
      (show Continuous (fun t : α => K (t,y)*f y) by fun_prop).continuousAt.tendsto)
  exact tendsto_integral_filter_of_dominated_convergence (fun y => ‖K‖*‖f y‖)
    hm hb (hf.norm.const_mul ‖K‖) ht

theorem integral_norm_Lp_le_norm {p : ℝ} (hp : 1 ≤ p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    (f : Lp ℂ (ENNReal.ofReal p) μ) : (∫ y, ‖f y‖ ∂μ) ≤ ‖f‖ := by
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hf := (Lp.memLp f).integrable hpE
  have hh : ENNReal.ofReal (∫ y, ‖f y‖ ∂μ) ≤ eLpNorm (f : α → ℂ) (ENNReal.ofReal p) μ := by
    rw [ofReal_integral_norm_eq_lintegral_enorm hf]
    exact lintegral_enorm_le_eLpNorm_one.trans (eLpNorm_le_eLpNorm_of_exponent_le hpE)
  have hr := ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top hh
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (fun y => norm_nonneg (f y))),
    Lp.norm_def] using hr

theorem applyKernel_Lp_norm_le (K : C(α × α, ℂ)) {p : ℝ} (hp : 1 ≤ p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    (f : Lp ℂ (ENNReal.ofReal p) μ) (x : α) :
    ‖applyKernel (μ := μ) K f x‖ ≤ ‖K‖*‖f‖ := by
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  exact (applyKernel_norm_le_integral K ((Lp.memLp f).integrable hpE) x).trans
    (mul_le_mul_of_nonneg_left (integral_norm_Lp_le_norm hp f) (norm_nonneg K))

theorem applyKernel_Lp_sub (K : C(α × α, ℂ)) {p : ℝ} (hp : 1 ≤ p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    (g f : Lp ℂ (ENNReal.ofReal p) μ) (x : α) :
    applyKernel (μ := μ) K g x - applyKernel (μ := μ) K f x =
      applyKernel (μ := μ) K ((g-f : Lp ℂ (ENNReal.ofReal p) μ) : α → ℂ) x := by
  have hpE : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  unfold applyKernel
  rw [← integral_sub (applyKernel_integrable K ((Lp.memLp g).integrable hpE) x)
    (applyKernel_integrable K ((Lp.memLp f).integrable hpE) x)]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub g f] with y hy
  rw [hy]
  simp only [Pi.sub_apply]
  ring

theorem applyKernel_Lp_sub_norm_le (K : C(α × α, ℂ)) {p : ℝ} (hp : 1 ≤ p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    (g f : Lp ℂ (ENNReal.ofReal p) μ) (x : α) :
    ‖applyKernel (μ := μ) K g x - applyKernel (μ := μ) K f x‖ ≤ ‖K‖*‖g-f‖ := by
  rw [applyKernel_Lp_sub K hp g f x]
  exact applyKernel_Lp_norm_le K hp (g-f) x

theorem applyKernel_toLp (K : C(α × α, ℂ)) {p : ℝ}
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    (g : C(α,ℂ)) (x : α) :
    applyKernel (μ := μ) K g x =
      applyKernel (μ := μ) K ((ContinuousMap.toLp (ENNReal.ofReal p) μ ℂ) g) x := by
  exact applyKernel_congr_ae K
    (ContinuousMap.coeFn_toLp (p := ENNReal.ofReal p) (𝕜 := ℂ) (μ := μ) g).symm x

variable {p : ℝ}

theorem lpMoment_eq_norm_rpow (hp0 : 0 < p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    (f : Lp ℂ (ENNReal.ofReal p) μ) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ) =
      ENNReal.ofReal (‖f‖^p) := by
  have hpE0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hpET : ENNReal.ofReal p ≠ ∞ := ENNReal.ofReal_ne_top
  have hraw : (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
    rw [eLpNorm_eq_eLpNorm' hpE0 hpET (Lp.memLp f).aestronglyMeasurable]
    simpa [ENNReal.toReal_ofReal hp0.le] using
      (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := f) (q := p) hp0)
  rw [show (fun x => ENNReal.ofReal (‖f x‖^p)) =
      fun x => ‖f x‖ₑ ^ p by
        funext x
        rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hp0.le,
          ofReal_norm]
      ]
  rw [hraw, Lp.norm_def]
  rw [← ENNReal.ofReal_rpow_of_nonneg (ENNReal.toReal_nonneg) hp0.le]
  rw [ENNReal.ofReal_toReal (Lp.memLp f).eLpNorm_ne_top]

/-- A finite-family moment estimate for continuous-kernel operators extends
from continuous inputs to every actual Lp class. Kernel norms enter only in
showing convergence of the approximating outputs. -/
theorem finiteKernel_moment_le_of_continuous
    {ι : Type*} [Fintype ι]
    {K : ι → C(α × α, ℂ)} {p : ℝ} (hp0 : 0 < p) (hp1 : 1 ≤ p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    {Γ : ℝ≥0∞} (hΓ : Γ ≠ ∞)
    (hcont : ∀ g : C(α,ℂ),
      (∫⁻ x, ENNReal.ofReal
        ((∑ i : ι, ‖applyKernel (μ := μ) (K i) g x‖^2)^(p/2)) ∂μ) ≤
      Γ * ∫⁻ x, ENNReal.ofReal (‖g x‖^p) ∂μ)
    (f : Lp ℂ (ENNReal.ofReal p) μ) :
    (∫⁻ x, ENNReal.ofReal
      ((∑ i : ι, ‖applyKernel (μ := μ) (K i) (f : α → ℂ) x‖^2)^(p/2)) ∂μ) ≤
      Γ * ∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ := by
  classical
  let T : C(α,ℂ) →L[ℂ] Lp ℂ (ENNReal.ofReal p) μ :=
    ContinuousMap.toLp (ENNReal.ofReal p) μ ℂ
  have hDense : DenseRange T := by
    exact ContinuousMap.toLp_denseRange (E := ℂ) (p := ENNReal.ofReal p)
      (μ := μ) (𝕜 := ℂ) ENNReal.ofReal_ne_top
  have happrox (n : ℕ) : ∃ g : C(α,ℂ),
      ‖T g - f‖ < 1 / ((n:ℝ)+1) := by
    have hcl : f ∈ closure (Set.range T) := hDense f
    rcases Metric.mem_closure_iff.1 hcl _ (by positivity : (0:ℝ) < 1/((n:ℝ)+1)) with
      ⟨u, hu, hdist⟩
    rcases hu with ⟨g,hg⟩
    refine ⟨g, ?_⟩
    rw [← hg] at hdist
    simpa [dist_eq_norm, norm_sub_rev] using hdist
  let g : ℕ → C(α,ℂ) := fun n => Classical.choose (happrox n)
  have hdist (n : ℕ) : ‖T (g n)-f‖ < 1/((n:ℝ)+1) :=
    Classical.choose_spec (happrox n)
  let u : ℕ → Lp ℂ (ENNReal.ofReal p) μ := fun n => T (g n)
  have hu : Tendsto u atTop (𝓝 f) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall : ∀ᶠ n : ℕ in atTop, (1/((n:ℝ)+1)) < ε := by
      have hlim := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      exact hlim.eventually (Iio_mem_nhds hε)
    filter_upwards [hsmall] with n hn
    have hn' := hdist n
    simpa [dist_eq_norm, norm_sub_rev] using lt_trans hn' hn

  have hsrc_eq (n : ℕ) :
      (∫⁻ x, ENNReal.ofReal (‖g n x‖^p) ∂μ) =
        ENNReal.ofReal (‖u n‖^p) := by
    rw [← lpMoment_eq_norm_rpow hp0 (u n)]
    apply lintegral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp
      (p := ENNReal.ofReal p) (𝕜 := ℂ) (μ := μ) (g n)] with x hx
    rw [hx]
  have hsrc_f :
      (∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ) = ENNReal.ofReal (‖f‖^p) :=
    lpMoment_eq_norm_rpow hp0 f
  have hsrc_tendsto : Tendsto
      (fun n => ∫⁻ x, ENNReal.ofReal (‖g n x‖^p) ∂μ) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ)) := by
    rw [hsrc_f]
    have hnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 ‖f‖) :=
      continuous_norm.continuousAt.tendsto.comp hu
    have hrpow : Tendsto (fun n => ‖u n‖^p) atTop (𝓝 (‖f‖^p)) :=
      (Real.continuousAt_rpow_const _ _ (Or.inr (le_of_lt hp0))).tendsto.comp hnorm
    have hof : Tendsto (fun n => ENNReal.ofReal (‖u n‖^p)) atTop
        (𝓝 (ENNReal.ofReal (‖f‖^p))) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hrpow
    exact hof.congr' (Filter.Eventually.of_forall (fun n => (hsrc_eq n).symm))

  let V : (ι → ℂ) → ℝ := fun v => (∑ i, ‖v i‖^2)^(p/2)
  have hV : Continuous V := by
    dsimp [V]
    exact (Real.continuous_rpow_const (by linarith : 0 ≤ p/2)).comp (by fun_prop)
  let out : (ι → ℂ) → ℝ≥0∞ := fun v => ENNReal.ofReal (V v)
  have hout : Continuous out := ENNReal.continuous_ofReal.comp hV
  let Aseq : ℕ → α → ℝ≥0∞ := fun n x =>
    out (fun i => applyKernel (μ := μ) (K i) (g n) x)
  let A : α → ℝ≥0∞ := fun x =>
    out (fun i => applyKernel (μ := μ) (K i) (f : α → ℂ) x)
  have hcoord (i : ι) (x : α) :
      Tendsto (fun n => applyKernel (μ := μ) (K i) (g n) x) atTop
        (𝓝 (applyKernel (μ := μ) (K i) (f : α → ℂ) x)) := by
    have hnorm : Tendsto (fun n => ‖u n-f‖) atTop (𝓝 0) := by
      have hdistT : Tendsto (fun n => dist (u n) f) atTop (𝓝 0) := by
        simpa using hu.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f))
      simpa [dist_eq_norm, norm_sub_rev] using hdistT
    have hprod : Tendsto (fun n => ‖K i‖ * ‖u n-f‖) atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hnorm
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hsmall := hprod.eventually (Iio_mem_nhds hε)
    filter_upwards [hsmall] with n hn
    have hEq : applyKernel (μ := μ) (K i) (g n) x =
        applyKernel (μ := μ) (K i) (u n : α → ℂ) x := by
      exact applyKernel_toLp (μ := μ) (K i) (g n) x
    have hbound := applyKernel_Lp_sub_norm_le (μ := μ) (K i) hp1 (u n) f x
    rw [hEq]
    simpa [dist_eq_norm] using lt_of_le_of_lt hbound hn
  have hApoint (x : α) : Tendsto (fun n => Aseq n x) atTop (𝓝 (A x)) := by
    have hv : Tendsto (fun n i => applyKernel (μ := μ) (K i) (g n) x)
        atTop (𝓝 (fun i => applyKernel (μ := μ) (K i) (f : α → ℂ) x)) :=
      tendsto_pi_nhds.mpr (fun i => hcoord i x)
    exact hout.continuousAt.tendsto.comp hv
  have hAmeas (n : ℕ) : Measurable (Aseq n) := by
    have hf : Integrable (g n : α → ℂ) μ :=
      (g n).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hc (i : ι) : Continuous (applyKernel (μ := μ) (K i) (g n)) :=
      applyKernel_continuous (K i) hf
    change Measurable (fun x => ENNReal.ofReal
      ((∑ i, ‖applyKernel (μ := μ) (K i) (g n) x‖^2)^(p/2)))
    exact ENNReal.continuous_ofReal.measurable.comp
      ((Real.continuous_rpow_const (by linarith : 0 ≤ p/2)).measurable.comp (by fun_prop))
  have hAmeas' : Measurable A := by
    have hf : Integrable (f : α → ℂ) μ := by
      have hpE : (1:ℝ≥0∞) ≤ ENNReal.ofReal p := Fact.out
      exact (Lp.memLp f).integrable hpE
    have hc (i : ι) : Continuous (applyKernel (μ := μ) (K i) (f : α → ℂ)) :=
      applyKernel_continuous (K i) hf
    change Measurable (fun x => ENNReal.ofReal
      ((∑ i, ‖applyKernel (μ := μ) (K i) (f : α → ℂ) x‖^2)^(p/2)))
    exact ENNReal.continuous_ofReal.measurable.comp
      ((Real.continuous_rpow_const (by linarith : 0 ≤ p/2)).measurable.comp (by fun_prop))
  have hAint_le (n : ℕ) : (∫⁻ x, Aseq n x ∂μ) ≤
      Γ * ∫⁻ x, ENNReal.ofReal (‖g n x‖^p) ∂μ := by
    simpa [Aseq, out, V] using hcont (g n)
  have hlimA : (∫⁻ x, A x ∂μ) ≤ Filter.liminf (fun n => ∫⁻ x, Aseq n x ∂μ) atTop := by
    have hFatou := lintegral_liminf_le (μ := μ) (u := atTop) hAmeas
    calc
      _ = ∫⁻ x, Filter.liminf (fun n => Aseq n x) atTop ∂μ := by
        apply lintegral_congr
        intro x
        exact (hApoint x).liminf_eq.symm
      _ ≤ _ := hFatou
  have hlimB : Tendsto (fun n => Γ * (∫⁻ x, ENNReal.ofReal (‖g n x‖^p) ∂μ))
      atTop (𝓝 (Γ * ∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ)) := by
    exact (ENNReal.continuous_const_mul hΓ).continuousAt.tendsto.comp hsrc_tendsto
  have hlimI : Filter.liminf (fun n => ∫⁻ x, Aseq n x ∂μ) atTop ≤
      Γ * ∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ := by
    calc
      _ ≤ Filter.liminf
          (fun n => Γ * (∫⁻ x, ENNReal.ofReal (‖g n x‖^p) ∂μ)) atTop :=
        liminf_le_liminf (Filter.Eventually.of_forall hAint_le)
      _ = _ := hlimB.liminf_eq
  exact hlimA.trans hlimI
end BrownianSharp.AlignmentPaperFiniteKernelLpDensity
