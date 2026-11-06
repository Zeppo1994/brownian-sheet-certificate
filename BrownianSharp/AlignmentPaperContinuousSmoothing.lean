import BrownianSharp.AlignmentContinuousLInfinity
import BrownianSharp.TorusFoundations
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Concrete positive integral smoothing from the actual L-infinity space
into continuous functions. The source is the a.e. quotient, and all bounds
are uniform over its unit ball. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperContinuousSmoothing

variable {α : Type*} [MetricSpace α] [CompactSpace α]
  [MeasurableSpace α] [BorelSpace α]
variable (μ : Measure α) [IsFiniteMeasure μ]

private theorem lpTop_ae_norm_le (g : Lp ℝ ⊤ μ) :
    ∀ᵐ y ∂μ, ‖g y‖ ≤ ‖g‖ := by
  have h : ∀ᵐ y ∂μ, ‖g y‖ₑ ≤ ‖g‖ₑ := by
    rw [Lp.enorm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable g)]
    exact ae_le_eLpNormEssSup
  filter_upwards [h] with y hy
  exact enorm_le_iff_norm_le.mp hy

/-- Actual integral against a continuous kernel on the compact product. -/
def kernelIntegral (k : C(α × α, ℝ)) (g : Lp ℝ ⊤ μ) (x : α) : ℝ :=
  ∫ y, k (x,y) * g y ∂μ

private theorem kernelIntegrand_integrable (k : C(α × α, ℝ))
    (g : Lp ℝ ⊤ μ) (x : α) :
    Integrable (fun y => k (x,y) * g y) μ := by
  apply Integrable.of_bound
    (((k.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable g)) (‖k‖ * ‖g‖)
  filter_upwards [lpTop_ae_norm_le μ g] with y hy
  change ‖k (x,y) * g y‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul (ContinuousMap.norm_coe_le_norm k (x,y)) hy (norm_nonneg _) (norm_nonneg _)

theorem kernelIntegral_continuous (k : C(α × α, ℝ)) (g : Lp ℝ ⊤ μ) :
    Continuous (kernelIntegral μ k g) := by
  apply continuous_of_dominated
    (bound := fun _ => ‖k‖ * ‖g‖)
  · intro x
    exact (kernelIntegrand_integrable μ k g x).aestronglyMeasurable
  · intro x
    filter_upwards [lpTop_ae_norm_le μ g] with y hy
    rw [norm_mul]
    exact mul_le_mul (ContinuousMap.norm_coe_le_norm k (x,y)) hy (norm_nonneg _) (norm_nonneg _)
  · exact integrable_const _
  · filter_upwards [] with y
    exact (k.continuous.comp (continuous_id.prodMk continuous_const)).mul_const _

/-- Nonnegative row-normalized kernels are contractive on the genuine
L-infinity quotient. -/
theorem kernelIntegral_norm_le (k : C(α × α, ℝ))
    (hk : ∀ x y, 0 ≤ k (x,y)) (hmass : ∀ x, (∫ y, k (x,y) ∂μ) = 1)
    (g : Lp ℝ ⊤ μ) (x : α) :
    ‖kernelIntegral μ k g x‖ ≤ ‖g‖ := by
  have hki : Integrable (fun y => k (x,y)) μ :=
    (k.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    ‖kernelIntegral μ k g x‖ ≤ ∫ y, ‖k (x,y) * g y‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, k (x,y) * ‖g‖ ∂μ := by
      apply integral_mono_ae (kernelIntegrand_integrable μ k g x).norm (hki.mul_const _)
      filter_upwards [lpTop_ae_norm_le μ g] with y hy
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hk x y)]
      exact mul_le_mul_of_nonneg_left hy (hk x y)
    _ = ‖g‖ := by rw [integral_mul_const, hmass, one_mul]

/-- The actual bounded linear smoothing operator, rather than a smoothing
premise supplied by a caller. -/
def kernelSmoother (k : C(α × α, ℝ))
    (hk : ∀ x y, 0 ≤ k (x,y)) (hmass : ∀ x, (∫ y, k (x,y) ∂μ) = 1) :
    Lp ℝ ⊤ μ →L[ℝ] C(α, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun g => ⟨kernelIntegral μ k g, kernelIntegral_continuous μ k g⟩
      map_add' := by
        intro g h
        ext x
        change (∫ y, k (x,y) * (g+h) y ∂μ) = _
        calc
          _ = ∫ y, (k (x,y)*g y + k (x,y)*h y) ∂μ := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_add g h] with y hy
            simp only [hy, Pi.add_apply, mul_add]
          _ = _ := integral_add (kernelIntegrand_integrable μ k g x)
            (kernelIntegrand_integrable μ k h x)
      map_smul' := by
        intro c g
        ext x
        change (∫ y, k (x,y) * (c • g) y ∂μ) = _
        calc
          _ = ∫ y, c * (k (x,y)*g y) ∂μ := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_smul c g] with y hy
            rw [hy]
            simp only [Pi.smul_apply, smul_eq_mul]
            ring
          _ = _ := integral_const_mul _ _ }
    1 (by
      intro g
      simp only [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg g)).2
      intro x
      change ‖kernelIntegral μ k g x‖ ≤ ‖g‖
      exact kernelIntegral_norm_le μ k hk hmass g x)

@[simp] theorem kernelSmoother_apply (k : C(α × α, ℝ))
    (hk : ∀ x y, 0 ≤ k (x,y)) (hmass : ∀ x, (∫ y, k (x,y) ∂μ) = 1)
    (g : Lp ℝ ⊤ μ) (x : α) :
    kernelSmoother μ k hk hmass g x = ∫ y, k (x,y) * g y ∂μ := rfl

theorem kernelSmoother_contractile (k : C(α × α, ℝ))
    (hk : ∀ x y, 0 ≤ k (x,y)) (hmass : ∀ x, (∫ y, k (x,y) ∂μ) = 1)
    (g : Lp ℝ ⊤ μ) : ‖kernelSmoother μ k hk hmass g‖ ≤ ‖g‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg g)).2
  intro x
  exact kernelIntegral_norm_le μ k hk hmass g x

section AddGroup
variable [AddCommGroup α] [IsTopologicalAddGroup α]
  [μ.IsAddLeftInvariant] [μ.IsNegInvariant] [μ.IsOpenPosMeasure]

/-- A nonnegative continuous approximate-identity kernel. Its integral is
positive because the measure has full support. -/
def tentKernel (δ : ℝ) : C(α, ℝ) :=
  ⟨fun y => max (δ - dist y 0) 0, by fun_prop⟩

theorem tentKernel_integral_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < ∫ y, tentKernel (α := α) δ y ∂μ := by
  apply integral_pos_of_integrable_nonneg_nonzero
    (tentKernel δ).continuous
    ((tentKernel δ).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))
    (fun y => le_max_right _ _)
    (x := 0)
  simp [tentKernel, max_eq_left hδ.le, hδ.ne']

/-- Actual translation kernel for convolution on the compact additive group. -/
def normalizedConvolutionKernel (δ : ℝ) : C(α × α, ℝ) :=
  ⟨fun p => tentKernel δ (p.1-p.2) / (∫ y, tentKernel δ y ∂μ),
    ((tentKernel δ).continuous.comp (continuous_fst.sub continuous_snd)).div_const _⟩

theorem normalizedConvolutionKernel_nonneg {δ : ℝ} (hδ : 0 < δ) (x y : α) :
    0 ≤ normalizedConvolutionKernel μ δ (x,y) :=
  div_nonneg (le_max_right _ _) (tentKernel_integral_pos μ hδ).le

theorem normalizedConvolutionKernel_mass {δ : ℝ} (hδ : 0 < δ) (x : α) :
    (∫ y, normalizedConvolutionKernel μ δ (x,y) ∂μ) = 1 := by
  change (∫ y, tentKernel δ (x-y) / (∫ z, tentKernel δ z ∂μ) ∂μ) = 1
  rw [integral_div]
  have h : (∫ y, tentKernel δ (x-y) ∂μ) = ∫ y, tentKernel δ y ∂μ := by
    simp_rw [sub_eq_add_neg]
    rw [integral_neg_eq_self (fun y => tentKernel δ (x+y)),
      integral_add_left_eq_self]
  rw [h, div_self (tentKernel_integral_pos μ hδ).ne']

theorem normalizedConvolutionKernel_support {δ : ℝ} {x y : α}
    (h : normalizedConvolutionKernel μ δ (x,y) ≠ 0) : dist (x-y) 0 < δ := by
  have hnum : max (δ-dist (x-y) 0) 0 ≠ 0 := by
    intro hz
    exact h (by simp [normalizedConvolutionKernel, tentKernel, hz])
  have hpos : 0 < max (δ-dist (x-y) 0) 0 :=
    lt_of_le_of_ne (le_max_right _ _) (Ne.symm hnum)
  by_contra hn
  have hz : δ-dist (x-y) 0 ≤ 0 := by linarith
  exact hnum (max_eq_right hz)

/-- Compactness supplies one spatial modulus for every function in the
class; no modulus is selected separately for each target. -/
theorem compact_class_translation_modulus (K : Set C(α, ℝ)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ K, ∀ x z : α, dist z 0 < δ →
      ‖f x - f (x-z)‖ < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : Continuous (fun p : K × α × α => (p.1 : C(α,ℝ)) (p.2.1-p.2.2)) := by
    exact continuous_eval.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        ((continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)))
  obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp (CompactSpace.uniformContinuous_of_continuous hc) ε hε
  refine ⟨δ,hδ,?_⟩
  intro f hf x z hz
  have hp : dist ((⟨f,hf⟩ : K),x,(0:α)) ((⟨f,hf⟩ : K),x,z) < δ := by
    simpa [Prod.dist_eq, dist_comm, max_eq_right (dist_nonneg : 0 ≤ dist z 0)] using hz
  have hh := hmod hp
  simpa only [sub_zero, dist_eq_norm] using hh

/-- Smoothing the approximants also smooths the target. This is the precise
additional error term that contractivity alone does not remove. -/
theorem kernelSmoother_error_le (k : C(α × α, ℝ))
    (hk : ∀ x y, 0 ≤ k (x,y)) (hmass : ∀ x, (∫ y, k (x,y) ∂μ) = 1)
    (f : C(α,ℝ)) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ x y, k (x,y) ≠ 0 → ‖f x-f y‖ ≤ ε) :
    ‖f - kernelSmoother μ k hk hmass
      (AlignmentAmbientWidth.continuousToLInfinity μ f)‖ ≤ ε := by
  apply (ContinuousMap.norm_le _ hε).2
  intro x
  have hki : Integrable (fun y => k (x,y)) μ :=
    (k.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfi : Integrable (fun y => k (x,y)*f y) μ :=
    ((k.continuous.comp (continuous_const.prodMk continuous_id)).mul f.continuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq : kernelSmoother μ k hk hmass
      (AlignmentAmbientWidth.continuousToLInfinity μ f) x = ∫ y, k (x,y)*f y ∂μ := by
    rw [kernelSmoother_apply]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p := ⊤) (𝕜 := ℝ) (μ := μ) f] with y hy
    exact congrArg (fun z => k (x,y)*z) hy
  have herr : f x - kernelSmoother μ k hk hmass
      (AlignmentAmbientWidth.continuousToLInfinity μ f) x =
      ∫ y, k (x,y)*(f x-f y) ∂μ := by
    rw [heq]
    simp_rw [mul_sub]
    rw [integral_sub (hki.mul_const _) hfi, integral_mul_const, hmass, one_mul]
  change ‖f x - kernelSmoother μ k hk hmass
    (AlignmentAmbientWidth.continuousToLInfinity μ f) x‖ ≤ ε
  rw [herr]
  calc
    _ ≤ ∫ y, ‖k (x,y)*(f x-f y)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, k (x,y)*ε ∂μ := by
      apply integral_mono
        (((k.continuous.comp (continuous_const.prodMk continuous_id)).mul
          (continuous_const.sub f.continuous)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).norm
        (hki.mul_const ε)
      intro y
      change ‖k (x,y)*(f x-f y)‖ ≤ k (x,y)*ε
      by_cases hz : k (x,y) = 0
      · simp [hz]
      · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hk x y)]
        exact mul_le_mul_of_nonneg_left (hosc x y hz) (hk x y)
    _ = ε := by rw [integral_mul_const, hmass, one_mul]

/-- A genuine contractive convolution smoother exists for each desired
uniform accuracy on a compact continuous function class. -/
theorem exists_contractive_smoothing (K : Set C(α,ℝ)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Lp ℝ ⊤ μ →L[ℝ] C(α,ℝ),
      (∀ g, ‖S g‖ ≤ ‖g‖) ∧
      ∀ f ∈ K, ‖f-S (AlignmentAmbientWidth.continuousToLInfinity μ f)‖ ≤ ε := by
  obtain ⟨δ,hδ,hmod⟩ := compact_class_translation_modulus K hK hε
  let k := normalizedConvolutionKernel μ δ
  have hk := normalizedConvolutionKernel_nonneg μ hδ
  have hm := normalizedConvolutionKernel_mass μ hδ
  refine ⟨kernelSmoother μ k hk hm, kernelSmoother_contractile μ k hk hm, ?_⟩
  intro f hf
  apply kernelSmoother_error_le μ k hk hm f hε.le
  intro x y hxy
  have hz := normalizedConvolutionKernel_support μ hxy
  have hh := hmod f hf x (x-y) hz
  simpa only [sub_sub_cancel] using hh.le

end AddGroup

/-- The precise torus ambient-space equality used for periodic approximants.
A relatively compact target class is enough; the smoothing is selected on
its compact closure. -/
theorem torus_width_eq_LInfinity_width {d : ℕ}
    (K : Set C(UnitAddTorus (Fin d),ℝ)) (hK : IsCompact (closure K)) (m : ℕ) :
    HaarQuarter.TheoremD.Width.kolmogorovWidth K m =
      HaarQuarter.TheoremD.Width.kolmogorovWidth
        (AlignmentAmbientWidth.continuousToLInfinity
          (volume : Measure (UnitAddTorus (Fin d))) '' K) m := by
  apply AlignmentAmbientWidth.continuous_width_eq_LInfinity_width_of_smoothing volume K
  intro δ hδ
  obtain ⟨S,hS,happ⟩ := exists_contractive_smoothing
    (volume : Measure (UnitAddTorus (Fin d))) (closure K) hK hδ
  exact ⟨S,hS,fun f hf => happ f (subset_closure hf)⟩

end BrownianSharp.AlignmentPaperContinuousSmoothing
