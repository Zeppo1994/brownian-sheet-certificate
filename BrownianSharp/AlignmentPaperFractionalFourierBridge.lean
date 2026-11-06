import BrownianSharp.AlignmentPaperFractionalFourierMultiplier
import BrownianSharp.AlignmentPaperFractionalSchwartzSource
import BrownianSharp.AlignmentPaperFractionalDampingLimit
import Mathlib.Analysis.Fourier.LpSpace

noncomputable section

set_option maxHeartbeats 5000000

open scoped FourierTransform SchwartzMap Convolution
open scoped Topology
open MeasureTheory
open Filter
open ContinuousLinearMap

namespace BrownianSharp.AlignmentPaperFractionalFourierBridge

open BrownianSharp.AlignmentPaperFractionalFourierMultiplier

/-- The complex-valued zero extension of the exponentially damped causal kernel. -/
def complexDampedKernel (β ε t : ℝ) : ℂ :=
  Set.indicator (Set.Ioi 0) (fun t => (dampedFractionalKernel β ε t : ℂ)) t

theorem complexDampedKernel_integrable {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    Integrable (complexDampedKernel β ε) := by
  have hpow := integrableOn_dampedComplexPower hβ hε (ω := 0)
  have hkernel : IntegrableOn (fun t : ℝ =>
      (dampedFractionalKernel β ε t : ℂ)) (Set.Ioi 0) := by
    have h := hpow.const_mul ((Real.Gamma β : ℂ)⁻¹)
    apply h.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp [dampedFractionalKernel, Complex.ofReal_mul, Complex.ofReal_exp,
      mul_assoc, mul_comm, mul_left_comm]
  change Integrable (Set.indicator (Set.Ioi 0)
    (fun t => (dampedFractionalKernel β ε t : ℂ))) volume
  exact hkernel.integrable_indicator measurableSet_Ioi

/-- The causal convolution of the damped kernel with a Schwartz source. -/
def dampedCausalConvolution (β ε : ℝ) (f : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ :=
  ((complexDampedKernel β ε) ⋆[mul ℂ ℂ] (f : ℝ → ℂ)) t

/-- The actual Fourier transform of the L¹ convolution is the product of
the actual kernel transform and the Schwartz source transform. -/
theorem fourier_dampedCausalConvolution {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε)
    (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    𝓕 (dampedCausalConvolution β ε f) ξ =
      (𝓕 (complexDampedKernel β ε) ξ) * (𝓕 (f : ℝ → ℂ) ξ) := by
  change 𝓕 ((complexDampedKernel β ε) ⋆[mul ℂ ℂ] (f : ℝ → ℂ)) ξ = _
  exact Real.fourier_mul_convolution_eq
    (complexDampedKernel_integrable hβ hε) f.integrable ξ

/-- The Fourier transform of the actual zero-extended kernel is the damped
fractional multiplier, with Mathlib's `2π` frequency normalization. -/
theorem fourier_complexDampedKernel {β ε ξ : ℝ} (hβ : 0 < β) (hε : 0 < ε) :
    𝓕 (complexDampedKernel β ε) ξ =
      ((ε : ℂ) + (2 * Real.pi * ξ : ℝ) * Complex.I) ^ (-(β : ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  have hfun : (fun t : ℝ =>
      Complex.exp (↑(-2 * Real.pi * t * ξ) * Complex.I) • complexDampedKernel β ε t) =
      Set.indicator (Set.Ioi 0) (fun t =>
        Complex.exp (↑(-2 * Real.pi * t * ξ) * Complex.I) *
          (dampedFractionalKernel β ε t : ℂ)) := by
    funext t
    by_cases ht : 0 < t <;>
      simp [complexDampedKernel, Set.mem_Ioi, ht, smul_eq_mul]
  rw [hfun, MeasureTheory.integral_indicator measurableSet_Ioi]
  convert dampedFractionalKernel_fourier hβ hε using 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [mul_comm]
  congr 2
  push_cast
  ring

/-- The damped convolution is in `L¹`, by the standard convolution theorem. -/
theorem dampedCausalConvolution_integrable {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε)
    (f : 𝓢(ℝ, ℂ)) : Integrable (dampedCausalConvolution β ε f) := by
  change Integrable ((complexDampedKernel β ε) ⋆[mul ℂ ℂ] (f : ℝ → ℂ))
  exact (complexDampedKernel_integrable hβ hε).integrable_convolution
    (mul ℂ ℂ) f.integrable

/-- `L¹ ∩ L∞` suffices to put the actual damped convolution in `L²`. -/
theorem dampedCausalConvolution_memLp_two {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε)
    (f : 𝓢(ℝ, ℂ)) : MemLp (dampedCausalConvolution β ε f) 2 := by
  let g := dampedCausalConvolution β ε f
  have hg1 : Integrable g := dampedCausalConvolution_integrable hβ hε f
  have hk1 : MemLp (complexDampedKernel β ε) 1 := memLp_one_iff_integrable.mpr
    (complexDampedKernel_integrable hβ hε)
  have hfTop : MemLp (f : ℝ → ℂ) ⊤ := SchwartzMap.memLp_top f
  let B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ
  let A : ENNReal := eLpNorm (complexDampedKernel β ε) (1 : ENNReal) volume
  let D : ENNReal := eLpNorm (f : ℝ → ℂ) ⊤ volume
  let C : ENNReal := (‖B‖ₑ * A) * D
  have hC : C < ⊤ := by
    dsimp [C]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by finiteness) (by simpa [A] using hk1.eLpNorm_lt_top))
      (by simpa [D] using hfTop.eLpNorm_lt_top)
  have hgTop : MemLp g ⊤ := by
    apply memLp_top_of_bound_enorm hg1.aestronglyMeasurable C.toNNReal
    filter_upwards with t
    have hpoint := MeasureTheory.enorm_convolution_le (L := B) (p := 1) (q := ⊤)
      hk1.aestronglyMeasurable hfTop.aestronglyMeasurable t
    dsimp [g, dampedCausalConvolution, C, A, D] at hpoint ⊢
    have hCeq : (C.toNNReal : ENNReal) = C := ENNReal.coe_toNNReal hC.ne
    exact hpoint.trans (le_of_eq hCeq.symm)
  have hgOne : MemLp g 1 := memLp_one_iff_integrable.mpr hg1
  have hstarTop : MemLp (fun t => star (g t)) ⊤ := hgTop.star
  have hprod : MemLp (fun t => g t * star (g t)) 1 :=
    hgOne.mul hstarTop (p := 1) (q := ⊤)
  have hprodInt : Integrable (fun t => g t * star (g t)) :=
    memLp_one_iff_integrable.mp hprod
  have hnormEq : (fun t : ℝ => ‖g t * star (g t)‖) =ᵐ[volume]
      fun t => ‖g t‖ ^ 2 := by
    filter_upwards with t
    rw [norm_mul, norm_star, pow_two]
  have hsq : Integrable (fun t : ℝ => ‖g t‖ ^ 2) := hprodInt.norm.congr hnormEq
  rw [memLp_two_iff_integrable_sq_norm hg1.aestronglyMeasurable]
  exact hsq

/-- The actual Fourier transform of the damped convolution with the `q`th
derivative of a Schwartz source obeys the fractional multiplier bound. -/
theorem fourier_dampedDerivativeConvolution_bound {q : ℕ} {r β ε ξ : ℝ}
    (hr : 0 < r) (hrq : r < q) (hβ : β = (q : ℝ) - r) (hε : 0 < ε)
    (ψ : 𝓢(ℝ, ℂ)) :
    ‖𝓕 (dampedCausalConvolution β ε (iteratedLineDerivative q ψ)) ξ‖ ≤
      (2 * Real.pi * |ξ|) ^ r * ‖𝓕 ψ ξ‖ := by
  have hβpos : 0 < β := by rw [hβ]; exact_mod_cast (sub_pos.mpr hrq)
  rw [fourier_dampedCausalConvolution hβpos hε,
    fourier_complexDampedKernel hβpos hε,
    ← SchwartzMap.fourier_coe (iteratedLineDerivative q ψ),
    fourier_iteratedLineDerivative_multiplier, hβ]
  have hmult := dampedFractionalDerivativeMultiplier_bound
    (q := q) (r := r) (ε := ε) (ξ := ξ) hr hrq hε
  calc
    ‖((ε : ℂ) + (2 * Real.pi * ξ : ℝ) * Complex.I) ^
        (-(↑((q : ℝ) - r) : ℂ)) *
        ((2 * Real.pi * Complex.I * ξ) ^ q * (𝓕 ψ) ξ)‖ =
      ‖(((ε : ℂ) + (2 * Real.pi * ξ : ℝ) * Complex.I) ^
        (-(↑((q : ℝ) - r) : ℂ)) * (2 * Real.pi * Complex.I * ξ) ^ q) *
        (𝓕 ψ) ξ‖ := by congr 1 <;> ring
    _ = ‖((ε : ℂ) + (2 * Real.pi * ξ : ℝ) * Complex.I) ^
        (-(↑((q : ℝ) - r) : ℂ)) * (2 * Real.pi * Complex.I * ξ) ^ q‖ * ‖(𝓕 ψ) ξ‖ := norm_mul _ _
    _ ≤ (2 * Real.pi * |ξ|) ^ r * ‖(𝓕 ψ) ξ‖ :=
      mul_le_mul_of_nonneg_right hmult (norm_nonneg _)

/-- The pointwise multiplier bound also shows that the classical Fourier
transform of the damped convolution is in `L²`: split frequencies at unit
scale and dominate by the transforms of the source and its integer derivative. -/
theorem fourier_dampedDerivativeConvolution_memLp_two {q : ℕ} {r β ε : ℝ}
    (hr : 0 < r) (hrq : r < q) (hβ : β = (q : ℝ) - r) (hε : 0 < ε)
    (ψ : 𝓢(ℝ, ℂ)) :
    MemLp (𝓕 (dampedCausalConvolution β ε (iteratedLineDerivative q ψ))) 2 := by
  let fhat : 𝓢(ℝ, ℂ) := 𝓕 ψ
  let dhat : 𝓢(ℝ, ℂ) := 𝓕 (iteratedLineDerivative q ψ)
  have hfmem : MemLp (fun ξ => ‖fhat ξ‖) 2 := (SchwartzMap.memLp fhat 2).norm
  have hdmem : MemLp (fun ξ => ‖dhat ξ‖) 2 := (SchwartzMap.memLp dhat 2).norm
  have hsum : MemLp (fun ξ => ‖fhat ξ‖ + ‖dhat ξ‖) 2 := hfmem.add hdmem
  have hg : Integrable (dampedCausalConvolution β ε (iteratedLineDerivative q ψ)) :=
    dampedCausalConvolution_integrable (by rw [hβ]; exact_mod_cast (sub_pos.mpr hrq)) hε _
  have hcont : Continuous
      (𝓕 (dampedCausalConvolution β ε (iteratedLineDerivative q ψ))) := by
    have heq : 𝓕 (dampedCausalConvolution β ε (iteratedLineDerivative q ψ)) =
        VectorFourier.fourierIntegral Real.fourierChar volume
          (innerSL ℝ).toLinearMap₁₂
          (dampedCausalConvolution β ε (iteratedLineDerivative q ψ)) := by
      funext ξ
      rw [Real.fourier_real_eq]
      simp [VectorFourier.fourierIntegral, innerSL_apply_apply, mul_comm]
    rw [heq]
    exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg
  apply MemLp.of_le_enorm hsum hcont.aestronglyMeasurable
  filter_upwards with ξ
  have hpoint := fourier_dampedDerivativeConvolution_bound
    (ξ := ξ) hr hrq hβ hε ψ
  have hx : 0 ≤ 2 * Real.pi * |ξ| := by positivity
  have hderiv : ‖dhat ξ‖ = (2 * Real.pi * |ξ|) ^ (q : ℝ) * ‖fhat ξ‖ := by
    dsimp [dhat, fhat]
    rw [fourier_iteratedLineDerivative_multiplier, norm_mul, norm_pow]
    have hnorm : ‖2 * Real.pi * Complex.I * ξ‖ = 2 * Real.pi * |ξ| := by
      rw [norm_mul, norm_mul, norm_mul]
      simp only [Complex.norm_real, Complex.norm_I, Complex.norm_ofNat, Real.norm_eq_abs]
      rw [abs_of_pos Real.pi_pos]
      ring
    rw [hnorm]
    rw [← Real.rpow_natCast]
  have hreal : ‖𝓕 (dampedCausalConvolution β ε (iteratedLineDerivative q ψ)) ξ‖ ≤
      ‖fhat ξ‖ + ‖dhat ξ‖ := by
    have hmul := hpoint
    by_cases hsmall : 2 * Real.pi * |ξ| ≤ 1
    · calc
        ‖𝓕 (dampedCausalConvolution β ε (iteratedLineDerivative q ψ)) ξ‖ ≤
            (2 * Real.pi * |ξ|) ^ r * ‖fhat ξ‖ := by simpa [fhat] using hmul
        _ ≤ 1 * ‖fhat ξ‖ := by
          have hpow := Real.rpow_le_rpow hx hsmall (le_of_lt hr)
          have hpow' : (2 * Real.pi * |ξ|) ^ r ≤ 1 := by
            simpa only [Real.one_rpow] using hpow
          exact mul_le_mul_of_nonneg_right hpow' (norm_nonneg _)
        _ ≤ ‖fhat ξ‖ + ‖dhat ξ‖ := by linarith [norm_nonneg (dhat ξ)]
    · have hlarge : 1 ≤ 2 * Real.pi * |ξ| := le_of_not_ge hsmall
      have hpow : (2 * Real.pi * |ξ|) ^ r ≤ (2 * Real.pi * |ξ|) ^ (q : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlarge (le_of_lt hrq)
      calc
        ‖𝓕 (dampedCausalConvolution β ε (iteratedLineDerivative q ψ)) ξ‖ ≤
            (2 * Real.pi * |ξ|) ^ r * ‖fhat ξ‖ := by simpa [fhat] using hmul
        _ ≤ (2 * Real.pi * |ξ|) ^ (q : ℝ) * ‖fhat ξ‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
        _ = ‖dhat ξ‖ := hderiv.symm
        _ ≤ ‖fhat ξ‖ + ‖dhat ξ‖ := by linarith [norm_nonneg (fhat ξ)]
  have hnorm : ‖𝓕 (dampedCausalConvolution β ε (iteratedLineDerivative q ψ)) ξ‖ₑ ≤
      ‖‖fhat ξ‖ + ‖dhat ξ‖‖ₑ := by
    rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
    apply ENNReal.coe_le_coe.mpr
    apply NNReal.coe_le_coe.mpr
    change ‖𝓕 (dampedCausalConvolution β ε (iteratedLineDerivative q ψ)) ξ‖ ≤
      ‖(‖fhat ξ‖ + ‖dhat ξ‖ : ℝ)‖
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact hreal
  exact hnorm

/-- Classical Plancherel for the actual damped output. The identification with
Mathlib's `L²` Fourier transform is proved by testing both tempered
distributions and applying the Fourier pairing identity. -/
theorem fourier_dampedDerivativeConvolution_l2_norm_eq {q : ℕ} {r β ε : ℝ}
    (hr : 0 < r) (hrq : r < q) (hβ : β = (q : ℝ) - r) (hε : 0 < ε)
    (ψ : 𝓢(ℝ, ℂ)) :
    ‖(fourier_dampedDerivativeConvolution_memLp_two hr hrq hβ hε ψ).toLp‖ =
      ‖(dampedCausalConvolution_memLp_two
        (β := β) (ε := ε)
        (by rw [hβ]; exact_mod_cast (sub_pos.mpr hrq)) hε
        (iteratedLineDerivative q ψ)).toLp‖ := by
  let g := dampedCausalConvolution β ε (iteratedLineDerivative q ψ)
  let gmem := dampedCausalConvolution_memLp_two
    (β := β) (ε := ε)
    (by rw [hβ]; exact_mod_cast (sub_pos.mpr hrq)) hε
    (iteratedLineDerivative q ψ)
  let hmem := fourier_dampedDerivativeConvolution_memLp_two hr hrq hβ hε ψ
  have hg : Integrable g := dampedCausalConvolution_integrable (β := β) (ε := ε)
    (by rw [hβ]; exact_mod_cast (sub_pos.mpr hrq)) hε _
  have hdist : (hmem.toLp : 𝓢'(ℝ, ℂ)) =
      𝓕 (gmem.toLp : 𝓢'(ℝ, ℂ)) := by
    ext φ
    rw [MeasureTheory.Lp.toTemperedDistribution_apply,
      TemperedDistribution.fourier_apply,
      MeasureTheory.Lp.toTemperedDistribution_apply]
    have hpair := VectorFourier.integral_fourierIntegral_smul_eq_flip
      (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (L := (innerSL ℝ).toLinearMap₁₂) Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg (φ.integrable (μ := (volume : Measure ℝ)))
    have hG : (𝓕 g) = VectorFourier.fourierIntegral Real.fourierChar volume
        (innerSL ℝ).toLinearMap₁₂ g := by
      funext x
      rw [Real.fourier_real_eq]
      simp [VectorFourier.fourierIntegral, Real.fourierChar_apply,
        innerSL_apply_apply, mul_comm]
    have hφ : ((𝓕 (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) =
        VectorFourier.fourierIntegral Real.fourierChar volume
          (innerSL ℝ).toLinearMap₁₂.flip (φ : ℝ → ℂ) := by
      funext x
      rw [SchwartzMap.fourier_coe φ, Real.fourier_real_eq]
      simp [VectorFourier.fourierIntegral, Real.fourierChar_apply,
        innerSL_apply_apply, mul_comm, real_inner_comm]
    have hleft :
        (∫ x, φ x • (hmem.toLp (𝓕 g)) x ∂volume) =
          ∫ x, φ x • 𝓕 g x ∂volume := by
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp (μ := (volume : Measure ℝ))] with x hx
      rw [hx]
    have hpair' : (∫ x, φ x • 𝓕 g x ∂volume) =
        ∫ x, (𝓕 φ) x • g x ∂volume := by
      simpa only [← hG, ← hφ, smul_eq_mul, mul_comm] using hpair
    have hright : (∫ x, (𝓕 φ) x • g x ∂volume) =
        ∫ x, (𝓕 φ) x • (gmem.toLp g) x ∂volume := by
      have hrep : dampedCausalConvolution β ε (iteratedLineDerivative q ψ) =ᵐ[volume]
          gmem.toLp (dampedCausalConvolution β ε (iteratedLineDerivative q ψ)) :=
        (gmem.coeFn_toLp (μ := (volume : Measure ℝ))).symm
      have hfun : (fun x => (𝓕 φ) x • dampedCausalConvolution β ε
          (iteratedLineDerivative q ψ) x) =ᵐ[volume]
          (fun x => (𝓕 φ) x • gmem.toLp
            (dampedCausalConvolution β ε (iteratedLineDerivative q ψ)) x) := by
        filter_upwards [hrep] with x hx
        rw [hx]
      exact integral_congr_ae hfun
    change (∫ x, φ x • (hmem.toLp (𝓕 g)) x ∂volume) =
      ∫ x, (𝓕 φ) x • (gmem.toLp g) x ∂volume
    exact hleft.trans (hpair'.trans hright)
  have hFourier :
      (𝓕 (gmem.toLp : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ)) =
        hmem.toLp := by
    have hinj : Function.Injective
        (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2) := by
      exact LinearMap.ker_eq_bot.mp
        (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
          (E := ℝ) (F := ℂ) (μ := (volume : Measure ℝ)) (p := 2))
    apply hinj
    change (MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2
      (𝓕 (gmem.toLp : Lp ℂ 2 (volume : Measure ℝ)))) =
      MeasureTheory.Lp.toTemperedDistributionCLM ℂ (volume : Measure ℝ) 2 hmem.toLp
    rw [MeasureTheory.Lp.toTemperedDistributionCLM_apply,
      MeasureTheory.Lp.toTemperedDistributionCLM_apply]
    rw [← MeasureTheory.Lp.fourier_toTemperedDistribution_eq]
    exact hdist.symm
  calc
    ‖hmem.toLp‖ = ‖𝓕 (gmem.toLp : Lp ℂ 2 (volume : Measure ℝ))‖ := by rw [hFourier]
    _ = ‖gmem.toLp‖ := MeasureTheory.Lp.norm_fourier_eq _

/-- The Mathlib-frequency majorant for the damped fractional derivative is
itself square integrable. The exact frequency factor is `2π|ξ|`, matching
Mathlib's Fourier convention. -/
theorem fractionalFourierWeight_memLp_two {q : ℕ} {r : ℝ}
    (hr : 0 < r) (hrq : r < q) (ψ : 𝓢(ℝ, ℂ)) :
    MemLp (fun ξ : ℝ => (2 * Real.pi * |ξ|) ^ r * ‖(𝓕 ψ) ξ‖) 2 := by
  let fhat : 𝓢(ℝ, ℂ) := 𝓕 ψ
  let dhat : 𝓢(ℝ, ℂ) := 𝓕 (iteratedLineDerivative q ψ)
  let weight : ℝ → ℝ := fun ξ => (2 * Real.pi * |ξ|) ^ r * ‖fhat ξ‖
  have hfmem : MemLp (fun ξ => ‖fhat ξ‖) 2 := (SchwartzMap.memLp fhat 2).norm
  have hdmem : MemLp (fun ξ => ‖dhat ξ‖) 2 := (SchwartzMap.memLp dhat 2).norm
  have hsum : MemLp (fun ξ => ‖fhat ξ‖ + ‖dhat ξ‖) 2 := hfmem.add hdmem
  have hcontX : Continuous (fun ξ : ℝ => 2 * Real.pi * |ξ|) := by
    convert continuous_abs.const_mul (2 * Real.pi) using 1 <;> funext ξ <;> ring
  have hcontF : Continuous (fun ξ : ℝ => ‖fhat ξ‖) := fhat.continuous.norm
  have hweightCont : Continuous weight := by
    dsimp [weight]
    exact (Real.continuous_rpow_const (le_of_lt hr)).comp hcontX |>.mul hcontF
  apply MemLp.of_le_enorm hsum hweightCont.aestronglyMeasurable
  filter_upwards with ξ
  have hx : 0 ≤ 2 * Real.pi * |ξ| := by positivity
  have hderiv : ‖dhat ξ‖ = (2 * Real.pi * |ξ|) ^ (q : ℝ) * ‖fhat ξ‖ := by
    dsimp [dhat, fhat]
    rw [fourier_iteratedLineDerivative_multiplier, norm_mul, norm_pow]
    have hnorm : ‖2 * Real.pi * Complex.I * ξ‖ = 2 * Real.pi * |ξ| := by
      rw [norm_mul, norm_mul, norm_mul]
      simp only [Complex.norm_real, Complex.norm_I, Complex.norm_ofNat, Real.norm_eq_abs]
      rw [abs_of_pos Real.pi_pos]
      ring
    rw [hnorm, ← Real.rpow_natCast]
  have hweight : weight ξ ≤ ‖fhat ξ‖ + ‖dhat ξ‖ := by
    by_cases hsmall : 2 * Real.pi * |ξ| ≤ 1
    · have hpow := Real.rpow_le_rpow hx hsmall (le_of_lt hr)
      have hpow' : (2 * Real.pi * |ξ|) ^ r ≤ 1 := by
        simpa only [Real.one_rpow] using hpow
      dsimp [weight]
      calc
        _ ≤ 1 * ‖fhat ξ‖ := mul_le_mul_of_nonneg_right hpow' (norm_nonneg _)
        _ ≤ ‖fhat ξ‖ + ‖dhat ξ‖ := by linarith [norm_nonneg (dhat ξ)]
    · have hlarge : 1 ≤ 2 * Real.pi * |ξ| := le_of_not_ge hsmall
      have hpow : (2 * Real.pi * |ξ|) ^ r ≤ (2 * Real.pi * |ξ|) ^ (q : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlarge (le_of_lt hrq)
      dsimp [weight]
      calc
        _ ≤ (2 * Real.pi * |ξ|) ^ (q : ℝ) * ‖fhat ξ‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
        _ = ‖dhat ξ‖ := hderiv.symm
        _ ≤ ‖fhat ξ‖ + ‖dhat ξ‖ := by linarith [norm_nonneg (fhat ξ)]
  have hnn : ‖weight ξ‖₊ ≤ ‖‖fhat ξ‖ + ‖dhat ξ‖‖₊ := by
    apply NNReal.coe_le_coe.mpr
    change ‖weight ξ‖ ≤ ‖(‖fhat ξ‖ + ‖dhat ξ‖ : ℝ)‖
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hx _)
      (norm_nonneg _)), Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact hweight
  rw [enorm_eq_nnnorm, enorm_eq_nnnorm]
  exact ENNReal.coe_le_coe.mpr hnn

/-- Plancherel and the damped multiplier bound give the actual convolution's
`L²` norm bound by the fractional Fourier energy of the Schwartz source. -/
theorem dampedCausalConvolution_l2_norm_le_fractionalFourierWeight
    {q : ℕ} {r β ε : ℝ} (hr : 0 < r) (hrq : r < q)
    (hβ : β = (q : ℝ) - r) (hε : 0 < ε) (ψ : 𝓢(ℝ, ℂ)) :
    ‖(dampedCausalConvolution_memLp_two
      (β := β) (ε := ε) (by rw [hβ]; exact_mod_cast (sub_pos.mpr hrq)) hε
      (iteratedLineDerivative q ψ)).toLp‖ ≤
    ‖(fractionalFourierWeight_memLp_two hr hrq ψ).toLp _‖ := by
  let gmem := dampedCausalConvolution_memLp_two
    (β := β) (ε := ε) (by rw [hβ]; exact_mod_cast (sub_pos.mpr hrq)) hε
    (iteratedLineDerivative q ψ)
  let hmem := fourier_dampedDerivativeConvolution_memLp_two hr hrq hβ hε ψ
  let wmem := fractionalFourierWeight_memLp_two hr hrq ψ
  let H : ℝ → ℂ := 𝓕 (dampedCausalConvolution β ε (iteratedLineDerivative q ψ))
  let W : ℝ → ℝ := fun ξ => (2 * Real.pi * |ξ|) ^ r * ‖(𝓕 ψ) ξ‖
  have hpoint : ∀ ξ, ‖H ξ‖ ≤ W ξ := by
    intro ξ
    exact fourier_dampedDerivativeConvolution_bound hr hrq hβ hε ψ
  have hLpPoint : ∀ᵐ ξ ∂volume,
      ‖hmem.toLp H ξ‖ ≤ ‖wmem.toLp W ξ‖ := by
    filter_upwards [hmem.coeFn_toLp (μ := (volume : Measure ℝ)),
      wmem.coeFn_toLp (μ := (volume : Measure ℝ))] with ξ hH hW
    rw [hH, hW]
    have hWnonneg : 0 ≤ W ξ := mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)
    simpa [H, W, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 2 * Real.pi * |ξ|) r)]
      using hpoint ξ
  have hnorm : ‖hmem.toLp H‖ ≤ ‖wmem.toLp W‖ :=
    MeasureTheory.Lp.norm_le_norm_of_ae_le hLpPoint
  calc
    ‖gmem.toLp (dampedCausalConvolution β ε (iteratedLineDerivative q ψ))‖ =
        ‖hmem.toLp H‖ := by
      simpa [H] using (fourier_dampedDerivativeConvolution_l2_norm_eq
        hr hrq hβ hε ψ).symm
    _ ≤ ‖wmem.toLp W‖ := hnorm

/-- For a compactly supported causal Schwartz source, the actual full-line
convolution is the damped Riemann--Liouville interval integral. This is the
interface used to pass the Fourier-regularized outputs to the causal profile. -/
theorem dampedCausalConvolution_eq_interval {β ε t : ℝ} (hβ : 0 < β)
    (hε : 0 < ε) (ht : 0 ≤ t) (f : 𝓢(ℝ, ℂ))
    (hfsupp : Function.support (f : ℝ → ℂ) ⊆ Set.Icc (0:ℝ) 1) :
    dampedCausalConvolution β ε f t =
      ∫ u in (0:ℝ)..t, complexDampedKernel β ε (t-u) * f u := by
  let k : ℝ → ℂ := complexDampedKernel β ε
  let G : ℝ → ℂ := fun u => k (t-u) * f u
  have hfcompact : HasCompactSupport (f : ℝ → ℂ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hfsupp
  have hsourceCont : Continuous (fun s : ℝ => f (t-s)) :=
    f.continuous.comp (continuous_const.sub continuous_id)
  have hsourceCompact : HasCompactSupport (fun s : ℝ => f (t-s)) :=
    hfcompact.comp_homeomorph (Homeomorph.subLeft t)
  have hGint : Integrable (fun s : ℝ => k s * f (t-s)) := by
    simpa only [smul_eq_mul, k] using
      LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
        (complexDampedKernel_integrable hβ hε).locallyIntegrable hsourceCont hsourceCompact
  have hneg : MeasurePreserving (fun x : ℝ => -x) volume volume :=
    Measure.measurePreserving_neg (volume : Measure ℝ)
  have hadd : MeasurePreserving (fun x : ℝ => t+x) volume volume := by
    refine ⟨measurable_const.add measurable_id, ?_⟩
    exact Measure.IsAddLeftInvariant.map_add_left_eq_self t
  have hchangeMap : MeasurePreserving (fun s : ℝ => t-s) volume volume := by
    convert hadd.comp hneg using 1 <;> funext s <;> simp [sub_eq_add_neg]
  have hchange : (∫ s, k s * f (t-s)) = ∫ u, G u := by
    calc
      (∫ s, k s * f (t-s)) = ∫ s, G (t-s) := by
        apply integral_congr_ae
        filter_upwards with s
        simp [G, k, sub_sub_cancel]
      _ = ∫ u, G u :=
        hchangeMap.integral_comp (Homeomorph.subLeft t).measurableEmbedding G
  have hGmeas : AEStronglyMeasurable G := by
    have hHmeas : AEStronglyMeasurable (fun s : ℝ => k s * f (t-s))
        (Measure.map (fun u : ℝ => t-u) volume) := by
      rw [hchangeMap.map_eq]
      exact hGint.aestronglyMeasurable
    have hcomp := hHmeas.comp_measurable
      (continuous_const.sub continuous_id).measurable
    simpa [G, k, Function.comp_def, sub_sub_cancel] using hcomp
  have hGint' : Integrable G := by
    have heq : (fun s : ℝ => G (t-s)) = (fun s => k s * f (t-s)) := by
      funext s
      simp [G, k]
    have hcomp : Integrable (fun s : ℝ => G (t-s)) := by simpa [heq] using hGint
    exact (hchangeMap.integrable_comp hGmeas).mp hcomp
  have hsupport : Function.support G ⊆ Set.Ioc (-1) (t+1) := by
    intro u hu
    have hk : k (t-u) ≠ 0 := by
      intro hk0
      apply hu
      simp [G, hk0]
    have hf : f u ≠ 0 := by
      intro hf0
      apply hu
      simp [G, hf0]
    have hu0 : 0 ≤ u := (hfsupp hf).1
    have hut : u ≤ t := by
      by_contra hnot
      have htu : t-u ≤ 0 := by linarith
      apply hk
      simp [k, complexDampedKernel, not_lt.mpr htu]
    exact ⟨by linarith, by linarith⟩
  have houter : (∫ u in (-1:ℝ)..(t+1), G u) = ∫ u, G u :=
    intervalIntegral.integral_eq_integral_of_support_subset hsupport
  have hGii : IntervalIntegrable G volume (-1) (t+1) := hGint'.intervalIntegrable
  have hGleft : IntervalIntegrable G volume (-1) 0 := hGint'.intervalIntegrable
  have hGmid : IntervalIntegrable G volume 0 t := hGint'.intervalIntegrable
  have hGright : IntervalIntegrable G volume t (t+1) := hGint'.intervalIntegrable
  have hleftZero : ∀ᵐ u ∂volume, u ∈ Set.Ioc (-1:ℝ) 0 → G u = 0 := by
    filter_upwards [volume.ae_ne (0:ℝ)] with u hne hu
    have hu0 : u < 0 := lt_of_le_of_ne hu.2 hne
    have hfu : f u = 0 := by
      by_contra hne0
      have hmem : u ∈ Function.support (f : ℝ → ℂ) := by
        simpa [Function.mem_support] using hne0
      have : 0 ≤ u := (hfsupp hmem).1
      linarith
    simp [G, hfu]
  have hleftZero' : ∀ᵐ u ∂volume, u ∈ Set.Ioc (0:ℝ) (-1) → G u = 0 := by
    filter_upwards with u hu
    have hu1 : 0 < u := hu.1
    have hu2 : u ≤ -1 := hu.2
    linarith
  have hleft : (∫ u in (-1:ℝ)..0, G u) = 0 := by
    calc
      (∫ u in (-1:ℝ)..0, G u) = ∫ u in (-1:ℝ)..0, (fun _ : ℝ => (0:ℂ)) u :=
        intervalIntegral.integral_congr_ae' hleftZero hleftZero'
      _ = 0 := by simp
  have hright : (∫ u in t..(t+1), G u) = 0 := by
    have hzero : ∀ᵐ u ∂volume, u ∈ Set.Ioc t (t+1) → G u = 0 := by
      filter_upwards with u hu
      have hut : t < u := hu.1
      have htu : t-u ≤ 0 := by linarith
      have hk0 : k (t-u) = 0 := by
        simp [k, complexDampedKernel, not_lt.mpr htu]
      change k (t-u) * f u = 0
      rw [hk0]
      simp
    have hzero' : ∀ᵐ u ∂volume, u ∈ Set.Ioc (t+1) t → G u = 0 := by
      filter_upwards with u hu
      have hu1 : t+1 < u := hu.1
      have hu2 : u ≤ t := hu.2
      linarith
    calc
      (∫ u in t..(t+1), G u) = ∫ u in t..(t+1), (fun _ : ℝ => (0:ℂ)) u :=
        intervalIntegral.integral_congr_ae' hzero hzero'
      _ = 0 := by simp
  have hGfirst : IntervalIntegrable G volume (-1) t := hGleft.trans hGmid
  have hsplit1 : (∫ u in (-1:ℝ)..0, G u) + (∫ u in 0..t, G u) =
      ∫ u in (-1:ℝ)..t, G u := intervalIntegral.integral_add_adjacent_intervals hGleft hGmid
  have hsplit2 : (∫ u in (-1:ℝ)..t, G u) + (∫ u in t..(t+1), G u) =
      ∫ u in (-1:ℝ)..(t+1), G u :=
    intervalIntegral.integral_add_adjacent_intervals hGfirst hGright
  calc
    dampedCausalConvolution β ε f t = ∫ s, k s * f (t-s) := rfl
    _ = ∫ u, G u := hchange
    _ = ∫ u in (-1:ℝ)..(t+1), G u := houter.symm
    _ = ∫ u in 0..t, G u := by rw [← hsplit2, ← hsplit1, hleft, hright]; simp

/-- On nonnegative times the actual complex convolution equals the real
damped Riemann--Liouville integral after complexification of the source. -/
theorem dampedCausalConvolution_eq_dampedRLIntegral {β ε t : ℝ}
    (hβ : 1/2 < β) (hε : 0 < ε) (ht : 0 ≤ t) (F : ℝ → ℝ)
    (hF : Continuous F) (f : 𝓢(ℝ, ℂ))
    (hfsupp : Function.support (f : ℝ → ℂ) ⊆ Set.Icc (0:ℝ) 1)
    (hf : ∀ u, f u = (F u : ℂ)) :
    dampedCausalConvolution β ε f t =
      (BrownianSharp.AlignmentPaperFractionalDampingLimit.dampedRLIntegral β ε F t : ℂ) := by
  rw [dampedCausalConvolution_eq_interval (by linarith : 0 < β) hε ht f hfsupp]
  unfold BrownianSharp.AlignmentPaperFractionalDampingLimit.dampedRLIntegral
  have hforward : ∀ᵐ u ∂volume, u ∈ Set.Ioc (0:ℝ) t →
      complexDampedKernel β ε (t-u) * f u =
        ((Real.exp (-ε*(t-u)) *
          BrownianSharp.AlignmentFractionalKernel.kernel β (t-u) * F u : ℝ) : ℂ) := by
    filter_upwards [volume.ae_ne t] with u hne hu
    have htu : 0 < t-u := by
      have : u < t := by
        by_contra hn
        have htu' : t ≤ u := le_of_not_gt hn
        exact hne (le_antisymm hu.2 htu')
      linarith
    rw [hf]
    simp [complexDampedKernel, Set.mem_Ioi.mpr htu, dampedFractionalKernel,
      BrownianSharp.AlignmentFractionalKernel.kernel, Complex.ofReal_mul,
      Complex.ofReal_exp]
    · apply Or.inl
      ring
  have hbackward : ∀ᵐ u ∂volume, u ∈ Set.Ioc t 0 →
      complexDampedKernel β ε (t-u) * f u =
        ((Real.exp (-ε*(t-u)) *
          BrownianSharp.AlignmentFractionalKernel.kernel β (t-u) * F u : ℝ) : ℂ) := by
    filter_upwards with u hu
    have : False := by linarith [ht, hu.1, hu.2]
    exact this.elim
  rw [intervalIntegral.integral_congr_ae' hforward hbackward]
  rw [intervalIntegral.integral_ofReal]

private theorem iteratedDeriv_support_subset_Icc {F : ℝ → ℝ}
    (hFsupport : Function.support F ⊆ Set.Icc (0:ℝ) 1) :
    ∀ q : ℕ, Function.support (iteratedDeriv q F) ⊆ Set.Icc (0:ℝ) 1 := by
  intro q
  induction q with
  | zero => simpa using hFsupport
  | succ q ih =>
      rw [iteratedDeriv_succ]
      exact support_deriv_subset.trans
        (closure_minimal ih isClosed_Icc)

/-- The genuine causal Riemann--Liouville profile of a compactly supported
smooth source has the Fourier-derived L² bound. This is the fractional
Liouville bridge: actual damped convolutions are bounded by the Schwartz
Fourier weight, identified with the damped interval integrals, and passed to
the causal profile by the pinned Lp Fatou theorem. -/
theorem causalRLProfile_global_eLpNorm_le_fractionalFourierWeight
    {q : ℕ} {r β : ℝ} (hr : 0 < r) (hrq : r < q)
    (hβ : β = (q : ℝ) - r) (hβhalf : 1/2 < β) (F : ℝ → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupport : Function.support F ⊆ Set.Icc (0:ℝ) 1) :
    MeasureTheory.eLpNorm
        (fun t : ℝ => (BrownianSharp.AlignmentFractionalTail.causalRLProfile
          β (iteratedDeriv q F) t : ℂ)) 2 volume ≤
      MeasureTheory.eLpNorm
        (fun ξ : ℝ => (2 * Real.pi * |ξ|) ^ r *
          ‖𝓕 ((BrownianSharp.AlignmentPaperFractionalSchwartzSource.realCompactSchwartz
            F hF (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hFsupport)
              : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ξ‖) 2 volume := by
  let hcompact : HasCompactSupport F :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hFsupport
  let ψ : 𝓢(ℝ, ℂ) :=
    BrownianSharp.AlignmentPaperFractionalSchwartzSource.realCompactSchwartz F hF hcompact
  let Fq : ℝ → ℝ := iteratedDeriv q F
  let ε : ℕ → ℝ := fun n => 1 / ((n:ℝ) + 1)
  let out : ℕ → ℝ → ℂ := fun n t =>
    dampedCausalConvolution β (ε n) (iteratedLineDerivative q ψ) t
  let lim : ℝ → ℂ := fun t =>
    (BrownianSharp.AlignmentFractionalTail.causalRLProfile β Fq t : ℂ)
  let μ : Measure ℝ := volume
  let w : ℝ → ℝ := fun ξ => (2 * Real.pi * |ξ|) ^ r * ‖(𝓕 ψ) ξ‖
  have hβpos : 0 < β := by linarith
  have hFq : ContDiff ℝ (⊤ : ℕ∞) Fq := by
    dsimp [Fq]
    simpa only [iteratedDeriv_eq_iterate] using ContDiff.iterate_deriv q hF
  have hFqcont : Continuous Fq := hFq.continuous
  have hFqsupport : Function.support Fq ⊆ Set.Icc (0:ℝ) 1 := by
    exact iteratedDeriv_support_subset_Icc hFsupport q
  have hsourceSupport : Function.support
      (iteratedLineDerivative q ψ : ℝ → ℂ) ⊆ Set.Icc (0:ℝ) 1 := by
    intro x hx
    have hreal : Fq x ≠ 0 := by
      intro hz
      apply hx
      rw [BrownianSharp.AlignmentPaperFractionalSchwartzSource.iteratedLineDerivative_realCompactSchwartz
        F hF hcompact q x]
      simp [Fq, hz]
    exact hFqsupport hreal
  have hsourceValue : ∀ x,
      iteratedLineDerivative q ψ x = (Fq x : ℂ) := by
    intro x
    simpa [ψ, Fq] using
      BrownianSharp.AlignmentPaperFractionalSchwartzSource.iteratedLineDerivative_realCompactSchwartz
        F hF hcompact q x
  have hεpos : ∀ n, 0 < ε n := by
    intro n
    positivity
  have hεnonneg : ∀ n, 0 ≤ ε n := fun n => (hεpos n).le
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    dsimp [ε]
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpointwise : ∀ᵐ t ∂μ, Tendsto (fun n => out n t) atTop (𝓝 (lim t)) := by
    filter_upwards with t
    by_cases ht : 0 ≤ t
    · have hrl := BrownianSharp.AlignmentPaperFractionalDampingLimit.dampedRLIntegral_tendsto
        hβhalf ht Fq hFqcont ε hεnonneg hεlim
      have hcast : Tendsto
          (fun n => (BrownianSharp.AlignmentPaperFractionalDampingLimit.dampedRLIntegral
            β (ε n) Fq t : ℂ)) atTop
          (𝓝 (BrownianSharp.AlignmentFractionalKernel.rlIntegral β Fq t : ℂ)) :=
        Complex.continuous_ofReal.continuousAt.tendsto.comp hrl
      have hout : ∀ n, out n t =
          (BrownianSharp.AlignmentPaperFractionalDampingLimit.dampedRLIntegral
            β (ε n) Fq t : ℂ) := by
        intro n
        exact dampedCausalConvolution_eq_dampedRLIntegral hβhalf (hεpos n)
          ht Fq hFqcont (iteratedLineDerivative q ψ)
          hsourceSupport hsourceValue
      have hlimEq : lim t =
          (BrownianSharp.AlignmentFractionalKernel.rlIntegral β Fq t : ℂ) := by
        by_cases htpos : 0 < t
        · dsimp [lim, Fq]
          rw [BrownianSharp.AlignmentPaperFractionalFourier.causalRLProfile_eq_rlIntegral_of_pos
            (iteratedDeriv q F) htpos]
        · have ht0 : t = 0 := le_antisymm (le_of_not_gt htpos) ht
          simp [lim, Fq, ht0,
            BrownianSharp.AlignmentFractionalTail.causalRLProfile,
            BrownianSharp.AlignmentFractionalKernel.rlIntegral]
      rw [hlimEq]
      simpa only [hout] using hcast
    · have htneg : t < 0 := lt_of_not_ge ht
      have houtzero : ∀ n, out n t = 0 := by
        intro n
        change ((complexDampedKernel β (ε n)) ⋆[mul ℂ ℂ]
          (iteratedLineDerivative q ψ : ℝ → ℂ)) t = 0
        change (∫ s : ℝ, complexDampedKernel β (ε n) s *
          iteratedLineDerivative q ψ (t-s)) = 0
        calc
          (∫ s : ℝ, complexDampedKernel β (ε n) s *
              iteratedLineDerivative q ψ (t-s)) =
              ∫ s : ℝ, (0:ℂ) := by
            apply integral_congr_ae
            filter_upwards with s
            by_cases hs : 0 < s
            · have hsrc : iteratedLineDerivative q ψ (t-s) = 0 := by
                by_contra hne
                have hmem : t-s ∈ Function.support
                    (iteratedLineDerivative q ψ : ℝ → ℂ) := by
                  simpa [Function.mem_support] using hne
                have hnonneg : 0 ≤ t-s := (hsourceSupport hmem).1
                linarith
              simp [hsrc]
            · simp [complexDampedKernel, Set.mem_Ioi, hs]
          _ = 0 := by simp
      have hlimzero : lim t = 0 := by
        simp [lim, BrownianSharp.AlignmentFractionalTail.causalRLProfile,
          le_of_lt htneg]
      simp only [houtzero, hlimzero]
      exact tendsto_const_nhds
  have houtMem : ∀ n, MemLp (out n) 2 volume := by
    intro n
    dsimp [out]
    exact dampedCausalConvolution_memLp_two hβpos (hεpos n) (iteratedLineDerivative q ψ)
  have houtAes : ∀ n, AEStronglyMeasurable (out n) μ := by
    intro n
    exact (houtMem n).aestronglyMeasurable
  have hlimAes : AEStronglyMeasurable lim μ :=
    aestronglyMeasurable_of_tendsto_ae atTop houtAes hpointwise
  let wmem := fractionalFourierWeight_memLp_two hr hrq ψ
  have hbound : ∀ᶠ n in atTop, MeasureTheory.eLpNorm (out n) 2 μ ≤
      MeasureTheory.eLpNorm w 2 volume := by
    filter_upwards with n
    have hnorm := dampedCausalConvolution_l2_norm_le_fractionalFourierWeight
      hr hrq hβ (hεpos n) ψ
    have henorm :
        MeasureTheory.eLpNorm
          (dampedCausalConvolution β (ε n) (iteratedLineDerivative q ψ)) 2 volume ≤
        MeasureTheory.eLpNorm w 2 volume := by
      rw [← MeasureTheory.Lp.enorm_toLp
        (dampedCausalConvolution_memLp_two hβpos (hεpos n)
          (iteratedLineDerivative q ψ))]
      rw [← MeasureTheory.Lp.enorm_toLp wmem]
      exact (enorm_le_iff_norm_le).2 hnorm
    simpa only [out, μ] using henorm
  have hfatou := MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto hbound houtAes
    hlimAes hpointwise
  simpa [μ, lim, w, SchwartzMap.fourier_coe] using hfatou

end BrownianSharp.AlignmentPaperFractionalFourierBridge
