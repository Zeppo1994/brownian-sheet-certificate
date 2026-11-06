import BrownianSharp.External.WeakCZ.CircleBadKernel
import BrownianSharp.External.WeakCZ.CircleKernelFiniteRep
import BrownianSharp.External.WeakCZ.CircleWhitneyException
import BrownianSharp.AlignmentPaperSignedKernelBadSeries
import BrownianSharp.AlignmentPaperSignedKernelGoodControl
import BrownianSharp.External.WeakCZ.CircleMaximalDifferentiation
import BrownianSharp.External.WeakCZ.WhitneyAverage
import BrownianSharp.External.WeakCZ.WeakOneClosure
import Mathlib.MeasureTheory.Integral.Prod

/-! The actual finite signed smooth-resolution convolution has a uniform
weak-(1,1) bound on the period-one circle. This file assembles the actual
Whitney partition, cancellation estimate, and good/bad distribution closure.
-/

noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 4096
open MeasureTheory Set Metric
open scoped ENNReal

namespace BrownianSharp.External.WeakCZ

open BrownianSharp.AlignmentPaperSignedKernelOperator
open BrownianSharp.AlignmentPaperSignedKernelBadSeries
open BrownianSharp.AlignmentPaperSignedKernelGoodControl
open BrownianSharp.AlignmentPaperKernelHörmander

private def circleWhitneyException {Ω : Set UnitAddCircle}
    (d : CircleWhitneyPieceData Ω) : Set UnitAddCircle :=
  ⋃ i, ball (d.center i) (64 * d.radius i)

private theorem lintegral_badConvolution_restrict_le_of_support
    (μ ν : Measure UnitAddCircle) [SFinite μ] [SFinite ν]
    (E : Set UnitAddCircle) (K : UnitAddCircle → UnitAddCircle → ℂ)
    (K₀ : UnitAddCircle → ℂ) (b : UnitAddCircle → ℂ) (H : ℝ≥0∞)
    (hmeas : AEMeasurable
      (fun p : UnitAddCircle × UnitAddCircle =>
        ‖(K p.1 p.2-K₀ p.1)*b p.2‖ₑ) ((μ.restrict E).prod ν))
    (hbmeas : AEMeasurable (fun y => ‖b y‖ₑ) ν)
    (hH : ∀ y, b y ≠ 0 →
      ∫⁻ x, ‖K x y-K₀ x‖ₑ ∂(μ.restrict E) ≤ H)
    (hzero : ∫ y, b y ∂ν = 0)
    (hKint : ∀ x, Integrable (fun y => K x y*b y) ν)
    (hcint : ∀ x, Integrable (fun y => K₀ x*b y) ν) :
    ∫⁻ x, ‖∫ y, K x y*b y ∂ν‖ₑ ∂(μ.restrict E) ≤
      H * ∫⁻ y, ‖b y‖ₑ ∂ν := by
  calc
    _ = ∫⁻ x, ‖∫ y, (K x y-K₀ x)*b y ∂ν‖ₑ ∂(μ.restrict E) := by
      apply lintegral_congr
      intro x
      exact congrArg (fun z : ℂ => ‖z‖ₑ)
        ((integral_kernel_difference_eq_of_zeroMean ν (K x) b (K₀ x)
          (hKint x) (hcint x) hzero).symm)
    _ ≤ ∫⁻ x, ∫⁻ y, ‖(K x y-K₀ x)*b y‖ₑ ∂ν ∂(μ.restrict E) := by
      apply lintegral_mono
      intro x
      exact enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ y, ∫⁻ x, ‖(K x y-K₀ x)*b y‖ₑ ∂(μ.restrict E) ∂ν :=
      lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ y, H * ‖b y‖ₑ ∂ν := by
      apply lintegral_mono
      intro y
      by_cases hy : b y = 0
      · simp [hy]
      · calc
          ∫⁻ x, ‖(K x y-K₀ x)*b y‖ₑ ∂(μ.restrict E)
              = ‖b y‖ₑ * ∫⁻ x, ‖K x y-K₀ x‖ₑ ∂(μ.restrict E) := by
                simp_rw [enorm_mul, mul_comm]
                exact lintegral_const_mul' _ _ (by simp : ‖b y‖ₑ ≠ ⊤)
          _ ≤ ‖b y‖ₑ * H := by gcongr; exact hH y hy
          _ = H * ‖b y‖ₑ := mul_comm _ _
    _ = H * ∫⁻ y, ‖b y‖ₑ ∂ν := by
      rw [lintegral_const_mul'' H hbmeas]

/-- One actual mean-zero Whitney piece has uniformly bounded output L¹ away
from the union of the 64-fold core balls. -/
theorem circle_badPiece_lintegral_outside_exception_le
    {Ω : Set UnitAddCircle}
    (d : CircleWhitneyPieceData Ω) (i : d.Index)
    (N : ℕ) (ε : Fin (N+1) → ℝ) (hε : ∀ s, |ε s| ≤ 1)
    {f : UnitAddCircle → ℂ}
    (hf : Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle))
    {H : ℝ}
    (hbad : ∀ (S : Finset ℕ) (coeff : ℕ → ℝ),
      (∀ s ∈ S, |coeff s| ≤ 1) → ∀ (center y : UnitAddCircle) (r : ℝ),
      0 ≤ r → y ∈ ball center (5*r) →
      ∫⁻ x, ‖circleSignedKernelDifference S coeff
        (AddCircle.equivIoc (1:ℝ) (-1/2:ℝ) (center-y) : ℝ) (x-center)‖ₑ ∂
        (volume.restrict (ball center (64*r))ᶜ) ≤ ENNReal.ofReal H) :
    ∫⁻ x in (circleWhitneyException d)ᶜ,
      ‖circleSignedConvolutionOperator N ε
        (badPiece (AddCircle.haarAddCircle : Measure UnitAddCircle) (d.piece i) f) x‖ₑ
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) ≤
      ENNReal.ofReal H * ∫⁻ y,
        ‖badPiece (AddCircle.haarAddCircle : Measure UnitAddCircle) (d.piece i) f y‖ₑ
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  let b : UnitAddCircle → ℂ := badPiece μ (d.piece i) f
  let output : Set UnitAddCircle := (circleWhitneyException d)ᶜ
  let K : UnitAddCircle → UnitAddCircle → ℂ :=
    fun x y => circleSignedKernel N ε (x-y)
  let K₀ : UnitAddCircle → ℂ := fun x => circleSignedKernel N ε (x-d.center i)
  have hb : Integrable b μ := integrable_badPiece μ (d.piece i) f
    (d.piece_measurable i) hf
  have hzero : ∫ y, b y ∂μ = 0 := integral_badPiece_eq_zero μ (d.piece i) f
    (d.piece_measurable i) hf
  have hcoeff : ∀ n ∈ Finset.range (N+1),
      |signedKernelNaturalCoefficients N ε n| ≤ 1 :=
    signedKernelNaturalCoefficients_bound N ε hε
  have hkernelDifference (y x : UnitAddCircle) :
      K x y - K₀ x = circleSignedKernelDifference (Finset.range (N+1))
        (signedKernelNaturalCoefficients N ε)
        (AddCircle.equivIoc (1:ℝ) (-1/2:ℝ) (d.center i-y) : ℝ)
        (x-d.center i) := by
    have hcoe : ((AddCircle.equivIoc (1:ℝ) (-1/2:ℝ)
        (d.center i-y) : ℝ) : UnitAddCircle) = d.center i-y :=
      AddCircle.coe_equivIoc
    rw [circleSignedKernelDifference_eq_actual]
    dsimp [K, K₀]
    rw [hcoe]
    congr 1
    abel_nf
  have hpieceInside (y : UnitAddCircle) (hy : y ∈ d.piece i) :
      y ∈ ball (d.center i) (5*d.radius i) := d.piece_subset_five i hy
  have hH' (y : UnitAddCircle) (hby : b y ≠ 0) :
      ∫⁻ x in output, ‖K x y-K₀ x‖ₑ ∂μ ≤ ENNReal.ofReal H := by
    have hsupport : y ∈ d.piece i := by
      by_contra hnot
      apply hby
      simp [b, badPiece, hnot]
    have hfull := hbad (Finset.range (N+1))
      (signedKernelNaturalCoefficients N ε) hcoeff (d.center i) y (d.radius i)
      (le_of_lt (d.radius_pos i)) (hpieceInside y hsupport)
    have hsubset : output ⊆ (ball (d.center i) (64*d.radius i))ᶜ := by
      intro x hx hxball
      apply hx
      exact mem_iUnion.mpr ⟨i, hxball⟩
    calc
      ∫⁻ x in output, ‖K x y-K₀ x‖ₑ ∂μ
          ≤ ∫⁻ x in (ball (d.center i) (64*d.radius i))ᶜ,
              ‖K x y-K₀ x‖ₑ ∂μ := lintegral_mono_set hsubset
      _ = ∫⁻ x, ‖circleSignedKernelDifference (Finset.range (N+1))
            (signedKernelNaturalCoefficients N ε)
            (AddCircle.equivIoc (1:ℝ) (-1/2:ℝ) (d.center i-y) : ℝ)
            (x-d.center i)‖ₑ ∂
            (volume.restrict (ball (d.center i) (64*d.radius i))ᶜ) := by
              have heq : ∫⁻ x in (ball (d.center i) (64*d.radius i))ᶜ,
                    ‖K x y-K₀ x‖ₑ ∂volume =
                  ∫⁻ x in (ball (d.center i) (64*d.radius i))ᶜ,
                    ‖circleSignedKernelDifference (Finset.range (N+1))
                      (signedKernelNaturalCoefficients N ε)
                      (AddCircle.equivIoc (1:ℝ) (-1/2:ℝ) (d.center i-y) : ℝ)
                      (x-d.center i)‖ₑ ∂volume := by
                apply lintegral_congr
                intro x
                exact congrArg (fun z : ℂ => ‖z‖ₑ) (hkernelDifference y x)
              simpa [BrownianSharp.unitAddCircle_volume_eq_haar] using heq
      _ ≤ ENNReal.ofReal H := hfull
  have hKmeas (y : UnitAddCircle) : Measurable (fun x => ‖K x y-K₀ x‖ₑ) := by
    fun_prop
  have hdiffMeas : Measurable (fun p : UnitAddCircle × UnitAddCircle =>
      K p.1 p.2-K₀ p.1) := by
    fun_prop
  have hprod : AEMeasurable
      (fun p : UnitAddCircle × UnitAddCircle => ‖(K p.1 p.2-K₀ p.1)*b p.2‖ₑ)
      ((μ.restrict output).prod μ) := by
    have hbprod : AEStronglyMeasurable (fun p : UnitAddCircle × UnitAddCircle => b p.2)
        ((μ.restrict output).prod μ) := hb.aestronglyMeasurable.comp_snd
    exact (hdiffMeas.aemeasurable.mul hbprod.aemeasurable).enorm
  have hbound (x : UnitAddCircle) : Integrable (fun y => K x y*b y) μ := by
    exact circleSignedConvolutionOperator_integrand_integrable N ε hb x
  have hbound0 (x : UnitAddCircle) : Integrable (fun y => K₀ x*b y) μ := by
    exact hb.const_mul (K₀ x)
  change ∫⁻ x in output, ‖∫ y, K x y*b y ∂μ‖ₑ ∂μ ≤ _
  calc
    _ ≤ ENNReal.ofReal H * ∫⁻ y, ‖b y‖ₑ ∂μ :=
      lintegral_badConvolution_restrict_le_of_support μ μ output K K₀ b
        (ENNReal.ofReal H) hprod (hb.aestronglyMeasurable.enorm)
        hH' hzero hbound hbound0
    _ = _ := by rfl

/-- Summing all actual Whitney bad-piece convolutions preserves the same
uniform off-exception L¹ bound, with the source L¹ mass counted once. -/
theorem circle_badSeries_lintegral_outside_exception_le
    {Ω : Set UnitAddCircle} (d : CircleWhitneyPieceData Ω)
    (N : ℕ) (ε : Fin (N+1) → ℝ) (hε : ∀ s, |ε s| ≤ 1)
    {f : UnitAddCircle → ℂ}
    (hf : Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle))
    {H : ℝ}
    (hbad : ∀ (S : Finset ℕ) (coeff : ℕ → ℝ),
      (∀ s ∈ S, |coeff s| ≤ 1) → ∀ (center y : UnitAddCircle) (r : ℝ),
      0 ≤ r → y ∈ ball center (5*r) →
      ∫⁻ x, ‖circleSignedKernelDifference S coeff
        (AddCircle.equivIoc (1:ℝ) (-1/2:ℝ) (center-y) : ℝ) (x-center)‖ₑ ∂
        (volume.restrict (ball center (64*r))ᶜ) ≤ ENNReal.ofReal H) :
    let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
    ∫⁻ x in (circleWhitneyException d)ᶜ,
      ‖(fun x => ∑' i, circleSignedConvolutionOperator N ε
        (badPiece μ (d.piece i) f) x) x‖ₑ ∂μ ≤
      ENNReal.ofReal H * (2 * ∫⁻ y, ‖f y‖ₑ ∂μ) := by
  classical
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  let output : Set UnitAddCircle := (circleWhitneyException d)ᶜ
  let B : UnitAddCircle → ℂ := fun x => ∑' i,
    circleSignedConvolutionOperator N ε (badPiece μ (d.piece i) f) x
  have hpiece (i : d.Index) : Integrable (badPiece μ (d.piece i) f) μ :=
    integrable_badPiece μ (d.piece i) f (d.piece_measurable i) hf
  have hpieceBound (i : d.Index) :
      ∫⁻ x in output,
        ‖circleSignedConvolutionOperator N ε (badPiece μ (d.piece i) f) x‖ₑ ∂μ ≤
        ENNReal.ofReal H * ∫⁻ y, ‖badPiece μ (d.piece i) f y‖ₑ ∂μ :=
    circle_badPiece_lintegral_outside_exception_le d i N ε hε hf hbad
  have hTmeas (i : d.Index) :
      AEMeasurable (fun x => ‖circleSignedConvolutionOperator N ε
        (badPiece μ (d.piece i) f) x‖ₑ) (μ.restrict output) := by
    have hcont := circleSignedConvolutionOperator_continuous N ε (hpiece i)
    exact ((hcont.measurable.enorm).aemeasurable).mono_measure
      Measure.restrict_le_self
  have hseries : circleSignedConvolutionOperator N ε
      (badPieceSeries μ d.piece f) = B := by
    funext x
    exact circleSignedConvolutionOperator_badPieceSeries d.piece f
      d.piece_measurable d.piece_pairwiseDisjoint hf N ε x
  have hsource : ∑' i : d.Index,
      ∫⁻ y, ‖badPiece μ (d.piece i) f y‖ₑ ∂μ ≤
      2 * ∫⁻ y, ‖f y‖ₑ ∂μ :=
    tsum_lintegral_enorm_badPiece_le μ d.piece f d.piece_measurable
      d.piece_pairwiseDisjoint hf
  calc
    ∫⁻ x in output, ‖B x‖ₑ ∂μ ≤
        ∫⁻ x in output, ∑' i : d.Index,
          ‖circleSignedConvolutionOperator N ε
            (badPiece μ (d.piece i) f) x‖ₑ ∂μ := by
      apply lintegral_mono
      intro x
      exact enorm_tsum_le_tsum_enorm
    _ = ∑' i : d.Index, ∫⁻ x in output,
        ‖circleSignedConvolutionOperator N ε
          (badPiece μ (d.piece i) f) x‖ₑ ∂μ := lintegral_tsum hTmeas
    _ ≤ ∑' i : d.Index, ENNReal.ofReal H *
        ∫⁻ y, ‖badPiece μ (d.piece i) f y‖ₑ ∂μ := ENNReal.tsum_le_tsum hpieceBound
    _ = ENNReal.ofReal H * ∑' i : d.Index,
        ∫⁻ y, ‖badPiece μ (d.piece i) f y‖ₑ ∂μ := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal H * (2 * ∫⁻ y, ‖f y‖ₑ ∂μ) := by gcongr
    _ = _ := by rfl

/-- Uniform weak-(1,1) estimate for the actual finite signed smooth-resolution
convolution on the period-one circle. The constant is independent of depth
and of all signs. -/
theorem exists_circle_signed_convolution_weak_one :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (ε : Fin (N+1) → ℝ),
      (∀ s, |ε s| ≤ 1) → ∀ f : UnitAddCircle → ℂ,
      Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle) →
      ∀ t > 0,
        (AddCircle.haarAddCircle : Measure UnitAddCircle)
          {y | t < ‖circleSignedConvolutionOperator N ε f y‖} ≤
          ENNReal.ofReal (C/t) * ∫⁻ x,
            ENNReal.ofReal (‖f x‖) ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  obtain ⟨H, hH, hbad⟩ := exists_uniform_signedKernel_badPiece_lintegral
  let C : ℝ := 464 + 4*H
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro N ε hε f hf t ht
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  let I : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ∂μ
  let Ireal : ℝ := ∫ x, ‖f x‖ ∂μ
  have hIfin : I ≠ ∞ := by
    have hfi := hf.hasFiniteIntegral
    change I < ⊤ at hfi
    exact ne_of_lt hfi
  have hI : I = ENNReal.ofReal Ireal := by
    dsimp [I, Ireal, μ]
    exact (ofReal_integral_norm_eq_lintegral_enorm hf).symm
  have hIofRealNorm : I = ∫⁻ x, ENNReal.ofReal (‖f x‖) ∂μ := by
    dsimp [I]
    apply lintegral_congr
    intro x
    simp [enorm_eq_nnnorm, ofReal_norm]
  have hIreal_nonneg : 0 ≤ Ireal := integral_nonneg fun _ => norm_nonneg _
  have hfive : (5:ℝ≥0∞)*(ENNReal.ofReal t)⁻¹ = ENNReal.ofReal (5/t) := by
    rw [show (5:ℝ≥0∞) = ENNReal.ofReal (5:ℝ) by norm_num,
      ← ENNReal.ofReal_inv_of_pos ht]
    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 5)]
    congr 1
  have hcoeff : (∀ s, |ε s| ≤ 1) := hε
  by_cases hsmall : t ≤ 5*Ireal
  · have hC : 5 ≤ C := by dsimp [C]; nlinarith [hH]
    have hreal : 1 ≤ C*Ireal/t := by
      have hbase : 1 ≤ 5*Ireal/t := by
        rw [le_div_iff₀ ht]
        simpa using hsmall
      have hnum : 5*Ireal ≤ C*Ireal :=
        mul_le_mul_of_nonneg_right hC hIreal_nonneg
      exact hbase.trans (div_le_div_of_nonneg_right hnum ht.le)
    have hrhs : (1:ℝ≥0∞) ≤ ENNReal.ofReal (C/t) * I := by
      calc
        _ ≤ ENNReal.ofReal (C*Ireal/t) := by simpa using ENNReal.ofReal_le_ofReal hreal
        _ = ENNReal.ofReal (C/t) * I := by
          rw [hI, ← ENNReal.ofReal_mul (by positivity : 0 ≤ C/t)]
          congr 1
          ring
    have hprob : μ {y | t < ‖circleSignedConvolutionOperator N ε f y‖} ≤ 1 := by
      calc
        _ ≤ μ Set.univ := measure_mono (by intro x hx; exact Set.mem_univ x)
        _ = 1 := measure_univ
    have hmul : (1:ℝ≥0∞) ≤ ENNReal.ofReal (C/t)*I := by simpa [mul_one] using hrhs
    calc
      _ ≤ 1 := hprob
      _ ≤ ENNReal.ofReal (C/t)*I := hmul
      _ = ENNReal.ofReal (C/t) * ∫⁻ x, ENNReal.ofReal (‖f x‖) ∂μ := by rw [hIofRealNorm]
  · have hlarge : 5*Ireal < t := lt_of_not_ge hsmall
    have hbudget : (5:ℝ≥0∞) * (ENNReal.ofReal t)⁻¹ * I < 1 := by
      rw [hI, hfive, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 5/t)]
      have hratio_lt : (5/t)*Ireal < 1 := by
        have heq : (5/t)*Ireal = 5*Ireal/t := by ring
        rw [heq]
        exact (div_lt_one ht).2 hlarge
      have hh := (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ) < 1)).2 hratio_lt
      simpa using hh
    let Ω : Set UnitAddCircle := circleHighAverageSet f t
    have hΩne : Ω ≠ Set.univ := circleHighAverageSet_ne_univ_of_budget f ht hbudget
    let d : CircleWhitneyPieceData Ω := circleWhitneyPieceData Ω
      (isOpen_circleHighAverageSet f t) hΩne
    let E : d.Index → Set UnitAddCircle := d.piece
    let exception : Set UnitAddCircle := circleWhitneyException d
    let G : UnitAddCircle → ℂ :=
      circleSignedConvolutionOperator N ε (goodPart μ E f)
    let B : UnitAddCircle → ℂ := fun x => ∑' i,
      circleSignedConvolutionOperator N ε (badPiece μ (E i) f) x
    have hEmeas : ∀ i, MeasurableSet (E i) := d.piece_measurable
    have hdisj : Pairwise (fun i j => Disjoint (E i) (E j)) := d.piece_pairwiseDisjoint
    have hout : ∀ᵐ x ∂μ, x ∉ ⋃ i, E i → ‖f x‖ ≤ 12*t := by
      have houtΩ := ae_norm_le_of_notMem_circleHighAverageSet f hf ht
      filter_upwards [houtΩ] with x hx
      intro hxE
      have hxΩ : x ∉ Ω := by
        intro hxΩ
        have : x ∈ ⋃ i, E i := by simpa [E, d.piece_iUnion] using hxΩ
        exact hxE this
      exact le_trans (hx hxΩ) (by nlinarith [ht])
    have havg : ∀ i, ‖⨍ y in E i, f y ∂μ‖ ≤ 12*t := by
      intro i
      have hfvol : Integrable f (volume : Measure UnitAddCircle) := by
        simpa [BrownianSharp.unitAddCircle_volume_eq_haar] using hf
      have h := norm_circleHighAverage_piece_average_le f t (E i)
        (d.center i) (d.radius i) hfvol (d.piece_measurable i)
        (by simpa [d.core_eq_ball i] using d.core_subset_piece i)
        (by simpa [d.core_eq_ball i] using d.core_positive i)
        (d.radius_pos i) (le_of_lt ht)
        (d.piece_subset_five i) (d.contact i)
      simpa [setAverage_eq', μ, smul_eq_mul, Measure.real_def,
        abs_of_nonneg, inv_nonneg.mpr ENNReal.toReal_nonneg,
        BrownianSharp.unitAddCircle_volume_eq_haar] using h
    have hGmoment :
        (∫⁻ x, ENNReal.ofReal (‖G x‖^2) ∂μ) ≤
          ENNReal.ofReal (36*t) * I := by
      have h := goodPart_square_moment_le μ E f hEmeas hdisj hf
        (by positivity : 0 ≤ 12*t) havg hout
      have hLp := goodPart_memLp_two_of_average_bounds μ E f hEmeas hdisj hf havg hout
      have hstrong := circleSignedConvolutionOperator_lintegral_sq_le N ε hε hLp
      calc
        _ ≤ ∫⁻ x, ENNReal.ofReal (‖goodPart μ E f x‖^2) ∂μ := by
          simpa [G] using hstrong
        _ ≤ ENNReal.ofReal (36*t) * I := by
          simpa [I, show 3*(12*t)=36*t by ring] using h
    have hGint : Integrable (goodPart μ E f) μ :=
      goodPart_integrable μ E f hEmeas hdisj hf
    have hGmeas : AEStronglyMeasurable G μ := by
      exact (circleSignedConvolutionOperator_continuous N ε hGint).aestronglyMeasurable
    have hbadSeries :
        ∫⁻ x in exceptionᶜ, ‖B x‖ₑ ∂μ ≤ ENNReal.ofReal (2*H) * I := by
      calc
        _ ≤ ENNReal.ofReal H * (2*I) := by
          simpa [B, E, exception, I, μ] using
            circle_badSeries_lintegral_outside_exception_le d N ε hε hf hbad
        _ = ENNReal.ofReal (2*H) * I := by
          calc
            ENNReal.ofReal H * (2*I) = (ENNReal.ofReal H*2)*I := by ac_rfl
            _ = (ENNReal.ofReal H*ENNReal.ofReal (2:ℝ))*I := by norm_num
            _ = ENNReal.ofReal (H*2)*I := by
              rw [← ENNReal.ofReal_mul hH]
            _ = ENNReal.ofReal (2*H)*I := by congr 2; ring
    have hBmeas : AEStronglyMeasurable B μ := by
      let bsum := badPieceSeries μ E f
      have hbi : Integrable bsum μ := badPieceSeries_integrable μ E f hEmeas hdisj hf
      have hEq : circleSignedConvolutionOperator N ε bsum = B := by
        funext x
        exact circleSignedConvolutionOperator_badPieceSeries E f hEmeas hdisj hf N ε x
      rw [← hEq]
      exact (circleSignedConvolutionOperator_continuous N ε hbi).aestronglyMeasurable
    have hdecomp : ∀ x, circleSignedConvolutionOperator N ε f x = G x+B x := by
      have h := circleSignedConvolutionOperator_good_bad_decomposition E f hEmeas hdisj hf N ε
      intro x
      dsimp [G, B, μ]
      simpa only [Pi.add_apply] using congrFun h x
    have hEx : μ exception ≤ ENNReal.ofReal (320/t) * I := by
      calc
        _ ≤ ENNReal.ofReal 64 * μ Ω := circleWhitney_exception_measure_le d
        _ ≤ ENNReal.ofReal 64 *
            ((5:ENNReal)*(ENNReal.ofReal t)⁻¹*I) := by
              gcongr
              exact circleHighAverageSet_measure_le f ht
        _ = ENNReal.ofReal (320/t)*I := by
              rw [hfive]
              calc
                ENNReal.ofReal 64 * (ENNReal.ofReal (5/t) * I) =
                    (ENNReal.ofReal 64*ENNReal.ofReal (5/t))*I := by ac_rfl
                _ = ENNReal.ofReal (320/t)*I := by
                    rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 64)]
                    congr 1
                    field_simp
                    ring_nf
    have hEmeasurable : MeasurableSet exception := by
      dsimp [exception, circleWhitneyException]
      exact MeasurableSet.iUnion fun i => measurableSet_ball
    have hCbad : 0 ≤ 2*H := by positivity
    have hCgood : 0 ≤ (36:ℝ) := by norm_num
    have hCone : 0 ≤ (320:ℝ) := by norm_num
    have hclosure := weak_one_of_good_bad_bounds μ
      (circleSignedConvolutionOperator N ε f) G B exception hEmeasurable
      hGmeas hBmeas hdecomp ht hCone hCgood hCbad I hEx hGmoment hbadSeries
    have hconstant : (320+4*36+2*(2*H))/t = C/t := by
      dsimp [C]
      ring
    have hfinal := hclosure
    rw [hconstant] at hfinal
    simpa [μ, hIofRealNorm] using hfinal

end BrownianSharp.External.WeakCZ
