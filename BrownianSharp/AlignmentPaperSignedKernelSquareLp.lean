import BrownianSharp.AlignmentPaperSignedKernelOperator
import BrownianSharp.AlignmentPaperSquareFunctionRandomization
import BrownianSharp.AlignmentPaperHilbertRademacherLower
import Mathlib.Analysis.Convolution
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperSignedKernelSquareLp

open BrownianSharp.AlignmentPaperSignedKernelOperator
open BrownianSharp.AlignmentPaperSquareFunctionRandomization
open BrownianSharp.AlignmentPaperRademacherLower
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff

local instance circleMeasureSpace_squareLp : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance circleProbability_squareLp : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The actual smooth scalar dyadic block, applied to an arbitrary integrable
complex density on the circle. -/
def circleSmoothBlockConvolution (s : ℕ) (f : UnitAddCircle → ℂ)
    (x : UnitAddCircle) : ℂ :=
  ∫ y : UnitAddCircle,
    scalarBlockKernel smoothResolutionCutoff s (x-y) * f y
      ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)

private lemma circleSmoothBlockKernel_bdd (s : ℕ) :
    BddAbove (Set.range fun x : UnitAddCircle =>
      ‖scalarBlockKernel smoothResolutionCutoff s x‖) := by
  have hc : IsCompact
      ((fun x : UnitAddCircle => ‖scalarBlockKernel smoothResolutionCutoff s x‖) '' Set.univ) :=
    isCompact_univ.image (scalarBlockKernel smoothResolutionCutoff s).continuous.norm
  rw [← Set.image_univ]
  exact hc.bddAbove

private lemma circleSmoothBlockConvolution_integrand_integrable
    (s : ℕ) {f : UnitAddCircle → ℂ}
    (hf : Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (x : UnitAddCircle) :
    Integrable (fun y : UnitAddCircle =>
      scalarBlockKernel smoothResolutionCutoff s (x-y) * f y)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  rcases circleSmoothBlockKernel_bdd s with ⟨M,hM⟩
  apply hf.bdd_mul (by fun_prop)
  filter_upwards with y
  exact hM ⟨x-y,rfl⟩

lemma circleSmoothBlockConvolution_continuous (s : ℕ)
    {f : UnitAddCircle → ℂ}
    (hf : Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    Continuous (circleSmoothBlockConvolution s f) := by
  have hcont : Continuous (MeasureTheory.convolution f
      (scalarBlockKernel smoothResolutionCutoff s) (ContinuousLinearMap.mul ℂ ℂ)
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) := by
    exact BddAbove.continuous_convolution_right_of_integrable
      (ContinuousLinearMap.mul ℂ ℂ) (circleSmoothBlockKernel_bdd s) hf
      (scalarBlockKernel smoothResolutionCutoff s).continuous
  apply hcont.congr
  intro x
  simp only [MeasureTheory.convolution, circleSmoothBlockConvolution]
  congr 1
  ext y
  exact mul_comm _ _

lemma circleSignedConvolution_eq_sum_blocks
    (N : ℕ) (ε : Fin (N+1) → ℝ) {f : UnitAddCircle → ℂ}
    (hf : Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (x : UnitAddCircle) :
    circleSignedConvolutionOperator N ε f x =
      ∑ s : Fin (N+1), (ε s : ℂ) * circleSmoothBlockConvolution s.val f x := by
  simp only [circleSignedConvolutionOperator, circleSignedKernel,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  rw [show (fun y : UnitAddCircle =>
      (∑ s : Fin (N+1),
        (ε s : ℂ) * scalarBlockKernel smoothResolutionCutoff s.val (x-y)) * f y) =
      (fun y => ∑ s : Fin (N+1),
        ((ε s : ℂ) * scalarBlockKernel smoothResolutionCutoff s.val (x-y)) * f y) by
        ext y
        rw [Finset.sum_mul]]
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro s hs
    have hsInt := circleSmoothBlockConvolution_integrand_integrable s.val hf x
    simpa [circleSmoothBlockConvolution, smul_eq_mul, mul_assoc] using
      (hsInt.integral_smul (ε s : ℂ))
  · intro s hs
    have hsInt := circleSmoothBlockConvolution_integrand_integrable s.val hf x
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      hsInt.const_mul (ε s : ℂ)

/-- Conditional scalar dyadic square-function Lp bound. The only external
analytic input is the uniform weak-(1,1) estimate for the actual signed
smooth-resolution convolution, with constant `Cw`; this is supplied by the
Circle CZ leaf. -/
theorem circleSmoothSquareFunction_lintegral_lp_le_of_weak_one
    (N : ℕ) {Cw p : ℝ} (hCw : 0 ≤ Cw) (hp1 : 1 < p) (hp2 : p < 2)
    (hweak : ∀ (ε : Fin (N+1) → ℝ), (∀ s, |ε s| ≤ 1) →
      ∀ f, Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle) →
        ∀ t > 0,
          (AddCircle.haarAddCircle : Measure UnitAddCircle)
              {y | t < ‖circleSignedConvolutionOperator N ε f y‖} ≤
            ENNReal.ofReal (Cw/t) *
              ∫⁻ x, ENNReal.ofReal (‖f x‖)
                ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
    (f : Lp ℂ (ENNReal.ofReal p)
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    ∫⁻ x : UnitAddCircle,
      ENNReal.ofReal ((∑ s : Fin (N+1),
        ‖circleSmoothBlockConvolution s.val f x‖^2)^(p/2))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) ≤
      ENNReal.ofReal (24*(2:ℝ)^(p/2) *
        (2^p*(p*Cw/(p-1)+p/(2-p)))) *
      ∫⁻ x : UnitAddCircle, ENNReal.ofReal (‖f x‖^p)
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  let src : Fin (N+1) → UnitAddCircle → ℂ :=
    fun i x => if i = 0 then f x else 0
  have hfint : Integrable (fun x : UnitAddCircle => f x) μ := by
    exact (Lp.memLp f).integrable (by
      simpa using ENNReal.ofReal_le_ofReal hp1.le)
  have hsrc_meas : ∀ i, Measurable (src i) := by
    intro i
    dsimp [src]
    split_ifs with h
    · exact (Lp.stronglyMeasurable f).measurable
    · exact measurable_const
  have hblock_meas : ∀ i : Fin (N+1), Measurable (circleSmoothBlockConvolution i.val f) := by
    intro i
    exact (circleSmoothBlockConvolution_continuous i.val hfint).measurable
  have hsource_norm (x : UnitAddCircle) (ε : Fin (N+1) → Bool) :
      ‖complexSignRow (fun i => src i x) ε‖ = ‖f x‖ := by
    classical
    have hrow : complexSignRow (fun i => src i x) ε =
        (sign (ε 0) : ℂ) * f x := by
      simp [complexSignRow, src, Fin.sum_univ_succ]
    rw [hrow]
    by_cases h : ε 0 <;> simp [norm_mul, sign, h]
  have hsquare_source (x : UnitAddCircle) :
      (∑ i : Fin (N+1), ‖src i x‖^2)^(p/2) = ‖f x‖^p := by
    have hs : (∑ i : Fin (N+1), ‖src i x‖^2) = ‖f x‖^2 := by
      classical
      simp [src, Fin.sum_univ_succ]
    rw [hs]
    have hn : 0 ≤ ‖f x‖ := norm_nonneg _
    calc
      (‖f x‖^2)^(p/2) = (‖f x‖^(2:ℝ))^(p/2) := by
        simp [Real.rpow_natCast]
      _ = ‖f x‖^(2*(p/2)) :=
        (Real.rpow_mul hn 2 (p/2)).symm
      _ = ‖f x‖^p := by congr 1; ring
  have hbound : ∀ ε : Fin (N+1) → Bool,
      (∫⁻ y, ENNReal.ofReal
        (‖complexSignRow (fun i => circleSmoothBlockConvolution i.val f y) ε‖^p) ∂μ) ≤
        ENNReal.ofReal (2^p*(p*Cw/(p-1)+p/(2-p))) *
          (∫⁻ x, ENNReal.ofReal
            (‖complexSignRow (fun i => src i x) ε‖^p) ∂μ) := by
    intro ε
    let coeff : Fin (N+1) → ℝ := fun i => sign (ε i)
    have hcoeff : ∀ i, |coeff i| ≤ 1 := by
      intro i
      by_cases h : ε i <;> simp [coeff, sign, h, abs_of_nonneg]
    have hrow (y : UnitAddCircle) :
        complexSignRow (fun i => circleSmoothBlockConvolution i.val f y) ε =
          circleSignedConvolutionOperator N coeff f y := by
      rw [circleSignedConvolution_eq_sum_blocks N coeff hfint y]
      simp [complexSignRow, coeff, mul_comm]
    have hlp := circleSignedConvolutionOperator_lintegral_lp_le_of_weak_one
      N coeff hcoeff hCw hp1 hp2
      (by
        intro g hg t ht
        exact hweak coeff hcoeff g hg t ht) f
    have hleft : (∫⁻ y, ENNReal.ofReal
        (‖complexSignRow (fun i => circleSmoothBlockConvolution i.val f y) ε‖^p) ∂μ) =
        ∫⁻ y, ENNReal.ofReal
          (‖circleSignedConvolutionOperator N coeff f y‖^p) ∂μ := by
      apply lintegral_congr
      intro y
      rw [hrow y]
    have hright : (∫⁻ x, ENNReal.ofReal
        (‖complexSignRow (fun i => src i x) ε‖^p) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ := by
      apply lintegral_congr
      intro x
      rw [hsource_norm x ε]
    rw [hleft, hright]
    exact hlp
  have hsq := square_moment_le_of_signed_moments μ μ
    (fun i x => src i x)
    (fun i y => circleSmoothBlockConvolution i.val f y)
    hsrc_meas hblock_meas (p := p) (C := 2^p*(p*Cw/(p-1)+p/(2-p)))
    (by positivity) (by linarith) (by positivity) hbound
  have hsource : (∫⁻ x, ENNReal.ofReal
      ((∑ i : Fin (N+1), ‖src i x‖^2)^(p/2)) ∂μ) =
      ∫⁻ x, ENNReal.ofReal (‖f x‖^p) ∂μ := by
    apply lintegral_congr
    intro x
    rw [hsquare_source]
  rw [hsource] at hsq
  have hconst : (ENNReal.ofReal (24*(2:ℝ)^(p/2)) *
      ENNReal.ofReal (2^p*(p*Cw/(p-1)+p/(2-p)))) =
      ENNReal.ofReal (24*(2:ℝ)^(p/2) *
        (2^p*(p*Cw/(p-1)+p/(2-p)))) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
  rw [hconst] at hsq
  simpa [μ] using hsq

/-- The one-dimensional smooth square function is stable on finite Hilbert
families, with no loss depending on the family length. -/
theorem circleSmoothSquareFunction_vector_lintegral_lp_le_of_weak_one
    (N m : ℕ) {Cw p : ℝ} (hCw : 0 ≤ Cw) (hp1 : 1 < p) (hp2 : p < 2)
    (hweak : ∀ (ε : Fin (N+1) → ℝ), (∀ s, |ε s| ≤ 1) →
      ∀ f, Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle) →
        ∀ t > 0,
          (AddCircle.haarAddCircle : Measure UnitAddCircle)
              {y | t < ‖circleSignedConvolutionOperator N ε f y‖} ≤
            ENNReal.ofReal (Cw/t) *
              ∫⁻ x, ENNReal.ofReal (‖f x‖)
                ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
    (u : Fin m → Lp ℂ (ENNReal.ofReal p)
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    ∫⁻ x : UnitAddCircle, ENNReal.ofReal
      ((∑ i : Fin m, ∑ s : Fin (N+1),
        ‖circleSmoothBlockConvolution s.val (u i) x‖^2)^(p/2))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) ≤
      ENNReal.ofReal ((24*(2:ℝ)^(p/2))^2 *
        (2^p*(p*Cw/(p-1)+p/(2-p)))) *
      ∫⁻ x : UnitAddCircle, ENNReal.ofReal
        ((∑ i : Fin m, ‖u i x‖^2)^(p/2))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  classical
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  have huInt : ∀ i : Fin m, Integrable (fun x : UnitAddCircle => u i x) μ := by
    intro i
    exact (Lp.memLp (u i)).integrable (by
      simpa using ENNReal.ofReal_le_ofReal hp1.le)
  have huMeas : ∀ i : Fin m, Measurable (fun x : UnitAddCircle => u i x) := by
    intro i
    exact (Lp.stronglyMeasurable (u i)).measurable
  let src : Fin m → UnitAddCircle → ℂ := fun i x => u i x
  let out : Fin m → Fin (N+1) → UnitAddCircle → ℂ :=
    fun i s x => circleSmoothBlockConvolution s.val (u i) x
  have houtMeas : ∀ i s, Measurable (out i s) := by
    intro i s
    exact (circleSmoothBlockConvolution_continuous s.val (huInt i)).measurable
  have hblockLin : ∀ (δ : Fin m → Bool) (s : Fin (N+1)) (x : UnitAddCircle),
      circleSmoothBlockConvolution s.val
          (fun z => complexSignRow (fun i => u i z) δ) x =
        complexSignRow (fun i => out i s x) δ := by
    intro δ s x
    let a : Fin m → ℂ := fun i => (sign (δ i) : ℂ)
    have hsumInt : ∀ i : Fin m, Integrable
        (fun z : UnitAddCircle =>
          a i • (scalarBlockKernel smoothResolutionCutoff s.val (x-z) * u i z)) μ := by
      intro i
      exact (circleSmoothBlockConvolution_integrand_integrable s.val
        (huInt i) x).smul (a i)
    change (∫ z, scalarBlockKernel smoothResolutionCutoff s.val (x-z) *
        complexSignRow (fun i => u i z) δ ∂μ) = _
    have hrewrite (z : UnitAddCircle) :
        scalarBlockKernel smoothResolutionCutoff s.val (x-z) *
          complexSignRow (fun i => u i z) δ =
        ∑ i : Fin m, a i •
          (scalarBlockKernel smoothResolutionCutoff s.val (x-z) * u i z) := by
      simp [complexSignRow, a, Finset.mul_sum]
      ring
    rw [show (fun z : UnitAddCircle =>
        scalarBlockKernel smoothResolutionCutoff s.val (x-z) *
          complexSignRow (fun i => u i z) δ) =
        (fun z => ∑ i : Fin m, a i •
          (scalarBlockKernel smoothResolutionCutoff s.val (x-z) * u i z)) by
            funext z
            exact hrewrite z]
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro i hi
      have hiInt := circleSmoothBlockConvolution_integrand_integrable s.val
        (huInt i) x
      simpa [out, circleSmoothBlockConvolution, a, smul_eq_mul] using
        hiInt.integral_smul (a i)
    · intro i hi
      exact hsumInt i
  let Csf : ℝ := (24*(2:ℝ)^(p/2)) *
    (2^p*(p*Cw/(p-1)+p/(2-p)))
  let Kh : ℝ := 24*(2:ℝ)^(p/2)
  have hKnonneg : 0 ≤ Kh := by dsimp [Kh]; positivity
  have hCsf_nonneg : 0 ≤ Csf := by dsimp [Csf]; positivity
  have hbound : ∀ δ : Fin m → Bool,
      (∫⁻ x, ENNReal.ofReal
        ((∑ s : Fin (N+1),
          ‖complexSignRow (fun i => out i s x) δ‖^2)^(p/2)) ∂μ) ≤
        ENNReal.ofReal Csf *
          (∫⁻ x, ENNReal.ofReal
            (‖complexSignRow (fun i => src i x) δ‖^p) ∂μ) := by
    intro δ
    let v : Lp ℂ (ENNReal.ofReal p) μ :=
      ∑ i : Fin m, (sign (δ i) : ℂ) • u i
    have hv : (v : UnitAddCircle → ℂ) =ᵐ[μ]
        fun x => complexSignRow (fun i => src i x) δ := by
      have hsum : (v : UnitAddCircle → ℂ) =ᵐ[μ]
          fun x => ∑ i : Fin m, ((sign (δ i) : ℂ) • u i) x := by
        simpa [v] using Lp.coeFn_fun_finsetSum Finset.univ
          (fun i : Fin m => (sign (δ i) : ℂ) • u i)
      have hsmul : ∀ᵐ x ∂μ, ∀ i : Fin m,
          ((sign (δ i) : ℂ) • u i) x = (sign (δ i) : ℂ) * u i x := by
        filter_upwards [ae_all_iff.2 (fun i : Fin m => Lp.coeFn_smul
          (sign (δ i) : ℂ) (u i))] with x hx
        exact fun i => by simpa [smul_eq_mul] using hx i
      filter_upwards [hsum, hsmul] with x hx hterms
      simpa [complexSignRow, src] using hx.trans (by
        congr 1
        funext i
        exact hterms i)
    have hvint := (Lp.memLp v).integrable (by
      simpa using ENNReal.ofReal_le_ofReal hp1.le)
    have hsf := circleSmoothSquareFunction_lintegral_lp_le_of_weak_one
      N hCw hp1 hp2
      (by
        intro ε hε g hg t ht
        exact hweak ε hε g hg t ht) v
    have hrow (s : Fin (N+1)) (x : UnitAddCircle) :
        circleSmoothBlockConvolution s.val v x =
          complexSignRow (fun i => out i s x) δ := by
      calc
        circleSmoothBlockConvolution s.val v x =
            circleSmoothBlockConvolution s.val
              (fun z => complexSignRow (fun i => src i z) δ) x := by
                unfold circleSmoothBlockConvolution
                apply integral_congr_ae
                filter_upwards [hv] with z hz
                rw [hz]
        _ = complexSignRow (fun i => out i s x) δ := by
              simpa [src] using hblockLin δ s x
    have hleft : (∫⁻ x, ENNReal.ofReal
        ((∑ s : Fin (N+1),
          ‖complexSignRow (fun i => out i s x) δ‖^2)^(p/2)) ∂μ) =
        ∫⁻ x, ENNReal.ofReal
          ((∑ s : Fin (N+1),
            ‖circleSmoothBlockConvolution s.val v x‖^2)^(p/2)) ∂μ := by
      apply lintegral_congr
      intro x
      congr 2
      apply Finset.sum_congr rfl
      intro s hs
      rw [hrow s x]
    have hright : (∫⁻ x, ENNReal.ofReal
        (‖complexSignRow (fun i => src i x) δ‖^p) ∂μ) =
        ∫⁻ x, ENNReal.ofReal (‖v x‖^p) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
    rw [hleft, hright]
    have hsf' := hsf
    simpa [Csf] using hsf'
  have hpoint (x : UnitAddCircle) :
      ENNReal.ofReal ((∑ i : Fin m, ∑ s : Fin (N+1),
        ‖out i s x‖^2)^(p/2)) ≤
        ENNReal.ofReal Kh * finiteAverage
          (fun δ : Fin m → Bool => ENNReal.ofReal
            ((∑ s : Fin (N+1), ‖complexSignRow
              (fun i => out i s x) δ‖^2)^(p/2))) := by
    have h := AlignmentPaperHilbertRademacherLower.hilbertRow_lower_moment
      (fun i s => out i s x) (p := p) (by positivity) (by linarith)
    have hnonneg : ∀ δ : Fin m → Bool,
        0 ≤ (∑ s : Fin (N+1), ‖complexSignRow
          (fun i => out i s x) δ‖^2)^(p/2) := by
      intro δ
      exact Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) _
    have hsum : (∑ i : Fin m, ∑ s : Fin (N+1), ‖out i s x‖^2) =
        ∑ s : Fin (N+1), ∑ i : Fin m, ‖out i s x‖^2 := by
      rw [Finset.sum_comm]
    calc
      _ = ENNReal.ofReal ((∑ s : Fin (N+1),
          ∑ i : Fin m, ‖out i s x‖^2)^(p/2)) := by rw [hsum]
      _ ≤ ENNReal.ofReal (Kh * 𝔼 δ : Fin m → Bool,
          (∑ s : Fin (N+1), ‖complexSignRow
            (fun i => out i s x) δ‖^2)^(p/2)) :=
          ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal Kh * finiteAverage
          (fun δ : Fin m → Bool => ENNReal.ofReal
            ((∑ s : Fin (N+1), ‖complexSignRow
              (fun i => out i s x) δ‖^2)^(p/2))) := by
            rw [ENNReal.ofReal_mul hKnonneg,
              AlignmentPaperSquareFunctionRandomization.ofReal_expect _ hnonneg]
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal Kh * finiteAverage
        (fun δ : Fin m → Bool => ENNReal.ofReal
          ((∑ s : Fin (N+1), ‖complexSignRow
            (fun i => out i s x) δ‖^2)^(p/2))) ∂μ := by
      apply lintegral_mono
      intro x
      exact hpoint x
    _ = ENNReal.ofReal Kh * finiteAverage
        (fun δ : Fin m → Bool => ∫⁻ x, ENNReal.ofReal
          ((∑ s : Fin (N+1), ‖complexSignRow
            (fun i => out i s x) δ‖^2)^(p/2)) ∂μ) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        AlignmentPaperSquareFunctionRandomization.lintegral_finiteAverage μ _]
      · intro δ
        have hm : ∀ s : Fin (N+1), Measurable
            (fun x => complexSignRow (fun i => out i s x) δ) := by
          intro s
          dsimp [complexSignRow]
          fun_prop
        have hs : Measurable (fun x : UnitAddCircle =>
            ∑ s : Fin (N+1), ‖complexSignRow
              (fun i => out i s x) δ‖^2) := by
          fun_prop
        fun_prop
    _ ≤ ENNReal.ofReal Kh * finiteAverage
        (fun δ : Fin m → Bool => ENNReal.ofReal Csf *
          ∫⁻ x, ENNReal.ofReal (‖complexSignRow
            (fun i => src i x) δ‖^p) ∂μ) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact finiteAverage_mono hbound
    _ = (ENNReal.ofReal Kh * ENNReal.ofReal Csf) *
        finiteAverage (fun δ : Fin m → Bool => ∫⁻ x,
          ENNReal.ofReal (‖complexSignRow
            (fun i => src i x) δ‖^p) ∂μ) := by
      rw [finiteAverage_const_mul]
      ring
    _ ≤ (ENNReal.ofReal Kh * ENNReal.ofReal Csf) *
        ∫⁻ x, ENNReal.ofReal
          ((∑ i : Fin m, ‖src i x‖^2)^(p/2)) ∂μ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        finiteAverage (fun δ : Fin m → Bool => ∫⁻ x,
            ENNReal.ofReal (‖complexSignRow (fun i => src i x) δ‖^p) ∂μ) =
          ∫⁻ x, finiteAverage (fun δ : Fin m → Bool =>
            ENNReal.ofReal (‖complexSignRow (fun i => src i x) δ‖^p)) ∂μ := by
              symm
              rw [AlignmentPaperSquareFunctionRandomization.lintegral_finiteAverage μ _]
              intro δ
              dsimp [complexSignRow]
              fun_prop
        _ ≤ ∫⁻ x, ENNReal.ofReal
            ((∑ i : Fin m, ‖src i x‖^2)^(p/2)) ∂μ := by
              apply lintegral_mono
              intro x
              have h := complexSignRow_upper_moment
                (fun i => src i x) (p := p) (by linarith) (by linarith)
              calc
                finiteAverage (fun δ : Fin m → Bool =>
                    ENNReal.ofReal (‖complexSignRow (fun i => src i x) δ‖^p)) =
                  ENNReal.ofReal (𝔼 δ : Fin m → Bool,
                    ‖complexSignRow (fun i => src i x) δ‖^p) := by
                      symm
                      apply AlignmentPaperSquareFunctionRandomization.ofReal_expect
                      intro δ
                      exact Real.rpow_nonneg (norm_nonneg _) _
                _ ≤ ENNReal.ofReal
                    ((∑ i : Fin m, ‖src i x‖^2)^(p/2)) :=
                      ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (Kh*Csf) *
        ∫⁻ x, ENNReal.ofReal
          ((∑ i : Fin m, ‖src i x‖^2)^(p/2)) ∂μ := by
      rw [← ENNReal.ofReal_mul hKnonneg]
    _ = _ := by
      congr 1
      dsimp [Csf, Kh]
      ring

end BrownianSharp.AlignmentPaperSignedKernelSquareLp
