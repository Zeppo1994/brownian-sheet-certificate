import BrownianSharp.TrigonometricTensorExtraction
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.Fourier.PoissonSummation

/-!
# Smooth cutoff and kernel setup for Fourier block extraction

The cutoff is an explicit difference of two centered smooth bumps.  The
outer bump is one through radius `1` and supported in radius `3/2`; the inner
bump is one through radius `3/8` and supported in radius `1/2`.  Their
subtraction is therefore an even smooth annular cutoff equal to one on the
critical band.
-/

noncomputable section

open Set
open Filter
open MeasureTheory
open TopologicalSpace Asymptotics
open scoped ContDiff
open scoped Topology
open scoped FourierTransform ComplexInnerProductSpace
open scoped SchwartzMap
open scoped Convolution

namespace HaarQuarter.FourierExtractionKernel

set_option maxHeartbeats 500000

/-- Outer smooth bump, equal to one on `[-1,1]`, supported in `(-3/2,3/2)`. -/
def outerBump : ContDiffBump (0 : ℝ) := ⟨1, 3 / 2, by norm_num, by norm_num⟩

/-- Inner smooth bump, equal to one on `[-3/8,3/8]`, supported in `(-1/2,1/2)`. -/
def innerBump : ContDiffBump (0 : ℝ) := ⟨3 / 8, 1 / 2, by norm_num, by norm_num⟩

/-- Even smooth annular cutoff for the critical Fourier band. -/
def blockCutoff (u : ℝ) : ℝ := outerBump u - innerBump u

theorem blockCutoff_contDiff : ContDiff ℝ ∞ blockCutoff := by
  exact outerBump.contDiff.sub innerBump.contDiff

theorem blockCutoff_even (u : ℝ) : blockCutoff (-u) = blockCutoff u := by
  simp [blockCutoff, outerBump, innerBump, ContDiffBump.neg]

theorem blockCutoff_mem_Icc (u : ℝ) : blockCutoff u ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hu : |u| < 1 / 2
  · have ho : outerBump u = 1 := by
      apply outerBump.one_of_mem_closedBall
      have hnorm : |u| ≤ 1 := by linarith
      simpa [Metric.mem_closedBall, outerBump, Real.dist_eq] using hnorm
    rw [blockCutoff, ho]
    have h0 : 0 ≤ innerBump u := innerBump.nonneg (x := u)
    have h1 : innerBump u ≤ 1 := innerBump.le_one (x := u)
    constructor <;> nlinarith
  · have hi : innerBump u = 0 := by
      apply innerBump.zero_of_le_dist
      have hnorm : 1 / 2 ≤ |u| := le_of_not_gt hu
      simpa [innerBump, Real.dist_eq] using hnorm
    rw [blockCutoff, hi]
    constructor <;> nlinarith [outerBump.nonneg (x := u), outerBump.le_one (x := u)]

theorem blockCutoff_eq_one_of_mem_criticalBand {u : ℝ}
    (hu₁ : 1 / 2 ≤ |u|) (hu₂ : |u| ≤ 1) : blockCutoff u = 1 := by
  have ho : outerBump u = 1 := by
    apply outerBump.one_of_mem_closedBall
    simpa [Metric.mem_closedBall, outerBump, Real.dist_eq] using hu₂
  have hi : innerBump u = 0 := by
    apply innerBump.zero_of_le_dist
    have hnorm : 1 / 2 ≤ |u| := by linarith
    simpa [innerBump, Real.dist_eq] using hnorm
  simp [blockCutoff, ho, hi]

/-- The cutoff vanishes on a neighborhood of the origin. -/
theorem blockCutoff_eq_zero_of_abs_le_inner {u : ℝ} (hu : |u| ≤ 3 / 8) :
    blockCutoff u = 0 := by
  have ho : outerBump u = 1 := by
    apply outerBump.one_of_mem_closedBall
    have hnorm : |u| ≤ 1 := by linarith
    simpa [Metric.mem_closedBall, outerBump, Real.dist_eq] using hnorm
  have hi : innerBump u = 1 := by
    apply innerBump.one_of_mem_closedBall
    simpa [Metric.mem_closedBall, innerBump, Real.dist_eq] using hu
  simp [blockCutoff, ho, hi]

/-- The cutoff vanishes outside the outer bump's support radius. -/
theorem blockCutoff_eq_zero_of_outerRadius_le {u : ℝ} (hu : 3 / 2 ≤ |u|) :
    blockCutoff u = 0 := by
  have ho : outerBump u = 0 := by
    apply outerBump.zero_of_le_dist
    simpa [outerBump, Real.dist_eq] using hu
  have hi : innerBump u = 0 := by
    apply innerBump.zero_of_le_dist
    have hnorm : 1 / 2 ≤ |u| := by linarith
    simpa [innerBump, Real.dist_eq] using hnorm
  simp [blockCutoff, ho, hi]

/-- The scalar averaged-detail multiplier from the manuscript. -/
def detailMultiplier (u : ℝ) : ℝ :=
  Real.sinc (Real.pi * u / 2) ^ 2 - Real.sinc (Real.pi * u) ^ 2

/-- Away from zero the detail multiplier has its positive sine-fourth form. -/
theorem detailMultiplier_eq_sin_fourth {u : ℝ} (hu : u ≠ 0) :
    detailMultiplier u =
      Real.sin (Real.pi * u / 2) ^ 4 / (Real.pi * u / 2) ^ 2 := by
  let t : ℝ := Real.pi * u / 2
  have ht : t ≠ 0 := by dsimp [t]; positivity
  have h2t : 2 * t ≠ 0 := mul_ne_zero (by norm_num) ht
  have harg : Real.pi * u = 2 * t := by dsimp [t]; ring
  rw [detailMultiplier, show Real.pi * u / 2 = t by rfl, harg,
    Real.sinc_of_ne_zero ht, Real.sinc_of_ne_zero h2t, Real.sin_two_mul]
  have hs : Real.sin t ^ 2 + Real.cos t ^ 2 = 1 := Real.sin_sq_add_cos_sq t
  field_simp
  nlinarith [hs]

/-- The sinc-square difference is strictly positive on the multiplier support
annulus used by the extraction cutoff. -/
theorem detailMultiplier_pos_of_abs_lt_two {u : ℝ}
    (hlo : 0 < |u|) (hhi : |u| < 2) : 0 < detailMultiplier u := by
  have hu : u ≠ 0 := abs_pos.mp hlo
  have habs : 0 < |u| := hlo
  have htpos : 0 < Real.pi * |u| / 2 := by positivity
  have htlt : Real.pi * |u| / 2 < Real.pi := by
    nlinarith [mul_lt_mul_of_pos_left hhi Real.pi_pos]
  have hsin : 0 < Real.sin (Real.pi * |u| / 2) :=
    Real.sin_pos_of_mem_Ioo ⟨htpos, htlt⟩
  have hsinc : 0 < Real.sinc (Real.pi * |u| / 2) := by
    rw [Real.sinc_of_ne_zero]
    · exact div_pos hsin htpos
    · positivity
  have hformula : detailMultiplier u =
      Real.sin (Real.pi * u / 2) ^ 4 / (Real.pi * u / 2) ^ 2 :=
    detailMultiplier_eq_sin_fourth hu
  have hsinabs : Real.sin (Real.pi * u / 2) ≠ 0 := by
    intro hzero
    have harg : Real.pi * u / 2 = Real.pi * |u| / 2 ∨
        Real.pi * u / 2 = -(Real.pi * |u| / 2) := by
      rcases le_total 0 u with hu' | hu'
      · left
        rw [abs_of_nonneg hu']
      · right
        rw [abs_of_nonpos hu']
        ring
    rcases harg with harg | harg
    · rw [harg] at hzero
      exact ne_of_gt hsin hzero
    · rw [harg, Real.sin_neg] at hzero
      linarith
  rw [hformula]
  have hden : 0 < (Real.pi * u / 2) ^ 2 := sq_pos_of_ne_zero (by positivity)
  have hnum : 0 < Real.sin (Real.pi * u / 2) ^ 4 := by positivity
  exact div_pos hnum hden

/-- Smooth annular quotient symbol: on the open annulus where the detail
multiplier is nonzero it is the cutoff divided by that multiplier, and it is
extended by zero outside. -/
def blockQuotientSymbol (u : ℝ) : ℝ :=
  if 1 / 4 < |u| ∧ |u| < 7 / 4 then
    blockCutoff u * ((Real.pi * u / 2) ^ 2 / Real.sin (Real.pi * u / 2) ^ 4)
  else 0

def blockRawQuotientSymbol (u : ℝ) : ℝ :=
  blockCutoff u * ((Real.pi * u / 2) ^ 2 / Real.sin (Real.pi * u / 2) ^ 4)

def blockQuotientAnnulus : Set ℝ := {u | 1 / 4 < |u| ∧ |u| < 7 / 4}

theorem isOpen_blockQuotientAnnulus : IsOpen blockQuotientAnnulus := by
  have h1 : IsOpen {u : ℝ | 1 / 4 < |u|} := isOpen_Ioi.preimage continuous_abs
  have h2 : IsOpen {u : ℝ | |u| < 7 / 4} := isOpen_Iio.preimage continuous_abs
  convert h1.inter h2 using 1 <;> ext u <;> simp [blockQuotientAnnulus]

theorem blockQuotient_sin_ne_zero {u : ℝ} (hu₁ : 0 < |u|) (hu₂ : |u| < 2) :
    Real.sin (Real.pi * u / 2) ≠ 0 := by
  have hpos := detailMultiplier_pos_of_abs_lt_two hu₁ hu₂
  have hu : u ≠ 0 := abs_pos.mp hu₁
  rw [detailMultiplier_eq_sin_fourth hu] at hpos
  intro hz
  simp [hz] at hpos

theorem blockRawQuotientSymbol_contDiffAt {u : ℝ}
    (hu₁ : 0 < |u|) (hu₂ : |u| < 2) :
    ContDiffAt ℝ ∞ blockRawQuotientSymbol u := by
  have hs : ContDiffAt ℝ ∞ (fun x : ℝ => Real.sin (Real.pi * x / 2)) u := by fun_prop
  have hsin := blockQuotient_sin_ne_zero hu₁ hu₂
  have hden : Real.sin (Real.pi * u / 2) ^ 4 ≠ 0 := pow_ne_zero _ hsin
  unfold blockRawQuotientSymbol
  have hc : ContDiffAt ℝ ∞ blockCutoff u := blockCutoff_contDiff.contDiffAt
  fun_prop (disch := exact hden)

theorem blockQuotientSymbol_contDiffAt (u : ℝ) :
    ContDiffAt ℝ ∞ blockQuotientSymbol u := by
  by_cases hu : u ∈ blockQuotientAnnulus
  · have hu₁ : 0 < |u| := lt_trans (by norm_num : (0 : ℝ) < 1 / 4) hu.1
    have hu₂ : |u| < 2 := lt_trans hu.2 (by norm_num : (7 / 4 : ℝ) < 2)
    have hraw := blockRawQuotientSymbol_contDiffAt hu₁ hu₂
    apply hraw.congr_of_eventuallyEq
    filter_upwards [isOpen_blockQuotientAnnulus.mem_nhds hu] with v hv
    change 1 / 4 < |v| ∧ |v| < 7 / 4 at hv
    rw [blockQuotientSymbol, if_pos hv, blockRawQuotientSymbol]
  · have hlocal : blockQuotientSymbol =ᶠ[𝓝 u] fun _ : ℝ => 0 := by
      by_cases hlo : |u| ≤ 1 / 4
      · have hnear : ∀ᶠ v in 𝓝 u, |v| < 3 / 8 :=
          continuous_abs.continuousAt.eventually (Iio_mem_nhds (by linarith))
        filter_upwards [hnear] with v hv
        by_cases hV : v ∈ blockQuotientAnnulus
        · change 1 / 4 < |v| ∧ |v| < 7 / 4 at hV
          rw [blockQuotientSymbol, if_pos hV]
          simp [blockCutoff_eq_zero_of_abs_le_inner (by linarith : |v| ≤ 3 / 8)]
        · change ¬ (1 / 4 < |v| ∧ |v| < 7 / 4) at hV
          rw [blockQuotientSymbol, if_neg hV]
      · have hlow : 1 / 4 < |u| := lt_of_not_ge hlo
        have hnot : ¬ |u| < 7 / 4 := by
          intro hhi
          exact hu ⟨hlow, hhi⟩
        have hhi : 7 / 4 ≤ |u| := le_of_not_gt hnot
        have hnear : ∀ᶠ v in 𝓝 u, 3 / 2 < |v| :=
          continuous_abs.continuousAt.eventually (Ioi_mem_nhds (by linarith))
        filter_upwards [hnear] with v hv
        by_cases hV : v ∈ blockQuotientAnnulus
        · change 1 / 4 < |v| ∧ |v| < 7 / 4 at hV
          rw [blockQuotientSymbol, if_pos hV]
          simp [blockCutoff_eq_zero_of_outerRadius_le (by linarith : 3 / 2 ≤ |v|)]
        · change ¬ (1 / 4 < |v| ∧ |v| < 7 / 4) at hV
          rw [blockQuotientSymbol, if_neg hV]
    exact contDiffAt_const.congr_of_eventuallyEq hlocal

theorem blockQuotientSymbol_contDiff : ContDiff ℝ ∞ blockQuotientSymbol := by
  rw [contDiff_iff_contDiffAt]
  exact fun u => blockQuotientSymbol_contDiffAt u

theorem blockQuotientSymbol_zero_of_outer_support {u : ℝ} (hu : 7 / 4 ≤ |u|) :
    blockQuotientSymbol u = 0 := by
  have hU : ¬ (1 / 4 < |u| ∧ |u| < 7 / 4) := by
    rintro ⟨_, h⟩
    linarith
  rw [blockQuotientSymbol, if_neg hU]

theorem blockQuotientSymbol_hasCompactSupport : HasCompactSupport blockQuotientSymbol := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℝ) (7 / 4 : ℝ))
  apply Function.support_subset_iff'.2
  intro u hu
  have hnot : ¬ dist u 0 ≤ (7 / 4 : ℝ) := by
    simpa [Metric.mem_closedBall] using hu
  have hrad' : 7 / 4 < dist u 0 := lt_of_not_ge hnot
  have hrad : 7 / 4 ≤ |u| := by simpa [Real.dist_eq] using hrad'.le
  exact blockQuotientSymbol_zero_of_outer_support hrad

def blockQuotientSymbolComplex (u : ℝ) : ℂ := blockQuotientSymbol u

theorem blockQuotientSymbolComplex_contDiff :
    ContDiff ℝ ∞ blockQuotientSymbolComplex := by
  exact Complex.ofRealCLM.contDiff.comp blockQuotientSymbol_contDiff

theorem blockQuotientSymbolComplex_hasCompactSupport :
    HasCompactSupport blockQuotientSymbolComplex := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ℝ) (7 / 4 : ℝ))
  apply Function.support_subset_iff'.2
  intro u hu
  have hnot : ¬ dist u 0 ≤ (7 / 4 : ℝ) := by
    simpa [Metric.mem_closedBall] using hu
  have hrad' : 7 / 4 < dist u 0 := lt_of_not_ge hnot
  have hrad : 7 / 4 ≤ |u| := by simpa [Real.dist_eq] using hrad'.le
  simp [blockQuotientSymbolComplex, blockQuotientSymbol_zero_of_outer_support hrad]

/-- Schwartz extension of the explicitly constructed quotient symbol. -/
def blockQuotientSchwartz : 𝓢(ℝ, ℂ) :=
  blockQuotientSymbolComplex_hasCompactSupport.toSchwartzMap
    blockQuotientSymbolComplex_contDiff

/-- The inverse Fourier transform is a genuine integrable Schwartz kernel. -/
def inverseFourierBlockKernel : 𝓢(ℝ, ℂ) := 𝓕⁻ blockQuotientSchwartz

theorem inverseFourierBlockKernel_integrable :
    Integrable (inverseFourierBlockKernel : ℝ → ℂ) := by
  exact inverseFourierBlockKernel.integrable

/-- Circle convolution with Haar probability measure. -/
def circleConvolution (K A : AddCircle (1 : ℝ) → ℂ) : AddCircle (1 : ℝ) → ℂ :=
  K ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] A

/-- Convolution by a continuous circle kernel acts diagonally on each actual
continuous-circle character. -/
theorem circleConvolution_fourier (K : C(AddCircle (1 : ℝ), ℂ))
    (n : ℤ) (x : AddCircle (1 : ℝ)) :
    circleConvolution K (fourier n) x = fourierCoeff K n * fourier n x := by
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have hvol : (volume : Measure (AddCircle (1 : ℝ))) =
      AddCircle.haarAddCircle (T := (1 : ℝ)) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  have hphase (y : AddCircle (1 : ℝ)) :
      fourier n (x - y) = fourier n x * fourier (-n) y := by
    calc
      fourier n (x - y) = AddCircle.toCircle (n • (x - y) :) := rfl
      _ = AddCircle.toCircle (n • x :) * AddCircle.toCircle (n • -y :) := by
        rw [sub_eq_add_neg, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
      _ = fourier n x * fourier (-n) y := by
        simp [fourier_apply, neg_smul]
  rw [circleConvolution, hvol]
  calc
    (∫ y, K y * fourier n (x - y) ∂AddCircle.haarAddCircle) =
        fourier n x * ∫ y, fourier (-n) y * K y ∂AddCircle.haarAddCircle := by
          calc
            _ = ∫ y, fourier n x * (fourier (-n) y * K y) ∂AddCircle.haarAddCircle := by
              apply integral_congr_ae
              filter_upwards with y
              rw [hphase]
              ring
            _ = fourier n x * ∫ y, fourier (-n) y * K y ∂AddCircle.haarAddCircle := by
              rw [integral_const_mul]
    _ = fourierCoeff K n * fourier n x := by
      rw [show fourierCoeff K n = ∫ y, fourier (-n) y * K y ∂AddCircle.haarAddCircle by
        simp [fourierCoeff, smul_eq_mul]]
      ring

/-- A genuine finite Fourier polynomial on the continuous unit circle. -/
def finiteCircleFourierPolynomial (s : Finset ℤ) (a : ℤ → ℂ) :
    C(UnitAddCircle, ℂ) :=
  ∑ n ∈ s, a n • fourier n

/-- Convolution by a continuous circle kernel acts on a finite Fourier
polynomial by multiplying each mode by the corresponding Fourier
coefficient of the kernel. -/
theorem circleConvolution_finiteFourierPolynomial
    (K : C(UnitAddCircle, ℂ)) (s : Finset ℤ) (a : ℤ → ℂ)
    (x : UnitAddCircle) :
    circleConvolution K (finiteCircleFourierPolynomial s a) x =
      ∑ n ∈ s, (a n * fourierCoeff K n) * fourier n x := by
  classical
  have hterm (n : ℤ) (hn : n ∈ s) :
      Integrable (fun y : UnitAddCircle =>
        K y * (a n * fourier n (x - y))) volume := by
    have hc : Continuous (fun y : UnitAddCircle =>
        K y * (a n * fourier n (x - y))) := by fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [circleConvolution, convolution_mul]
  simp only [finiteCircleFourierPolynomial, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum s hterm]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    (∫ y : UnitAddCircle, K y * (a n * fourier n (x - y)) ∂volume) =
        a n * ∫ y : UnitAddCircle, K y * fourier n (x - y) ∂volume := by
          calc
            _ = ∫ y : UnitAddCircle, a n * (K y * fourier n (x - y)) ∂volume := by
              apply integral_congr_ae
              filter_upwards with y
              ring
            _ = _ := integral_const_mul _ _
    _ = (a n * fourierCoeff K n) * fourier n x := by
      have hconv : (∫ y : UnitAddCircle,
          K y * fourier n (x - y) ∂volume) =
          circleConvolution K (fourier n) x := by
        rw [circleConvolution, convolution_mul]
      rw [hconv, circleConvolution_fourier]
      ring

/-- Young's L¹ bound on the circle, proved directly by norm-integral, Fubini,
and Haar translation invariance. -/
theorem circleConvolution_L1_le (K A : C(AddCircle (1 : ℝ), ℂ)) :
    (∫ x, ‖circleConvolution K A x‖ ∂volume) ≤
      (∫ x, ‖K x‖ ∂volume) * (∫ x, ‖A x‖ ∂volume) := by
  let G := AddCircle (1 : ℝ)
  have hK : Integrable (K : G → ℂ) volume :=
    K.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace K)
  have hA : Integrable (A : G → ℂ) volume :=
    A.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace A)
  have hconv : Integrable (circleConvolution K A) volume := by
    exact hK.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hA
  have hprod : Integrable
      (fun p : G × G => ‖K p.2‖ * ‖A (p.1 - p.2)‖) (volume.prod volume) := by
    have hcont : Continuous (fun p : G × G => ‖K p.2‖ * ‖A (p.1 - p.2)‖) := by
      fun_prop
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hH : Integrable (fun x : G => ∫ y, ‖K y‖ * ‖A (x - y)‖ ∂volume) volume := by
    exact hprod.integral_prod_left
  have hpoint (x : G) :
      ‖circleConvolution K A x‖ ≤ ∫ y, ‖K y‖ * ‖A (x - y)‖ ∂volume := by
    rw [circleConvolution]
    calc
      ‖∫ y, K y * A (x - y) ∂volume‖ ≤ ∫ y, ‖K y * A (x - y)‖ ∂volume :=
        norm_integral_le_integral_norm _
      _ = ∫ y, ‖K y‖ * ‖A (x - y)‖ ∂volume := by simp_rw [norm_mul]
  calc
    _ ≤ ∫ x, ∫ y, ‖K y‖ * ‖A (x - y)‖ ∂volume ∂volume :=
      integral_mono hconv.norm hH hpoint
    _ = ∫ y, ∫ x, ‖K y‖ * ‖A (x - y)‖ ∂volume ∂volume :=
      integral_integral_swap hprod
    _ = ∫ y, ‖K y‖ * (∫ x, ‖A x‖ ∂volume) ∂volume := by
      apply integral_congr_ae
      filter_upwards with y
      rw [integral_const_mul]
      congr 1
      rw [← integral_add_left_eq_self (-y) (f := fun x : G => ‖A x‖)]
      apply integral_congr_ae
      filter_upwards with x
      congr 1
      simp [sub_eq_add_neg, add_comm]
    _ = (∫ x, ‖K x‖ ∂volume) * (∫ x, ‖A x‖ ∂volume) := by
      rw [integral_mul_const]

/-- Real-line dilation of the inverse Fourier Schwartz kernel, normalized so
its Fourier transform samples the quotient at frequencies divided by `m`. -/
def scaledInverseKernelSchwartz (m : ℝ) (hm : m ≠ 0) : 𝓢(ℝ, ℂ) :=
  (m : ℂ) • (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 m hm)) inverseFourierBlockKernel)

@[simp] theorem scaledInverseKernelSchwartz_apply (m : ℝ) (hm : m ≠ 0) (x : ℝ) :
    scaledInverseKernelSchwartz m hm x = (m : ℂ) * inverseFourierBlockKernel (m * x) := by
  simp [scaledInverseKernelSchwartz, Units.smul_def, smul_eq_mul]

/-- The scaled inverse kernel has precisely the desired sampled Fourier
symbol. -/
theorem fourier_scaledInverseKernelSchwartz (m : ℝ) (hm : 0 < m) (ξ : ℝ) :
    𝓕 (scaledInverseKernelSchwartz m hm.ne') ξ = blockQuotientSchwartz (ξ / m) := by
  rw [SchwartzMap.fourier_coe]
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp_rw [smul_eq_mul]
  simp_rw [scaledInverseKernelSchwartz_apply]
  let g : ℝ → ℂ := fun y =>
    Complex.exp (↑(-2 * Real.pi * y * (ξ / m)) * Complex.I) * inverseFourierBlockKernel y
  have hchange := Measure.integral_comp_mul_left g m
  have hkernel (x : ℝ) :
      Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) *
          ((m : ℂ) * inverseFourierBlockKernel (m * x)) =
        (m : ℂ) * g (m * x) := by
    dsimp [g]
    have hphase :
        Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) =
          Complex.exp (↑(-2 * Real.pi * (m * x) * (ξ / m)) * Complex.I) := by
      congr 1
      push_cast
      field_simp [hm.ne']
    rw [hphase]
    ring
  calc
    (∫ x : ℝ, Complex.exp (↑(-2 * Real.pi * x * ξ) * Complex.I) *
        ((m : ℂ) * inverseFourierBlockKernel (m * x))) =
      (m : ℂ) * ∫ x : ℝ, g (m * x) := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hkernel), integral_const_mul]
    _ = (m : ℂ) * ((m : ℝ)⁻¹ • ∫ y : ℝ, g y) := by
        rw [hchange, abs_of_pos (inv_pos.mpr hm)]
    _ = ∫ y : ℝ, g y := by
        change (m : ℂ) * ((m : ℝ)⁻¹ • (∫ y : ℝ, g y)) = ∫ y : ℝ, g y
        rw [Complex.real_smul, Complex.ofReal_inv]
        have hcancel : (m : ℂ) * (m : ℂ)⁻¹ = 1 :=
          mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hm.ne')
        calc
          (m : ℂ) * ((m : ℂ)⁻¹ * (∫ y : ℝ, g y)) =
              ((m : ℂ) * (m : ℂ)⁻¹) * (∫ y : ℝ, g y) := by ring
          _ = ∫ y : ℝ, g y := by rw [hcancel, one_mul]
    _ = 𝓕 (inverseFourierBlockKernel : ℝ → ℂ) (ξ / m) := by
        rw [Real.fourier_real_eq_integral_exp_smul]
        simp only [smul_eq_mul]
        dsimp [g]
    _ = blockQuotientSchwartz (ξ / m) := by
        change (𝓕 (inverseFourierBlockKernel : ℝ → ℂ)) (ξ / m) = _
        change (𝓕 ((𝓕⁻ blockQuotientSchwartz : 𝓢(ℝ, ℂ)) : ℝ → ℂ)) (ξ / m) = _
        rw [← SchwartzMap.fourier_coe]
        exact congrFun (congrArg (fun f : 𝓢(ℝ, ℂ) => (f : ℝ → ℂ))
          (FourierTransform.fourier_fourierInv_eq blockQuotientSchwartz)) (ξ / m)

/-- Poisson summation periodizes the actual scaled real-line inverse kernel
and gives exactly the sampled smooth block symbol on the continuous circle. -/
theorem periodization_eq_blockFourierSeries (m : ℝ) (hm : 0 < m) (x : ℝ) :
    ∑' n : ℤ, scaledInverseKernelSchwartz m hm.ne' (x + n) =
      ∑' n : ℤ, blockQuotientSchwartz ((n : ℝ) / m) *
        fourier n (x : UnitAddCircle) := by
  simpa only [fourier_scaledInverseKernelSchwartz m hm] using
    (SchwartzMap.tsum_eq_tsum_fourier (scaledInverseKernelSchwartz m hm.ne') x)

/-- The sampled compactly supported block symbol has only finitely many
nonzero integer frequencies at each positive scale. -/
theorem sampledBlockSymbol_support_finite (m : ℝ) (hm : 0 < m) :
    {n : ℤ | blockQuotientSchwartz ((n : ℝ) / m) ≠ 0}.Finite := by
  let N : ℕ := Nat.ceil (2 * m + 2)
  apply (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset
  intro n hn
  have hlt : |(n : ℝ) / m| < 7 / 4 := by
    by_contra hnot
    have hrad : 7 / 4 ≤ |(n : ℝ) / m| := le_of_not_gt hnot
    have hz : blockQuotientSchwartz ((n : ℝ) / m) = 0 := by
      change blockQuotientSymbolComplex ((n : ℝ) / m) = 0
      simp [blockQuotientSymbolComplex,
        blockQuotientSymbol_zero_of_outer_support hrad]
    exact hn hz
  have habs : |(n : ℝ)| ≤ 7 * m / 4 := by
    have hlt' : |(n : ℝ)| / m < 7 / 4 := by
      simpa [abs_div, abs_of_pos hm] using hlt
    have hmul : |(n : ℝ)| < (7 / 4) * m := (div_lt_iff₀ hm).mp hlt'
    nlinarith
  have hceil : 2 * m + 2 ≤ (N : ℝ) := by
    dsimp [N]
    exact_mod_cast (Nat.le_ceil (2 * m + 2))
  have hbound : |(n : ℝ)| ≤ (N : ℝ) := by nlinarith
  have hnabs : |n| ≤ N := by exact_mod_cast hbound
  have hnlo : -(N : ℤ) ≤ n := (abs_le.mp hnabs).1
  have hnhi : n ≤ (N : ℤ) := (abs_le.mp hnabs).2
  exact ⟨hnlo, hnhi⟩

/-- The finite frequency support of the smooth block kernel at scale `m`. -/
def sampledBlockSupport (m : ℝ) (hm : 0 < m) : Finset ℤ :=
  (sampledBlockSymbol_support_finite m hm).toFinset

/-- The continuous circle kernel whose Fourier coefficients are the sampled
smooth quotient symbol. -/
def circleBlockKernel (m : ℝ) (hm : 0 < m) : C(UnitAddCircle, ℂ) :=
  ∑ n ∈ sampledBlockSupport m hm,
    blockQuotientSchwartz ((n : ℝ) / m) • fourier n

/-- The actual periodized inverse Fourier kernel agrees pointwise with the
continuous circle kernel, by Poisson summation and compact symbol support. -/
theorem periodization_eq_circleBlockKernel (m : ℝ) (hm : 0 < m) (x : ℝ) :
    ∑' n : ℤ, scaledInverseKernelSchwartz m hm.ne' (x + n) =
      circleBlockKernel m hm (x : UnitAddCircle) := by
  rw [periodization_eq_blockFourierSeries m hm x]
  rw [tsum_eq_sum (s := sampledBlockSupport m hm)]
  · simp [circleBlockKernel, smul_eq_mul]
  · intro n hn
    have hq : blockQuotientSchwartz ((n : ℝ) / m) = 0 := by
      by_contra hq
      exact hn (by simp [sampledBlockSupport, hq])
    simp [hq]

/-- The translates of the scaled Schwartz kernel form a summable series in
the compact-open topology, so their periodization is a genuine continuous map. -/
theorem scaledKernel_translateSeries_summable (m : ℝ) (hm : 0 < m) :
    Summable (fun n : ℤ =>
      (⟨(scaledInverseKernelSchwartz m hm.ne' : ℝ → ℂ),
        (scaledInverseKernelSchwartz m hm.ne').continuous⟩ : C(ℝ, ℂ)).comp
          (ContinuousMap.addRight n)) := by
  let f : C(ℝ, ℂ) :=
    ⟨(scaledInverseKernelSchwartz m hm.ne' : ℝ → ℂ),
      (scaledInverseKernelSchwartz m hm.ne').continuous⟩
  have hf : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
    simpa [f] using
      (scaledInverseKernelSchwartz m hm.ne').isBigO_cocompact_rpow (-2)
  have hnorm : ∀ K : Compacts ℝ,
      Summable fun n : ℤ => ‖(f.comp (ContinuousMap.addRight n)).restrict K‖ := by
    intro K
    apply summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : 1 < (2 : ℝ)))
    exact Asymptotics.IsBigO.comp_tendsto
      (isBigO_norm_restrict_cocompact f (by norm_num : 0 < (2 : ℝ)) hf K)
      Int.tendsto_coe_cofinite
  simpa [f] using ContinuousMap.summable_of_locally_summable_norm hnorm

/-- The translates of the pointwise norm also converge locally uniformly. -/
theorem scaledKernel_normTranslateSeries_summable (m : ℝ) (hm : 0 < m) :
    Summable (fun n : ℤ =>
      (⟨(fun x : ℝ => ‖scaledInverseKernelSchwartz m hm.ne' x‖),
        continuous_norm.comp (scaledInverseKernelSchwartz m hm.ne').continuous⟩ :
          C(ℝ, ℝ)).comp (ContinuousMap.addRight n)) := by
  let f : C(ℝ, ℂ) :=
    ⟨(scaledInverseKernelSchwartz m hm.ne' : ℝ → ℂ),
      (scaledInverseKernelSchwartz m hm.ne').continuous⟩
  let g : C(ℝ, ℝ) := ⟨fun x => ‖f x‖, continuous_norm.comp f.continuous⟩
  have hf : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
    simpa [f] using (scaledInverseKernelSchwartz m hm.ne').isBigO_cocompact_rpow (-2)
  have hg : g =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
    simpa [g] using hf.norm_norm
  have hnorm : ∀ K : Compacts ℝ,
      Summable fun n : ℤ => ‖(g.comp (ContinuousMap.addRight n)).restrict K‖ := by
    intro K
    apply summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : 1 < (2 : ℝ)))
    exact Asymptotics.IsBigO.comp_tendsto
      (isBigO_norm_restrict_cocompact g (by norm_num : 0 < (2 : ℝ)) hg K)
      Int.tendsto_coe_cofinite
  simpa [f, g] using ContinuousMap.summable_of_locally_summable_norm hnorm

/-- The continuous real-line periodization of the Schwartz kernel. -/
def scaledKernelPeriodization (m : ℝ) (hm : 0 < m) : C(ℝ, ℂ) :=
  ∑' n : ℤ,
    (⟨(scaledInverseKernelSchwartz m hm.ne' : ℝ → ℂ),
      (scaledInverseKernelSchwartz m hm.ne').continuous⟩ : C(ℝ, ℂ)).comp
        (ContinuousMap.addRight n)

/-- Its periodic lift is the genuine continuous circle kernel. -/
def scaledKernelCirclePeriodization (m : ℝ) (hm : 0 < m) :
    C(UnitAddCircle, ℂ) :=
  let f : C(ℝ, ℂ) :=
    ⟨(scaledInverseKernelSchwartz m hm.ne' : ℝ → ℂ),
      (scaledInverseKernelSchwartz m hm.ne').continuous⟩
  ⟨(f.periodic_tsum_comp_add_zsmul 1).lift,
    continuous_coinduced_dom.mpr (map_continuous _)⟩

/-- On every real lift, the continuous periodization is the Poisson kernel
whose Fourier coefficients are the smooth block symbol. -/
theorem scaledKernelCirclePeriodization_apply (m : ℝ) (hm : 0 < m) (x : ℝ) :
    scaledKernelCirclePeriodization m hm (x : UnitAddCircle) =
      circleBlockKernel m hm (x : UnitAddCircle) := by
  simp only [scaledKernelCirclePeriodization, ContinuousMap.coe_mk,
    Function.Periodic.lift_coe]
  simp only [zsmul_one]
  change (∑' n : ℤ,
    (⟨(scaledInverseKernelSchwartz m hm.ne' : ℝ → ℂ),
      (scaledInverseKernelSchwartz m hm.ne').continuous⟩ : C(ℝ, ℂ)).comp
        (ContinuousMap.addRight n)) x = _
  rw [← ContinuousMap.tsum_apply (scaledKernel_translateSeries_summable m hm)]
  simpa using (periodization_eq_circleBlockKernel m hm x)

/-- The periodized circle kernel has L1 norm at most the L1 norm of the
real-line Schwartz kernel. -/
theorem circleBlockKernel_L1_le_realKernel (m : ℝ) (hm : 0 < m) :
    (∫ x : UnitAddCircle, ‖circleBlockKernel m hm x‖ ∂volume) ≤
      ∫ x : ℝ, ‖scaledInverseKernelSchwartz m hm.ne' x‖ := by
  let f : C(ℝ, ℂ) :=
    ⟨(scaledInverseKernelSchwartz m hm.ne' : ℝ → ℂ),
      (scaledInverseKernelSchwartz m hm.ne').continuous⟩
  let F : ℤ → C(ℝ, ℂ) := fun n => f.comp (ContinuousMap.addRight n)
  let g : C(ℝ, ℝ) := ⟨fun x => ‖f x‖, continuous_norm.comp f.continuous⟩
  let G : ℤ → C(ℝ, ℝ) := fun n => g.comp (ContinuousMap.addRight n)
  have hF : Summable F := by
    simpa [F, f] using scaledKernel_translateSeries_summable m hm
  have hG : Summable G := by
    simpa [G, g, f] using scaledKernel_normTranslateSeries_summable m hm
  have hcircle_interval :
      (∫ x : UnitAddCircle, ‖circleBlockKernel m hm x‖ ∂volume) =
        ∫ x in (0 : ℝ)..1, ‖circleBlockKernel m hm (x : UnitAddCircle)‖ := by
    letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
    have hLift : (fun a : UnitAddCircle =>
        AddCircle.liftIoc (1 : ℝ) 0
          (fun x : ℝ => ‖circleBlockKernel m hm (x : UnitAddCircle)‖) a) =
        fun a => ‖circleBlockKernel m hm a‖ := by
      funext a
      obtain ⟨x, hx, hxa⟩ := AddCircle.eq_coe_Ioc a
      rw [← hxa, AddCircle.liftIoc_coe_apply (by simpa only [zero_add] using hx)]
    calc
      _ = ∫ a : UnitAddCircle, AddCircle.liftIoc (1 : ℝ) 0
          (fun x : ℝ => ‖circleBlockKernel m hm (x : UnitAddCircle)‖) a ∂volume := by
        rw [hLift]
      _ = ∫ x in (0 : ℝ)..1, ‖circleBlockKernel m hm (x : UnitAddCircle)‖ := by
        simpa only [zero_add] using
          (AddCircle.integral_liftIoc_eq_intervalIntegral
            (T := (1 : ℝ)) (t := (0 : ℝ))
            (f := fun x : ℝ => ‖circleBlockKernel m hm (x : UnitAddCircle)‖))
  have hperiod (x : ℝ) : (∑' n : ℤ, F n x) = circleBlockKernel m hm (x : UnitAddCircle) := by
    simpa [F, f, ContinuousMap.comp_apply, ContinuousMap.coe_addRight, zsmul_one,
      add_comm] using (periodization_eq_circleBlockKernel m hm x)
  have hpoint (x : ℝ) :
      ‖(∑' n : ℤ, F n) x‖ ≤ (∑' n : ℤ, G n) x := by
    rw [← ContinuousMap.tsum_apply hF, ← ContinuousMap.tsum_apply hG]
    have hval : Summable (fun n : ℤ => ‖F n x‖) :=
      (ContinuousMap.summable_apply hF x).norm
    calc
      ‖∑' n : ℤ, F n x‖ ≤ ∑' n : ℤ, ‖F n x‖ := norm_tsum_le_tsum_norm hval
      _ = ∑' n : ℤ, G n x := by
        apply tsum_congr
        intro n
        simp [F, G, g, ContinuousMap.comp_apply, ContinuousMap.coe_addRight,
          zsmul_one, add_comm]
  have hleft_int : IntervalIntegrable
      (fun x : ℝ => ‖(∑' n : ℤ, F n) x‖) volume 0 1 := by
    exact (continuous_norm.comp (∑' n : ℤ, F n).continuous).intervalIntegrable 0 1
  have hright_int : IntervalIntegrable (fun x : ℝ => (∑' n : ℤ, G n) x) volume 0 1 := by
    exact (∑' n : ℤ, G n).continuous.intervalIntegrable 0 1
  have hmono :
      (∫ x in (0 : ℝ)..1, ‖(∑' n : ℤ, F n) x‖) ≤
        ∫ x in (0 : ℝ)..1, (∑' n : ℤ, G n) x :=
    intervalIntegral.integral_mono (by norm_num) hleft_int hright_int hpoint
  let K : Compacts ℝ := ⟨Set.uIcc 0 1, isCompact_uIcc⟩
  have hG_restrict : Summable (fun n : ℤ => ‖(G n).restrict K‖) := by
    let h : C(ℝ, ℝ) := g
    have hh : h =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
      have hf : f =O[cocompact ℝ] (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
        simpa [f] using
          (scaledInverseKernelSchwartz m hm.ne').isBigO_cocompact_rpow (-2)
      simpa [h, g] using hf.norm_norm
    apply summable_of_isBigO (Real.summable_abs_int_rpow (by norm_num : 1 < (2 : ℝ)))
    exact Asymptotics.IsBigO.comp_tendsto
      (isBigO_norm_restrict_cocompact h (by norm_num : 0 < (2 : ℝ)) hh K)
      Int.tendsto_coe_cofinite
  have hswap :
      (∫ x in (0 : ℝ)..1, (∑' n : ℤ, G n) x) =
        ∑' n : ℤ, ∫ x in (0 : ℝ)..1, G n x := by
    calc
      (∫ x in (0 : ℝ)..1, (∑' n : ℤ, G n) x) =
          ∫ x in (0 : ℝ)..1, ∑' n : ℤ, G n x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact (ContinuousMap.tsum_apply hG x).symm
      _ = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, G n x :=
        (intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm hG_restrict).symm
  have hint : Integrable (fun x : ℝ => ‖f x‖) volume := by
    simpa [f] using (scaledInverseKernelSchwartz m hm.ne').integrable.norm
  have hsum_int :
      (∑' n : ℤ, ∫ x in (0 : ℝ)..1, G n x) = ∫ x : ℝ, ‖f x‖ := by
    simpa [G, g, f, ContinuousMap.comp_apply, ContinuousMap.coe_addRight,
      zsmul_one, add_comm] using hint.hasSum_intervalIntegral_comp_add_int.tsum_eq
  have hperiod_integral :
      (∫ x in (0 : ℝ)..1, ‖circleBlockKernel m hm (x : UnitAddCircle)‖) =
        ∫ x in (0 : ℝ)..1, ‖(∑' n : ℤ, F n) x‖ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x _
    rw [← ContinuousMap.tsum_apply hF x, ← hperiod x]
  calc
    (∫ x : UnitAddCircle, ‖circleBlockKernel m hm x‖ ∂volume)
        = ∫ x in (0 : ℝ)..1, ‖circleBlockKernel m hm (x : UnitAddCircle)‖ := hcircle_interval
    _ = ∫ x in (0 : ℝ)..1, ‖(∑' n : ℤ, F n) x‖ := hperiod_integral
    _ ≤ ∫ x in (0 : ℝ)..1, (∑' n : ℤ, G n) x := hmono
    _ = ∑' n : ℤ, ∫ x in (0 : ℝ)..1, G n x := hswap
    _ = ∫ x : ℝ, ‖f x‖ := hsum_int
    _ = ∫ x : ℝ, ‖scaledInverseKernelSchwartz m hm.ne' x‖ := by rfl

/-- The quotient symbol exactly inverts the detail multiplier wherever the
cutoff is supported. -/
theorem detailMultiplier_mul_blockQuotientSymbol (u : ℝ) :
    detailMultiplier u * blockQuotientSymbol u = blockCutoff u := by
  by_cases hU : 1 / 4 < |u| ∧ |u| < 7 / 4
  · have hu : u ≠ 0 := by
      intro hz
      subst u
      norm_num at hU
    have hsin : Real.sin (Real.pi * u / 2) ≠ 0 := by
      have hpos := detailMultiplier_pos_of_abs_lt_two
        (by have := abs_pos.mpr hu; positivity)
        (by linarith [hU.2])
      rw [detailMultiplier_eq_sin_fourth hu] at hpos
      intro hz
      simp [hz] at hpos
    rw [blockQuotientSymbol, if_pos hU, detailMultiplier_eq_sin_fourth hu]
    field_simp [hsin]
  · rw [blockQuotientSymbol, if_neg hU]
    by_cases hlo : 1 / 4 < |u|
    · have hnot : ¬ |u| < 7 / 4 := by
        intro hh
        exact hU ⟨hlo, hh⟩
      have hhi : 7 / 4 ≤ |u| := le_of_not_gt hnot
      have hout : 3 / 2 ≤ |u| := by linarith
      rw [blockCutoff_eq_zero_of_outerRadius_le hout]
      simp
    · have hsmall : |u| ≤ 3 / 8 := by linarith [le_of_not_gt hlo]
      rw [blockCutoff_eq_zero_of_abs_le_inner hsmall]
      simp

/-- Coefficientwise, the translated-Haar detail multiplier followed by the
smooth inverse-kernel symbol is exactly the desired cutoff. -/
theorem detailMultiplier_mul_blockQuotientSchwartz (u : ℝ) :
    (detailMultiplier u : ℂ) * blockQuotientSchwartz u = (blockCutoff u : ℂ) := by
  change (detailMultiplier u : ℂ) * (blockQuotientSymbol u : ℂ) = _
  rw [← Complex.ofReal_mul]
  exact congrArg (fun x : ℝ => (x : ℂ)) (detailMultiplier_mul_blockQuotientSymbol u)

/-- The finite Fourier polynomial obtained by composing the averaged detail
multiplier with the actual sampled inverse-kernel multiplier. -/
def finiteDetailThenBlockPolynomial (m : ℝ) (hm : 0 < m)
    (s : Finset ℤ) (a : ℤ → ℂ) : C(UnitAddCircle, ℂ) :=
  ∑ n ∈ s,
    (a n * (detailMultiplier ((n : ℝ) / m) : ℂ) *
      blockQuotientSchwartz ((n : ℝ) / m)) • fourier n

/-- On every finite Fourier polynomial, detail followed by the smooth
inverse-kernel multiplier is exactly the smooth cutoff projection. This is an
algebraic identity on the actual integer-frequency modes of the continuous
circle, with no finite cyclic-group replacement. -/
theorem finiteDetailThenBlockPolynomial_eq_cutoff (m : ℝ) (hm : 0 < m)
    (s : Finset ℤ) (a : ℤ → ℂ) :
    finiteDetailThenBlockPolynomial m hm s a =
      ∑ n ∈ s, (a n * (blockCutoff ((n : ℝ) / m) : ℂ)) • fourier n := by
  unfold finiteDetailThenBlockPolynomial
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  calc
    a n * (detailMultiplier ((n : ℝ) / m) : ℂ) *
        blockQuotientSchwartz ((n : ℝ) / m) =
      a n * ((detailMultiplier ((n : ℝ) / m) : ℂ) *
        blockQuotientSchwartz ((n : ℝ) / m)) := by ring
    _ = a n * (blockCutoff ((n : ℝ) / m) : ℂ) := by
      rw [detailMultiplier_mul_blockQuotientSchwartz]

/-- The actual finite-cell projection and dyadic difference, applied to a
finite trigonometric polynomial by linearity on its characters. -/
def translatedDetailPolynomialResponse (m : ℕ) (s : Finset ℤ)
    (a : ℤ → ℂ) (x β : ℝ) : ℂ :=
  ∑ n ∈ s, a n *
    (HaarQuarter.TrigonometricHaarExtraction.translatedGridCellProjection n
        (((2 * m : ℕ) : ℝ)⁻¹) x β -
      HaarQuarter.TrigonometricHaarExtraction.translatedGridCellProjection n
        ((m : ℝ)⁻¹) x β)

/-- Averaging the genuine shifted finite-cell detail of any finite Fourier
polynomial acts mode by mode with the sinc-square Haar detail multiplier. -/
theorem translatedDetailPolynomialResponse_average (m : ℕ) (hm : 0 < m)
    (s : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) :
    (∫ β in (0 : ℝ)..1, translatedDetailPolynomialResponse m s a x β) =
      ∑ n ∈ s, a n *
        ((((Real.sinc (Real.pi * (n : ℝ) * (((2 * m : ℕ) : ℝ)⁻¹)) : ℂ) ^ 2 -
          (Real.sinc (Real.pi * (n : ℝ) * ((m : ℝ)⁻¹)) : ℂ) ^ 2) *
            HaarQuarter.TrigonometricHaarExtraction.character n x)) := by
  unfold translatedDetailPolynomialResponse
  have hInt (n : ℤ) (hn : n ∈ s) :
      IntervalIntegrable (fun β : ℝ => a n *
        (HaarQuarter.TrigonometricHaarExtraction.translatedGridCellProjection n
            (((2 * m : ℕ) : ℝ)⁻¹) x β -
          HaarQuarter.TrigonometricHaarExtraction.translatedGridCellProjection n
            ((m : ℝ)⁻¹) x β)) MeasureSpace.volume 0 1 := by
    have h1 := HaarQuarter.TrigonometricHaarExtraction.translatedGridCellProjection_intervalIntegrable
      (h := (((2 * m : ℕ) : ℝ)⁻¹)) n (by positivity) x
      (a := 0) (b := 1) (by norm_num)
    have h2 := HaarQuarter.TrigonometricHaarExtraction.translatedGridCellProjection_intervalIntegrable
      (h := ((m : ℝ)⁻¹)) n (by positivity) x (a := 0) (b := 1) (by norm_num)
    exact (h1.sub h2).const_mul (a n)
  rw [intervalIntegral.integral_finset_sum hInt]
  apply Finset.sum_congr rfl
  intro n hn
  rw [intervalIntegral.integral_const_mul]
  congr 1
  exact HaarQuarter.TrigonometricHaarExtraction.translatedGridHaarDetailMultiplier m hm n x

/-- The actual adjacent-scale translated-cell average is the scalar symbol
`detailMultiplier (k/m)` times its continuous-circle character. -/
theorem translatedGridHaarDetailMultiplier_eq_detailMultiplier_ratio
    (m : ℕ) (hm : 0 < m) (k : ℤ) (x : ℝ) :
    (∫ β in (0 : ℝ)..1,
      (HaarQuarter.TrigonometricHaarExtraction.translatedGridCellProjection k
          (((2 * m : ℕ) : ℝ)⁻¹) x β -
        HaarQuarter.TrigonometricHaarExtraction.translatedGridCellProjection k
          ((m : ℝ)⁻¹) x β)) =
      (detailMultiplier ((k : ℝ) / (m : ℝ)) : ℂ) *
        HaarQuarter.TrigonometricHaarExtraction.character k x := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdouble : (((2 * m : ℕ) : ℝ)⁻¹) = ((m : ℝ)⁻¹) / 2 := by
    have htwo : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by norm_num
    rw [htwo]
    field_simp [hmR.ne']
  have hhalf : Real.pi * (k : ℝ) * (((2 * m : ℕ) : ℝ)⁻¹) =
      Real.pi * ((k : ℝ) / (m : ℝ)) / 2 := by
    rw [hdouble]
    field_simp [hmR.ne']
  have hone : Real.pi * (k : ℝ) * ((m : ℝ)⁻¹) =
      Real.pi * ((k : ℝ) / (m : ℝ)) := by
    field_simp [hmR.ne']
  have hcoef :
      ((Real.sinc (Real.pi * ((k : ℝ) / (m : ℝ)) / 2) : ℂ) ^ 2 -
        (Real.sinc (Real.pi * ((k : ℝ) / (m : ℝ))) : ℂ) ^ 2) =
        (detailMultiplier ((k : ℝ) / (m : ℝ)) : ℂ) := by
    rw [detailMultiplier]
    push_cast
    ring
  rw [HaarQuarter.TrigonometricHaarExtraction.translatedGridHaarDetailMultiplier m hm k x,
    hhalf, hone]
  rw [hcoef]

/-- Composing the genuine averaged finite-cell detail with the sampled smooth
inverse-kernel multiplier yields the finite smooth-cutoff Fourier projection.
-/
theorem translatedDetailPolynomialResponse_average_after_blockSymbol
    (m : ℕ) (hm : 0 < m) (s : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) :
    (∫ β in (0 : ℝ)..1,
      translatedDetailPolynomialResponse m s
        (fun n => a n * blockQuotientSchwartz ((n : ℝ) / (m : ℝ))) x β) =
      ∑ n ∈ s,
        (a n * (blockCutoff ((n : ℝ) / (m : ℝ) : ℝ) : ℂ)) *
          HaarQuarter.TrigonometricHaarExtraction.character n x := by
  rw [translatedDetailPolynomialResponse_average m hm]
  apply Finset.sum_congr rfl
  intro n hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdouble : (((2 * m : ℕ) : ℝ)⁻¹) = ((m : ℝ)⁻¹) / 2 := by
    have htwo : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by norm_num
    rw [htwo]
    field_simp [hmR.ne']
  have hhalf : Real.pi * (n : ℝ) * (((2 * m : ℕ) : ℝ)⁻¹) =
      Real.pi * ((n : ℝ) / (m : ℝ)) / 2 := by
    rw [hdouble]
    field_simp [hmR.ne']
  have hone : Real.pi * (n : ℝ) * ((m : ℝ)⁻¹) =
      Real.pi * ((n : ℝ) / (m : ℝ)) := by
    field_simp [hmR.ne']
  have hcoef :
      ((Real.sinc (Real.pi * ((n : ℝ) / (m : ℝ)) / 2) : ℂ) ^ 2 -
        (Real.sinc (Real.pi * ((n : ℝ) / (m : ℝ))) : ℂ) ^ 2) =
        (detailMultiplier ((n : ℝ) / (m : ℝ)) : ℂ) := by
    rw [detailMultiplier]
    push_cast
    ring
  rw [hhalf, hone]
  calc
    (a n * blockQuotientSchwartz ((n : ℝ) / (m : ℝ))) *
        (((Real.sinc (Real.pi * ((n : ℝ) / (m : ℝ)) / 2) : ℂ) ^ 2 -
          (Real.sinc (Real.pi * ((n : ℝ) / (m : ℝ))) : ℂ) ^ 2) *
            HaarQuarter.TrigonometricHaarExtraction.character n x) =
      (a n * ((detailMultiplier ((n : ℝ) / (m : ℝ)) : ℂ) *
        blockQuotientSchwartz ((n : ℝ) / (m : ℝ)))) *
          HaarQuarter.TrigonometricHaarExtraction.character n x := by
            rw [hcoef]
            ring
    _ = (a n * (blockCutoff ((n : ℝ) / (m : ℝ)) : ℂ)) *
          HaarQuarter.TrigonometricHaarExtraction.character n x := by
        rw [detailMultiplier_mul_blockQuotientSchwartz]

end HaarQuarter.FourierExtractionKernel
