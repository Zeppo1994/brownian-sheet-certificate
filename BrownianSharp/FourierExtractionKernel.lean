import BrownianSharp.TrigonometricHaarExtraction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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

/-- A genuine finite Fourier polynomial on the continuous unit circle. -/
def finiteCircleFourierPolynomial (s : Finset ℤ) (a : ℤ → ℂ) :
    C(UnitAddCircle, ℂ) :=
  ∑ n ∈ s, a n • fourier n

/-- Real-line dilation of the inverse Fourier Schwartz kernel, normalized so
its Fourier transform samples the quotient at frequencies divided by `m`. -/
def scaledInverseKernelSchwartz (m : ℝ) (hm : m ≠ 0) : 𝓢(ℝ, ℂ) :=
  (m : ℂ) • (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.smulLeft (Units.mk0 m hm)) inverseFourierBlockKernel)

@[simp] theorem scaledInverseKernelSchwartz_apply (m : ℝ) (hm : m ≠ 0) (x : ℝ) :
    scaledInverseKernelSchwartz m hm x = (m : ℂ) * inverseFourierBlockKernel (m * x) := by
  simp [scaledInverseKernelSchwartz, Units.smul_def, smul_eq_mul]

end HaarQuarter.FourierExtractionKernel
