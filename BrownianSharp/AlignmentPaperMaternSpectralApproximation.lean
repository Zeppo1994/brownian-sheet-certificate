import BrownianSharp.AlignmentMaternSpectralFeature
import BrownianSharp.AlignmentMaternScalarFeature
import BrownianSharp.AlignmentPaperMaternRealPhase
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! Spectral mass estimates for the Matérn Gaussian small-ball approximation
filtration. -/

noncomputable section
open MeasureTheory
open Filter
open scoped ENNReal Topology RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperMaternSpectralApproximation

open BrownianSharp.AlignmentMaternSpectralFeature
open BrownianSharp.AlignmentMaternScalarFeature

def complexTaylorSum (z : ℂ) (q : ℕ) : ℂ :=
  ∑ m ∈ Finset.range q, z^m / (m.factorial : ℂ)

/-- Uniform local Taylor remainder for the complex spectral phase on the
unit spatial interval. This is the analytic estimate behind each frequency
cell polynomial approximation. -/
theorem complexPhase_taylor_cell_error (t a ξ δ : ℝ) (q : ℕ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hξ : |ξ-a| ≤ δ) :
    ‖Complex.exp (Complex.I * (2*Real.pi*t*ξ)) -
      Complex.exp (Complex.I * (2*Real.pi*t*a)) *
        complexTaylorSum (Complex.I * (2*Real.pi*t*(ξ-a))) q‖ ≤
      (2*Real.pi*δ)^q * Real.exp (2*Real.pi*δ) := by
  let z : ℂ := Complex.I * (2*Real.pi*t*(ξ-a))
  have hω : 0 ≤ 2*Real.pi*t := by positivity
  have hz : ‖z‖ ≤ 2*Real.pi*δ := by
    calc
      ‖z‖ = |2*Real.pi*t*(ξ-a)| := by
        calc
          ‖z‖ = ‖((2*Real.pi*t*(ξ-a) : ℝ) : ℂ)‖ := by
            simp [z, Complex.norm_mul, Complex.norm_I, mul_comm]
          _ = |2*Real.pi*t*(ξ-a)| := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ = (2*Real.pi*t)*|ξ-a| := by rw [abs_mul, abs_of_nonneg hω]
      _ ≤ (2*Real.pi*t)*δ := mul_le_mul_of_nonneg_left hξ hω
      _ ≤ 2*Real.pi*δ := by
        apply mul_le_mul_of_nonneg_right _ hδ0
        nlinarith [Real.pi_pos, ht1]
  have harg : Complex.I * (2*Real.pi*t*a) + z =
      Complex.I * (2*Real.pi*t*ξ) := by
    dsimp [z]
    congr 1
    ring
  have hfactor : Complex.exp (Complex.I * (2*Real.pi*t*ξ)) -
      Complex.exp (Complex.I * (2*Real.pi*t*a)) * complexTaylorSum z q =
      Complex.exp (Complex.I * (2*Real.pi*t*a)) *
        (Complex.exp z - complexTaylorSum z q) := by
    rw [← harg, Complex.exp_add]
    ring
  rw [show complexTaylorSum (Complex.I * (2*Real.pi*t*(ξ-a))) q =
      complexTaylorSum z q by rfl, hfactor, norm_mul]
  have hunit : ‖Complex.exp (Complex.I * (2*Real.pi*t*a))‖ = 1 := by
    convert Complex.norm_exp_I_mul_ofReal (2*Real.pi*t*a) using 1 <;>
      push_cast <;> ring
  rw [hunit, one_mul]
  calc
    ‖Complex.exp z - complexTaylorSum z q‖ ≤ ‖z‖^q * Real.exp ‖z‖ := by
      exact Complex.norm_exp_sub_sum_le_norm_mul_exp z q
    _ ≤ (2*Real.pi*δ)^q * Real.exp (2*Real.pi*δ) := by
      gcongr

def complexPhaseCellTaylor (t a ξ : ℝ) (q : ℕ) : ℂ :=
  Complex.exp (Complex.I * ((2*Real.pi*t*a:ℝ):ℂ)) *
    complexTaylorSum (Complex.I * ((2*Real.pi*t*(ξ-a):ℝ):ℂ)) q

/-- The actual real cosine-plus-sine spectral feature is approximated by the
projection of the frequency-cell Taylor polynomial, with only the factor-two
loss from the real projection map. -/
theorem scalarPhase_taylor_cell_error (t a ξ δ : ℝ) (q : ℕ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hξ : |ξ-a| ≤ δ) :
    |scalarPhase t ξ -
      BrownianSharp.AlignmentPaperMaternRealPhase.realPhaseProjection
        (complexPhaseCellTaylor t a ξ q)| ≤
      2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ) := by
  rw [show complexPhaseCellTaylor t a ξ q =
      Complex.exp (Complex.I * (2*Real.pi*t*a)) *
        complexTaylorSum (Complex.I * (2*Real.pi*t*(ξ-a))) q by
      simp [complexPhaseCellTaylor]]
  calc
    |scalarPhase t ξ -
        BrownianSharp.AlignmentPaperMaternRealPhase.realPhaseProjection
          (Complex.exp (Complex.I * (2*Real.pi*t*a)) *
            complexTaylorSum (Complex.I * (2*Real.pi*t*(ξ-a))) q)| ≤
        2*‖Complex.exp (Complex.I * ((2*Real.pi*t*ξ:ℝ):ℂ)) -
          (Complex.exp (Complex.I * (2*Real.pi*t*a)) *
            complexTaylorSum (Complex.I * (2*Real.pi*t*(ξ-a))) q)‖ := by
          exact BrownianSharp.AlignmentPaperMaternRealPhase.scalarPhase_error_le
            t ξ _
    _ ≤ 2*(2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ) := by
          have htaylor := complexPhase_taylor_cell_error t a ξ δ q
            ht0 ht1 hδ0 hδ1 hξ
          have hnorm : ‖Complex.exp (Complex.I * ((2*Real.pi*t*ξ:ℝ):ℂ)) -
              Complex.exp (Complex.I * (2*Real.pi*t*a)) *
                complexTaylorSum (Complex.I * (2*Real.pi*t*(ξ-a))) q‖ ≤
              (2*Real.pi*δ)^q*Real.exp (2*Real.pi*δ) := by
            convert htaylor using 1 <;> push_cast <;> congr 1 <;> ring
          nlinarith [hnorm]

abbrev SpectralAxisL2 (κ h : ℝ) := Lp ℝ 2 (spectralMeasure κ h)

/-- A normalized monomial supported on one bounded frequency cell. Its
weighted spectral L² realization is bounded by one, independently of the
cell location and Matérn parameters. -/
def spectralCellMonomialFunction (a b : ℝ) (ell : ℕ) : ℝ → ℝ :=
  (Set.Ico a b).indicator (fun ξ => ((ξ-a)/(b-a))^ell)

theorem spectralCellMonomial_memLp (κ h a b : ℝ) (ell : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) (hab : a < b) :
    MemLp (spectralCellMonomialFunction a b ell) 2 (spectralMeasure κ h) := by
  letI : IsFiniteMeasure (spectralMeasure κ h) := spectralMeasure_isFinite κ h hκ hh
  apply MemLp.of_bound (by
    exact ((continuous_id.sub continuous_const).div_const (b-a)).pow ell
      |>.aestronglyMeasurable.indicator measurableSet_Ico) 1
  filter_upwards with ξ
  change ‖spectralCellMonomialFunction a b ell ξ‖ ≤ 1
  by_cases hξ : ξ ∈ Set.Ico a b
  · have hleft : 0 ≤ (ξ-a)/(b-a) := by
      apply div_nonneg
      · exact sub_nonneg.mpr hξ.1
      · linarith
    have hright : (ξ-a)/(b-a) ≤ 1 := by
      rw [div_le_one (by linarith : 0 < b-a)]
      linarith [hξ.2]
    simp only [spectralCellMonomialFunction, Set.indicator_of_mem hξ,
      Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hleft ell)]
    exact pow_le_one₀ hleft hright
  · simp [spectralCellMonomialFunction, hξ]

/-- The corresponding bounded vector in the actual weighted spectral L²
space. -/
def spectralCellMonomial (κ h a b : ℝ) (ell : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) (hab : a < b) : SpectralAxisL2 κ h :=
  (spectralCellMonomial_memLp κ h a b ell hκ hh hab).toLp
    (spectralCellMonomialFunction a b ell)

/-- Degree-`q` polynomials on one finite frequency cell, realized as a
finite-dimensional subspace of the Matérn spectral source space. -/
def spectralCellPolynomialSubmodule (κ h a b : ℝ) (q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) (hab : a < b) :
    Submodule ℝ (SpectralAxisL2 κ h) :=
  Submodule.span ℝ (Set.range (fun ell : Fin q =>
    spectralCellMonomial κ h a b ell.val hκ hh hab))

/-- Coefficients of the real frequency-cell Taylor polynomial, obtained by
applying the real phase projection to each complex Taylor coefficient. -/
def scalarTaylorCellCoefficient (t a b : ℝ) (m : ℕ) : ℝ :=
  BrownianSharp.AlignmentPaperMaternRealPhase.realPhaseProjection
    (Complex.exp (Complex.I * ((2*Real.pi*t*a:ℝ):ℂ)) *
      ((Complex.I * ((2*Real.pi*t*(b-a):ℝ):ℂ))^m / (m.factorial:ℂ)))

theorem realPhaseProjection_mul_real (z : ℂ) (r : ℝ) :
    BrownianSharp.AlignmentPaperMaternRealPhase.realPhaseProjection
        (z * (r:ℂ)) =
      BrownianSharp.AlignmentPaperMaternRealPhase.realPhaseProjection z * r := by
  change (z * (r:ℂ)).re + (z * (r:ℂ)).im = (z.re+z.im)*r
  rw [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

def scalarTaylorCellApproxFunction (t a b ξ : ℝ) (q : ℕ) : ℝ :=
  ∑ m ∈ Finset.range q,
    scalarTaylorCellCoefficient t a b m * (((ξ-a)/(b-a))^m)

/-- The explicit real polynomial is exactly the real projection of the
complex phase Taylor polynomial. -/
theorem scalarTaylorCellApproxFunction_eq_projection
    (t a b ξ : ℝ) (q : ℕ) (hab : a < b) :
    scalarTaylorCellApproxFunction t a b ξ q =
      BrownianSharp.AlignmentPaperMaternRealPhase.realPhaseProjection
        (complexPhaseCellTaylor t a ξ q) := by
  let u : ℝ := (ξ-a)/(b-a)
  have hden : b-a ≠ 0 := by linarith
  have hu : ξ-a = (b-a)*u := by
    dsimp [u]
    field_simp
  let base : ℂ := Complex.exp (Complex.I * ((2*Real.pi*t*a:ℝ):ℂ))
  let slope : ℂ := Complex.I * ((2*Real.pi*t*(b-a):ℝ):ℂ)
  have hr : (2*Real.pi*t*(b-a))*((ξ-a)/(b-a)) = 2*Real.pi*t*(ξ-a) := by
    field_simp [hden]
  have hsu : slope * (u:ℂ) = Complex.I * ((2*Real.pi*t*(ξ-a):ℝ):ℂ) := by
    calc
      slope * (u:ℂ) = Complex.I * (((2*Real.pi*t*(b-a))*((ξ-a)/(b-a)):ℝ):ℂ) := by
        dsimp [slope, u]
        push_cast
        ring
      _ = Complex.I * ((2*Real.pi*t*(ξ-a):ℝ):ℂ) := by rw [hr]
  have hsum : complexPhaseCellTaylor t a ξ q =
      ∑ m ∈ Finset.range q,
        (base * (slope^m / (m.factorial:ℂ))) * (u^m:ℂ) := by
    unfold complexPhaseCellTaylor complexTaylorSum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← hsu, mul_pow]
    dsimp [base, slope]
    ring
  unfold scalarTaylorCellApproxFunction scalarTaylorCellCoefficient
  rw [hsum, map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  change BrownianSharp.AlignmentPaperMaternRealPhase.realPhaseProjection
      (base * (slope^m / (m.factorial:ℂ))) * u^m =
    BrownianSharp.AlignmentPaperMaternRealPhase.realPhaseProjection
      (base * (slope^m / (m.factorial:ℂ)) * (u^m:ℂ))
  have hpow : ((u^m:ℝ):ℂ) = (u:ℂ)^m := by simp
  rw [← hpow]
  rw [← realPhaseProjection_mul_real]

/-- On a dyadic cell, the explicit real polynomial source approximation has
the same uniform error as the complex Taylor remainder (up to the real
projection factor). This is the pointwise estimate used before integrating
against the actual Matérn spectral measure. -/
theorem scalarPhase_cellPolynomial_error (t a b ξ : ℝ) (q : ℕ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hab : a < b)
    (hξ : ξ ∈ Set.Ico a b) (hwidth : b-a ≤ 1) :
    |scalarPhase t ξ - scalarTaylorCellApproxFunction t a b ξ q| ≤
      2*(2*Real.pi*(b-a))^q*Real.exp (2*Real.pi*(b-a)) := by
  rw [scalarTaylorCellApproxFunction_eq_projection t a b ξ q hab]
  apply scalarPhase_taylor_cell_error t a ξ (b-a) q ht0 ht1 (by linarith)
    hwidth
  have hxi := hξ.2
  have hleft := hξ.1
  rw [abs_le]
  constructor <;> linarith

def scalarCellTaylorErrorFunction (t a b : ℝ) (q : ℕ) : ℝ → ℝ :=
  (Set.Ico a b).indicator
    (fun ξ => scalarPhase t ξ - scalarTaylorCellApproxFunction t a b ξ q)

/-- The pointwise Taylor estimate integrates to an actual weighted spectral
L² residual estimate on one cell. The right side is the spectral mass of the
cell, so these estimates can be summed over disjoint dyadic cells. -/
theorem scalarCellTaylorError_eLpNorm_le (κ h t a b : ℝ) (q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hab : a < b) (hwidth : b-a ≤ 1) :
    eLpNorm (scalarCellTaylorErrorFunction t a b q) 2 (spectralMeasure κ h) ≤
      ENNReal.ofReal
        (2*(2*Real.pi*(b-a))^q*Real.exp (2*Real.pi*(b-a))) *
        (spectralMeasure κ h (Set.Ico a b)) ^ (1/2:ℝ) := by
  let M : ℝ := 2*(2*Real.pi*(b-a))^q*Real.exp (2*Real.pi*(b-a))
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hset : MeasurableSet (Set.Ico a b) := measurableSet_Ico
  have hmeas : Measurable (scalarCellTaylorErrorFunction t a b q) := by
    unfold scalarCellTaylorErrorFunction
    have hp : Continuous (scalarTaylorCellApproxFunction t a b · q) := by
      unfold scalarTaylorCellApproxFunction
      fun_prop
    have hs : Continuous (scalarPhase t) := by
      unfold scalarPhase
      fun_prop
    exact (hs.sub hp).measurable.indicator hset
  have hdom (ξ : ℝ) :
      ‖scalarCellTaylorErrorFunction t a b q ξ‖ₑ ≤
        ‖(Set.Ico a b).indicator (fun _ : ℝ => M) ξ‖ₑ := by
    by_cases hξ : ξ ∈ Set.Ico a b
    · simp only [scalarCellTaylorErrorFunction, Set.indicator_of_mem hξ,
        Set.indicator_of_mem hξ, Real.enorm_eq_ofReal_abs]
      apply ENNReal.ofReal_le_ofReal
      rw [abs_of_nonneg hM]
      simpa [M] using scalarPhase_cellPolynomial_error t a b ξ q
        ht0 ht1 hab hξ hwidth
    · simp [scalarCellTaylorErrorFunction, hξ]
  calc
    eLpNorm (scalarCellTaylorErrorFunction t a b q) 2 (spectralMeasure κ h) ≤
        eLpNorm ((Set.Ico a b).indicator (fun _ : ℝ => M)) 2
          (spectralMeasure κ h) :=
      eLpNorm_mono_enorm hmeas.aestronglyMeasurable hdom
    _ = ENNReal.ofReal M *
        (spectralMeasure κ h (Set.Ico a b)) ^ (1/2:ℝ) := by
      rw [eLpNorm_indicator_const hset.nullMeasurableSet (by norm_num) (by norm_num)]
      rw [show (2:ENNReal).toReal = 2 by norm_num]
      rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hM]

/-- The finite spectral source vector formed from the normalized cell
monomials with the actual Taylor coefficients. -/
def spectralCellTaylorApproxL2 (κ h t a b : ℝ) (q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) (hab : a < b) : SpectralAxisL2 κ h :=
  ∑ m ∈ Finset.range q,
    scalarTaylorCellCoefficient t a b m •
      spectralCellMonomial κ h a b m hκ hh hab

/-- The finite spectral source vector has the claimed polynomial as its
actual weighted-L² representative. This identifies the candidate in the
finite-dimensional source space with the pointwise Taylor polynomial; without
this step, cellwise scalar error estimates do not bound source distance. -/
theorem spectralCellTaylorApproxL2_coeFn (κ h t a b : ℝ) (q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) (hab : a < b) :
    (spectralCellTaylorApproxL2 κ h t a b q hκ hh hab : ℝ → ℝ) =ᵐ[
      spectralMeasure κ h]
      (Set.Ico a b).indicator (scalarTaylorCellApproxFunction t a b · q) := by
  let μ := spectralMeasure κ h
  letI : IsFiniteMeasure μ := spectralMeasure_isFinite κ h hκ hh
  have hmon (m : ℕ) :
      (spectralCellMonomial κ h a b m hκ hh hab : ℝ → ℝ) =ᵐ[μ]
        spectralCellMonomialFunction a b m := by
    exact (spectralCellMonomial_memLp κ h a b m hκ hh hab).coeFn_toLp
  have hterm (m : ℕ) :
      ((scalarTaylorCellCoefficient t a b m •
        spectralCellMonomial κ h a b m hκ hh hab : SpectralAxisL2 κ h) : ℝ → ℝ) =ᵐ[μ]
        (fun ξ => scalarTaylorCellCoefficient t a b m *
          spectralCellMonomialFunction a b m ξ) := by
    filter_upwards [Lp.coeFn_smul (scalarTaylorCellCoefficient t a b m)
        (spectralCellMonomial κ h a b m hκ hh hab), hmon m] with ξ hs hm
    calc
      ((scalarTaylorCellCoefficient t a b m •
          spectralCellMonomial κ h a b m hκ hh hab : SpectralAxisL2 κ h) : ℝ → ℝ) ξ =
          (scalarTaylorCellCoefficient t a b m •
            (spectralCellMonomial κ h a b m hκ hh hab : ℝ → ℝ)) ξ := hs
      _ = scalarTaylorCellCoefficient t a b m *
          spectralCellMonomial κ h a b m hκ hh hab ξ := by simp
      _ = scalarTaylorCellCoefficient t a b m *
          spectralCellMonomialFunction a b m ξ := by rw [hm]
  have hall : ∀ᵐ ξ ∂μ, ∀ m ∈ Finset.range q,
      ((scalarTaylorCellCoefficient t a b m •
        spectralCellMonomial κ h a b m hκ hh hab : SpectralAxisL2 κ h) : ℝ → ℝ) ξ =
        scalarTaylorCellCoefficient t a b m *
          spectralCellMonomialFunction a b m ξ := by
    rw [eventually_all_finset]
    intro m hm
    exact hterm m
  have hsum := Lp.coeFn_fun_finsetSum (Finset.range q)
    (fun m => scalarTaylorCellCoefficient t a b m •
      spectralCellMonomial κ h a b m hκ hh hab)
  filter_upwards [hsum, hall] with ξ hξ hξmon
  change (∑ m ∈ Finset.range q,
      scalarTaylorCellCoefficient t a b m •
        spectralCellMonomial κ h a b m hκ hh hab) ξ = _
  rw [hξ]
  rw [show (Set.Ico a b).indicator
      (scalarTaylorCellApproxFunction t a b · q) ξ =
      ∑ m ∈ Finset.range q,
        scalarTaylorCellCoefficient t a b m *
          spectralCellMonomialFunction a b m ξ by
    by_cases hx : ξ ∈ Set.Ico a b
    · simp [scalarTaylorCellApproxFunction, spectralCellMonomialFunction,
        Set.indicator_of_mem, hx]
    · simp [scalarTaylorCellApproxFunction, spectralCellMonomialFunction,
        hx]]
  apply Finset.sum_congr rfl
  intro m hm
  exact hξmon m hm

noncomputable def scalarCellFeatureRestrictedL2 (κ h t a b : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) : SpectralAxisL2 κ h :=
  ((scalarPhaseMemLp κ h t hκ hh).indicator measurableSet_Ico).toLp
    ((Set.Ico a b).indicator (scalarPhase t))

theorem scalarCellFeatureRestrictedL2_coeFn (κ h t a b : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) :
    (scalarCellFeatureRestrictedL2 κ h t a b hκ hh : ℝ → ℝ) =ᵐ[ spectralMeasure κ h ]
      (Set.Ico a b).indicator (scalarPhase t) := by
  exact (((scalarPhaseMemLp κ h t hκ hh).indicator measurableSet_Ico).coeFn_toLp)

/-- The actual restricted feature in weighted spectral L² is approximated by
the actual finite-dimensional Taylor source vector with the cellwise error
from the pointwise phase estimate. -/
theorem scalarCellFeatureRestrictedL2_taylor_error_norm_le
    (κ h t a b : ℝ) (q : ℕ) (hκ : 0 < κ) (hh : 0 < h)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hab : a < b) (hwidth : b-a ≤ 1) :
    ‖scalarCellFeatureRestrictedL2 κ h t a b hκ hh -
      spectralCellTaylorApproxL2 κ h t a b q hκ hh hab‖ ≤
      2*(2*Real.pi*(b-a))^q*Real.exp (2*Real.pi*(b-a)) *
        (spectralMeasure κ h (Set.Ico a b)).toReal ^ (1/2:ℝ) := by
  let μ := spectralMeasure κ h
  letI : IsFiniteMeasure μ := spectralMeasure_isFinite κ h hκ hh
  let K := scalarCellFeatureRestrictedL2 κ h t a b hκ hh
  let A := spectralCellTaylorApproxL2 κ h t a b q hκ hh hab
  let M : ℝ := 2*(2*Real.pi*(b-a))^q*Real.exp (2*Real.pi*(b-a))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK : (K : ℝ → ℝ) =ᵐ[μ] (Set.Ico a b).indicator (scalarPhase t) :=
    scalarCellFeatureRestrictedL2_coeFn κ h t a b hκ hh
  have hA : (A : ℝ → ℝ) =ᵐ[μ]
      (Set.Ico a b).indicator (scalarTaylorCellApproxFunction t a b · q) :=
    spectralCellTaylorApproxL2_coeFn κ h t a b q hκ hh hab
  have hD : (↑(K-A) : ℝ → ℝ) =ᵐ[μ]
      scalarCellTaylorErrorFunction t a b q := by
    filter_upwards [Lp.coeFn_sub K A, hK, hA] with ξ hsub hphase htaylor
    change ((K-A : SpectralAxisL2 κ h) : ℝ → ℝ) ξ = _
    rw [hsub, Pi.sub_apply, hphase, htaylor]
    by_cases hx : ξ ∈ Set.Ico a b
    · simp [scalarCellTaylorErrorFunction, hx]
    · simp [scalarCellTaylorErrorFunction, hx]
  have herr := scalarCellTaylorError_eLpNorm_le κ h t a b q
    hκ hh ht0 ht1 hab hwidth
  have hmass : μ (Set.Ico a b) ≠ ∞ := measure_ne_top μ (Set.Ico a b)
  have hmasspow : (μ (Set.Ico a b)) ^ (1/2:ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) hmass
  have hRtop : ENNReal.ofReal M * (μ (Set.Ico a b)) ^ (1/2:ℝ) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmasspow
  rw [Lp.norm_def, eLpNorm_congr_ae hD]
  calc
    ENNReal.toReal (eLpNorm (scalarCellTaylorErrorFunction t a b q) 2 μ) ≤
        ENNReal.toReal
          (ENNReal.ofReal M * (μ (Set.Ico a b)) ^ (1/2:ℝ)) :=
      ENNReal.toReal_mono hRtop (by simpa [M, μ] using herr)
    _ = M * (μ (Set.Ico a b)).toReal ^ (1/2:ℝ) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM, ← ENNReal.toReal_rpow]

/-- Pythagoras for a finite family of pairwise orthogonal vectors. This is
used to add the actual L² errors on disjoint frequency cells without losing a
factor equal to the square root of the number of cells. -/
theorem norm_sq_sum_of_pairwise_orthogonal (κ h : ℝ) {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → SpectralAxisL2 κ h)
    (horth : ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j → inner ℝ (f i) (f j) = 0) :
    ‖∑ i ∈ s, f i‖^2 = ∑ i ∈ s, ‖f i‖^2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hcross : ⟪f a, ∑ i ∈ s, f i⟫ = 0 := by
        rw [inner_sum]
        apply Finset.sum_eq_zero
        intro i hi
        have hai : a ≠ i := by
          intro heq
          subst i
          exact ha hi
        exact horth a (Finset.mem_insert_self _ _) i
          (Finset.mem_insert_of_mem hi) hai
      have hrec := ih (by
        intro i hi j hj hij
        exact horth i (Finset.mem_insert_of_mem hi)
          j (Finset.mem_insert_of_mem hj) hij)
      rw [Finset.sum_insert ha]
      calc
        ‖f a + ∑ i ∈ s, f i‖^2 =
            ‖f a + ∑ i ∈ s, f i‖ * ‖f a + ∑ i ∈ s, f i‖ := by ring
        _ = ‖f a‖ * ‖f a‖ + ‖∑ i ∈ s, f i‖ * ‖∑ i ∈ s, f i‖ :=
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hcross
        _ = ‖f a‖^2 + ‖∑ i ∈ s, f i‖^2 := by ring
        _ = ∑ i ∈ insert a s, ‖f i‖^2 := by
          rw [hrec, Finset.sum_insert ha]

/-- The positive and reflected negative cells in dyadic frequency band `j`.
The index `k` ranges over all cells of width `2^-m` in that band. -/
def dyadicBandCellInterval (j m : ℕ) (k : Fin (2^(j+m)))
    (side : Fin 2) : ℝ × ℝ :=
  let a := (2:ℝ)^j + (k.val:ℝ)/(2:ℝ)^m
  let b := (2:ℝ)^j + ((k.val+1:ℕ):ℝ)/(2:ℝ)^m
  if side.val = 0 then (a,b) else (-b,-a)

theorem dyadicBandCellInterval_order (j m : ℕ) (k : Fin (2^(j+m)))
    (side : Fin 2) :
    (dyadicBandCellInterval j m k side).1 <
      (dyadicBandCellInterval j m k side).2 := by
  dsimp [dyadicBandCellInterval]
  split_ifs with hs
  · have hden : 0 < (2:ℝ)^m := by positivity
    have hnat : (k.val:ℝ) < (k.val+1:ℕ) := by exact_mod_cast Nat.lt_succ_self k.val
    dsimp
    exact add_lt_add_right (div_lt_div_of_pos_right hnat hden) ((2:ℝ)^j)
  · have hden : 0 < (2:ℝ)^m := by positivity
    have hnat : (k.val:ℝ) < (k.val+1:ℕ) := by exact_mod_cast Nat.lt_succ_self k.val
    dsimp
    have h := div_lt_div_of_pos_right hnat hden
    linarith

/-- The central spectral interval `[-1,1]` is split into `2^N` cells.
Its mesh width is `2^(1-N)`, so it is fine enough to contribute the same
level-N approximation rate as the positive-frequency dyadic bands. -/
def centralDyadicCellInterval (N : ℕ) (k : Fin (2^N)) : ℝ × ℝ :=
  (-1 + 2*(k.val:ℝ)/(2:ℝ)^N,
   -1 + 2*((k.val+1:ℕ):ℝ)/(2:ℝ)^N)

theorem centralDyadicCellInterval_order (N : ℕ) (k : Fin (2^N)) :
    (centralDyadicCellInterval N k).1 < (centralDyadicCellInterval N k).2 := by
  have hden : 0 < (2:ℝ)^N := by positivity
  have hnat : (k.val:ℝ) < ((k.val+1:ℕ):ℝ) := by
    exact_mod_cast Nat.lt_succ_self k.val
  have hmul : 2*(k.val:ℝ) < 2*((k.val+1:ℕ):ℝ) := by nlinarith
  unfold centralDyadicCellInterval
  change -1 + 2*(k.val:ℝ)/(2:ℝ)^N <
    -1 + 2*((k.val+1:ℕ):ℝ)/(2:ℝ)^N
  linarith [div_lt_div_of_pos_right hmul hden]

theorem centralDyadicCellInterval_width (N : ℕ) (k : Fin (2^N)) :
    (centralDyadicCellInterval N k).2 -
      (centralDyadicCellInterval N k).1 = 2/(2:ℝ)^N := by
  unfold centralDyadicCellInterval
  have hden : (2:ℝ)^N ≠ 0 := by positivity
  field_simp
  push_cast
  ring

theorem centralDyadicCellIntervals_disjoint {N : ℕ} {k l : Fin (2^N)}
    (hkl : k ≠ l) :
    Disjoint (Set.Ico (centralDyadicCellInterval N k).1
        (centralDyadicCellInterval N k).2)
      (Set.Ico (centralDyadicCellInterval N l).1
        (centralDyadicCellInterval N l).2) := by
  have hval : k.val ≠ l.val := fun heq => hkl (Fin.ext heq)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · have hstep : k.val + 1 ≤ l.val := Nat.succ_le_of_lt hlt
    have hcast : ((k.val+1:ℕ):ℝ) ≤ (l.val:ℝ) := by exact_mod_cast hstep
    have hden : 0 < (2:ℝ)^N := by positivity
    have hend : (centralDyadicCellInterval N k).2 ≤
        (centralDyadicCellInterval N l).1 := by
      unfold centralDyadicCellInterval
      change -1 + 2*((k.val+1:ℕ):ℝ)/(2:ℝ)^N ≤
        -1 + 2*(l.val:ℝ)/(2:ℝ)^N
      have hfrac := (div_le_div_iff_of_pos_right hden).2
        (show 2*((k.val+1:ℕ):ℝ) ≤ 2*(l.val:ℝ) by nlinarith)
      linarith
    exact Set.disjoint_left.mpr fun x hxk hxl => by linarith [hxk.2, hxl.1, hend]
  · have hstep : l.val + 1 ≤ k.val := Nat.succ_le_of_lt hgt
    have hcast : ((l.val+1:ℕ):ℝ) ≤ (k.val:ℝ) := by exact_mod_cast hstep
    have hden : 0 < (2:ℝ)^N := by positivity
    have hend : (centralDyadicCellInterval N l).2 ≤
        (centralDyadicCellInterval N k).1 := by
      unfold centralDyadicCellInterval
      change -1 + 2*((l.val+1:ℕ):ℝ)/(2:ℝ)^N ≤
        -1 + 2*(k.val:ℝ)/(2:ℝ)^N
      have hfrac := (div_le_div_iff_of_pos_right hden).2
        (show 2*((l.val+1:ℕ):ℝ) ≤ 2*(k.val:ℝ) by nlinarith)
      linarith
    exact Set.disjoint_left.mpr fun x hxk hxl => by linarith [hxl.2, hxk.1, hend]

theorem centralDyadicCellInterval_bounds (N : ℕ) (k : Fin (2^N)) :
    -1 ≤ (centralDyadicCellInterval N k).1 ∧
      (centralDyadicCellInterval N k).2 ≤ 1 := by
  have hden : 0 < (2:ℝ)^N := by positivity
  have hstep : k.val + 1 ≤ 2^N := Nat.succ_le_of_lt k.isLt
  have hcast : ((k.val+1:ℕ):ℝ) ≤ (2^N:ℕ) := by exact_mod_cast hstep
  have hpow : ((2^N:ℕ):ℝ) = (2:ℝ)^N := by norm_num [Nat.cast_pow]
  constructor
  · unfold centralDyadicCellInterval
    have hk : 0 ≤ (k.val:ℝ) := Nat.cast_nonneg _
    have hfrac : 0 ≤ 2*(k.val:ℝ)/(2:ℝ)^N := by positivity
    linarith
  · unfold centralDyadicCellInterval
    have hnum : 2*((k.val+1:ℕ):ℝ) ≤ 2*(2:ℝ)^N := by rw [← hpow]; nlinarith
    have hfrac : 2*((k.val+1:ℕ):ℝ)/(2:ℝ)^N ≤ 2 :=
      (div_le_iff₀ hden).2 hnum
    linarith

theorem dyadicBandCellInterval_bounds (j m : ℕ) (k : Fin (2^(j+m)))
    (side : Fin 2) :
    if side.val = 0 then
      (2:ℝ)^j ≤ (dyadicBandCellInterval j m k side).1 ∧
        (dyadicBandCellInterval j m k side).2 ≤ (2:ℝ)^(j+1)
    else
      -((2:ℝ)^(j+1)) ≤ (dyadicBandCellInterval j m k side).1 ∧
        (dyadicBandCellInterval j m k side).2 ≤ -((2:ℝ)^j) := by
  have hden : 0 < (2:ℝ)^m := by positivity
  have hstep : k.val + 1 ≤ 2^(j+m) := Nat.succ_le_of_lt k.isLt
  have hcast : ((k.val+1:ℕ):ℝ) ≤ (2^(j+m):ℕ) := by exact_mod_cast hstep
  have hpowcast : ((2^(j+m):ℕ):ℝ) = (2:ℝ)^(j+m) := by norm_num [Nat.cast_pow]
  have hpow : (2:ℝ)^(j+m) = (2:ℝ)^j * (2:ℝ)^m := by rw [pow_add]
  have hfrac : ((k.val+1:ℕ):ℝ)/(2:ℝ)^m ≤ (2:ℝ)^j := by
    apply (div_le_iff₀ hden).2
    rw [← hpow, ← hpowcast]
    exact hcast
  have hbase : 0 ≤ (k.val:ℝ)/(2:ℝ)^m := by positivity
  unfold dyadicBandCellInterval
  split_ifs with hs
  · constructor
    · dsimp
      linarith
    · dsimp
      have hright : ((k.val:ℝ)+(1:ℝ))/(2:ℝ)^m ≤ (2:ℝ)^j := by
        convert hfrac using 1 <;> norm_num
      rw [pow_succ]
      nlinarith
  · constructor
    · dsimp
      have hright : ((k.val:ℝ)+(1:ℝ))/(2:ℝ)^m ≤ (2:ℝ)^j := by
        convert hfrac using 1 <;> norm_num
      rw [pow_succ]
      nlinarith
    · dsimp
      nlinarith [hbase]

/-- Cell indices for the full level-N partition of the real frequency line
up to the cutoff `2^(N+1)`: `2^N` central cells and the signed dyadic bands. -/
abbrev spectralLevelCellIndex (N : ℕ) :=
  Fin (2^N) ⊕
    (Σ j : Fin (N+1), Fin 2 × Fin (2^(j.val+(N-j.val)/2)))

def spectralLevelCellInterval (N : ℕ) (a : spectralLevelCellIndex N) : ℝ × ℝ :=
  match a with
  | Sum.inl k => centralDyadicCellInterval N k
  | Sum.inr band =>
      dyadicBandCellInterval band.1.val ((N-band.1.val)/2) band.2.2 band.2.1

theorem spectralLevelCellInterval_order (N : ℕ) (a : spectralLevelCellIndex N) :
    (spectralLevelCellInterval N a).1 < (spectralLevelCellInterval N a).2 := by
  cases a with
  | inl k => exact centralDyadicCellInterval_order N k
  | inr band => exact (dyadicBandCellInterval_order band.1.val
      ((N-band.1.val)/2) band.2.2 band.2.1)

/-- The sum of the actual cellwise Taylor source vectors over every central
and signed dyadic cell at level N. -/
def spectralLevelTaylorApproxL2 (κ h t : ℝ) (N q : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) : SpectralAxisL2 κ h :=
  ∑ a : spectralLevelCellIndex N,
    let I := spectralLevelCellInterval N a
    spectralCellTaylorApproxL2 κ h t I.1 I.2 q hκ hh
      (spectralLevelCellInterval_order N a)

/-- The one-sided high-frequency tail of the raw Matérn spectral density is
bounded by its exact power-law tail once the cutoff exceeds one. -/
theorem density_tail_Ioi_le (κ h R : ℝ) (hκ : 0 < κ) (hh : 0 < h)
    (hR1 : 1 ≤ R) :
    (∫ ξ in Set.Ioi R, density κ h ξ) ≤ R ^ (-2*h) / (2*h) := by
  have hR : 0 < R := by linarith
  let f : ℝ → ℝ := fun x => -(x ^ (-2*h)) / (2*h)
  let fp : ℝ → ℝ := fun x => x ^ (-2*h-1)
  have hderiv : ∀ x ∈ Set.Ici R, HasDerivAt f (fp x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hR hx)
    have hpow := Real.hasDerivAt_rpow_const (x := x) (p := -2*h) (Or.inl hx0)
    have hdiv := hpow.neg.div_const (2*h)
    convert hdiv using 1 <;> dsimp [f, fp] <;> field_simp <;> ring
  have hfpnonneg : ∀ x ∈ Set.Ioi R, 0 ≤ fp x := by
    intro x hx
    dsimp [fp]
    exact Real.rpow_nonneg (le_of_lt (lt_trans hR hx)) _
  have hflim : Tendsto f atTop (𝓝 0) := by
    have hp : 0 < 2*h := by positivity
    have hpow := (tendsto_rpow_neg_atTop hp).const_mul (-(2*h)⁻¹)
    convert hpow using 1
    · funext x
      dsimp [f]
      field_simp
    · simp
  have hfpint : IntegrableOn fp (Set.Ioi R) := by
    exact integrableOn_Ioi_deriv_of_nonneg' hderiv hfpnonneg hflim
  have hpowtail := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hfpnonneg hflim
  have hdenint : IntegrableOn (density κ h) (Set.Ioi R) :=
    (density_integrable κ h hκ hh).integrableOn
  have hcomp : ∀ ξ ∈ Set.Ioi R, density κ h ξ ≤ fp ξ := by
    intro ξ hξ
    have hξ0 : 0 < ξ := lt_trans hR hξ
    have hbase : ξ^2 ≤ κ^2 + ξ^2 := by nlinarith [sq_nonneg κ]
    have hexp : -(h+1/2) ≤ 0 := by linarith
    have hmono := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hξ0) hbase hexp
    have hdens : density κ h ξ = Real.rpow (κ^2+ξ^2) (-(h+1/2)) := by
      rfl
    rw [hdens]
    dsimp [fp]
    have hxpow : Real.rpow (ξ^2) (-(h+1/2)) = ξ ^ (-2*h-1) := by
      rw [← Real.rpow_natCast ξ 2]
      calc
        Real.rpow (Real.rpow ξ (2:ℝ)) (-(h+1/2)) =
            Real.rpow ξ (2 * (-(h+1/2))) :=
              (Real.rpow_mul (le_of_lt hξ0) (2:ℝ) (-(h+1/2))).symm
        _ = Real.rpow ξ (-2*h-1) := by congr 1 <;> ring
    rw [← hxpow]
    exact hmono
  exact (setIntegral_mono_on hdenint hfpint measurableSet_Ioi hcomp).trans
    (by rw [hpowtail]; dsimp [f]; ring_nf; exact le_rfl)

/-- The high-frequency tail after dyadic level `N` has the explicit
`2^(-2hN)` energy decay. -/
theorem density_dyadic_tail_le (κ h : ℝ) (N : ℕ)
    (hκ : 0 < κ) (hh : 0 < h) :
    (∫ ξ in Set.Ioi ((2:ℝ)^N), density κ h ξ) ≤
      ((2:ℝ)^N) ^ (-2*h) / (2*h) := by
  apply density_tail_Ioi_le κ h _ hκ hh
  exact one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)

end BrownianSharp.AlignmentPaperMaternSpectralApproximation
