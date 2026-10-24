import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.Floor

/-!
# Continuous translated Haar detail: the one-frequency calculation

This file works on the continuous circle.  In particular, it does not replace
the translated dyadic partition by a finite cyclic group.  The first lemma
records the local cell calculation, including the phase of the cell center;
the next lemma averages that phase over its full cell of possible translations.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace HaarQuarter.TrigonometricHaarExtraction

/-- The real-frequency character on the lift of the unit circle. -/
def character (k : ℤ) (x : ℝ) : ℂ :=
  Complex.exp ((2 * Real.pi * (k : ℝ) * x) * Complex.I)

/-- Mathlib's continuous character on the unit circle. -/
def addCircleCharacter (k : ℤ) : C(AddCircle (1 : ℝ), ℂ) :=
  fourier k

/-- The real-line character used in the interval calculation is exactly the
lift of the continuous `AddCircle` character. -/
theorem addCircleCharacter_coe (k : ℤ) (x : ℝ) :
    addCircleCharacter k (x : AddCircle (1 : ℝ)) = character k x := by
  rw [addCircleCharacter, fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem character_add (k : ℤ) (x y : ℝ) :
    character k (x + y) = character k x * character k y := by
  rw [character, character, character, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem character_norm (k : ℤ) (x : ℝ) : ‖character k x‖ = 1 := by
  simp [character, Complex.norm_exp]

/-- The response of a cell of width `h`, whose center is displaced by `u`
from the evaluation point, on a character.  The exponential factor is the
essential phase: a single translated cell projection is not a scalar Fourier
multiplier. -/
def translatedCellResponse (k : ℤ) (h u : ℝ) : ℂ :=
  character k u * (Real.sinc (Real.pi * (k : ℝ) * h) : ℂ)

/-- Response as a function of the normalized translation phase. -/
def phaseCellResponse (k : ℤ) (h : ℝ) (t : ℝ) : ℂ :=
  translatedCellResponse k h (h * (1 / 2 - Int.fract t))

theorem phaseCellResponse_periodic (k : ℤ) (h : ℝ) :
    Function.Periodic (phaseCellResponse k h) 1 := by
  intro t
  simp only [phaseCellResponse, Int.fract_add_one]

theorem phaseCellResponse_norm_le_one (k : ℤ) (h t : ℝ) :
    ‖phaseCellResponse k h t‖ ≤ 1 := by
  rw [phaseCellResponse, translatedCellResponse, norm_mul, character_norm]
  simpa only [Complex.norm_real, Real.norm_eq_abs, one_mul] using
    Real.abs_sinc_le_one (Real.pi * (k : ℝ) * h)

theorem phaseCellResponse_intervalIntegrable (k : ℤ) (h : ℝ) {a b : ℝ}
    (hab : a ≤ b) :
    IntervalIntegrable (phaseCellResponse k h) MeasureSpace.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply Measure.integrableOn_of_bounded (μ := MeasureSpace.volume) (s := Set.Ioc a b)
      (M := 1)
  · rw [Real.volume_Ioc]
    finiteness
  · have hmeas : Measurable (phaseCellResponse k h) := by
      change Measurable (fun t : ℝ =>
        translatedCellResponse k h (h * (1 / 2 - Int.fract t)))
      have hchar : Continuous (character k) := by fun_prop [character]
      have hu : Measurable (fun t : ℝ => h * (1 / 2 - Int.fract t)) :=
        measurable_const.mul (measurable_const.sub measurable_fract)
      change Measurable (fun t : ℝ =>
        character k (h * (1 / 2 - Int.fract t)) *
          (Real.sinc (Real.pi * (k : ℝ) * h) : ℂ))
      exact (hchar.measurable.comp hu).mul measurable_const
    exact hmeas.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => phaseCellResponse_norm_le_one k h t

/-- The finite-cell average of a function over the cell of width `h` centered
at `c`. -/
def cellAverage (h c : ℝ) (f : ℝ → ℂ) : ℂ :=
  h⁻¹ * (∫ y in c - h / 2..c + h / 2, f y)

/-- Displacement of the center of the translated-grid cell containing `x`.
It is the centered fractional part of `(x - β) / h`. -/
def translatedCellCenterDisplacement (h x β : ℝ) : ℝ :=
  h * (1 / 2 - Int.fract ((x - β) / h))

/-- The actual center of the shifted grid cell containing `x`. -/
def translatedCellCenter (h x β : ℝ) : ℝ :=
  β + (((⌊(x - β) / h⌋ : ℤ) : ℝ) + 1 / 2) * h

/-- The integer cell-center formula is exactly `x` plus its centered
fractional-part displacement. -/
theorem translatedCellCenter_eq (h : ℝ) (hh : h ≠ 0) (x β : ℝ) :
    translatedCellCenter h x β = x + translatedCellCenterDisplacement h x β := by
  let q : ℝ := (x - β) / h
  change β + ((Int.floor q : ℝ) + 1 / 2) * h = x + h * (1 / 2 - Int.fract q)
  have hf : Int.fract q + (Int.floor q : ℝ) = q := Int.fract_add_floor q
  have hq : q * h = x - β := by
    dsimp [q]
    field_simp [hh]
  have hfh := congrArg (fun t : ℝ => t * h) hf
  nlinarith [hfh]

/-- The displacement, and hence the shifted-cell projection at a fixed `x`,
is periodic in the translation parameter with period `h`. -/
theorem translatedCellCenterDisplacement_periodic (h : ℝ) (hh : h ≠ 0) (x : ℝ) :
    Function.Periodic (translatedCellCenterDisplacement h x) h := by
  intro β
  rw [translatedCellCenterDisplacement, translatedCellCenterDisplacement]
  have harg : (x - (β + h)) / h = (x - β) / h - 1 := by
    field_simp
    ring
  rw [harg]
  rw [show (x - β) / h - 1 = (x - β) / h - (1 : ℤ) by norm_num]
  rw [Int.fract_sub_intCast]

/-- The conditional expectation onto a translated dyadic cell, evaluated at
`x`, is the finite average over the cell whose center is computed by the
actual integer partition. -/
def translatedGridCellProjection (k : ℤ) (h x β : ℝ) : ℂ :=
  cellAverage h (translatedCellCenter h x β) (character k)


/-- Centered integration of a character over a cell returns the usual sinc
factor.  This is the exact interval-integral calculation underlying a
translated dyadic cell average. -/
theorem centeredCharacterAverage (k : ℤ) {h : ℝ} (hh : 0 < h) :
    h⁻¹ * (∫ u in -h / 2..h / 2, character k u) =
      (Real.sinc (Real.pi * (k : ℝ) * h) : ℂ) := by
  let r : ℝ := Real.pi * (k : ℝ) * h
  let c : ℝ := 2 * Real.pi * (k : ℝ)
  by_cases hk : k = 0
  · subst k
    simp [character, Real.sinc]
    field_simp [hh.ne']
    ring
  have hc : c ≠ 0 := by
    dsimp [c]
    have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) this
  have hcomp :
      (∫ u in -h / 2..h / 2, character k u) =
        c⁻¹ * (∫ v in -r..r, Complex.exp (v * Complex.I)) := by
    calc
      (∫ u in -h / 2..h / 2, character k u) =
          ∫ u in -h / 2..h / 2,
            Complex.exp (((c * u : ℝ) : ℂ) * Complex.I) := by
              apply intervalIntegral.integral_congr; intro u hu
              simp [character, c, Complex.ofReal_mul]
      _ = c⁻¹ * (∫ v in c * (-h / 2)..c * (h / 2),
            Complex.exp ((v : ℝ) * Complex.I)) := by
              have hchange := intervalIntegral.integral_comp_mul_left
                (f := fun v : ℝ => Complex.exp ((v : ℝ) * Complex.I))
                (a := -h / 2) (b := h / 2) hc
              convert hchange using 1
      _ = c⁻¹ * (∫ v in -r..r, Complex.exp (v * Complex.I)) := by
              congr 2 <;> dsimp [c, r] <;> ring
  rw [hcomp, integral_exp_mul_I_eq_sinc]
  have hcanc : h⁻¹ * c⁻¹ * 2 * r = 1 := by
    dsimp [c, r]
    field_simp [hh.ne', hk, Real.pi_ne_zero]
  calc
    (↑h⁻¹ : ℂ) * ((↑c⁻¹ : ℂ) *
        ((2 : ℂ) * (↑r : ℂ) * (Real.sinc r : ℂ))) =
        ((h⁻¹ * c⁻¹ * 2 * r : ℝ) : ℂ) * (Real.sinc r : ℂ) := by
          push_cast
          ring
    _ = (Real.sinc r : ℂ) := by rw [hcanc]; simp

/-- Averaging the displaced-cell response over all possible centers in a
cell gives the square-sinc multiplier.  The phase factor remains present
until the translation average is taken. -/
theorem averagedTranslatedCellResponse (k : ℤ) {h : ℝ} (hh : 0 < h) :
    h⁻¹ * (∫ u in -h / 2..h / 2, translatedCellResponse k h u) =
      ((Real.sinc (Real.pi * (k : ℝ) * h)) : ℂ) ^ 2 := by
  simp only [translatedCellResponse]
  let s : ℂ := (Real.sinc (Real.pi * (k : ℝ) * h) : ℂ)
  calc
    h⁻¹ * (∫ u in -h / 2..h / 2, character k u * s) =
        h⁻¹ * ((∫ u in -h / 2..h / 2, character k u) * s) := by
          rw [intervalIntegral.integral_mul_const]
    _ = (h⁻¹ * (∫ u in -h / 2..h / 2, character k u)) * s := by ring
    _ = s * s := by rw [centeredCharacterAverage k hh]
    _ = ((Real.sinc (Real.pi * (k : ℝ) * h) : ℂ)) ^ 2 := by simp [s, pow_two]

/-- Exact response of an individual translated cell projection.  The cell
center is `x + u`; its phase is retained in the conclusion. -/
theorem cellAverage_character (k : ℤ) {h : ℝ} (hh : 0 < h) (x u : ℝ) :
    cellAverage h (x + u) (character k) =
      character k x * translatedCellResponse k h u := by
  rw [cellAverage]
  have hshift :
      (∫ y in (x + u) - h / 2..(x + u) + h / 2, character k y) =
        ∫ v in -h / 2..h / 2, character k (v + (x + u)) := by
    rw [intervalIntegral.integral_comp_add_right]
    congr 1 <;> ring
  have hchar (v : ℝ) : character k (v + (x + u)) =
      character k x * character k u * character k v := by
    rw [character_add, character_add]
    ring
  have hfactor :
      (∫ v in -h / 2..h / 2, character k (v + (x + u))) =
        (character k x * character k u) *
          (∫ v in -h / 2..h / 2, character k v) := by
    calc
      (∫ v in -h / 2..h / 2, character k (v + (x + u))) =
          ∫ v in -h / 2..h / 2, (character k x * character k u) * character k v := by
            apply intervalIntegral.integral_congr
            intro v _
            simpa using hchar v
      _ = (character k x * character k u) *
          (∫ v in -h / 2..h / 2, character k v) := by
            rw [intervalIntegral.integral_const_mul]
  rw [hshift, hfactor]
  calc
    h⁻¹ * (character k x * character k u *
        (∫ v in -h / 2..h / 2, character k v)) =
        (character k x * character k u) *
          (h⁻¹ * (∫ v in -h / 2..h / 2, character k v)) := by ring
    _ = character k x * translatedCellResponse k h u := by
      rw [centeredCharacterAverage k hh]
      simp [translatedCellResponse, mul_assoc]

/-- Fourier response of one actual translated-grid cell projection, with its
translation-dependent phase exposed. -/
theorem translatedGridCellProjection_character (k : ℤ) {h : ℝ} (hh : 0 < h)
    (x β : ℝ) :
    translatedGridCellProjection k h x β =
      character k x * translatedCellResponse k h
        (translatedCellCenterDisplacement h x β) := by
  rw [translatedGridCellProjection, translatedCellCenter_eq h hh.ne']
  exact cellAverage_character k hh x _

theorem translatedGridCellProjection_eq_phaseResponse (k : ℤ) {h : ℝ}
    (hh : 0 < h) (x β : ℝ) :
    translatedGridCellProjection k h x β =
      character k x * phaseCellResponse k h ((x - β) / h) := by
  rw [translatedGridCellProjection_character k hh x β]
  simp [phaseCellResponse, translatedCellCenterDisplacement]

theorem translatedGridCellProjection_intervalIntegrable (k : ℤ) {h : ℝ}
    (hh : 0 < h) (x : ℝ) {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable (translatedGridCellProjection k h x) MeasureSpace.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply Measure.integrableOn_of_bounded (μ := MeasureSpace.volume) (s := Set.Ioc a b)
      (M := 1)
  · rw [Real.volume_Ioc]
    finiteness
  · have hm : Measurable (translatedGridCellProjection k h x) := by
      have heq : (fun β : ℝ => translatedGridCellProjection k h x β) =
          fun β => character k x * phaseCellResponse k h ((x - β) / h) := by
        funext β
        exact translatedGridCellProjection_eq_phaseResponse k hh x β
      change Measurable (fun β : ℝ => translatedGridCellProjection k h x β)
      rw [heq]
      fun_prop [phaseCellResponse, translatedCellResponse, character]
    exact hm.aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun β => by
      rw [translatedGridCellProjection_eq_phaseResponse k hh x]
      rw [norm_mul, character_norm]
      simpa using phaseCellResponse_norm_le_one k h ((x - β) / h)

/-- As a function of the translation parameter, the actual cell projection
has period `h`; averaging one period therefore averages all possible centers
containing the fixed point. -/
theorem translatedGridCellProjection_periodic (k : ℤ) {h : ℝ} (hh : 0 < h)
    (x : ℝ) :
    Function.Periodic (translatedGridCellProjection k h x) h := by
  intro β
  rw [translatedGridCellProjection_character k hh x (β + h),
    translatedGridCellProjection_character k hh x β]
  rw [translatedCellCenterDisplacement_periodic h hh.ne' x]

/-- Integrating one period of the actual shifted-cell projection is the same
as integrating its centered phase over one full period. -/
theorem translatedGridCellProjection_onePeriod (k : ℤ) {h : ℝ} (hh : 0 < h)
    (x : ℝ) :
    (∫ β in 0..h, translatedGridCellProjection k h x β) =
      character k x * (h * (∫ t in 0..1, phaseCellResponse k h t)) := by
  set_option maxHeartbeats 500000 in
  have hcomp :
      (∫ β in 0..h, phaseCellResponse k h ((x - β) / h)) =
        (-h : ℝ) • (∫ t in x / h..x / h - 1, phaseCellResponse k h t) := by
    have hc : -h⁻¹ ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hh.ne')
    have hchange := intervalIntegral.integral_comp_add_mul
      (f := phaseCellResponse k h) (a := 0) (b := h) hc (x / h)
    have harg (β : ℝ) : (x - β) / h = x / h + -h⁻¹ * β := by
      field_simp
      ring
    calc
      (∫ β in 0..h, phaseCellResponse k h ((x - β) / h)) =
          ∫ β in 0..h, phaseCellResponse k h (x / h + -h⁻¹ * β) := by
            apply intervalIntegral.integral_congr
            intro β _
            exact congrArg (phaseCellResponse k h) (harg β)
      _ = (-h⁻¹)⁻¹ • (∫ t in x / h + -h⁻¹ * 0..x / h + -h⁻¹ * h,
            phaseCellResponse k h t) := hchange
      _ = (-h : ℝ) • (∫ t in x / h..x / h - 1, phaseCellResponse k h t) := by
            have hinv : (-h⁻¹)⁻¹ = -h := by field_simp [hh.ne']
            have hend : x / h + -h⁻¹ * h = x / h - 1 := by field_simp [hh.ne']; ring
            simp only [hinv, mul_zero, add_zero, hend]
  have hperiod := phaseCellResponse_periodic k h
  have htranslated :
      (∫ t in x / h - 1..x / h, phaseCellResponse k h t) =
        ∫ t in 0..1, phaseCellResponse k h t := by
    simpa only [sub_add_cancel, zero_add] using hperiod.intervalIntegral_add_eq (x / h - 1) 0
  calc
    (∫ β in 0..h, translatedGridCellProjection k h x β) =
        character k x * (∫ β in 0..h,
          phaseCellResponse k h ((x - β) / h)) := by
            calc
              (∫ β in 0..h, translatedGridCellProjection k h x β) =
                  ∫ β in 0..h, character k x * phaseCellResponse k h ((x - β) / h) := by
                    apply intervalIntegral.integral_congr
                    intro β _
                    exact translatedGridCellProjection_eq_phaseResponse k hh x β
              _ = character k x * (∫ β in 0..h,
                    phaseCellResponse k h ((x - β) / h)) := by
                    rw [intervalIntegral.integral_const_mul]
    _ = character k x *
          ((-h : ℝ) • (∫ t in x / h..x / h - 1, phaseCellResponse k h t)) := by
            rw [hcomp]
    _ = character k x *
          (h * (∫ t in x / h - 1..x / h, phaseCellResponse k h t)) := by
            rw [intervalIntegral.integral_symm]
            change character k x * (((-h : ℝ) : ℂ) *
              (-(∫ t in x / h - 1..x / h, phaseCellResponse k h t))) = _
            push_cast
            ring
    _ = character k x * (h * (∫ t in 0..1, phaseCellResponse k h t)) := by
            rw [htranslated]

/-- Averaging the actual cell projection over the possible cell centers
containing `x` removes its phase and gives the square-sinc multiplier.  This
is the one-dimensional translated-grid average (the center displacement is
uniform on `[-h/2,h/2]`). -/
theorem averagedCellProjection_character (k : ℤ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    h⁻¹ * (∫ u in -h / 2..h / 2, cellAverage h (x + u) (character k)) =
      character k x * ((Real.sinc (Real.pi * (k : ℝ) * h) : ℂ)) ^ 2 := by
  simp_rw [cellAverage_character k hh]
  calc
    h⁻¹ * (∫ u in -h / 2..h / 2,
        character k x * translatedCellResponse k h u) =
        h⁻¹ * (character k x * (∫ u in -h / 2..h / 2,
          translatedCellResponse k h u)) := by
            rw [intervalIntegral.integral_const_mul]
    _ = character k x * (h⁻¹ * (∫ u in -h / 2..h / 2,
          translatedCellResponse k h u)) := by ring
    _ = character k x * ((Real.sinc (Real.pi * (k : ℝ) * h) : ℂ)) ^ 2 := by
        rw [averagedTranslatedCellResponse k hh]

/-- The average of the fine-cell response minus the average of the coarse-cell
response is exactly the manuscript's detail multiplier.  Under a uniformly
translated grid, these are the two marginal center-displacement averages of
the same translation parameter. -/
theorem averagedHaarDetailMultiplier (k : ℤ) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    (h / 2)⁻¹ * (∫ u in -(h / 2) / 2..(h / 2) / 2,
        cellAverage (h / 2) (x + u) (character k)) -
      h⁻¹ * (∫ u in -h / 2..h / 2, cellAverage h (x + u) (character k)) =
      (((Real.sinc (Real.pi * (k : ℝ) * (h / 2)) : ℂ)) ^ 2 -
        ((Real.sinc (Real.pi * (k : ℝ) * h) : ℂ)) ^ 2) * character k x := by
  have hh2 : 0 < h / 2 := by linarith
  rw [averagedCellProjection_character k hh2 x,
    averagedCellProjection_character k hh x]
  ring

/-- The phase integral over one period is the centered-cell average. -/
theorem phaseCellResponse_unitIntegral (k : ℤ) {h : ℝ} (hh : 0 < h) :
    (∫ t in 0..1, phaseCellResponse k h t) =
      h⁻¹ * (∫ u in -h / 2..h / 2, translatedCellResponse k h u) := by
  have hfract :
      (∫ t in 0..1, phaseCellResponse k h t) =
        ∫ t in 0..1, translatedCellResponse k h (h * (1 / 2 - t)) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [MeasureSpace.volume.ae_ne (1 : ℝ)] with t hne
    intro ht
    have ht' : t ∈ Set.Ioc 0 1 := by simpa using ht
    have hself : Int.fract t = t := Int.fract_eq_self.mpr
      ⟨le_of_lt ht'.1, lt_of_le_of_ne ht'.2 hne⟩
    simp [phaseCellResponse, hself]
  rw [hfract]
  have hc : -h ≠ 0 := by linarith
  have hchange :
      (∫ t in 0..1, translatedCellResponse k h (h * (1 / 2 - t))) =
        (-h)⁻¹ • (∫ u in h / 2..-h / 2, translatedCellResponse k h u) := by
    have hlinear (t : ℝ) : h * (1 / 2 - t) = h / 2 + -h * t := by ring
    calc
      (∫ t in 0..1, translatedCellResponse k h (h * (1 / 2 - t))) =
          ∫ t in 0..1, translatedCellResponse k h (h / 2 + -h * t) := by
            apply intervalIntegral.integral_congr
            intro t _
            exact congrArg (translatedCellResponse k h) (hlinear t)
      _ = (-h)⁻¹ • (∫ u in h / 2..-h / 2, translatedCellResponse k h u) := by
            have hchange := intervalIntegral.integral_comp_add_mul
              (f := translatedCellResponse k h) (a := 0) (b := 1) hc (h / 2)
            convert hchange using 1 <;> congr 2 <;> ring
  rw [hchange, intervalIntegral.integral_symm]
  rw [inv_neg, neg_smul]
  simp

/-- A periodic integrand whose period is a reciprocal integer averages over
the unit circle by repeating one period.  This is the bookkeeping step for
passing from translation on `AddCircle 1` to a uniform center-displacement
average at dyadic scale. -/
theorem integral_periodic_reciprocal {m : ℕ} (hm : 0 < m) (f : ℝ → ℂ)
    (hf : Function.Periodic f ((m : ℝ)⁻¹))
    (hfi : IntervalIntegrable f MeasureSpace.volume 0 ((m : ℝ)⁻¹)) :
    (∫ x in 0..1, f x) = (m : ℝ) • (∫ x in 0..(m : ℝ)⁻¹, f x) := by
  have hlen : (m : ℤ) • ((m : ℝ)⁻¹) = (1 : ℝ) := by
    rw [zsmul_eq_mul]
    norm_cast
    field_simp
  have hfi' : ∀ a b : ℝ, IntervalIntegrable f MeasureSpace.volume a b :=
    hf.intervalIntegrable₀ (by positivity) hfi
  calc
    (∫ x in 0..1, f x) = ∫ x in 0..(m : ℤ) • ((m : ℝ)⁻¹), f x := by rw [hlen]
    _ = (m : ℤ) • (∫ x in 0..(m : ℝ)⁻¹, f x) := by
      simpa [zero_add] using hf.intervalIntegral_add_zsmul_eq (m : ℤ) 0 hfi'
    _ = (m : ℝ) • (∫ x in 0..(m : ℝ)⁻¹, f x) := by
      simp only [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℝ]

/-- The actual uniform translation average on the unit circle is the
center-displacement average.  Here `h=1/m` is a genuine dyadic cell width. -/
theorem translatedGridCellProjection_unitAverage (m : ℕ) (hm : 0 < m)
    (k : ℤ) (x : ℝ) :
    (∫ β in 0..1,
      translatedGridCellProjection k ((m : ℝ)⁻¹) x β) =
      character k x *
        (∫ t in 0..1, phaseCellResponse k ((m : ℝ)⁻¹) t) := by
  have hpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hperiod := translatedGridCellProjection_periodic (k := k)
    (h := (m : ℝ)⁻¹) (by positivity) x
  have hfi := translatedGridCellProjection_intervalIntegrable (k := k)
    (h := (m : ℝ)⁻¹) (by positivity) x
    (a := 0) (b := (m : ℝ)⁻¹) (by positivity)
  rw [integral_periodic_reciprocal (m := m) hm
    (f := translatedGridCellProjection k ((m : ℝ)⁻¹) x) hperiod hfi]
  rw [translatedGridCellProjection_onePeriod (k := k) (h := (m : ℝ)⁻¹)
    (by positivity) x]
  have hcancel : (m : ℝ) * (m : ℝ)⁻¹ = 1 := by field_simp [hpos.ne']
  have hcancelC : (m : ℂ) * ((m : ℝ)⁻¹ : ℂ) = 1 := by exact_mod_cast hcancel
  calc
    (↑m : ℂ) * (character k x * ((m : ℝ)⁻¹ *
        (∫ t in 0..1, phaseCellResponse k ((m : ℝ)⁻¹) t))) =
        character k x * (∫ t in 0..1, phaseCellResponse k ((m : ℝ)⁻¹) t) := by
          calc
            _ = ((m : ℂ) * ((m : ℝ)⁻¹ : ℂ)) *
                (character k x * (∫ t in 0..1,
                  phaseCellResponse k ((m : ℝ)⁻¹) t)) := by
                    push_cast
                    ring
            _ = 1 * (character k x * (∫ t in 0..1,
                  phaseCellResponse k ((m : ℝ)⁻¹) t)) := by rw [hcancelC]
            _ = _ := by simp

/-- One-frequency average of the actual translated dyadic conditional
expectation, with the circle translation integrated over one full period. -/
theorem translatedGridCellProjection_squareSinc (m : ℕ) (hm : 0 < m)
    (k : ℤ) (x : ℝ) :
    (∫ β in 0..1,
      translatedGridCellProjection k ((m : ℝ)⁻¹) x β) =
      character k x *
        ((Real.sinc (Real.pi * (k : ℝ) * (m : ℝ)⁻¹) : ℂ)) ^ 2 := by
  rw [translatedGridCellProjection_unitAverage m hm k x,
    phaseCellResponse_unitIntegral k (by positivity)]
  rw [averagedTranslatedCellResponse k (by positivity)]

/-- The actual translation-averaged Haar detail multiplier at adjacent dyadic
scales is `sinc²(πu/2)-sinc²(πu)`, including the character phase at `x`. -/
theorem translatedGridHaarDetailMultiplier (m : ℕ) (hm : 0 < m)
    (k : ℤ) (x : ℝ) :
    (∫ β in 0..1,
      (translatedGridCellProjection k (((2 * m : ℕ) : ℝ)⁻¹) x β -
        translatedGridCellProjection k ((m : ℝ)⁻¹) x β)) =
      (((Real.sinc (Real.pi * (k : ℝ) * (((2 * m : ℕ) : ℝ)⁻¹)) : ℂ)) ^ 2 -
        ((Real.sinc (Real.pi * (k : ℝ) * (m : ℝ)⁻¹) : ℂ)) ^ 2) * character k x := by
  have hdouble : (((2 * m : ℕ) : ℝ)⁻¹) = ((m : ℝ)⁻¹) / 2 := by
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    calc
      (((2 * m : ℕ) : ℝ)⁻¹) = (2 * (m : ℝ))⁻¹ := by simp
      _ = ((m : ℝ)⁻¹) / 2 := by
        field_simp [hmpos.ne']
  rw [intervalIntegral.integral_sub]
  · rw [translatedGridCellProjection_squareSinc (2 * m) (by omega) k x,
      translatedGridCellProjection_squareSinc m hm k x]
    rw [hdouble]
    ring
  · exact translatedGridCellProjection_intervalIntegrable k (by positivity) x
      (a := 0) (b := 1) (by norm_num)
  · exact translatedGridCellProjection_intervalIntegrable k (by positivity) x
      (a := 0) (b := 1) (by norm_num)

end HaarQuarter.TrigonometricHaarExtraction
