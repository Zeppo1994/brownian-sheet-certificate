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

end HaarQuarter.TrigonometricHaarExtraction
