import BrownianSharp.AlignmentPaperAnchoredLp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The first-half identity underlying the reflection extension of anchored
primitives. The second half requires one affine change of variables and an
interval subdivision. -/

noncomputable section
open intervalIntegral
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperAnchoredLpReflection

/-- The one-dimensional fold map from the doubled interval to the unit
interval. -/
def foldUnitInterval (x : ℝ) : ℝ := min x (2-x)

/-- Integration of a folded source over the doubled interval counts the
unit-interval source exactly twice. This is the one-coordinate measure
identity used when tensorizing the reflection. -/
theorem integral_foldUnitInterval (g : ℝ → ℝ)
    (hg : IntegrableOn g (Set.Icc 0 1) volume) :
    (∫ x in (0:ℝ)..2, g (foldUnitInterval x)) =
      2 * ∫ x in (0:ℝ)..1, g x := by
  have hg01 : IntervalIntegrable g volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).2 hg
  have hfold01 : IntervalIntegrable (fun x => g (foldUnitInterval x)) volume 0 1 :=
    hg01.congr_uIoo (by
      intro x hx
      have hx' : x ∈ Set.Ioo (0:ℝ) 1 := by simpa using hx
      have hmin : min x (2-x) = x := min_eq_left (by linarith [hx'.2])
      simp [foldUnitInterval, hmin])
  have hcomp : IntervalIntegrable (fun x => g (2-x)) volume 1 2 := by
    have h := (hg01.comp_sub_left 2).symm
    convert h using 1 <;> norm_num
  have hfold12 : IntervalIntegrable (fun x => g (foldUnitInterval x)) volume 1 2 :=
    hcomp.congr_uIoo (by
      intro x hx
      have hx' : x ∈ Set.Ioo (1:ℝ) 2 := by simpa using hx
      have hmin : min x (2-x) = 2-x := min_eq_right (by linarith [hx'.1])
      simp [foldUnitInterval, hmin])
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hfold01 hfold12
  have hleft : (∫ x in (0:ℝ)..1, g (foldUnitInterval x)) =
      ∫ x in (0:ℝ)..1, g x := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro x hx
    have hx' : x ∈ Set.Ioo (0:ℝ) 1 := by simpa using hx
    have hmin : min x (2-x) = x := min_eq_left (by linarith [hx'.2])
    simp [foldUnitInterval, hmin]
  have hright : (∫ x in (1:ℝ)..2, g (foldUnitInterval x)) =
      ∫ x in (0:ℝ)..1, g x := by
    calc
      (∫ x in (1:ℝ)..2, g (foldUnitInterval x)) =
          ∫ x in (1:ℝ)..2, g (2-x) := by
            apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
            intro x hx
            have hx' : x ∈ Set.Ioo (1:ℝ) 2 := by simpa using hx
            have hmin : min x (2-x) = 2-x := min_eq_right (by linarith [hx'.1])
            simp [foldUnitInterval, hmin]
      _ = ∫ x in (0:ℝ)..1, g x := by
            rw [intervalIntegral.integral_comp_sub_left]
            norm_num
  calc
    (∫ x in (0:ℝ)..2, g (foldUnitInterval x)) =
        (∫ x in (0:ℝ)..1, g (foldUnitInterval x)) +
          ∫ x in (1:ℝ)..2, g (foldUnitInterval x) := hsplit.symm
    _ = 2 * ∫ x in (0:ℝ)..1, g x := by rw [hleft, hright]; ring

end BrownianSharp.AlignmentPaperAnchoredLpReflection
