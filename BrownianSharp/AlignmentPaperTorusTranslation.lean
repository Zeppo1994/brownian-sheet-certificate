import BrownianSharp.TorusFoundations
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Translation invariance for the genuine torus Lp source. These interfaces
make no sampling or finite-feature replacement of that source. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperTorusTranslation

abbrev torusMeasure (d : ℕ) : Measure (UnitAddTorus (Fin d)) :=
  Measure.pi fun _ : Fin d => AddCircle.haarAddCircle

theorem torusMeasure_eq_volume (d : ℕ) : torusMeasure d = volume := by
  have hc : AddCircle.haarAddCircle = (volume : Measure UnitAddCircle) := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1:ℝ))).symm
  simp only [torusMeasure, hc]
  rfl

instance torusMeasure_negInvariant (d : ℕ) : (torusMeasure d).IsNegInvariant := by
  rw [torusMeasure_eq_volume]
  infer_instance

theorem sub_left_measurePreserving {d : ℕ} (x : UnitAddTorus (Fin d)) :
    MeasurePreserving (fun y : UnitAddTorus (Fin d) => x-y)
      (torusMeasure d) (torusMeasure d) := by
  simpa [sub_eq_add_neg, Function.comp_def] using
    (measurePreserving_add_left (torusMeasure d) x).comp (Measure.measurePreserving_neg (torusMeasure d))

variable {E : Type*} [NormedAddCommGroup E]

theorem integral_norm_rpow_sub_left {d : ℕ}
    (f : UnitAddTorus (Fin d) → E) (p : ℝ) (x : UnitAddTorus (Fin d)) :
    (∫ y, ‖f (x-y)‖ ^ p ∂torusMeasure d) =
      ∫ y, ‖f y‖ ^ p ∂torusMeasure d := by
  exact integral_sub_left_eq_self (fun y => ‖f y‖ ^ p) (torusMeasure d) x

end BrownianSharp.AlignmentPaperTorusTranslation
