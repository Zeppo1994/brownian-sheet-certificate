import BrownianSharp.TorusFoundations
import Mathlib.Tactic

/-! The manuscript's normalized torus volume is the explicit product Haar
measure used by the scalar and tensor operator estimates. -/
noncomputable section
open MeasureTheory
namespace BrownianSharp

theorem unitAddCircle_volume_eq_haar :
    (volume : Measure UnitAddCircle) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle]
  norm_num

theorem unitAddTorus_volume_eq_productHaar (d : ℕ) :
    (volume : Measure (UnitAddTorus (Fin d))) =
      Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle) := by
  change Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle)) = _
  simp only [unitAddCircle_volume_eq_haar]

end BrownianSharp
