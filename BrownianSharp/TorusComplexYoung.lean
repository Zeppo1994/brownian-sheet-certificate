import BrownianSharp.CompactGroupComplexYoung
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Group.Prod

noncomputable section
open MeasureTheory
open UnitAddTorus

namespace BrownianSharp

/-- Complex Young inequality for convolution on a finite product of unit
circles with its product Haar probability measure. -/
theorem unitAddTorus_complex_convolution_rpow_le {d : ℕ}
    (K u : C(UnitAddTorus (Fin d), ℂ)) (p : ℝ) (hp : 1 ≤ p) :
    (∫ x : UnitAddTorus (Fin d),
      ‖∫ y : UnitAddTorus (Fin d), K y * u (x-y)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∫ y : UnitAddTorus (Fin d), ‖K y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p *
      (∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) := by
  let μ : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have htrans : ∀ y : UnitAddTorus (Fin d),
      MeasurePreserving (fun x : UnitAddTorus (Fin d) => x-y) μ μ := by
    intro y
    letI : Measure.IsAddLeftInvariant μ := inferInstance
    simpa [sub_eq_add_neg, add_comm] using measurePreserving_add_left μ (-y)
  simpa [μ] using compactGroup_complex_convolution_rpow_le μ htrans K u p hp

end BrownianSharp

end
