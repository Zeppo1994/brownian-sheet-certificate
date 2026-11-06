import BrownianSharp.AlignmentPaperContinuumVariance
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed

noncomputable section
open MeasureTheory
open Filter
open scoped Topology

namespace BrownianSharp.AlignmentPaperContinuumResidual

open BrownianSharp.AlignmentPaperContinuumHulls
open BrownianSharp.AlignmentPaperContinuumVariance
open BrownianSharp.AlignmentPaperContinuumGoodRegion

/-- The terminal residual in spatial coordinates has exactly the tensor
coordinate residual measure. -/
theorem spatialPairCoordinateResidual_measure_eq {d : ℕ} (N : ℕ) :
    ((cubeLebesgue d).prod (cubeLebesgue d))
        (spatialPairCoordinateResidual (d := d) N) =
      coordinatePairLebesgue d (tensorCoordinateResidual (d := d) N) := by
  let e := (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d)).symm
  have hMP := measurePreserving_cubePairEquiv_coordinatePairLebesgue d
  have hs : MeasurableSet (tensorCoordinateResidual (d := d) N) := by
    exact (spatialPairCoordinateResidual_measurable (d := d) N).preimage
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin d)).measurable
  have hpre : e ⁻¹' tensorCoordinateResidual (d := d) N =
      spatialPairCoordinateResidual (d := d) N := by
    ext p
    rfl
  calc
    _ = ((cubeLebesgue d).prod (cubeLebesgue d))
        (e ⁻¹' tensorCoordinateResidual (d := d) N) := by rw [hpre]
    _ = Measure.map e ((cubeLebesgue d).prod (cubeLebesgue d))
        (tensorCoordinateResidual (d := d) N) := by
          rw [Measure.map_apply e.measurable hs]
    _ = coordinatePairLebesgue d (tensorCoordinateResidual (d := d) N) := by
          rw [hMP.map_eq]

/-- Literal residual pair-cube volume bound, before taking real-valued
integrals. -/
theorem spatialPairCoordinateResidual_measure_le {d : ℕ} (N : ℕ) :
    ((cubeLebesgue d).prod (cubeLebesgue d))
        (spatialPairCoordinateResidual (d := d) N) ≤
      (d : ENNReal) * ENNReal.ofReal ((1 / 2 : ℝ) ^ N) := by
  rw [spatialPairCoordinateResidual_measure_eq]
  exact tensorCoordinateResidual_measure_le (d := d) N

/-- The corresponding real-valued residual-volume estimate used in the
integral remainder. -/
theorem spatialPairCoordinateResidual_real_measure_le {d : ℕ} (N : ℕ) :
    ((cubeLebesgue d).prod (cubeLebesgue d)).real
        (spatialPairCoordinateResidual (d := d) N) ≤
      (d : ℝ) * (1 / 2 : ℝ) ^ N := by
  rw [measureReal_def]
  have h := spatialPairCoordinateResidual_measure_le (d := d) N
  have hfinite :
      (d : ENNReal) * ENNReal.ofReal ((1 / 2 : ℝ) ^ N) ≠ ⊤ := by
    finiteness
  calc
    ENNReal.toReal
        (((cubeLebesgue d).prod (cubeLebesgue d))
          (spatialPairCoordinateResidual (d := d) N)) ≤
      ENNReal.toReal ((d : ENNReal) * ENNReal.ofReal ((1 / 2 : ℝ) ^ N)) :=
        ENNReal.toReal_mono hfinite h
    _ = (d : ℝ) * (1 / 2 : ℝ) ^ N := by simp

end BrownianSharp.AlignmentPaperContinuumResidual
