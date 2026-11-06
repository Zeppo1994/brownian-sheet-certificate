import BrownianSharp.SmoothVariance
import BrownianSharp.AlignmentPaperSpatialVariance
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Continuous spatial version of the smooth-layer energy and good set.

The construction below is over the actual cube with Lebesgue restriction;
it does not identify this measure with the midpoint grid. -/

noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
open MeasureTheory
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperContinuumGoodRegion

def cubeSet (d : ℕ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1)

def cubeLebesgue (d : ℕ) : Measure (Fin d → ℝ) :=
  volume.restrict (cubeSet d)

theorem cubeLebesgue_eq_pi (d : ℕ) :
    cubeLebesgue d =
      Measure.pi (fun _ : Fin d =>
        volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  rw [cubeLebesgue, volume_pi]
  change (Measure.pi (fun _ : Fin d => volume)).restrict
      (Set.univ.pi (fun _ : Fin d => Set.Icc (0 : ℝ) 1)) = _
  rw [Measure.restrict_pi_pi]

theorem cubeLebesgue_univ (d : ℕ) :
    cubeLebesgue d Set.univ = 1 := by
  rw [cubeLebesgue_eq_pi]
  simp [Measure.pi_univ]

instance cubeLebesgue_probability (d : ℕ) :
    IsProbabilityMeasure (cubeLebesgue d) where
  measure_univ := cubeLebesgue_univ d

def smoothCubeAtom {d n : ℕ} (x : Fin d → ℝ)
    (a : LayerIndex d n) : ℝ :=
  ∏ i : Fin d,
    smoothAtom ((2 : ℝ) ^ layerIndexDepth a i * x i -
      (layerIndexCell a i : ℝ))

end BrownianSharp.AlignmentPaperContinuumGoodRegion
