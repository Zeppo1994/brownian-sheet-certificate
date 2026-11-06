import BrownianSharp.AlignmentPaperAnchoredLpReflectionTensor
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import BrownianSharp.TorusFoundations
import BrownianSharp.BrownianCubeSpan
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Topology.ContinuousMap.Algebra

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension

open BrownianSharp.AlignmentPaperAnchoredLpReflection
open BrownianSharp.AlignmentPaperAnchoredLpReflectionTensor
open BrownianSharp.Torus
open HaarQuarter

/-- The continuous triangular fold from the unit circle to the unit interval.
The fundamental interval has length one; doubling its representative gives
the full reflected source interval. -/
def triangleWave (x : UnitAddCircle) : ℝ :=
  AddCircle.liftIco (1:ℝ) 0 (fun t => foldUnitInterval (2*t)) x

theorem continuous_triangleWave : Continuous triangleWave := by
  unfold triangleWave
  apply AddCircle.liftIco_zero_continuous (p := (1:ℝ))
  · simp [foldUnitInterval]
  · have hmul : Continuous (fun t : ℝ => (2:ℝ)*t) :=
      (continuous_const : Continuous fun _ : ℝ => (2:ℝ)).mul continuous_id
    exact ((continuous_id.min
      ((continuous_const : Continuous fun _ : ℝ => (2:ℝ)).sub continuous_id)).comp
        hmul).continuousOn

theorem triangleWave_mem_Icc (x : UnitAddCircle) :
    triangleWave x ∈ Set.Icc (0:ℝ) 1 := by
  obtain ⟨t, ht, htx⟩ := AddCircle.eq_coe_Ico x
  have ht' : t ∈ Set.Ico (0:ℝ) (0+1) := by simpa using ht
  rw [← htx, triangleWave, AddCircle.liftIco_coe_apply ht']
  constructor
  · unfold foldUnitInterval
    apply le_min
    · exact mul_nonneg (by norm_num) ht.1
    · have ht0 : 0 ≤ t := ht.1
      have ht1 : t ≤ 1 := ht.2.le
      linarith
  · unfold foldUnitInterval
    by_cases h : 2*t ≤ 1
    · exact (min_le_left _ _).trans h
    · have ht1 : t ≤ 1 := ht.2.le
      exact (min_le_right _ _).trans (by linarith)

/-- Fold each unit-circle coordinate into the original cube. -/
def periodicFoldAnchor (d : ℕ) (x : UnitAddTorus (Fin d)) :
    BrownianCubeAnchor d :=
  ⟨fun i => triangleWave (x i), fun i => triangleWave_mem_Icc (x i)⟩

/-- The representative in the half-open fundamental interval `[0,1)`. -/
def circleIcoRepresentative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1:ℝ) 0 x).val

/-- The right-closed representative, chosen to match the standard periodic
integral fundamental domain `(0,1]`. -/
def circleIocRepresentative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIoc (1:ℝ) 0 x).val

theorem circleIcoRepresentative_mem (x : UnitAddCircle) :
    circleIcoRepresentative x ∈ Set.Ico (0:ℝ) 1 :=
  by simpa [circleIcoRepresentative] using
    (AddCircle.equivIco (1:ℝ) 0 x).property

theorem triangleWave_eq_fold_representative (x : UnitAddCircle) :
    triangleWave x = foldUnitInterval (2 * circleIcoRepresentative x) := by
  rfl

theorem measurable_circleIocRepresentative : Measurable circleIocRepresentative := by
  unfold circleIocRepresentative
  exact measurable_subtype_coe.comp
    (AddCircle.measurableEquivIoc (T := (1:ℝ)) 0).measurable

theorem measurePreserving_circleIocRepresentative :
    MeasurePreserving circleIocRepresentative (volume : Measure UnitAddCircle)
      (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
  have h := AddCircle.measurePreserving_equivIoc (T := (1:ℝ)) (a := 0)
  convert (measurePreserving_subtype_coe measurableSet_Ioc).comp h using 1 <;>
    norm_num <;> funext x <;> rfl

theorem continuous_periodicFoldAnchor (d : ℕ) :
    Continuous (periodicFoldAnchor d) := by
  exact (continuous_pi fun i =>
    continuous_triangleWave.comp (continuous_apply i)).subtype_mk
      (fun x i => triangleWave_mem_Icc (x i))

/-- Periodic extension of a continuous cube path by reflecting each
coordinate at both endpoints. -/
def periodicFoldExtension {d : ℕ}
    (f : C(BrownianCubeAnchor d, ℝ)) : RealPeriodic d :=
  ⟨fun x => f (periodicFoldAnchor d x),
    f.continuous.comp (continuous_periodicFoldAnchor d)⟩

/-- The cube is recovered from the first half of the unit-periodic extension.
This is the rescaling needed because the source reflection has period two. -/
theorem periodicFoldExtension_halfCube {d : ℕ}
    (f : C(BrownianCubeAnchor d, ℝ)) (t : BrownianCubeAnchor d) :
    periodicFoldExtension f (fun i => ((t.val i / 2 : ℝ) : UnitAddCircle)) = f t := by
  apply congrArg f
  apply Subtype.ext
  funext i
  change triangleWave ((t.val i / 2 : ℝ) : UnitAddCircle) = t.val i
  unfold triangleWave
  rw [AddCircle.liftIco_coe_apply]
  · have ht := (t.property i)
    simp only [foldUnitInterval]
    rw [show 2 * (t.val i / 2) = t.val i by ring]
    exact min_eq_left (by linarith [ht.2])
  · constructor
    · have ht := (t.property i).1
      linarith
    · have ht := (t.property i).2
      norm_num
      linarith

end BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
