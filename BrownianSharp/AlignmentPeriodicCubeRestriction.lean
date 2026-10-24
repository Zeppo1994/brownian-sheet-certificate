import BrownianSharp.TorusFoundations
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentIsometricEntropy
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.ContinuousMap.Algebra

/-! Restriction of periodic continuous functions to a closed fundamental cube
preserves the uniform norm exactly. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped RealInnerProductSpace
namespace BrownianSharp.AlignmentPeriodicCubeRestriction
open Torus

def cubeToTorus (d : ℕ) : C(BrownianCubeAnchor d, UnitAddTorus (Fin d)) where
  toFun t i := (t.val i : UnitAddCircle)
  continuous_toFun := continuous_pi fun i =>
    (AddCircle.continuous_mk' (1:ℝ)).comp
      ((continuous_apply i).comp continuous_subtype_val)

theorem cubeToTorus_surjective (d : ℕ) : Function.Surjective (cubeToTorus d) := by
  intro x
  let a : Fin d → Set.Ico (0:ℝ) (0+1) := fun i => AddCircle.equivIco (1:ℝ) 0 (x i)
  let t : BrownianCubeAnchor d := ⟨fun i => (a i).val, fun i => by
    have hi := (a i).property
    exact ⟨hi.1, by simpa using hi.2.le⟩⟩
  refine ⟨t,?_⟩
  funext i
  exact AddCircle.coe_equivIco

def periodicCubeRestriction (d : ℕ) :
    RealPeriodic d →L[ℝ] C(BrownianCubeAnchor d,ℝ) :=
  ContinuousMap.compCLM ℝ ℝ (cubeToTorus d)

theorem periodicCubeRestriction_apply {d : ℕ} (f : RealPeriodic d)
    (t : BrownianCubeAnchor d) :
    periodicCubeRestriction d f t = f (fun i => (t.val i : UnitAddCircle)) := rfl

theorem periodicCubeRestriction_norm {d : ℕ} (f : RealPeriodic d) :
    ‖periodicCubeRestriction d f‖ = ‖f‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro t
    exact f.norm_coe_le_norm (cubeToTorus d t)
  · apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro x
    obtain ⟨t,rfl⟩ := cubeToTorus_surjective d x
    exact (periodicCubeRestriction d f).norm_coe_le_norm t

theorem periodicCubeRestriction_isometry (d : ℕ) :
    Isometry (periodicCubeRestriction d) := by
  apply isometry_iff_dist_eq.mpr
  intro f g
  rw [dist_eq_norm, ← map_sub, periodicCubeRestriction_norm, dist_eq_norm]

end BrownianSharp.AlignmentPeriodicCubeRestriction
