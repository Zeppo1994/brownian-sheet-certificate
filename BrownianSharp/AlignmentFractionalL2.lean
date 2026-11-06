import BrownianSharp.AlignmentFractionalKernel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.CompactOpen

/-! Fixed-interval `L²` realizations of the fractional kernel. -/

noncomputable section
open MeasureTheory
open scoped BoundedContinuousFunction

namespace BrownianSharp.AlignmentFractionalL2

open BrownianSharp.AlignmentFractionalKernel

/-- The causal RL kernel viewed as a function on the fixed source interval. -/
def causalKernel (α t u : ℝ) : ℝ :=
  if u < t then kernel α (t - u) else 0

/-- The causal kernel is square-integrable on the fixed unit source interval.
The singular part is precisely the translated `[0,t]` kernel; above `t` it
vanishes. -/
theorem causalKernel_memLp_unit {α t : ℝ} (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    MemLp (fun u : ℝ => causalKernel α t u) 2
      (volume.restrict (Set.Icc 0 1)) := by
  have hbase : IntervalIntegrable (fun u : ℝ => kernel α (t-u)) volume 0 t := by
    have hker : IntervalIntegrable (kernel α) volume 0 t := kernel_intervalIntegrable hα
    have hshift := hker.comp_sub_left t
    simpa using hshift.symm
  have hbaseSq : IntervalIntegrable (fun u : ℝ => (kernel α (t-u))^2) volume 0 t := by
    have hker : IntervalIntegrable (fun x : ℝ => (kernel α x)^2) volume 0 t :=
      kernel_sq_intervalIntegrable hα ht0
    have hshift := hker.comp_sub_left t
    simpa using hshift.symm
  have hleft : IntervalIntegrable (fun u : ℝ => causalKernel α t u) volume 0 t := by
    have heq : Set.EqOn (fun u : ℝ => causalKernel α t u)
        (fun u => kernel α (t-u)) (Set.uIoo 0 t) := by
      intro u hu
      have hu0 : 0 < u := by
        simpa [Set.uIoo, min_eq_left ht0] using hu.1
      have hut : u < t := by
        have hmax : u < max (0:ℝ) t := by simpa [Set.uIoo, min_eq_left ht0] using hu.2
        rcases lt_max_iff.mp hmax with h | h
        · linarith
        · exact h
      simp [causalKernel, hut]
    exact (intervalIntegrable_congr_uIoo heq).mpr hbase
  have hleftSq : IntervalIntegrable (fun u : ℝ => (causalKernel α t u)^2) volume 0 t := by
    have heq : Set.EqOn (fun u : ℝ => (causalKernel α t u)^2)
        (fun u => (kernel α (t-u))^2) (Set.uIoo 0 t) := by
      intro u hu
      have hu0 : 0 < u := by
        simpa [Set.uIoo, min_eq_left ht0] using hu.1
      have hut : u < t := by
        have hmax : u < max (0:ℝ) t := by simpa [Set.uIoo, min_eq_left ht0] using hu.2
        rcases lt_max_iff.mp hmax with h | h
        · linarith
        · exact h
      simp [causalKernel, hut]
    exact (intervalIntegrable_congr_uIoo heq).mpr hbaseSq
  have hright : IntervalIntegrable (fun u : ℝ => causalKernel α t u) volume t 1 := by
    have heq : Set.EqOn (fun u : ℝ => causalKernel α t u)
        (fun _ => (0:ℝ)) (Set.uIoo t 1) := by
      intro u hu
      have huLow : t < u := by
        have hmin : min t (1:ℝ) < u := by simpa [Set.uIoo] using hu.1
        rcases min_lt_iff.mp hmin with h | h
        · exact h
        · linarith
      simp [causalKernel, le_of_lt huLow]
    have hz : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume t 1 := by
      exact continuous_const.intervalIntegrable t 1
    exact (intervalIntegrable_congr_uIoo heq).mpr hz
  have hrightSq : IntervalIntegrable (fun u : ℝ => (causalKernel α t u)^2) volume t 1 := by
    have heq : Set.EqOn (fun u : ℝ => (causalKernel α t u)^2)
        (fun _ => (0:ℝ)) (Set.uIoo t 1) := by
      intro u hu
      have huLow : t < u := by
        have hmin : min t (1:ℝ) < u := by simpa [Set.uIoo] using hu.1
        rcases min_lt_iff.mp hmin with h | h
        · exact h
        · linarith
      simp [causalKernel, le_of_lt huLow]
    have hz : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume t 1 := by
      exact continuous_const.intervalIntegrable t 1
    exact (intervalIntegrable_congr_uIoo heq).mpr hz
  have h : IntervalIntegrable (fun u : ℝ => causalKernel α t u) volume 0 1 :=
    hleft.trans hright
  have hs : IntervalIntegrable (fun u : ℝ => (causalKernel α t u)^2) volume 0 1 :=
    hleftSq.trans hrightSq
  have h1 : Integrable (fun u : ℝ => causalKernel α t u)
      (volume.restrict (Set.Icc 0 1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp h
  have h2 : Integrable (fun u : ℝ => (causalKernel α t u)^2)
      (volume.restrict (Set.Icc 0 1)) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (0:ℝ) ≤ 1)).mp hs
  exact (memLp_two_iff_integrable_sq h1.aestronglyMeasurable).2 h2

/-- The source Hilbert space for the fixed unit interval. -/
abbrev UnitL2 := Lp ℝ 2 (volume.restrict (Set.Icc (0:ℝ) 1))

/-- The causal kernel represented as an element of the source Hilbert space. -/
noncomputable def kernelVector (α t : ℝ) (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : UnitL2 :=
  MemLp.toLp (fun u : ℝ => causalKernel α t u)
    (causalKernel_memLp_unit hα ht0 ht1)

/-- Bounded linear evaluation against the fractional kernel. -/
noncomputable def evaluationFunctional (α t : ℝ) (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : UnitL2 →L[ℝ] ℝ :=
  innerSL ℝ (kernelVector α t hα ht0 ht1)

/-- The evaluation functional is bounded with norm equal to the `L²` norm of
its kernel vector. -/
theorem evaluationFunctional_norm (α t : ℝ) (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖evaluationFunctional α t hα ht0 ht1‖ = ‖kernelVector α t hα ht0 ht1‖ := by
  rw [evaluationFunctional]
  exact innerSL_apply_norm (𝕜 := ℝ) (E := UnitL2) (kernelVector α t hα ht0 ht1)

/-- The bounded functional agrees with integration against the causal kernel. -/
theorem evaluationFunctional_apply (α t : ℝ) (hα : 1/2 < α)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (g : UnitL2) :
    evaluationFunctional α t hα ht0 ht1 g =
      ∫ u, causalKernel α t u * g u ∂(volume.restrict (Set.Icc (0:ℝ) 1)) := by
  rw [evaluationFunctional, innerSL_apply_apply, MeasureTheory.L2.inner_def]
  have hk : kernelVector α t hα ht0 ht1 =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
      (fun u : ℝ => causalKernel α t u) := by
    exact MemLp.coeFn_toLp (causalKernel_memLp_unit hα ht0 ht1)
  apply integral_congr_ae
  filter_upwards [hk] with u hu
  change (g u) * (kernelVector α t hα ht0 ht1) u =
      causalKernel α t u * (g u)
  rw [hu]
  ring

/-- The unit interval as the compact parameter and source space. -/
abbrev UnitInterval := Set.Icc (0:ℝ) 1

/-- Clamp a real source coordinate to the unit interval. -/
def clipUnit (x : ℝ) : UnitInterval :=
  ⟨min 1 (max 0 x), ⟨le_min (by norm_num) (le_max_left 0 x), min_le_left _ _⟩⟩

theorem clipUnit_continuous : Continuous clipUnit := by
  apply Continuous.subtype_mk
  fun_prop

/-- Extend a continuous unit-interval profile to a bounded continuous function
on the real line by evaluating it at the clipped coordinate. -/
noncomputable def extendUnitProfile :
    C(UnitInterval, ℝ) →L[ℝ] (ℝ →ᵇ ℝ) := by
  let L : C(UnitInterval, ℝ) →ₗ[ℝ] (ℝ →ᵇ ℝ) := {
    toFun := fun f => ⟨⟨fun x => f (clipUnit x), f.continuous.comp clipUnit_continuous⟩,
      ⟨2 * ‖f‖, fun x y => by
        calc
          dist (f (clipUnit x)) (f (clipUnit y)) ≤
              ‖f (clipUnit x)‖ + ‖f (clipUnit y)‖ := dist_le_norm_add_norm _ _
          _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
          _ = 2 * ‖f‖ := by ring⟩⟩
    map_add' f g := by ext x; rfl
    map_smul' c f := by ext x; rfl
  }
  refine LinearMap.mkContinuous L 1 ?_
  intro f
  calc
    ‖L f‖ ≤ ‖f‖ := by
      rw [BoundedContinuousFunction.norm_le (norm_nonneg f)]
      intro x
      exact f.norm_coe_le_norm (clipUnit x)
    _ = 1 * ‖f‖ := by ring

end BrownianSharp.AlignmentFractionalL2
