import BrownianSharp.AlignmentPaperContinuumHulls
import BrownianSharp.AlignmentPaperSpatialVariance
import BrownianSharp.AlignmentPaperSupportedRows
import BrownianSharp.ShapeGrowth
import BrownianSharp.Moments

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperContinuumVariance

open AlignmentPaperContinuumGoodRegion
open AlignmentPaperContinuumHulls

/-- A grade-dependent bound for one literal continuum hull shell. -/
def continuumShellRemainderBound {d n : ℕ} (τ L : ℝ)
    (u : Fin d → ℕ) : ℝ :=
  if n ≤ ∑ i : Fin d, u i then
    let h := (∑ i : Fin d, u i) - n
    τ ^ 2 / 2 * shapeOverlapCap d n h L ^ 2 *
      Real.exp (τ * shapeOverlapCap d n h L)
  else 0

/-- Finite shell majorant on the actual good set. The finite hull partition
covers every good pair except the explicit terminal same-cell residual. -/
def continuumFiniteShellMajorant {d n N : ℕ} (τ L : ℝ)
    (p : (Fin d → ℝ) × (Fin d → ℝ)) : ℝ :=
  by
    classical
    exact (∑ u : BoundedHullProfile d N,
      continuumShellRemainderBound (d := d) (n := n) τ L u.1 *
        (if p ∈ spatialPairHullShell u.1 then 1 else 0)) +
      (τ ^ 2 / 2 * Real.exp τ) *
        (if (fun i => (p.1 i, p.2 i)) ∈ tensorCoordinateResidual N then 1 else 0)

private theorem continuumShellRemainderBound_nonneg {d n : ℕ}
    (hd : 1 ≤ d) (τ L : ℝ) (hτ : 0 ≤ τ) (hL : 0 ≤ L)
    (u : Fin d → ℕ) :
    0 ≤ continuumShellRemainderBound (d := d) (n := n) τ L u := by
  unfold continuumShellRemainderBound
  split_ifs with h
  · have hcap : 0 ≤ shapeOverlapCap d n
        ((∑ i : Fin d, u i) - n) L :=
      shapeOverlapCap_nonneg hd _ _ hL
    positivity
  · norm_num

/-- Pullback of the terminal coordinate residual to the spatial cube pair. -/
def spatialPairCoordinateResidual {d : ℕ} (N : ℕ) :
    Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
  {p | (fun i => (p.1 i, p.2 i)) ∈ tensorCoordinateResidual N}

private theorem oneDyadicSameDepthCellShell_measurable (N : ℕ) :
    MeasurableSet (oneDyadicSameDepthCellShell N) := by
  unfold oneDyadicSameDepthCellShell
  refine MeasurableSet.iUnion fun c => MeasurableSet.iUnion fun _ => ?_
  exact (measurableSet_Ico.prod measurableSet_Ico)

theorem spatialPairCoordinateResidual_measurable {d : ℕ} (N : ℕ) :
    MeasurableSet (spatialPairCoordinateResidual (d := d) N) := by
  classical
  have hset : spatialPairCoordinateResidual (d := d) N =
      ⋃ i : Fin d,
        {p : (Fin d → ℝ) × (Fin d → ℝ) |
          (p.1 i, p.2 i) ∈ oneDyadicSameDepthCellShell N} := by
    ext p
    simp [spatialPairCoordinateResidual, tensorCoordinateResidual]
  rw [hset]
  apply MeasurableSet.iUnion
  intro i
  have heval : Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      (p.1 i, p.2 i)) := Measurable.prodMk
        ((measurable_pi_apply i).comp measurable_fst)
        ((measurable_pi_apply i).comp measurable_snd)
  exact (oneDyadicSameDepthCellShell_measurable N).preimage heval

private theorem integral_const_if_mem_eq_realMeasure
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (s : Set α) [DecidablePred (fun x : α => x ∈ s)]
    (hs : MeasurableSet s) (c : ℝ) :
    (∫ x, (if x ∈ s then c else 0) ∂μ) = c * μ.real s := by
  classical
  have heq : (fun x => if x ∈ s then c else 0) =
      s.indicator (fun _ : α => c) := by
    funext x
    by_cases hx : x ∈ s <;> simp [Set.indicator, hx]
  rw [heq, integral_indicator_const c hs]
  simp [smul_eq_mul, mul_comm]

private theorem integral_const_mul_if_mem_eq_realMeasure
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    (s : Set α) [DecidablePred (fun x : α => x ∈ s)]
    (hs : MeasurableSet s) (c : ℝ) :
    (∫ x, c * (if x ∈ s then (1 : ℝ) else 0) ∂μ) = c * μ.real s := by
  classical
  have heq : (fun x => c * (if x ∈ s then (1 : ℝ) else 0)) =
      fun x => if x ∈ s then c else 0 := by
    funext x
    by_cases hx : x ∈ s <;> simp [hx]
  rw [heq, integral_const_if_mem_eq_realMeasure s hs c]

theorem continuumFiniteShellMajorant_integral_eq
    {d n N : ℕ} (τ L : ℝ) :
    (∫ p : (Fin d → ℝ) × (Fin d → ℝ),
      continuumFiniteShellMajorant (d := d) (n := n) (N := N) τ L p ∂
        ((cubeLebesgue d).prod (cubeLebesgue d))) =
      (∑ u : BoundedHullProfile d N,
        continuumShellRemainderBound (d := d) (n := n) τ L u.1 *
          (((cubeLebesgue d).prod (cubeLebesgue d)).real
            (spatialPairHullShell u.1))) +
        (τ ^ 2 / 2 * Real.exp τ) *
          (((cubeLebesgue d).prod (cubeLebesgue d)).real
            (spatialPairCoordinateResidual (d := d) N)) := by
  classical
  let μ := (cubeLebesgue d).prod (cubeLebesgue d)
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hsumInt : ∀ u : BoundedHullProfile d N,
      Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
        continuumShellRemainderBound (d := d) (n := n) τ L u.1 *
          (if p ∈ spatialPairHullShell u.1 then 1 else 0)) μ := by
    intro u
    have hconst : Integrable (fun _ : (Fin d → ℝ) × (Fin d → ℝ) =>
        continuumShellRemainderBound (d := d) (n := n) τ L u.1) μ := integrable_const _
    have hind := hconst.indicator (spatialPairHullShell_measurable u.1)
    convert hind using 1
    ext p
    by_cases hp : p ∈ spatialPairHullShell u.1 <;> simp [Set.indicator_apply, hp]
  have hresInt : Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      (τ ^ 2 / 2 * Real.exp τ) *
        (if p ∈ spatialPairCoordinateResidual (d := d) N then 1 else 0)) μ := by
    have hconst : Integrable (fun _ : (Fin d → ℝ) × (Fin d → ℝ) =>
        τ ^ 2 / 2 * Real.exp τ) μ := integrable_const _
    have hind := hconst.indicator (spatialPairCoordinateResidual_measurable N)
    convert hind using 1
    ext p
    by_cases hp : p ∈ spatialPairCoordinateResidual N <;> simp [Set.indicator_apply, hp]
  have hsumEq :
      (∫ p : (Fin d → ℝ) × (Fin d → ℝ),
        ∑ u : BoundedHullProfile d N,
          continuumShellRemainderBound (d := d) (n := n) τ L u.1 *
            (if p ∈ spatialPairHullShell u.1 then 1 else 0) ∂μ) =
      ∑ u : BoundedHullProfile d N,
        continuumShellRemainderBound (d := d) (n := n) τ L u.1 *
          μ.real (spatialPairHullShell u.1) := by
    rw [integral_finset_sum Finset.univ (fun u hu => hsumInt u)]
    apply Finset.sum_congr rfl
    intro u hu
    rw [integral_const_mul_if_mem_eq_realMeasure (μ := μ)
      (spatialPairHullShell u.1) (spatialPairHullShell_measurable u.1)
      (continuumShellRemainderBound (d := d) (n := n) τ L u.1)]
  have hresEq :
      (∫ p : (Fin d → ℝ) × (Fin d → ℝ),
        (τ ^ 2 / 2 * Real.exp τ) *
          (if p ∈ spatialPairCoordinateResidual (d := d) N then 1 else 0) ∂μ) =
      (τ ^ 2 / 2 * Real.exp τ) * μ.real (spatialPairCoordinateResidual N) := by
    rw [integral_const_mul_if_mem_eq_realMeasure (μ := μ)
      (spatialPairCoordinateResidual N) (spatialPairCoordinateResidual_measurable N)
      (τ ^ 2 / 2 * Real.exp τ)]
  change (∫ p : (Fin d → ℝ) × (Fin d → ℝ),
      (∑ u : BoundedHullProfile d N,
        continuumShellRemainderBound (d := d) (n := n) τ L u.1 *
          (if p ∈ spatialPairHullShell u.1 then 1 else 0)) +
        (τ ^ 2 / 2 * Real.exp τ) *
          (if p ∈ spatialPairCoordinateResidual (d := d) N then 1 else 0) ∂μ) = _
  rw [integral_add (by
    apply integrable_finset_sum
    intro u hu
    exact hsumInt u) hresInt]
  rw [hsumEq, hresEq]

theorem continuumFiniteShellMajorant_nonneg {d n N : ℕ}
    {τ L : ℝ} (hd : 1 ≤ d) (hτ : 0 ≤ τ) (hL : 0 ≤ L) :
    ∀ p, 0 ≤ continuumFiniteShellMajorant (d := d) (n := n) (N := N) τ L p := by
  classical
  intro p
  unfold continuumFiniteShellMajorant
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro u hu
    apply mul_nonneg
    · exact continuumShellRemainderBound_nonneg hd τ L hτ hL u.1
    · split_ifs <;> norm_num
  · apply mul_nonneg
    · positivity
    · split_ifs <;> norm_num

theorem continuumFiniteShellMajorant_integrable
    {d n N : ℕ} {τ L : ℝ} :
    Integrable (continuumFiniteShellMajorant (d := d) (n := n) (N := N) τ L)
      ((cubeLebesgue d).prod (cubeLebesgue d)) := by
  classical
  let μ := (cubeLebesgue d).prod (cubeLebesgue d)
  haveI : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hsumInt : ∀ u : BoundedHullProfile d N,
      Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
        continuumShellRemainderBound (d := d) (n := n) τ L u.1 *
          (if p ∈ spatialPairHullShell u.1 then 1 else 0)) μ := by
    intro u
    have hc : Integrable (fun _ : (Fin d → ℝ) × (Fin d → ℝ) =>
        continuumShellRemainderBound (d := d) (n := n) τ L u.1) μ := integrable_const _
    have hi := hc.indicator (spatialPairHullShell_measurable u.1)
    convert hi using 1
    ext p
    by_cases hp : p ∈ spatialPairHullShell u.1 <;> simp [Set.indicator, hp]
  have hresInt : Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      (τ ^ 2 / 2 * Real.exp τ) *
        (if p ∈ spatialPairCoordinateResidual (d := d) N then 1 else 0)) μ := by
    have hc : Integrable (fun _ : (Fin d → ℝ) × (Fin d → ℝ) =>
        τ ^ 2 / 2 * Real.exp τ) μ := integrable_const _
    have hi := hc.indicator (spatialPairCoordinateResidual_measurable N)
    convert hi using 1
    ext p
    by_cases hp : p ∈ spatialPairCoordinateResidual N <;> simp [Set.indicator, hp]
  unfold continuumFiniteShellMajorant
  apply (integrable_finset_sum Finset.univ (fun u hu => hsumInt u)).add hresInt

end BrownianSharp.AlignmentPaperContinuumVariance
