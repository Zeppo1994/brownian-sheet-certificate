import BrownianSharp.PeriodicCover
import BrownianSharp.ProbabilisticCover
import BrownianSharp.IndependentComparison
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-! Generic Anderson cover obstruction for finite Gaussian linear syntheses
into a compact-domain continuous-function space. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp.AlignmentExponentialContinuousCover

/-- Finite samples of a continuous-function linear synthesis. -/
def sampleMap {α : Type*} {N M : ℕ} [TopologicalSpace α]
    (F : (Fin N → ℝ) →ₗ[ℝ] C(α, ℝ)) (t : Fin M → α) :
    (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ) where
  toFun z j := F z (t j)
  map_add' z w := by
    ext j
    exact congrArg (fun f : C(α, ℝ) => f (t j)) (map_add F z w)
  map_smul' c z := by
    ext j
    exact congrArg (fun f : C(α, ℝ) => f (t j)) (map_smul F c z)

theorem synthesisBall_subset_sampleCube {α : Type*} {N M : ℕ}
    [TopologicalSpace α] [CompactSpace α] [Nonempty α]
    (F : (Fin N → ℝ) →ₗ[ℝ] C(α, ℝ)) (t : Fin M → α)
    (ρ : NNReal) (ε : ℝ) (hρε : (ρ : ℝ) ≤ ε) (hε : 0 ≤ ε)
    (f : C(α, ℝ)) (z : Fin N → ℝ)
    (hball : edist (F z) f ≤ (ρ : ℝ≥0∞)) :
    sampleMap F t z - (fun j => f (t j)) ∈ Metric.closedBall (0 : Fin M → ℝ) ε := by
  have hdist : dist (F z) f ≤ (ρ : ℝ) := by
    have hnn : nndist (F z) f ≤ ρ := edist_le_coe.mp hball
    exact_mod_cast hnn
  have hnorm : ‖F z - f‖ ≤ ρ := by
    simpa [dist_eq_norm] using hdist
  have hcoords : ∀ j, |F z (t j) - f (t j)| ≤ ε := by
    intro j
    have hcomp := (F z - f).norm_coe_le_norm (t j)
    have hle : ‖(F z - f) (t j)‖ ≤ ε := hcomp.trans (le_trans hnorm hρε)
    simpa [Real.norm_eq_abs] using hle
  change dist (sampleMap F t z - (fun j => f (t j))) 0 ≤ ε
  rw [dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg hε).2
  intro j
  simpa [sampleMap, Real.norm_eq_abs] using hcoords j

theorem gaussianSynthesis_ball_mass_le {α : Type*} {N M : ℕ}
    [TopologicalSpace α] [CompactSpace α] [Nonempty α]
    (hN : 0 < N) (F : (Fin N → ℝ) →ₗ[ℝ] C(α, ℝ)) (t : Fin M → α)
    (ρ : NNReal) (ε : ℝ) (hρε : (ρ : ℝ) ≤ ε) (hε : 0 < ε) (q : ℝ≥0∞)
    (hconf : (Measure.pi (fun _ : Fin N => gaussianReal 0 1))
      {z | ‖sampleMap F t z‖ ≤ ε} ≤ q) :
    ∀ f : C(α, ℝ),
      (Measure.pi (fun _ : Fin N => gaussianReal 0 1))
        {z | edist (F z) f ≤ (ρ : ℝ≥0∞)} ≤ q := by
  intro f
  let A := sampleMap F t
  let C : Set (Fin M → ℝ) := Metric.closedBall (0 : Fin M → ℝ) ε
  have hconv : Convex ℝ C := convex_closedBall _ _
  have hsymm : ∀ y, y ∈ C → -y ∈ C := by
    intro y hy
    have hy' : ‖y‖ ≤ ε := by simpa [C, Metric.mem_closedBall, dist_eq_norm] using hy
    simpa [C, Metric.mem_closedBall, dist_eq_norm] using hy'
  have hmeas : MeasurableSet C := measurableSet_closedBall
  have hshift : (Measure.pi (fun _ : Fin N => gaussianReal 0 1))
      {z | A z - (fun j => f (t j)) ∈ C} ≤ q := by
    have hset : {z | A z - (fun j => f (t j)) ∈ C} =
        {z | A z + (fun j => -f (t j)) ∈ C} := by
      ext z
      have hv : A z - (fun j => f (t j)) = A z + (fun j => -f (t j)) := by
        ext j
        exact sub_eq_add_neg (A z j) (f (t j))
      change (A z - (fun j => f (t j))) ∈ C ↔
        (A z + (fun j => -f (t j))) ∈ C
      exact Iff.of_eq (congrArg (fun y => y ∈ C) hv)
    calc
      _ ≤ (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) {z | A z ∈ C} := by
        rw [hset]
        exact standardGaussian_linear_shift_le_of_pos hN C A
          (fun j => -(f (t j))) hconv hsymm hmeas
      _ ≤ q := by simpa [A, C, Metric.mem_closedBall, dist_eq_norm] using hconf
  apply le_trans (measure_mono ?_) hshift
  intro z hz
  exact synthesisBall_subset_sampleCube F t ρ ε hρε (le_of_lt hε) f z hz

theorem externalCoveringNumber_gt_of_admissible_mass
    {α : Type*} {N M : ℕ} [TopologicalSpace α] [CompactSpace α] [Nonempty α]
    (hN : 0 < N) (F : (Fin N → ℝ) →ₗ[ℝ] C(α, ℝ)) (t : Fin M → α)
    (E : Set (Fin N → ℝ)) (K : Set (C(α, ℝ)))
    (ρ : NNReal) (ε : ℝ) (hρε : (ρ : ℝ) ≤ ε) (hε : 0 < ε)
    (q : ℝ≥0∞) (m : ℕ)
    (hclass : ∀ z ∈ E, F z ∈ K)
    (hconf : (Measure.pi (fun _ : Fin N => gaussianReal 0 1))
      {z | ‖sampleMap F t z‖ ≤ ε} ≤ q)
    (hmass : (m : ℝ≥0∞) * q <
      (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) E) :
    (m : ℕ∞) < Metric.externalCoveringNumber ρ K := by
  apply BrownianSharp.externalCoveringNumber_gt_of_admissible_mass
    (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) F E K ρ q m hclass
  · intro f
    exact gaussianSynthesis_ball_mass_le hN F t ρ ε hρε hε q hconf f
  · exact hmass

end BrownianSharp.AlignmentExponentialContinuousCover
