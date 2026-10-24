import BrownianSharp.SmoothAtomMass
import BrownianSharp.CameronMartinEntropy
import BrownianSharp.ProbabilisticCover
import BrownianSharp.IndependentComparison
import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
# Periodized smooth atoms and their Gaussian cover obstruction

This file gives a concrete smooth periodic atom family and the finite-Gaussian
cover argument for arbitrary finite linear combinations of those atoms. The
remaining application-specific inputs are displayed: the coefficient cutoff
must synthesize into the stated function class, and the centered finite-grid
confinement probability must be bounded.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace BrownianSharp.PeriodicCover
open BrownianSharp.Torus

/-- The one-dimensional smooth bump placed in the dyadic cell `j/2^s` and
periodized by the quotient map. The support of `smoothAtom` is strictly
inside `(0,1)`, so the two endpoint values match and the lift is continuous. -/
def periodizedDyadicAtom1 (s j : ℕ) (hj : j < 2 ^ s) : C(UnitAddCircle, ℝ) := by
  let f : ℝ → ℝ := fun x => smoothAtom ((2 : ℝ) ^ s * x - (j : ℝ))
  have hfend : f 0 = f 1 := by
    have hleft : (2 : ℝ) ^ s * 0 - (j : ℝ) ≤ 0 := by simp
    have hj' : j + 1 ≤ 2 ^ s := Nat.succ_le_of_lt hj
    have hright : 1 ≤ (2 : ℝ) ^ s * 1 - (j : ℝ) := by
      have hcast : ((2 ^ s : ℕ) : ℝ) = (2 : ℝ) ^ s := by norm_cast
      have hj'' : (j : ℝ) + 1 ≤ (2 ^ s : ℝ) := by exact_mod_cast hj'
      nlinarith
    change smoothAtom ((2 : ℝ) ^ s * 0 - (j : ℝ)) =
      smoothAtom ((2 : ℝ) ^ s * 1 - (j : ℝ))
    rw [smoothAtom_support _ (Or.inl hleft), smoothAtom_support _ (Or.inr hright)]
  have hfcont : Continuous f := by
    dsimp [f]
    exact smoothAtom_contDiff.continuous.comp
      ((continuous_const.mul continuous_id).sub continuous_const)
  exact ⟨AddCircle.liftIco (1 : ℝ) 0 f,
    AddCircle.liftIco_zero_continuous (p := (1 : ℝ)) hfend hfcont.continuousOn⟩

/-- A dependent dyadic address in the product torus. -/
structure AtomIndex (d : ℕ) where
  depth : Fin d → ℕ
  cell : Fin d → ℕ
  valid : ∀ i, cell i < 2 ^ depth i

/-- The actual tensor-product periodized dyadic atoms on the unit torus. -/
def periodizedDyadicAtom {d : ℕ} (a : AtomIndex d) : RealPeriodic d where
  toFun x := ∏ i : Fin d,
    periodizedDyadicAtom1 (a.depth i) (a.cell i) (a.valid i) (x i)
  continuous_toFun := by fun_prop

/-- Synthesis from finitely many independent Gaussian coefficients into an
actual continuous torus function. -/
def gaussianSynthesis {ι d : ℕ} (atoms : Fin ι → RealPeriodic d) :
    (Fin ι → ℝ) →ₗ[ℝ] RealPeriodic d where
  toFun z := ∑ i : Fin ι, z i • atoms i
  map_add' z w := by
    ext x
    simp only [ContinuousMap.coe_sum, ContinuousMap.coe_add,
      ContinuousMap.coe_smul, Pi.add_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  map_smul' c z := by
    simp [Finset.smul_sum, smul_smul]

/-- Values of the actual periodized-atom synthesis on a finite torus grid. -/
def synthesisGridMap {ι d M : ℕ} (atoms : Fin ι → RealPeriodic d)
    (t : Fin M → UnitAddTorus (Fin d)) :
    (Fin ι → ℝ) →ₗ[ℝ] (Fin M → ℝ) where
  toFun z j := gaussianSynthesis atoms z (t j)
  map_add' z w := by
    ext j
    exact congrArg (fun f : RealPeriodic d => f (t j))
      (map_add (gaussianSynthesis atoms) z w)
  map_smul' c z := by
    ext j
    exact congrArg (fun f : RealPeriodic d => f (t j))
      (map_smul (gaussianSynthesis atoms) c z)

/-- A path ball in the uniform norm implies the corresponding translated
finite-grid cube event for the coefficient Gaussian vector. -/
theorem synthesisBall_subset_gridCube {ι d M : ℕ}
    (atoms : Fin ι → RealPeriodic d) (t : Fin M → UnitAddTorus (Fin d))
    (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hρε : ρ ≤ ε) (hε : 0 ≤ ε)
    (f : RealPeriodic d) (z : Fin ι → ℝ)
    (hball : edist (gaussianSynthesis atoms z) f ≤ ENNReal.ofReal ρ) :
    synthesisGridMap atoms t z - (fun j => f (t j)) ∈
      Metric.closedBall (0 : Fin M → ℝ) ε := by
  have hdist : dist (gaussianSynthesis atoms z) f ≤ ρ := by
    have hnn : nndist (gaussianSynthesis atoms z) f ≤ ENNReal.toNNReal (ENNReal.ofReal ρ) :=
      edist_le_coe.mp (by simpa [ENNReal.ofReal_eq_coe_nnreal hρ] using hball)
    have hnn' : (ENNReal.toNNReal (ENNReal.ofReal ρ) : ℝ≥0) = ⟨ρ, hρ⟩ := by
      apply Subtype.ext
      simp [ENNReal.ofReal_eq_coe_nnreal hρ]
    have hcast : (nndist (gaussianSynthesis atoms z) f : ℝ) ≤ ρ := by
      have := hnn
      rw [hnn'] at this
      exact_mod_cast this
    simpa [dist_eq_norm] using hcast
  have hnorm : ‖gaussianSynthesis atoms z - f‖ ≤ ρ := by
    simpa [dist_eq_norm] using hdist
  have hcoords : ∀ j, |gaussianSynthesis atoms z (t j) - f (t j)| ≤ ε := by
    intro j
    have hcomp := (gaussianSynthesis atoms z - f).norm_coe_le_norm (t j)
    have hle : ‖(gaussianSynthesis atoms z - f) (t j)‖ ≤ ε := hcomp.trans (le_trans hnorm hρε)
    simpa [Real.norm_eq_abs] using hle
  change dist (synthesisGridMap atoms t z - (fun j => f (t j))) 0 ≤ ε
  rw [dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg hε).2
  intro j
  simpa [synthesisGridMap, gaussianSynthesis, Real.norm_eq_abs] using hcoords j

/-- Anderson controls every translated uniform path ball by a centered
finite-grid confinement probability. -/
theorem gaussianSynthesis_ball_mass_le {ι d M : ℕ} (hι : 0 < ι)
    (atoms : Fin ι → RealPeriodic d) (t : Fin M → UnitAddTorus (Fin d))
    (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hρε : ρ ≤ ε) (hε : 0 < ε) (q : ℝ≥0∞)
    (hconf : (Measure.pi (fun _ : Fin ι => gaussianReal 0 1))
      {z | ‖synthesisGridMap atoms t z‖ ≤ ε} ≤ q) :
    ∀ f : RealPeriodic d,
      (Measure.pi (fun _ : Fin ι => gaussianReal 0 1))
        {z | edist (gaussianSynthesis atoms z) f ≤ ENNReal.ofReal ρ} ≤ q := by
  intro f
  let A := synthesisGridMap atoms t
  let C : Set (Fin M → ℝ) := Metric.closedBall (0 : Fin M → ℝ) ε
  have hconv : Convex ℝ C := convex_closedBall _ _
  have hsymm : ∀ y, y ∈ C → -y ∈ C := by
    intro y hy
    have hy' : ‖y‖ ≤ ε := by simpa [C, Metric.mem_closedBall, dist_eq_norm] using hy
    simpa [C, Metric.mem_closedBall, dist_eq_norm] using hy'
  have hmeas : MeasurableSet C := measurableSet_closedBall
  have hshift : (Measure.pi (fun _ : Fin ι => gaussianReal 0 1))
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
      _ ≤ (Measure.pi (fun _ : Fin ι => gaussianReal 0 1)) {z | A z ∈ C} := by
        rw [hset]
        exact standardGaussian_linear_shift_le_of_pos hι
          C A (fun j => -(f (t j))) hconv hsymm hmeas
      _ ≤ q := by simpa [A, C, Metric.mem_closedBall, dist_eq_norm] using hconf
  apply le_trans (measure_mono ?_) hshift
  intro z hz
  exact synthesisBall_subset_gridCube atoms t ρ ε hρ hρε (le_of_lt hε) f z hz

/-- Actual periodized smooth atoms, driven by independent standard Gaussian
coefficients, obstruct finite external covers whenever the coefficient cutoff
is contained in the target class and the centered grid confinement estimate
holds. -/
theorem periodizedGaussian_externalCoveringNumber_gt
    {ι d M k : ℕ} (hι : 0 < ι) (addresses : Fin ι → AtomIndex d)
    (t : Fin M → UnitAddTorus (Fin d))
    (K : Set (RealPeriodic d)) (ρ ε : ℝ) (hρ : 0 ≤ ρ) (hρε : ρ ≤ ε) (hε : 0 < ε)
    (q : ℝ≥0∞)
    (hclass : ∀ z : Fin ι → ℝ,
      BrownianSharp.CameronMartinEntropy.coefficientEnergy z ≤
        4 * (ι : ℝ) → gaussianSynthesis (fun i => periodizedDyadicAtom (addresses i)) z ∈ K)
    (hconf : (Measure.pi (fun _ : Fin ι => gaussianReal 0 1))
      {z | ‖synthesisGridMap (fun i => periodizedDyadicAtom (addresses i)) t z‖ ≤ ε} ≤ q)
    (hmass : ((2 ^ (k - 1) : ℕ) : ℝ≥0∞) * q < (3 / 4 : ℝ≥0∞)) :
    ((2 ^ (k - 1) : ℕ) : ℕ∞) < Metric.externalCoveringNumber
      (⟨ρ, hρ⟩ : ℝ≥0) K := by
  classical
  let atoms : Fin ι → RealPeriodic d := fun i => periodizedDyadicAtom (addresses i)
  let P : Measure (Fin ι → ℝ) := Measure.pi fun _ : Fin ι => gaussianReal 0 1
  let E : Set (Fin ι → ℝ) :=
    {z | BrownianSharp.CameronMartinEntropy.coefficientEnergy z ≤
      4 * (ι : ℝ)}
  letI : Nonempty (Fin ι) := Fin.pos_iff_nonempty.mp hι
  have hmassE : (3 / 4 : ℝ≥0∞) ≤ P E := by
    simpa [P, E] using
      BrownianSharp.CameronMartinEntropy.standardGaussian_coefficientCutoff_mass
        (Fin ι)
  have hball : ∀ f : RealPeriodic d,
      P {z | edist (gaussianSynthesis atoms z) f ≤ ENNReal.ofReal ρ} ≤ q := by
    intro f
    simpa only [P] using gaussianSynthesis_ball_mass_le
      (ι := ι) (d := d) (M := M) hι atoms t ρ ε hρ hρε hε q hconf f
  have hcover := externalCoveringNumber_gt_of_admissible_mass P
    (gaussianSynthesis atoms) E K ⟨ρ, hρ⟩ q (2 ^ (k - 1))
    (by intro z hz; exact hclass z hz)
    (by
      intro f
      change P {ω | edist (gaussianSynthesis atoms ω) f ≤
        ENNReal.ofNNReal (⟨ρ, hρ⟩ : ℝ≥0)} ≤ q
      have hrad : ENNReal.ofReal ρ = ENNReal.ofNNReal (⟨ρ, hρ⟩ : ℝ≥0) :=
        ENNReal.ofReal_eq_coe_nnreal hρ
      rw [← hrad]
      exact hball f)
    (by
      calc
        ((2 ^ (k - 1) : ℕ) : ℝ≥0∞) * q < (3 / 4 : ℝ≥0∞) := hmass
        _ ≤ P E := hmassE)
  simpa using hcover

end BrownianSharp.PeriodicCover
