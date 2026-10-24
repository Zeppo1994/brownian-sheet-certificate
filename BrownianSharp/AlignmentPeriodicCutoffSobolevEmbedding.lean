import BrownianSharp.AlignmentPeriodicCutoffSobolevBridges
import BrownianSharp.AlignmentPeriodicSquareFunctionEmbedding

/-! The elementary Besov theta=2 to Sobolev embedding for arbitrary cutoff.
It supplies the Sobolev entropy lower bound without cross-cutoff vector-valued
Littlewood–Paley equivalence. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BrownianSharp.AlignmentPeriodicCutoffSobolevEmbedding
open BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses

theorem besov_two_implies_sobolev {d : ℕ} (φ : AdmissibleCutoff)
    (p : ℝ) (hp : 2 ≤ p) (r : ℝ) (f : RealPeriodic d)
    (hf : BesovUnitBall φ (ENNReal.ofReal p) r 2 f) :
    SobolevUnitBall φ p r f := by
  let w : (Fin d → ℕ) → ℝ := fun s => (2 : ℝ) ^ (r * ∑ i, (s i : ℝ))
  let g : (Fin d → ℕ) → UnitAddTorus (Fin d) → ℂ :=
    fun s x => admissibleBlock φ s f x
  have hw : ∀ s, 0 ≤ w s := by intro s; dsimp [w]; positivity
  have hg : ∀ s, StronglyMeasurable (g s) := by
    intro s
    exact (admissibleBlock φ s f).continuous.stronglyMeasurable
  have hbase :=
    AlignmentPeriodicSquareFunctionEmbedding.lintegral_tsum_square_function_le
      (μ := (volume : Measure (UnitAddTorus (Fin d)))) hp g w hw hg
  have hpoint : squareFunctionSquared φ r f =
      fun x => ∑' s : Fin d → ℕ, ENNReal.ofReal (w s ^ 2 * ‖g s x‖ ^ 2) := by
    funext x
    unfold squareFunctionSquared
    apply tsum_congr
    intro s
    dsimp [w, g]
    congr 1
    have hpow : ((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) ^ 2 =
        (2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      congr 1
      ring
    rw [hpow]
  have hsum : (∑' s : Fin d → ℕ,
      (weightedBlockNorm φ (ENNReal.ofReal p) r s f) ^ 2) ≤ 1 := by
    simpa [BesovUnitBall] using hf
  have hright : (∑' s : Fin d → ℕ,
      (weightedBlockNorm φ (ENNReal.ofReal p) r s f) ^ 2) ^ (p / 2) ≤ 1 := by
    simpa using ENNReal.rpow_le_rpow hsum (by linarith : 0 ≤ p / 2)
  change (∫⁻ x, squareFunctionSquared φ r f x ^ (p / 2)
    ∂(volume : Measure (UnitAddTorus (Fin d)))) ≤ 1
  rw [hpoint]
  exact hbase.trans hright

end BrownianSharp.AlignmentPeriodicCutoffSobolevEmbedding
