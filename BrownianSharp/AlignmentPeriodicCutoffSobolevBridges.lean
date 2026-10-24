import BrownianSharp.AlignmentPeriodicCutoffClasses

/-! Bridges between the p=2 square-function Sobolev norm and the θ=2 Besov
block norm, uniformly over the admissible cutoff family. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPeriodicCutoffSobolevBridges

open BrownianSharp.Torus
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff

private instance torusProbability (d : ℕ) :
    IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
  rw [BrownianSharp.unitAddTorus_volume_eq_productHaar]
  infer_instance

private theorem weighted_square_eq_block_weight_square {d : ℕ}
    (φ : AdmissibleCutoff) (r : ℝ) (s : Fin d → ℕ)
    (f : RealPeriodic d) (x : UnitAddTorus (Fin d)) :
    ENNReal.ofReal
        ((2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) *
          ‖admissibleBlock φ s f x‖ ^ 2) =
      ENNReal.ofReal (((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) ^ 2 *
          ‖admissibleBlock φ s f x‖ ^ 2) := by
  congr 1
  have hpow :
      ((2 : ℝ) ^ (r * ∑ i, (s i : ℝ))) ^ 2 =
        (2 : ℝ) ^ (2 * r * ∑ i, (s i : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
    congr 1
    ring
  rw [hpow]

/-- For every admissible cutoff, the p=2 integrated square-function unit ball
is exactly the Besov unit ball with summability exponent θ=2. -/
theorem sobolev_two_iff_besov_two {d : ℕ} (φ : AdmissibleCutoff) (r : ℝ)
    (f : RealPeriodic d) :
    SobolevUnitBall φ 2 r f ↔ BesovUnitBall φ 2 r 2 f := by
  let w : (Fin d → ℕ) → ℝ := fun s =>
    (2 : ℝ) ^ (r * ∑ i, (s i : ℝ))
  let g : (Fin d → ℕ) → UnitAddTorus (Fin d) → ℂ :=
    fun s x => admissibleBlock φ s f x
  have hw : ∀ s, 0 ≤ w s := by
    intro s
    dsimp [w]
    positivity
  have hg : ∀ s, AEStronglyMeasurable (g s)
      (volume : Measure (UnitAddTorus (Fin d))) := by
    intro s
    exact (admissibleBlock φ s f).continuous.aestronglyMeasurable
  have htonelli :=
    BrownianSharp.AlignmentPeriodicP2BesovIdentity.lintegral_tsum_weighted_block_sq_eq_tsum
      (μ := (volume : Measure (UnitAddTorus (Fin d)))) g w hw hg
  have hpoint : squareFunctionSquared φ r f =
      fun x => ∑' s : Fin d → ℕ,
        ENNReal.ofReal (w s ^ 2 * ‖g s x‖ ^ 2) := by
    funext x
    unfold squareFunctionSquared
    apply tsum_congr
    intro s
    dsimp [w, g]
    exact weighted_square_eq_block_weight_square φ r s f x
  have henergy :
      (∫⁻ x, squareFunctionSquared φ r f x
        ∂(volume : Measure (UnitAddTorus (Fin d)))) =
        ∑' s : Fin d → ℕ,
          (weightedBlockNorm φ 2 r s f) ^ 2 := by
    rw [hpoint, htonelli]
    apply tsum_congr
    intro s
    simp only [weightedBlockNorm, w, g]
  constructor
  · intro h
    change (∫⁻ x, (squareFunctionSquared φ r f x) ^ (2 / 2)
      ∂(volume : Measure (UnitAddTorus (Fin d)))) ≤ 1 at h
    have h' : (∫⁻ x, squareFunctionSquared φ r f x
      ∂(volume : Measure (UnitAddTorus (Fin d)))) ≤ 1 := by
      simpa using h
    rw [BesovUnitBall]
    simp only [ENNReal.toReal_ofNat]
    simpa [henergy] using h'
  · intro h
    change (∫⁻ x, (squareFunctionSquared φ r f x) ^ (2 / 2)
      ∂(volume : Measure (UnitAddTorus (Fin d)))) ≤ 1
    have h' : (∫⁻ x, squareFunctionSquared φ r f x
      ∂(volume : Measure (UnitAddTorus (Fin d)))) ≤ 1 := by
      rw [henergy]
      simpa [BesovUnitBall] using h
    simpa using h'

/-- On normalized Haar measure, increasing the spatial exponent only makes
the square-function unit-ball condition stronger. -/
theorem sobolev_unitBall_mono {d : ℕ} (φ : AdmissibleCutoff)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (r : ℝ)
    (f : RealPeriodic d) (hf : SobolevUnitBall φ q r f) :
    SobolevUnitBall φ p r f := by
  exact BrownianSharp.AlignmentSquareEnergyExponent.squareFunction_unit_energy_mono
    (squareFunctionSquared φ r f)
    ((measurable_squareFunctionSquared φ r f).aemeasurable)
    hp hpq hf

end BrownianSharp.AlignmentPeriodicCutoffSobolevBridges
