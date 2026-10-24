import BrownianSharp.AlignmentPeriodicUpperReduction
import BrownianSharp.AlignmentTrigonometricL2
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp.AlignmentPeriodicEnergy
open SmoothResolution Torus

/-- Each summand of the literal square function, integrated before summing. -/
def blockEnergy {d : ℕ} (r : ℝ) (f : RealPeriodic d) (s : Fin d → ℕ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal
    ((2 : ℝ) ^ (2*r*∑ i, (s i : ℝ)) * ‖block s f x‖^2)
    ∂(volume : Measure (UnitAddTorus (Fin d)))

theorem blockEnergy_sum_eq_squareFunction {d : ℕ} (r : ℝ) (f : RealPeriodic d) :
    ∑' s, blockEnergy r f s =
      ∫⁻ x, squareFunctionSquared r f x
        ∂(volume : Measure (UnitAddTorus (Fin d))) := by
  unfold blockEnergy squareFunctionSquared
  rw [lintegral_tsum]
  intro s
  exact (ENNReal.measurable_ofReal.comp
    (measurable_const.mul ((block s f).continuous.measurable.norm.pow_const 2))).aemeasurable

theorem sobolev_two_total_energy_le_one {d : ℕ} (r : ℝ) (f : RealPeriodic d)
    (hf : SobolevUnitBall 2 r f) : ∑' s, blockEnergy r f s ≤ 1 := by
  rw [blockEnergy_sum_eq_squareFunction]
  simpa only [SobolevUnitBall, show (2:ℝ)/2=1 by norm_num, ENNReal.rpow_one] using hf

theorem sobolev_two_block_energy_le_one {d : ℕ} (r : ℝ) (f : RealPeriodic d)
    (hf : SobolevUnitBall 2 r f) (s : Fin d → ℕ) : blockEnergy r f s ≤ 1 :=
  (ENNReal.le_tsum s).trans (sobolev_two_total_energy_le_one r f hf)

theorem blockEnergy_eq_weightedBlockNorm_sq {d : ℕ} (r : ℝ)
    (f : RealPeriodic d) (s : Fin d → ℕ) :
    blockEnergy r f s = (weightedBlockNorm 2 r s f)^2 := by
  have hp := eLpNorm_nnreal_pow_eq_lintegral (p := (2:ℝ≥0))
    (μ := (volume : Measure (UnitAddTorus (Fin d)))) (by norm_num)
    (block s f).continuous.aestronglyMeasurable
  norm_num only [NNReal.coe_ofNat, ENNReal.coe_ofNat] at hp
  rw [ENNReal.rpow_two] at hp
  unfold blockEnergy weightedBlockNorm
  rw [mul_pow, hp, ← lintegral_const_mul]
  · apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    congr 1
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
    congr 1
    ring
    all_goals simp only [ENNReal.rpow_two]
  · exact ((block s f).continuous.measurable.enorm.pow_const (2:ℝ))

theorem sobolev_two_weightedBlockNorm_sq_sum_le_one {d : ℕ} (r : ℝ)
    (f : RealPeriodic d) (hf : SobolevUnitBall 2 r f) :
    ∑' s, (weightedBlockNorm 2 r s f)^2 ≤ 1 := by
  simp_rw [← blockEnergy_eq_weightedBlockNorm_sq]
  exact sobolev_two_total_energy_le_one r f hf

theorem sobolev_two_subset_nikolsky_two {d : ℕ} (r : ℝ)
    (f : RealPeriodic d) (hf : SobolevUnitBall 2 r f) :
    NikolskyUnitBall 2 r f := by
  change ∀ s, weightedBlockNorm 2 r s f ≤ 1
  intro s
  have h := sobolev_two_block_energy_le_one r f hf s
  rw [blockEnergy_eq_weightedBlockNorm_sq] at h
  exact (pow_le_one_iff (by norm_num : (2:ℕ)≠0)).mp h

end BrownianSharp.AlignmentPeriodicEnergy
