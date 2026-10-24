import BrownianSharp.AlignmentPeriodicReconstruction
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp.AlignmentPeriodicRealEnergy
open Torus SmoothResolution AlignmentPeriodicEnergy AlignmentPeriodicReconstruction

def realBlockEnergy {d : ℕ} (r : ℝ) (f : RealPeriodic d) (s : Fin d → ℕ) : ℝ :=
  ((2:ℝ)^(r*∑ i,(s i:ℝ)) *
    ‖(block s f).toLp 2 (volume : Measure (UnitAddTorus (Fin d))) ℂ‖)^2

theorem realBlockEnergy_eq_toReal {d : ℕ} (r : ℝ) (f : RealPeriodic d)
    (s : Fin d → ℕ) :
    realBlockEnergy r f s = ((weightedBlockNorm 2 r s f)^2).toReal := by
  unfold realBlockEnergy weightedBlockNorm
  rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    block_toLp_norm]

theorem sobolev_two_real_energy_le_one {d : ℕ} (r : ℝ) (f : RealPeriodic d)
    (hf : SobolevUnitBall 2 r f) :
    Summable (realBlockEnergy r f) ∧ ∑' s, realBlockEnergy r f s ≤ 1 := by
  have h := sobolev_two_weightedBlockNorm_sq_sum_le_one r f hf
  have hfin : (∑' s : Fin d → ℕ, (weightedBlockNorm 2 r s f)^2) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) h
  have hs := ENNReal.summable_toReal hfin
  have heq : realBlockEnergy r f = fun s => ((weightedBlockNorm 2 r s f)^2).toReal :=
    funext (realBlockEnergy_eq_toReal r f)
  rw [heq]
  refine ⟨hs, ?_⟩
  rw [← ENNReal.tsum_toReal_eq (ENNReal.ne_top_of_tsum_ne_top hfin)]
  simpa using ENNReal.toReal_mono (by simp : (1:ENNReal)≠⊤) h

theorem sobolev_two_finite_real_energy_le_one {d : ℕ} (r : ℝ) (f : RealPeriodic d)
    (hf : SobolevUnitBall 2 r f) (S : Finset (Fin d → ℕ)) :
    ∑ s ∈ S, realBlockEnergy r f s ≤ 1 := by
  obtain ⟨hs,hbound⟩ := sobolev_two_real_energy_le_one r f hf
  exact (hs.sum_le_tsum S (fun s hs => by unfold realBlockEnergy; positivity)).trans hbound

end BrownianSharp.AlignmentPeriodicRealEnergy
