import BrownianSharp.AlignmentPaperJointGlobalRankProfile

/-! Upper size control for the high-grade ranks used in joint covers. -/

noncomputable section
set_option maxHeartbeats 10000000
set_option maxRecDepth 10000

namespace BrownianSharp.AlignmentPaperJointHighGradeRankUpper

open BrownianSharp.AlignmentPaperJointGlobalRankProfile
open BrownianSharp.AlignmentPaperJointSamplingBudget
open BrownianSharp.AlignmentPaperLpJointDvp

/-- The floored exponential rank is at most twice the initial sample dimension
times its prescribed exponential decay. -/
theorem high_profile_rank_upper {d N j : ℕ} {p : ℝ}
    (hd : 2 ≤ d) (hp1 : 1 < p) (hp2 : p < 2)
    (hj : j ≤ highProfileWindow p N) :
    ((2 : ℝ) ^ highProfileRank d p N j) ≤
      2 * (JointSampleDimension d N : ℝ) *
        Real.exp (-highProfileEta p * (j : ℝ)) := by
  let D : ℕ := JointSampleDimension d N
  let L : ℕ := Nat.log2 D
  let q : ℕ := highProfileDrop p j
  let η : ℝ := highProfileEta p
  have hp0 : 0 < p := by linarith
  have hpden : 0 < p - 1 := by linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hηpos : 0 < η := by
    dsimp [η, highProfileEta]
    positivity
  have hqfloor : (q : ℝ) ≤ η * (j : ℝ) / Real.log 2 := by
    dsimp [q, η, highProfileDrop, highProfileEta]
    exact Nat.floor_le (by positivity)
  have hfloorlt : η * (j : ℝ) / Real.log 2 < (q : ℝ) + 1 := by
    dsimp [q, η, highProfileDrop]
    exact Nat.lt_floor_add_one _
  have hqlogLower : η * (j : ℝ) - Real.log 2 < (q : ℝ) * Real.log 2 := by
    have hmul := (div_lt_iff₀ hlog).mp hfloorlt
    nlinarith
  have hexpUpper : Real.exp (-((q : ℝ) * Real.log 2)) ≤
      2 * Real.exp (-η * (j : ℝ)) := by
    have hlog2pos : Real.exp (Real.log (2 : ℝ)) = 2 :=
      Real.exp_log (by norm_num : (0 : ℝ) < 2)
    have hpow : -((q : ℝ) * Real.log 2) ≤
        Real.log 2 - η * (j : ℝ) := by linarith
    calc
      Real.exp (-((q : ℝ) * Real.log 2)) ≤
          Real.exp (Real.log 2 - η * (j : ℝ)) := Real.exp_le_exp.mpr hpow
      _ = 2 * Real.exp (-η * (j : ℝ)) := by
        rw [show Real.log 2 - η * (j : ℝ) =
          Real.log 2 + (-η * (j : ℝ)) by ring, Real.exp_add, hlog2pos]
  have hDpos : D ≠ 0 := by
    have hcard : 0 < Fintype.card (Shape d N) := by
      rw [shape_card d N (by omega : 0 < d)]
      exact Nat.choose_pos (by omega)
    have hdim : 0 < JointSampleDimension d N := by
      rw [jointSampleDimension_eq]
      exact Nat.mul_pos hcard (by positivity)
    dsimp [D]
    exact Nat.ne_of_gt hdim
  have hLq : q ≤ L := by
    have hfeas := highProfileRank_feasible hd hp1 hp2 hj
    exact hfeas.1
  have h2L : 2 ^ L ≤ D := by
    dsimp [L]
    exact Nat.log2_self_le hDpos
  have h2Lreal : (2 : ℝ) ^ L ≤ (D : ℝ) := by exact_mod_cast h2L
  have h2Lnonneg : 0 ≤ (2 : ℝ) ^ L := pow_nonneg (by norm_num) L
  have hpowEq : (2 : ℝ) ^ L * (2 : ℝ) ^ (-(q : ℝ)) =
      (2 : ℝ) ^ highProfileRank d p N j := by
    rw [← Real.rpow_natCast (2 : ℝ) L,
      ← Real.rpow_natCast (2 : ℝ) (highProfileRank d p N j),
      ← Real.rpow_add (by norm_num : 0 < (2 : ℝ))]
    have hcast : (L : ℝ) - (q : ℝ) =
        (highProfileRank d p N j : ℝ) := by
      dsimp [L, q, D, highProfileRank]
      rw [Nat.cast_sub hLq]
    rw [← sub_eq_add_neg, hcast]
  have hexpEq : Real.exp (-((q : ℝ) * Real.log 2)) =
      (2 : ℝ) ^ (-(q : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : 0 < (2 : ℝ))]
    congr 1
    ring
  calc
    (2 : ℝ) ^ highProfileRank d p N j =
        (2 : ℝ) ^ L * (2 : ℝ) ^ (-(q : ℝ)) := hpowEq.symm
    _ = (2 : ℝ) ^ L * Real.exp (-((q : ℝ) * Real.log 2)) := by rw [hexpEq]
    _ ≤ (D : ℝ) * (2 * Real.exp (-η * (j : ℝ))) :=
      calc
        (2 : ℝ) ^ L * Real.exp (-((q : ℝ) * Real.log 2)) ≤
            (2 : ℝ) ^ L * (2 * Real.exp (-η * (j : ℝ))) :=
          mul_le_mul_of_nonneg_left hexpUpper h2Lnonneg
        _ ≤ (D : ℝ) * (2 * Real.exp (-η * (j : ℝ))) :=
          mul_le_mul_of_nonneg_right h2Lreal (by positivity)
    _ = 2 * (JointSampleDimension d N : ℝ) *
        Real.exp (-highProfileEta p * (j : ℝ)) := by
          dsimp [D, η]
          ring

end BrownianSharp.AlignmentPaperJointHighGradeRankUpper

end
