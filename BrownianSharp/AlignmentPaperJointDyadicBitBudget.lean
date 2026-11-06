import BrownianSharp.AlignmentPaperJointDyadicStages
import BrownianSharp.AlignmentPaperJointAdaptiveScalarSums

/-! Uniform logarithmic budget of the actual finite-stage binary covers. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperJointDyadicBitBudget
open BrownianSharp.AlignmentPaperJointDyadicStages
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperAdaptiveCardinalityCost

def logRatio (D j : ℕ) : ℝ := Real.log (Real.exp 1 * (D:ℝ)/(2:ℝ)^j)
def codingConstant : ℝ := 10 + 2/Real.log 2 + 4*Real.log 7/Real.log 2

def bitCost (D J j : ℕ) : ℕ :=
  Nat.ceil ((Real.log 2 + 2*supportCost D (2^j) +
    4*((2^j:ℕ):ℝ)*(Real.log 7 + (2*(J-j):ℕ)*Real.log 2))/Real.log 2)

theorem codingConstant_pos : 0 < codingConstant := by
  have h₂ : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have h₇ : 0 < Real.log (7:ℝ) := Real.log_pos (by norm_num)
  unfold codingConstant
  positivity

theorem logRatio_one_le {D j : ℕ} (h : 2^j ≤ D) : 1 ≤ logRatio D j := by
  have hreal : (2:ℝ)^j ≤ (D:ℝ) := by exact_mod_cast h
  have hb : Real.exp 1 ≤ Real.exp 1*(D:ℝ)/(2:ℝ)^j := by
    rw [le_div_iff₀ (by positivity : 0 < (2:ℝ)^j)]
    exact mul_le_mul_of_nonneg_left hreal (Real.exp_nonneg _)
  have hl := Real.log_le_log (Real.exp_pos (1:ℝ)) hb
  simpa only [logRatio, Real.log_exp] using hl

theorem supportCost_pow_two_eq {D j : ℕ} (h : 2^j ≤ D) :
    supportCost D (2^j) = (2:ℝ)^j * logRatio D j := by
  have hD : 0 < (D:ℝ) := lt_of_lt_of_le (by positivity : 0 < (2:ℝ)^j)
    (by exact_mod_cast h)
  have hratio : 0 < (D:ℝ)/(2:ℝ)^j := div_pos hD (by positivity)
  unfold supportCost logRatio
  rw [if_neg (pow_ne_zero j (by norm_num : (2:ℕ) ≠ 0)), Nat.cast_pow, Nat.cast_ofNat]
  rw [show Real.exp 1*(D:ℝ)/(2:ℝ)^j = Real.exp 1*((D:ℝ)/(2:ℝ)^j) by ring,
    Real.log_mul (Real.exp_ne_zero _) hratio.ne', Real.log_exp]

theorem bitCost_le {D J j : ℕ} (h : 2^j ≤ D) :
    (bitCost D J j : ℝ) ≤
      codingConstant * (2:ℝ)^j * (logRatio D j + ((J-j:ℕ):ℝ)) := by
  let r : ℝ := (2:ℝ)^j
  let L := logRatio D j
  let gap : ℝ := ((J-j:ℕ):ℝ)
  let S := r*(L+gap)
  have hr : 1 ≤ r := one_le_pow₀ (by norm_num)
  have hL : 1 ≤ L := logRatio_one_le h
  have hg : 0 ≤ gap := Nat.cast_nonneg _
  have h₂ : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have h₇ : 0 < Real.log (7:ℝ) := Real.log_pos (by norm_num)
  have hrL : r*L ≤ S := by dsimp [S]; nlinarith
  have hrS : r ≤ S := by nlinarith
  have hgS : r*gap ≤ S := by dsimp [S]; nlinarith
  have hS : 1 ≤ S := le_trans hr hrS
  let A : ℝ := (Real.log 2 + 2*r*L + 4*r*(Real.log 7 + 2*gap*Real.log 2))/Real.log 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAe : A+1 = 2 + (2/Real.log 2)*(r*L) +
      (4*Real.log 7/Real.log 2)*r + 8*(r*gap) := by
    dsimp [A]
    field_simp
    <;> ring
  have hbc : bitCost D J j = Nat.ceil A := by
    unfold bitCost
    rw [supportCost_pow_two_eq h, Nat.cast_pow, Nat.cast_ofNat]
    congr 1
    dsimp [A, r, L, gap]
    push_cast
    ring
  rw [hbc]
  change (Nat.ceil A : ℝ) ≤ codingConstant*r*(L+gap)
  calc
    _ ≤ A+1 := (Nat.ceil_lt_add_one hA).le
    _ ≤ 2*S + (2/Real.log 2)*S + (4*Real.log 7/Real.log 2)*S + 8*S := by
      rw [hAe]
      have hcL := mul_le_mul_of_nonneg_left hrL (show 0 ≤ 2/Real.log 2 by positivity)
      have hcr := mul_le_mul_of_nonneg_left hrS
        (show 0 ≤ 4*Real.log 7/Real.log 2 by positivity)
      have hcg := mul_le_mul_of_nonneg_left hgS (show (0:ℝ)≤8 by norm_num)
      linarith
    _ = _ := by dsimp [codingConstant, S]; ring

theorem bits_sum_le {d n J : ℕ}
    (hJD : 2^J ≤ AlignmentPaperLpJointDvp.JointSampleDimension d n) :
    ((∑ j : Fin (J+1), bits d n J j : ℕ) : ℝ) ≤
      (6*codingConstant) * (2:ℝ)^J *
        logRatio (AlignmentPaperLpJointDvp.JointSampleDimension d n) J := by
  let D := AlignmentPaperLpJointDvp.JointSampleDimension d n
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ j : Fin (J+1), codingConstant*(2:ℝ)^j.val*
        (logRatio D j.val + ((J-j.val:ℕ):ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      have hj : 2^j.val ≤ D :=
        (Nat.pow_le_pow_right (by norm_num) (show j.val ≤ J by omega)).trans hJD
      exact bitCost_le hj
    _ = codingConstant * dyadicStageCost J (logRatio D) := by
      rw [Fin.sum_univ_eq_sum_range
        (fun j : ℕ => codingConstant*(2:ℝ)^j*(logRatio D j + ((J-j:ℕ):ℝ))) (J+1)]
      unfold dyadicStageCost
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ codingConstant * (6*(2:ℝ)^J*logRatio D J) :=
      mul_le_mul_of_nonneg_left (dyadicLogStageCost_le hJD) codingConstant_pos.le
    _ = _ := by ring
end BrownianSharp.AlignmentPaperJointDyadicBitBudget
