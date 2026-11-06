import BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1000000

namespace BrownianSharp.AlignmentPaperJointLowGradeCostSum

open BrownianSharp
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperLpJointDvp

/-- The total linear low-grade sample cost is controlled by the final joint
dimension. The bound uses the existing polynomial-times-dyadic envelopes and
the weighted geometric allocation estimate. -/
theorem joint_low_grade_dimension_cost_le {d N : ℕ} (hd : 1 ≤ d) :
    (∑ n ∈ Finset.range (N+1),
      (JointSampleDimension d n : ℝ) * (((N-n:ℕ)+1 : ℕ) : ℝ)) ≤
      (4 * (2:ℝ)^(3*d+1) /
        ((2:ℝ)^(3*d+1) / (Nat.factorial (d-1) : ℝ))) *
        (JointSampleDimension d N : ℝ) := by
  let U : ℝ := (2:ℝ)^(3*d+1)
  let c : ℝ := U / (Nat.factorial (d-1) : ℝ)
  have hU : 0 ≤ U := by positivity [U]
  have hc : 0 < c := by
    dsimp [c, U]
    positivity
  have hup : ∀ n : ℕ, (JointSampleDimension d n : ℝ) ≤
      U * (2:ℝ)^n * (n+1:ℝ)^(d-1) := by
    intro n
    simpa [U] using jointSampleDimension_upper_envelope (d := d) (n := n) hd
  have hlo : c * (2:ℝ)^N * (N+1:ℝ)^(d-1) ≤
      (JointSampleDimension d N : ℝ) := by
    simpa [c, U] using jointSampleDimension_lower_envelope (d := d) (n := N) hd
  have h := lowGradeAllocationCost_le (N := N) (q := d-1)
    (dim := fun n => (JointSampleDimension d n : ℝ)) hU hc hup hlo
  simpa [U, c, Nat.cast_add, add_comm, add_left_comm, add_assoc] using h

/-- The exact joint dimension always dominates the number of grades up to N. -/
theorem grade_count_le_joint_dimension {d N : ℕ} (hd : 1 ≤ d) :
    (N+1 : ℝ) ≤ (JointSampleDimension d N : ℝ) := by
  have hpowN : N + 1 ≤ 2^N := by
    induction N with
    | zero => norm_num
    | succ N ih =>
      rw [pow_succ]
      omega
  have hcard : 1 ≤ Fintype.card (Shape d N) := by
    rw [shape_card d N (by omega : 0 < d)]
    exact Nat.succ_le_iff.mpr (Nat.choose_pos (by omega))
  have hpow : 2^N ≤ 2^(N+3*d+1) := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) (by omega)
  have hmul : 2^(N+3*d+1) ≤
      2^(N+3*d+1) * Fintype.card (Shape d N) := by
    calc
      _ = 2^(N+3*d+1) * 1 := by simp
      _ ≤ 2^(N+3*d+1) * Fintype.card (Shape d N) :=
        Nat.mul_le_mul_left (2^(N+3*d+1)) hcard
  have hNat : N+1 ≤ 2^(N+3*d+1) * Fintype.card (Shape d N) :=
    hpowN.trans (hpow.trans hmul)
  rw [jointSampleDimension_eq_grid_formula]
  exact_mod_cast hNat

/-- Summing the integer ceiling allocation over all grades costs only a
dimensionwise constant times the top joint dimension. -/
theorem joint_low_grade_ceil_bit_sum_le {d N : ℕ} (hd : 1 ≤ d)
    (Cbit : ℝ) (hCbit : 0 ≤ Cbit) :
    (∑ n ∈ Finset.range (N+1),
      (Nat.ceil (Cbit * (JointSampleDimension d n : ℝ) *
        (((N-n:ℕ) : ℝ) + 1) : ℝ) : ℝ)) ≤
      (Cbit *
        (4 * (2:ℝ)^(3*d+1) /
          ((2:ℝ)^(3*d+1) / (Nat.factorial (d-1) : ℝ))) + 1) *
        (JointSampleDimension d N : ℝ) := by
  have hcost := joint_low_grade_dimension_cost_le (d := d) (N := N) hd
  have hceil : ∀ n ∈ Finset.range (N+1),
      (Nat.ceil (Cbit * (JointSampleDimension d n : ℝ) *
        (((N-n:ℕ) : ℝ)+1) : ℝ) : ℝ) ≤
      Cbit * (JointSampleDimension d n : ℝ) *
        (((N-n:ℕ) : ℝ)+1) + 1 := by
    intro n hn
    have hnN : n ≤ N := by simp only [Finset.mem_range] at hn; omega
    apply (Nat.ceil_lt_add_one ?_).le
    have hdim : 0 ≤ (JointSampleDimension d n : ℝ) := by positivity
    positivity
  calc
    _ ≤ ∑ n ∈ Finset.range (N+1),
        (Cbit * (JointSampleDimension d n : ℝ) *
          (((N-n:ℕ) : ℝ)+1) + 1) := by
      exact Finset.sum_le_sum (fun n hn => hceil n hn)
    _ = Cbit *
        (∑ n ∈ Finset.range (N+1),
          (JointSampleDimension d n : ℝ) * (((N-n:ℕ)+1:ℕ) : ℝ)) +
          (N+1:ℝ) := by
      calc
        _ = (∑ n ∈ Finset.range (N+1),
              Cbit * (JointSampleDimension d n : ℝ) *
                (((N-n:ℕ) : ℝ)+1)) +
              ∑ _n ∈ Finset.range (N+1), (1:ℝ) := by
          rw [Finset.sum_add_distrib]
        _ = Cbit *
              (∑ n ∈ Finset.range (N+1),
                (JointSampleDimension d n : ℝ) * (((N-n:ℕ)+1:ℕ) : ℝ)) +
              (N+1:ℝ) := by
          rw [show (∑ _n ∈ Finset.range (N+1), (1:ℝ)) = (N+1:ℝ) by simp]
          simp_rw [mul_assoc]
          rw [← Finset.mul_sum]
          apply congrArg (fun z : ℝ => Cbit * z + (N+1:ℝ))
          apply Finset.sum_congr rfl
          intro n hn
          simp only [Nat.cast_add, Nat.cast_one]
    _ ≤ Cbit *
        ((4 * (2:ℝ)^(3*d+1) /
          ((2:ℝ)^(3*d+1) / (Nat.factorial (d-1) : ℝ))) *
            (JointSampleDimension d N : ℝ)) +
          (N+1:ℝ) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left hcost hCbit
      · rfl
    _ ≤ (Cbit *
        (4 * (2:ℝ)^(3*d+1) /
          ((2:ℝ)^(3*d+1) / (Nat.factorial (d-1) : ℝ))) + 1) *
          (JointSampleDimension d N : ℝ) := by
      have hD : 0 ≤ (JointSampleDimension d N : ℝ) := by positivity
      have hgrades := grade_count_le_joint_dimension (d := d) (N := N) hd
      nlinarith

end BrownianSharp.AlignmentPaperJointLowGradeCostSum
