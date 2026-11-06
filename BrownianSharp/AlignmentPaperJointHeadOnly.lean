import BrownianSharp.AlignmentPaperJointAdaptiveEntropy

/-! The low-rank end of the adaptive chain uses only the sparse head.  This
leaf records the actual operator bound for the common-grid feature map and
turns the sharp `ℓ²` tail estimate into an output error bound. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperJointHeadOnly

open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperLpJointDvp

def jointRowBound (d n : ℕ) : ℝ :=
  Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
    ((25 / 4 : ℝ) ^ d)) + 1

theorem lpBudget_euclidean_norm_le {M : ℕ} {p B : ℝ}
    (hp : 0 < p) (hp2 : p ≤ 2) (hB : 0 < B)
    (x : Fin M → ℝ) (hx : (∑ i, |x i| ^ p) ≤ B ^ p) :
    ‖WithLp.toLp 2 x‖ ≤ B := by
  have hp0 : 0 < p := hp
  have hcoord : ∀ i, |x i| ^ p ≤ B ^ p := by
    intro i
    calc
      |x i| ^ p ≤ ∑ j, |x j| ^ p := Finset.single_le_sum
        (fun j hj => Real.rpow_nonneg (abs_nonneg _) p) (Finset.mem_univ i)
      _ ≤ B ^ p := hx
  have hxi : ∀ i, |x i| ≤ B := by
    intro i
    by_contra h
    have hlt : B < |x i| := lt_of_not_ge h
    have hpow := Real.rpow_lt_rpow hB.le hlt hp0
    exact not_lt_of_ge (hcoord i) hpow
  have hterm : ∀ i, |x i| ^ 2 ≤ B ^ (2 - p) * |x i| ^ p := by
    intro i
    by_cases hz : |x i| = 0
    · simp [hz, Real.zero_rpow hp0.ne']
    · have hpos : 0 < |x i| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hz)
      have heq : |x i| ^ 2 = |x i| ^ (2 - p) * |x i| ^ p := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
        congr 1
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (abs_nonneg _) (hxi i) (by linarith))
        (Real.rpow_nonneg (abs_nonneg _) _)
  have hsum : (∑ i, |x i| ^ 2) ≤ B ^ (2 - p) * B ^ p := by
    calc
      _ ≤ ∑ i, B ^ (2 - p) * |x i| ^ p := Finset.sum_le_sum fun i _ => hterm i
      _ = B ^ (2 - p) * ∑ i, |x i| ^ p := by rw [Finset.mul_sum]
      _ ≤ B ^ (2 - p) * B ^ p :=
        mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hB.le _)
  have hnormsq : ‖WithLp.toLp 2 x‖ ^ 2 ≤ B ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have hnormsum : (∑ i, ‖x i‖ ^ 2) = ∑ i, |x i| ^ 2 := by simp
    rw [hnormsum]
    calc
      _ ≤ B ^ (2 - p) * B ^ p := hsum
      _ = B ^ 2 := by
        rw [← Real.rpow_add hB]
        rw [show (2 - p) + p = (2 : ℝ) by ring, Real.rpow_two]
  exact (sq_le_sq₀ (norm_nonneg _) hB.le).mp hnormsq

theorem featureMap_norm_le {d n : ℕ}
    (hD : 0 < DictionaryDimension d n)
    (z : EuclideanSpace ℝ (Fin (JointSampleDimension d n))) :
    ‖featureMap (d := d) (n := n) z‖ ≤ jointRowBound d n * ‖z‖ := by
  letI : Nonempty (Fin (DictionaryDimension d n)) := ⟨⟨0, hD⟩⟩
  have hC : 0 ≤ jointRowBound d n :=
    add_nonneg (Real.sqrt_nonneg _) (by norm_num)
  rw [PiLp.norm_eq_ciSup]
  refine ciSup_le (f := fun i : Fin (DictionaryDimension d n) =>
    ‖(featureMap z).ofLp i‖) (c := jointRowBound d n * ‖z‖) ?_
  intro i
  change ‖featureMap z i‖ ≤ jointRowBound d n * ‖z‖
  rw [featureMap_apply, jointGradeCommonGridFeature_eq_inner_row, Real.norm_eq_abs]
  calc
    |inner ℝ z (dictionaryRow (d := d) (n := n) i)| ≤
        ‖z‖ * ‖dictionaryRow (d := d) (n := n) i‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖z‖ * jointRowBound d n :=
      mul_le_mul_of_nonneg_left (dictionaryRow_norm_le i) (norm_nonneg _)
    _ = jointRowBound d n * ‖z‖ := by ring

theorem joint_head_only_approximation {d n m : ℕ}
    {p B : ℝ} (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B)
    (hD : 0 < DictionaryDimension d n)
    (x : Fin (JointSampleDimension d n) → ℝ)
    (hx : (∑ i, |x i| ^ p) ≤ B ^ p) (hmpos : 0 < m) :
    ∃ A : Finset (Fin (JointSampleDimension d n)), A.card ≤ m ∧
      ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
        featureMap (d := d) (n := n)
          (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x))‖ ≤
        jointRowBound d n *
          Real.sqrt ((B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p) := by
  classical
  obtain ⟨A, hA, _, htail⟩ :=
    BrownianSharp.AlignmentPaperSparseHead.exists_threshold_head_tail
      hp hp2 hB x hx hmpos
  let tail := BrownianSharp.AlignmentPaperSparseHead.thresholdTail A x
  have hsplit : x = BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x + tail := by
    funext i
    by_cases hi : i ∈ A <;>
      simp [tail, BrownianSharp.AlignmentPaperSparseHead.thresholdHead,
        BrownianSharp.AlignmentPaperSparseHead.thresholdTail, hi]
  have hnormsq : ‖WithLp.toLp 2 tail‖ ^ 2 ≤
      (B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [tail, sq_abs] using htail
  have hrad : 0 ≤ (B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p := by positivity
  have htailnorm : ‖WithLp.toLp 2 tail‖ ≤
      Real.sqrt ((B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    calc
      ‖WithLp.toLp 2 tail‖ ^ 2 ≤
          (B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p := hnormsq
      _ = (Real.sqrt ((B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p)) ^ 2 := by
        rw [Real.sq_sqrt hrad]
  refine ⟨A, hA, ?_⟩
  have hiden : WithLp.toLp 2 x -
      WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x) =
      WithLp.toLp 2 tail := by
    ext i
    by_cases hi : i ∈ A <;>
      simp [tail, BrownianSharp.AlignmentPaperSparseHead.thresholdHead,
        BrownianSharp.AlignmentPaperSparseHead.thresholdTail, hi]
  rw [← map_sub, hiden]
  calc
    _ ≤ jointRowBound d n * ‖WithLp.toLp 2 tail‖ := featureMap_norm_le hD _
    _ ≤ _ := mul_le_mul_of_nonneg_left htailnorm
      (add_nonneg (Real.sqrt_nonneg _) (by norm_num))

end BrownianSharp.AlignmentPaperJointHeadOnly
