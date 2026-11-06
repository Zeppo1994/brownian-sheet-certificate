import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Threshold coding for the finite `ℓᵖ` ball when `1 < p < 2`.

The large-coordinate support is an adaptive label.  The remaining vector is
controlled in Euclidean norm with the sharp `m^(1/2-1/p)` tail factor. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentPaperSparseHead

def thresholdHead {M : ℕ} (A : Finset (Fin M)) (x : Fin M → ℝ) : Fin M → ℝ :=
  fun i => if i ∈ A then x i else 0

def thresholdTail {M : ℕ} (A : Finset (Fin M)) (x : Fin M → ℝ) : Fin M → ℝ :=
  fun i => if i ∈ A then 0 else x i

/-- At threshold `τ`, the support has at most `m` coordinates and the
remaining `ℓ²` energy is bounded by `τ^(2-p)` times the original `ℓᵖ`
energy. -/
theorem exists_threshold_head_tail {M : ℕ} {p B : ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B)
    (x : Fin M → ℝ) (hbudget : (∑ i, |x i| ^ p) ≤ B ^ p)
    {m : ℕ} (hm : 0 < m) :
    ∃ A : Finset (Fin M), A.card ≤ m ∧
      (∀ i ∉ A, |x i| ≤ B / (m : ℝ) ^ (1 / p)) ∧
      (∑ i, |thresholdTail A x i| ^ 2) ≤
        (B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p := by
  classical
  let τ : ℝ := B / (m : ℝ) ^ (1 / p)
  let A : Finset (Fin M) := Finset.univ.filter fun i => τ < |x i|
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hτ : 0 < τ := by
    dsimp [τ]
    positivity
  have hp0 : 0 < p := by linarith
  have hτp : τ ^ p = B ^ p / (m : ℝ) := by
    dsimp [τ]
    rw [Real.div_rpow hB.le (by positivity : 0 ≤ (m : ℝ) ^ (1 / p)),
      ← Real.rpow_mul hmR.le]
    have hpow : (1 / p) * p = 1 := by field_simp
    rw [hpow, Real.rpow_one]
  have hAcard : A.card ≤ m := by
    have hsmall : (A.card : ℝ) * τ ^ p ≤ B ^ p := by
      calc
        (A.card : ℝ) * τ ^ p = ∑ i ∈ A, τ ^ p := by simp
        _ ≤ ∑ i ∈ A, |x i| ^ p := by
          apply Finset.sum_le_sum
          intro i hi
          have hτx : τ < |x i| := (Finset.mem_filter.mp hi).2
          exact Real.rpow_le_rpow (by positivity) hτx.le hp0.le
        _ ≤ ∑ i, |x i| ^ p := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (by
            intro i hi
            exact Finset.mem_univ i) (by
              intro i hi hnot
              exact Real.rpow_nonneg (abs_nonneg _) p)
        _ ≤ B ^ p := hbudget
    rw [hτp] at hsmall
    have hcard : (A.card : ℝ) ≤ m := by
      have hmul : (A.card : ℝ) * B ^ p ≤ B ^ p * (m : ℝ) := by
        have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmR
        have h' := hsmall
        field_simp [hmne] at h'
        calc
          (A.card : ℝ) * B ^ p ≤ (m : ℝ) * B ^ p :=
            mul_le_mul_of_nonneg_right h' (Real.rpow_pos_of_pos hB p).le
          _ = B ^ p * (m : ℝ) := by ring
      nlinarith [Real.rpow_pos_of_pos hB p]
    exact_mod_cast hcard
  have htail : ∀ i, |thresholdTail A x i| ^ 2 ≤
      τ ^ (2 - p) * |x i| ^ p := by
    intro i
    by_cases hi : i ∈ A
    · simp [thresholdTail, hi]
      exact mul_nonneg (Real.rpow_nonneg hτ.le _) (Real.rpow_nonneg (abs_nonneg _) _)
    · have hxi : |x i| ≤ τ := by
        have hn : ¬ τ < |x i| := by
          intro hlt
          exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩)
        exact le_of_not_gt hn
      simp only [thresholdTail, if_neg hi]
      have hxi0 : 0 ≤ |x i| := abs_nonneg _
      by_cases hz : |x i| = 0
      · simp [hz, Real.zero_rpow hp0.ne']
      · have hxiPos : 0 < |x i| := lt_of_le_of_ne hxi0 (Ne.symm hz)
        have hsplit : |x i| ^ 2 = |x i| ^ (2 - p) * |x i| ^ p := by
          calc
            |x i| ^ 2 = |x i| ^ (2 : ℝ) :=
              (Real.rpow_natCast (|x i|) 2).symm
            _ = |x i| ^ ((2 - p) + p) := by congr 1 <;> ring
            _ = |x i| ^ (2 - p) * |x i| ^ p := Real.rpow_add hxiPos _ _
        rw [hsplit]
        have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ |x i|)
          hxi (by linarith : 0 ≤ 2 - p)
        exact mul_le_mul_of_nonneg_right hpow (by positivity)
  refine ⟨A, hAcard, ?_, ?_⟩
  · intro i hi
    have hnot : ¬ τ < |x i| := by
      intro hlt
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hlt⟩)
    simpa [τ] using le_of_not_gt hnot
  · calc
      _ ≤ ∑ i, τ ^ (2 - p) * |x i| ^ p :=
        Finset.sum_le_sum fun i _ => htail i
      _ = τ ^ (2 - p) * ∑ i, |x i| ^ p := by rw [Finset.mul_sum]
      _ ≤ τ ^ (2 - p) * B ^ p :=
        mul_le_mul_of_nonneg_left hbudget (by positivity)
      _ = (B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p := by rfl

end BrownianSharp.AlignmentPaperSparseHead
