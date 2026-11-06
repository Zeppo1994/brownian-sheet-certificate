import BrownianSharp.AlignmentPaperJointStageOutput
import BrownianSharp.AlignmentPaperJointHeadOnly
import BrownianSharp.AlignmentPaperJointRateScalars

/-! Uniform rank-stage approximations for the true joint feature image. -/

noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperJointStageRates

open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperJointStageOutput
open BrownianSharp.AlignmentPaperJointHeadOnly
open BrownianSharp.AlignmentPaperJointRateScalars
open BrownianSharp.AlignmentPaperLpJointDvp

structure JointStageData (d n : ℕ) (p B L : ℝ) (m : ℕ) where
  V : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ))
  rank_le : Module.rank ℝ V ≤ (m : Cardinal)
  approx : ∀ x : Fin (JointSampleDimension d n) → ℝ,
    (∑ i, |x i| ^ p) ≤ B ^ p →
      ∃ A : Finset (Fin (JointSampleDimension d n)), A.card ≤ m ∧
        ∃ y ∈ V,
          ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
            (featureMap (d := d) (n := n)
              (WithLp.toLp 2
                (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y)‖ ≤
            40 * Real.sqrt 50 * jointRowBound d n * B * Real.sqrt L *
              (m : ℝ) ^ (-1 / p)

theorem joint_head_stage_rate {d n m : ℕ} {p B L : ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B)
    (hD : 0 < DictionaryDimension d n) (hL : 0 < L)
    (hm : 0 < m) (hmL : (m : ℝ) ≤ 400 * L)
    (x : Fin (JointSampleDimension d n) → ℝ)
    (hx : (∑ i, |x i| ^ p) ≤ B ^ p) :
    ∃ A : Finset (Fin (JointSampleDimension d n)), A.card ≤ m ∧
      ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
        featureMap (d := d) (n := n)
          (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x))‖ ≤
        20 * jointRowBound d n * B * Real.sqrt L * (m : ℝ) ^ (-1 / p) := by
  obtain ⟨A, hA, herror⟩ :=
    joint_head_only_approximation hp hp2 hB hD x hx hm
  refine ⟨A, hA, ?_⟩
  calc
    _ ≤ jointRowBound d n *
        Real.sqrt ((B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p) := herror
    _ ≤ jointRowBound d n *
        (20 * B * Real.sqrt L * (m : ℝ) ^ (-1 / p)) := by
      apply mul_le_mul_of_nonneg_left
        (thresholdTailRadius_le_of_small_rank hp hp2 hB hm hL hmL)
      exact add_nonneg (Real.sqrt_nonneg _) (by norm_num)
    _ = 20 * jointRowBound d n * B * Real.sqrt L * (m : ℝ) ^ (-1 / p) := by ring

theorem joint_kgg_stage_rate {d n m : ℕ} {p B L : ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B)
    (hL : 0 < L)
    (hLid : L = Real.log ((DictionaryDimension d n : ℝ) + 1) +
      Real.log 129 + 1)
    (s : ℕ) (hs : 1 ≤ s)
    (hslo : (m : ℝ) / (400 * L) ≤ (s : ℝ))
    (V : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)))
    (hVrank : Module.rank ℝ V ≤ (m : Cardinal))
    (happrox : ∀ z : EuclideanSpace ℝ (Fin (JointSampleDimension d n)), ‖z‖ ≤ 1 →
      ∃ y ∈ V, ‖featureMap (d := d) (n := n) z - y‖ ≤
        2 * (Real.sqrt 50 * jointRowBound d n / Real.sqrt (s : ℝ)))
    (hm : 0 < m)
    (x : Fin (JointSampleDimension d n) → ℝ)
    (hx : (∑ i, |x i| ^ p) ≤ B ^ p) :
    ∃ A : Finset (Fin (JointSampleDimension d n)), A.card ≤ m ∧
      ∃ y ∈ V,
        ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y)‖ ≤
          40 * Real.sqrt 50 * jointRowBound d n * B * Real.sqrt L *
            (m : ℝ) ^ (-1 / p) := by
  have hslo' : (m : ℝ) / (400 * (Real.log ((DictionaryDimension d n : ℝ) + 1) +
      Real.log 129 + 1)) ≤ (s : ℝ) := by simpa [hLid] using hslo
  obtain ⟨A, hA, y, hy, herr⟩ :=
    exists_joint_stage_center hp hp2 hB s hs hslo' V hVrank happrox x hx hm
  refine ⟨A, hA, y, hy, ?_⟩
  have htail := thresholdTailRadius_eq hp hp2 hB hm
  have hspos : 0 < s := by omega
  have hscalar := stageRadius_over_sqrt_le hp hm hspos hL hslo
  have hscalarB : B * (m : ℝ) ^ (1 / 2 - 1 / p) / Real.sqrt (s : ℝ) ≤
      20 * B * Real.sqrt L * (m : ℝ) ^ (-1 / p) := by
    have := mul_le_mul_of_nonneg_left hscalar hB.le
    convert this using 1 <;> ring
  have hrow : 0 ≤ jointRowBound d n :=
    add_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have hC : 0 ≤ 2 * Real.sqrt 50 * jointRowBound d n :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hrow
  calc
    _ ≤ (2 * Real.sqrt 50 * jointRowBound d n) *
        (Real.sqrt ((B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p) /
          Real.sqrt (s : ℝ)) := by
      have herr' : ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y)‖ ≤
          2 * Real.sqrt 50 * jointRowBound d n / Real.sqrt (s : ℝ) *
            Real.sqrt ((B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p) := by
        simpa [jointRowBound] using herr
      calc
        _ ≤ 2 * Real.sqrt 50 * jointRowBound d n / Real.sqrt (s : ℝ) *
            Real.sqrt ((B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p) := herr'
        _ = _ := by ring
    _ ≤ (2 * Real.sqrt 50 * jointRowBound d n) *
        (20 * B * Real.sqrt L * (m : ℝ) ^ (-1 / p)) := by
      apply mul_le_mul_of_nonneg_left _ hC
      rw [htail]
      exact hscalarB
    _ = 40 * Real.sqrt 50 * jointRowBound d n * B * Real.sqrt L *
        (m : ℝ) ^ (-1 / p) := by ring

theorem exists_joint_kgg_stage_rate {d n m : ℕ} {p B L : ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B) (hL : 0 < L)
    (hLid : L = Real.log ((DictionaryDimension d n : ℝ) + 1) +
      Real.log 129 + 1)
    (hm : 400 * L ≤ (m : ℝ)) :
    ∃ s : ℕ, 1 ≤ s ∧ (m : ℝ) / (400 * L) ≤ (s : ℝ) ∧
      ∃ V : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)),
        Module.rank ℝ V ≤ (m : Cardinal) ∧
        ∀ x : Fin (JointSampleDimension d n) → ℝ,
          (∑ i, |x i| ^ p) ≤ B ^ p →
          ∃ A : Finset (Fin (JointSampleDimension d n)), A.card ≤ m ∧
            ∃ y ∈ V,
              ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
                (featureMap (d := d) (n := n)
                  (WithLp.toLp 2
                    (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y)‖ ≤
                40 * Real.sqrt 50 * jointRowBound d n * B * Real.sqrt L *
                  (m : ℝ) ^ (-1 / p) := by
  have hm' : 400 * (Real.log ((DictionaryDimension d n : ℝ) + 1) +
      Real.log 129 + 1) ≤ (m : ℝ) := by simpa [hLid] using hm
  obtain ⟨s, hs, hslo, V, hVrank, happrox⟩ :=
    exists_joint_dictionary_subspace (d := d) (n := n) (m := m) hm'
  refine ⟨s, hs, ?_, V, hVrank, ?_⟩
  · simpa [hLid] using hslo
  · intro x hx
    have hsloRate : (m : ℝ) / (400 * L) ≤ (s : ℝ) := by
      simpa [hLid] using hslo
    exact joint_kgg_stage_rate hp hp2 hB hL hLid s hs hsloRate V hVrank
      (by simpa [jointRowBound] using happrox) (by
        have hpos : 0 < (m : ℝ) := by linarith
        exact_mod_cast hpos) x hx

def exists_joint_stage_data {d n m : ℕ} {p B L : ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B)
    (hD : 0 < DictionaryDimension d n) (hL : 0 < L)
    (hLid : L = Real.log ((DictionaryDimension d n : ℝ) + 1) +
      Real.log 129 + 1)
    (hm : 0 < m) :
    JointStageData d n p B L m := by
  by_cases hlow : (m : ℝ) ≤ 400 * L
  · refine ⟨⊥, ?_, ?_⟩
    · simp
    · intro x hx
      obtain ⟨A, hA, herr⟩ := joint_head_stage_rate hp hp2 hB hD hL hm hlow x hx
      refine ⟨A, hA, 0, Submodule.zero_mem _, ?_⟩
      have hrow : 0 ≤ jointRowBound d n :=
        add_nonneg (Real.sqrt_nonneg _) (by norm_num)
      have hconstant : 20 * jointRowBound d n * B * Real.sqrt L ≤
          40 * Real.sqrt 50 * jointRowBound d n * B * Real.sqrt L := by
        have hbase : 0 ≤ jointRowBound d n * B * Real.sqrt L :=
          mul_nonneg (mul_nonneg hrow hB.le) (Real.sqrt_nonneg _)
        have hcoeff : (20 : ℝ) ≤ 40 * Real.sqrt 50 := by
          have hsqrt : (1 : ℝ) ≤ Real.sqrt 50 := by
            have := Real.sq_sqrt (show 0 ≤ (50 : ℝ) by norm_num)
            nlinarith [Real.sqrt_nonneg (50 : ℝ)]
          nlinarith
        convert mul_le_mul_of_nonneg_right hcoeff hbase using 1 <;> ring
      have herr' : ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2
              (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + 0)‖ ≤
          20 * jointRowBound d n * B * Real.sqrt L * (m : ℝ) ^ (-1 / p) := by
        simpa using herr
      exact herr'.trans (mul_le_mul_of_nonneg_right hconstant
        (Real.rpow_nonneg (by exact_mod_cast (Nat.zero_le m)) _))
  · have hhigh : 400 * L ≤ (m : ℝ) := le_of_not_ge hlow
    let hdata := exists_joint_kgg_stage_rate hp hp2 hB hL hLid hhigh
    let s := Classical.choose hdata
    have hsdata := Classical.choose_spec hdata
    have hs : 1 ≤ s := hsdata.1
    have hslo : (m : ℝ) / (400 * L) ≤ (s : ℝ) := hsdata.2.1
    let hVdata := hsdata.2.2
    let V := Classical.choose hVdata
    have hVspec := Classical.choose_spec hVdata
    have hVrank : Module.rank ℝ V ≤ (m : Cardinal) := hVspec.1
    have happrox := hVspec.2
    exact ⟨V, hVrank, happrox⟩

end BrownianSharp.AlignmentPaperJointStageRates
