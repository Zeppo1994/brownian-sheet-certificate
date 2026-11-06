import BrownianSharp.AlignmentPaperJointStageEntropy
import BrownianSharp.AlignmentPaperAdaptiveDyadicCardinality

/-! Dyadic rank stages for the actual feature image. The dictionaries are fixed
before the input, and the coding budget is derived from actual support counts. -/
noncomputable section
open scoped BigOperators NNReal ENNReal
namespace BrownianSharp.AlignmentPaperJointDyadicStages
open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperJointStageRates
open BrownianSharp.AlignmentPaperJointStageChain
open BrownianSharp.AlignmentPaperJointStagePieces
open BrownianSharp.AlignmentPaperJointStageImage
open BrownianSharp.AlignmentPaperJointStageEntropy
open BrownianSharp.AlignmentPaperJointHeadOnly
open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.AlignmentPaperAdaptiveDyadicRadius
open BrownianSharp.AlignmentPaperAdaptiveDyadicCardinality
open BrownianSharp.AlignmentPaperAdaptiveCardinalityCost

def dictionaryLog (d n : ℕ) : ℝ :=
  Real.log ((DictionaryDimension d n : ℝ)+1) + Real.log 129 + 1

def dyadicRanks (J : ℕ) (j : Fin (J+1)) : ℕ := 2^j.val

def stageScale (d n : ℕ) (B : ℝ) : ℝ :=
  40 * Real.sqrt 50 * jointRowBound d n * B * Real.sqrt (dictionaryLog d n)

def mesh (d n J : ℕ) (p B : ℝ) (j : Fin (J+1)) : ℝ :=
  dyadicMesh (stageScale d n B) p J j.val

def bits (d n J : ℕ) (j : Fin (J+1)) : ℕ :=
  Nat.ceil ((Real.log 2 +
    2 * supportCost (JointSampleDimension d n) (2^j.val) +
    4*((2^j.val : ℕ):ℝ)*(Real.log 7 + (2*(J-j.val):ℕ)*Real.log 2)) / Real.log 2)

theorem dictionaryLog_one_le (d n : ℕ) : 1 ≤ dictionaryLog d n := by
  have hdim : 0 ≤ (DictionaryDimension d n : ℝ) := Nat.cast_nonneg _
  have h₁ : 0 ≤ Real.log ((DictionaryDimension d n : ℝ)+1) :=
    Real.log_nonneg (by linarith)
  have h₂ : 0 ≤ Real.log (129:ℝ) := Real.log_nonneg (by norm_num)
  dsimp [dictionaryLog]
  linarith

theorem dictionaryDimension_pos (d n : ℕ) : 0 < DictionaryDimension d n := by
  haveI : Nonempty (GradeCommonGrid d n) := ⟨fun _ => ⟨0, by
    dsimp [gradeCommonBandwidth]
    positivity⟩⟩
  exact Nat.mul_pos Fintype.card_pos (by norm_num)

theorem stageScale_pos {d n : ℕ} {B : ℝ} (hB : 0 < B) : 0 < stageScale d n B := by
  have hL : 0 < dictionaryLog d n := lt_of_lt_of_le zero_lt_one (dictionaryLog_one_le d n)
  have hrow : 0 < jointRowBound d n := by unfold jointRowBound; positivity
  unfold stageScale
  positivity

theorem dyadic_stageRadius {d n J : ℕ} {p B : ℝ} (j : Fin (J+1)) :
    stageRadius (d := d) (n := n) (p := p) (B := B) (R := dictionaryLog d n)
      (dyadicRanks J) j = dyadicRadius (stageScale d n B) p j.val := by
  simp only [stageRadius, dyadicRanks, dyadicRadius, stageScale, Nat.cast_pow, Nat.cast_ofNat]

theorem initial_radius_ge {d n J : ℕ} {p B : ℝ} (hB : 0 < B) :
    jointRowBound d n * B ≤
      stageRadius (d := d) (n := n) (p := p) (B := B) (R := dictionaryLog d n)
        (dyadicRanks J) 0 := by
  rw [dyadic_stageRadius]
  simp only [dyadicRadius, Fin.val_zero, pow_zero, Real.one_rpow, mul_one]
  have hs : 1 ≤ Real.sqrt (dictionaryLog d n) :=
    (Real.le_sqrt (by norm_num : (0:ℝ)≤1)
      (zero_le_one.trans (dictionaryLog_one_le d n))).mpr
        (by simpa using dictionaryLog_one_le d n)
  have hs50 : 1 ≤ Real.sqrt (50:ℝ) :=
    (Real.le_sqrt (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)≤50)).mpr (by norm_num)
  have hrow : 0 ≤ jointRowBound d n := by unfold jointRowBound; positivity
  unfold stageScale
  nlinarith [mul_nonneg hrow hB.le,
    mul_le_mul hs50 hs (by norm_num : (0:ℝ)≤1) (Real.sqrt_nonneg 50)]

theorem dyadic_stageCoverCount_le {d n J : ℕ} {p B : ℝ}
    (hp : 1 < p) (hB : 0 < B) (hJD : 2^J ≤ JointSampleDimension d n)
    (j : Fin (J+1)) :
    stageCoverCount (d := d) (n := n) (p := p) (B := B) (R := dictionaryLog d n)
      (dyadicRanks J) (mesh d n J p B) j ≤ 2 ^ bits d n J j := by
  have hT := stageScale_pos (d := d) (n := n) hB
  have hrank (i : Fin (J+1)) : dyadicRanks J i ≤ JointSampleDimension d n :=
    (Nat.pow_le_pow_right (by norm_num) (show i.val ≤ J by omega)).trans hJD
  have hnonneg (i : Fin (J+1)) : 0 ≤
      stageRadius (d := d) (n := n) (p := p) (B := B) (R := dictionaryLog d n)
        (dyadicRanks J) i := by
    rw [dyadic_stageRadius]
    exact (dyadicRadius_pos hT i.val).le
  cases j using Fin.cases with
  | zero =>
      have hr := firstRadius_mesh_ratio (p := p) hT hp J
      have hc := pairCoverCount_le_binary_cost (d := d) (n := n)
        (r₁ := dyadicRanks J 0) (r₂ := 0) (gap := J)
        (R := 2 * stageRadius (d := d) (n := n) (p := p) (B := B)
          (R := dictionaryLog d n) (dyadicRanks J) 0) (ε := mesh d n J p B 0)
        (Nat.zero_le _) (hrank 0) (mul_nonneg (by norm_num) (hnonneg 0))
        (dyadicMesh_pos hT J 0) (by simpa only [dyadic_stageRadius, mesh, Fin.val_zero] using hr)
      simpa only [stageCoverCount, Fin.cases_zero, bits, dyadicRanks, Fin.val_zero,
        pow_zero, Nat.sub_zero, Nat.cast_one] using hc
  | succ i =>
      have hr := adjacentRadius_mesh_ratio (p := p) (j := i.val+1)
        (J := J) hT hp (by omega) (by omega)
      have hc := pairCoverCount_le_binary_cost (d := d) (n := n)
        (r₁ := dyadicRanks J i.succ) (r₂ := dyadicRanks J i.castSucc)
        (gap := J-(i.val+1))
        (R := stageRadius (d := d) (n := n) (p := p) (B := B)
            (R := dictionaryLog d n) (dyadicRanks J) i.succ +
          stageRadius (d := d) (n := n) (p := p) (B := B)
            (R := dictionaryLog d n) (dyadicRanks J) i.castSucc)
        (ε := mesh d n J p B i.succ)
        (Nat.pow_le_pow_right (by norm_num) (by simp only [Fin.val_succ, Fin.val_castSucc]; omega))
        (hrank i.succ) (add_nonneg (hnonneg i.succ) (hnonneg i.castSucc))
        (dyadicMesh_pos hT J _) (by
          simpa only [dyadic_stageRadius, mesh, Fin.val_succ, Fin.val_castSucc,
            Nat.add_sub_cancel] using hr)
      simpa only [stageCoverCount, Fin.cases_succ, bits, dyadicRanks,
        Fin.val_succ, Fin.val_castSucc] using hc

theorem jointFeature_dyadic_entropy {d n J : ℕ} {p B : ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B)
    (hJD : 2^J ≤ JointSampleDimension d n) :
    HaarQuarter.TheoremD.entropyNumber ((∑ j, bits d n J j)+1)
      (jointLpFeatureImage (d := d) (n := n) p B) ≤
      ENNReal.ofReal ((∑ j, mesh d n J p B j) +
        dyadicRadius (stageScale d n B) p J) := by
  let D : ∀ j : Fin (J+1), JointStageData d n p B (dictionaryLog d n) (dyadicRanks J j) :=
    fun j => exists_joint_stage_data hp hp2 hB (dictionaryDimension_pos d n)
      (lt_of_lt_of_le zero_lt_one (dictionaryLog_one_le d n)) rfl (by
        dsimp [dyadicRanks]
        positivity)
  have he := jointFeature_entropy_le_of_stage_counts hp hp2 hB
    (zero_le_one.trans (dictionaryLog_one_le d n)) (dictionaryDimension_pos d n)
    (dyadicRanks J) D (mesh d n J p B)
    (fun j => dyadicMesh_pos (stageScale_pos hB) J j.val)
    (bits d n J) (dyadic_stageCoverCount_le hp hB hJD) (initial_radius_ge hB)
  simpa only [dyadic_stageRadius, Fin.val_last] using he
end BrownianSharp.AlignmentPaperJointDyadicStages
