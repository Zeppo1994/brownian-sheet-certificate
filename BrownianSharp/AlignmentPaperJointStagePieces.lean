import BrownianSharp.AlignmentPaperJointStageChain

/-! Actual finite covers of the support-labelled increments.  The centers are
chosen before the input; their labels retain both adaptive sparse supports. -/
noncomputable section
open scoped BigOperators ENNReal
namespace BrownianSharp.AlignmentPaperJointStagePieces
open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperJointAdaptiveEntropy
open BrownianSharp.AlignmentPaperJointStageRates
open BrownianSharp.AlignmentPaperJointStageChain
open BrownianSharp.AlignmentPaperLpJointDvp

noncomputable def pairCoverCount (d n r₁ r₂ : ℕ) (R ε : ℝ) : ℕ :=
  Fintype.card (SupportLabel (D := JointSampleDimension d n) (r := r₁) ×
    SupportLabel (D := JointSampleDimension d n) (r := r₂)) *
  Nat.ceil ((1 + 2 * R / ε) ^ (r₁ + r₁ + r₂ + r₂))

noncomputable def stageCoverCount {d n K : ℕ} {p B R : ℝ}
    (m : Fin (K + 1) → ℕ) (ε : Fin (K + 1) → ℝ) (j : Fin (K + 1)) : ℕ :=
  Fin.cases (pairCoverCount d n (m 0) 0
      (2 * stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0) (ε 0))
    (fun i => pairCoverCount d n (m i.succ) (m i.castSucc)
      (stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m i.succ +
        stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m i.castSucc)
      (ε i.succ)) j

theorem exists_stage_increment_piece {d n K : ℕ} {p B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 ≤ R)
    (m : Fin (K + 1) → ℕ)
    (D : ∀ j, JointStageData d n p B R (m j))
    (ε : Fin (K + 1) → ℝ) (hε : ∀ j, 0 < ε j)
    (j : Fin (K + 1)) :
    ∃ piece : Carl.CoverPiece (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)),
      piece.source = stageStepSource m D j ∧
      piece.radius = NNReal.mk (ε j) (hε j).le ∧
      piece.centers.encard ≤ (stageCoverCount (d := d) (n := n)
        (p := p) (B := B) (R := R) m ε j : ℕ∞) := by
  classical
  cases j using Fin.cases with
  | zero =>
      obtain ⟨piece, hs, hr, hc⟩ := exists_supportPair_increment_piece
        (d := d) (n := n) (r₁ := m 0) (r₂ := 0) (D 0).V ⊥
        (Module.finrank_le_of_rank_le (D 0).rank_le) (by simp)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (stageRadius_nonneg (d := d) (n := n) (p := p) hB hR m 0))
        (hε 0)
      refine ⟨piece, ?_, hr, ?_⟩
      · simpa only [stageStepSource, Fin.cases_zero, firstStepFamily] using hs
      · simpa only [stageCoverCount, Fin.cases_zero, pairCoverCount, Nat.cast_mul] using hc
  | succ i =>
      obtain ⟨piece, hs, hr, hc⟩ := exists_supportPair_increment_piece
        (d := d) (n := n) (r₁ := m i.succ) (r₂ := m i.castSucc)
        (D i.succ).V (D i.castSucc).V
        (Module.finrank_le_of_rank_le (D i.succ).rank_le)
        (Module.finrank_le_of_rank_le (D i.castSucc).rank_le)
        (add_nonneg (stageRadius_nonneg (d := d) (n := n) (p := p) hB hR m i.succ)
          (stageRadius_nonneg (d := d) (n := n) (p := p) hB hR m i.castSucc)) (hε i.succ)
      refine ⟨piece, ?_, hr, ?_⟩
      · simpa only [stageStepSource, Fin.cases_succ] using hs
      · simpa only [stageCoverCount, Fin.cases_succ, pairCoverCount, Nat.cast_mul] using hc
end BrownianSharp.AlignmentPaperJointStagePieces
