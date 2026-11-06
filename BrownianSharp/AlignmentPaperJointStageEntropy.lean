import BrownianSharp.AlignmentPaperJointStagePieces

/-! Finite adaptive entropy covers of the actual joint feature image.  Only
explicit finite support counts are budgeted; adaptive heads are never treated
as one fixed approximation subspace. -/
noncomputable section
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp.AlignmentPaperJointStageEntropy
open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperJointStageRates
open BrownianSharp.AlignmentPaperJointStageImage
open BrownianSharp.AlignmentPaperJointStageChain
open BrownianSharp.AlignmentPaperJointStagePieces

theorem jointFeature_entropy_le_of_stage_counts {d n K : ℕ} {p B R : ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B) (hR : 0 ≤ R)
    (hD : 0 < DictionaryDimension d n)
    (m : Fin (K + 1) → ℕ) (D : ∀ j, JointStageData d n p B R (m j))
    (ε : Fin (K + 1) → ℝ) (hε : ∀ j, 0 < ε j)
    (e : Fin (K + 1) → ℕ)
    (hcount : ∀ j, stageCoverCount (d := d) (n := n)
      (p := p) (B := B) (R := R) m ε j ≤ 2 ^ e j)
    (hfirst : AlignmentPaperJointHeadOnly.jointRowBound d n * B ≤
      stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0) :
    HaarQuarter.TheoremD.entropyNumber ((∑ j, e j) + 1)
      (jointLpFeatureImage (d := d) (n := n) p B) ≤
      ENNReal.ofReal ((∑ j, ε j) +
        stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m (Fin.last K)) := by
  classical
  let X := PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)
  let δ := stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m (Fin.last K)
  have hδ : 0 ≤ δ := stageRadius_nonneg (d := d) (n := n) (p := p) hB.le hR m _
  choose P hPs hPr hPc using exists_stage_increment_piece (d := d) (n := n)
    (p := p) hB.le hR m D ε hε
  let pieces : List (Carl.CoverPiece X) :=
    Carl.zeroBallPiece 0 :: (List.ofFn P ++ [Carl.zeroBallPiece (NNReal.mk δ hδ)])
  let exponents := 0 :: (List.ofFn e ++ [0])
  have hsources : pieces.map Carl.CoverPiece.source =
      ({0} :: List.ofFn (stageStepSource m D) ++ [Metric.closedBall (0 : X) δ]) := by
    have hz : (Carl.zeroBallPiece (0 : ℝ≥0) : Carl.CoverPiece X).source = {0} := by
      ext x
      simp [Carl.zeroBallPiece]
    have hm : (List.ofFn P).map Carl.CoverPiece.source =
        List.ofFn (stageStepSource m D) := by
      rw [List.map_ofFn]
      congr 1
      funext j
      exact hPs j
    unfold pieces
    rw [List.map_cons, List.map_append, List.map_singleton, hm, hz]
    rfl
  have hcounts : List.Forall₂
      (fun q exponent => q.centers.encard ≤ ((2 ^ exponent : ℕ) : ℕ∞))
      pieces exponents := by
    have hmid : List.Forall₂
        (fun q exponent => q.centers.encard ≤ ((2 ^ exponent : ℕ) : ℕ∞))
        (List.ofFn P) (List.ofFn e) := by
      apply Carl.forall₂_ofFn
      intro j
      exact (hPc j).trans (by exact_mod_cast hcount j)
    exact List.Forall₂.cons (by simp [Carl.zeroBallPiece])
      (List.rel_append hmid (List.Forall₂.cons (by simp [Carl.zeroBallPiece]) List.Forall₂.nil))
  have htail : ∀ u : {f : X // f ∈ jointLpFeatureImage (d := d) (n := n) p B},
      u.1 - chainApproximant m D (Fin.last (K+1)) u ∈ Metric.closedBall (0 : X) δ := by
    intro u
    rw [← Fin.succ_last]
    simpa only [Metric.mem_closedBall, dist_zero_right, chainApproximant, Fin.cases_succ,
      δ, stageRadius] using stageOutput_error m D (Fin.last K) u
  have hent := AlignmentPaperNonlinearEntropyCover.entropyNumber_le_of_adaptive_increment_chain
    (jointLpFeatureImage (d := d) (n := n) p B) (K+1) ((∑ j, e j)+1)
    (chainApproximant m D) (stageStepSource m D) (Metric.closedBall (0 : X) δ)
    pieces exponents (chain_approximant_start_eq_zero m D)
    (fun j u => actual_chain_increment_mem hp hp2 hB hR hD m D u hfirst j)
    htail hsources hcounts (by
      unfold exponents
      rw [List.sum_cons, List.sum_append, List.sum_singleton, List.sum_ofFn]
      omega)
  have hsum : (Carl.sumRadii pieces : ℝ) = (∑ j, ε j) + δ := by
    rw [Carl.sumRadii_eq_list_sum]
    unfold pieces
    rw [List.map_cons, List.map_append, List.map_singleton, List.map_ofFn,
      List.sum_cons, List.sum_append, List.sum_singleton, List.sum_ofFn]
    simp only [Carl.zeroBallPiece, zero_add, NNReal.coe_add, NNReal.coe_sum,
      NNReal.coe_mk]
    simp [Function.comp_apply, hPr]
  rw [← hsum]
  simpa only [ENNReal.ofReal_coe_nnreal] using hent
end BrownianSharp.AlignmentPaperJointStageEntropy
