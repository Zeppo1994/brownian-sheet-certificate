import BrownianSharp.AlignmentPaperJointStageImage
import BrownianSharp.AlignmentPaperJointStageIncrements

set_option maxHeartbeats 500000

/-! Membership of the actual telescoping increments in the support-labelled
families covered by the nonlinear volumetric lemma. -/

noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperJointStageChain

open BrownianSharp.AlignmentPaperJointAdaptiveEntropy
open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperJointHeadOnly
open BrownianSharp.AlignmentPaperJointStageImage
open BrownianSharp.AlignmentPaperJointStageIncrements
open BrownianSharp.AlignmentPaperJointStageRates
open BrownianSharp.AlignmentPaperLpJointDvp

def stageRadius {d n K : ℕ} {p B R : ℝ}
    (m : Fin (K + 1) → ℕ) (j : Fin (K + 1)) : ℝ :=
  40 * Real.sqrt 50 * jointRowBound d n * B * Real.sqrt R *
    (m j : ℝ) ^ (-1 / p)

theorem stageRadius_nonneg {d n K : ℕ} {p B R : ℝ}
    (hB : 0 ≤ B) (hR : 0 ≤ R) (m : Fin (K + 1) → ℕ)
    (j : Fin (K + 1)) :
    0 ≤ stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m j := by
  unfold stageRadius jointRowBound
  positivity

noncomputable def firstStepFamily {d n K : ℕ} {p B R : ℝ}
    (m : Fin (K + 1) → ℕ)
    (D : ∀ j, JointStageData d n p B R (m j)) :=
  supportPairIncrementFamily (d := d) (n := n) (r₁ := m 0) (r₂ := 0)
    (D 0).V ⊥

noncomputable def stageStepSource {d n K : ℕ} {p B R : ℝ}
    (m : Fin (K + 1) → ℕ)
    (D : ∀ j, JointStageData d n p B R (m j))
    (j : Fin (K + 1)) :
    Set (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)) :=
  Fin.cases
    (AlignmentPaperNonlinearEntropyCover.familyBallSource
      (firstStepFamily m D)
      (2 * stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0))
    (fun i => AlignmentPaperNonlinearEntropyCover.familyBallSource
      (supportPairIncrementFamily (d := d) (n := n)
        (r₁ := m i.succ) (r₂ := m i.castSucc)
        (D i.succ).V (D i.castSucc).V)
      (stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m i.succ +
        stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m i.castSucc)) j

def stageStepRadius {d n K : ℕ} {p B R : ℝ}
    (m : Fin (K + 1) → ℕ) (j : Fin (K + 1)) : ℝ :=
  Fin.cases (2 * stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0)
    (fun i => stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m i.succ +
      stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m i.castSucc) j

theorem chain_approximant_start_eq_zero {d n K : ℕ} {p B R : ℝ}
    (m : Fin (K + 1) → ℕ)
    (D : ∀ j, JointStageData d n p B R (m j))
    (u : {f : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) //
      f ∈ jointLpFeatureImage (d := d) (n := n) p B}) :
    chainApproximant m D 0 u = 0 :=
  chainApproximant_start m D u

theorem actual_chain_increment_mem {d n K : ℕ} {p B R : ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B) (hR : 0 ≤ R)
    (hD : 0 < DictionaryDimension d n)
    (m : Fin (K + 1) → ℕ)
    (D : ∀ j, JointStageData d n p B R (m j))
    (u : {f : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) //
      f ∈ jointLpFeatureImage (d := d) (n := n) p B})
    (hfirst : jointRowBound d n * B ≤
      stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0)
    (j : Fin (K + 1)) :
    chainApproximant m D j.succ u - chainApproximant m D j.castSucc u ∈
      stageStepSource (d := d) (n := n) (p := p) (B := B) (R := R) m D j := by
  classical
  cases j using Fin.cases with
  | zero =>
      let A := stageSupport m D 0 u
      let y := stageOutput m D 0 u
      have hA : A.card ≤ m 0 := stageSupport_card_le m D 0 u
      have hy : y ∈ (D 0).V := stageOutput_mem m D 0 u
      have herrA : ‖featureMap (d := d) (n := n)
          (WithLp.toLp 2 (sourceVector u)) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2
              (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A
          (sourceVector u))) + y)‖ ≤
          stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0 := by
        have he := stageOutput_error m D 0 u
        rw [← sourceVector_featureMap u] at he
        simpa [A, y, stageRadius] using he
      have hzero : ‖u.1 - (0 :
          PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ))‖ ≤
          stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0 := by
        have hfeature := featureMap_norm_le hD (WithLp.toLp 2 (sourceVector u))
        have hsource := lpBudget_euclidean_norm_le (by linarith : 0 < p)
          (by linarith : p ≤ 2) hB (sourceVector u)
          (sourceVector_budget u)
        have hu : ‖u.1‖ ≤ jointRowBound d n * B := by
          rw [← sourceVector_featureMap u]
          exact hfeature.trans (mul_le_mul_of_nonneg_left hsource
            (add_nonneg (Real.sqrt_nonneg _) (by norm_num)))
        have hfirst' : ‖u.1‖ ≤
            stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0 := hu.trans hfirst
        simpa using hfirst'
      have hzero' : ‖featureMap (d := d) (n := n)
          (WithLp.toLp 2 (sourceVector u)) -
          featureMap (d := d) (n := n)
            (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead
              (∅ : Finset (Fin (JointSampleDimension d n))) (sourceVector u)))‖ ≤
          stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0 := by
        have hh : BrownianSharp.AlignmentPaperSparseHead.thresholdHead
            (∅ : Finset (Fin (JointSampleDimension d n))) (sourceVector u) = 0 := by
          funext i
          simp [BrownianSharp.AlignmentPaperSparseHead.thresholdHead]
        rw [hh]
        have hmap : featureMap (d := d) (n := n)
            (WithLp.toLp 2 (0 : Fin (JointSampleDimension d n) → ℝ)) = 0 := by
          simp
        rw [hmap, sub_zero, sourceVector_featureMap]
        simpa using hzero
      have hzero'' : ‖featureMap (d := d) (n := n)
          (WithLp.toLp 2 (sourceVector u)) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead
              (∅ : Finset (Fin (JointSampleDimension d n))) (sourceVector u))) + 0)‖ ≤
          stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0 := by
        simpa only [add_zero] using hzero'
      have hmem := joint_stage_increment_mem_familyBallSource_of_two_radii
        (d := d) (n := n) (r₁ := m 0) (r₂ := 0)
        (D 0).V ⊥ (sourceVector u) A ∅ hA (by simp) y 0 hy (Submodule.zero_mem _)
        (R₁ := stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0)
        (R₂ := stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0)
        (stageRadius_nonneg (d := d) (n := n) hB.le hR m 0)
        (stageRadius_nonneg (d := d) (n := n) hB.le hR m 0) herrA hzero''
      have hempty : BrownianSharp.AlignmentPaperSparseHead.thresholdHead
          (∅ : Finset (Fin (JointSampleDimension d n))) (sourceVector u) = 0 := by
        funext i
        simp only [BrownianSharp.AlignmentPaperSparseHead.thresholdHead, Finset.notMem_empty,
          ↓reduceIte, Pi.zero_apply]
      have hemptyMap : featureMap (d := d) (n := n)
          (WithLp.toLp 2 (0 : Fin (JointSampleDimension d n) → ℝ)) = 0 := by simp
      rw [hempty, hemptyMap, add_zero, sub_zero, ← two_mul] at hmem
      simp only [chainApproximant, stageStepSource, Fin.castSucc_zero,
        Fin.cases_zero, Fin.cases_succ, sub_zero]
      change (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A (sourceVector u))) + y) ∈
        AlignmentPaperNonlinearEntropyCover.familyBallSource (firstStepFamily m D)
          (2 * stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m 0)
      exact hmem
  | succ i =>
      let A := stageSupport m D i.succ u
      let B' := stageSupport m D i.castSucc u
      let y := stageOutput m D i.succ u
      let z := stageOutput m D i.castSucc u
      have hA : A.card ≤ m i.succ := stageSupport_card_le m D i.succ u
      have hBc : B'.card ≤ m i.castSucc := stageSupport_card_le m D i.castSucc u
      have hy : y ∈ (D i.succ).V := stageOutput_mem m D i.succ u
      have hz : z ∈ (D i.castSucc).V := stageOutput_mem m D i.castSucc u
      have herrA : ‖featureMap (d := d) (n := n)
          (WithLp.toLp 2 (sourceVector u)) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2
              (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A
          (sourceVector u))) + y)‖ ≤
          stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m i.succ := by
        have he := stageOutput_error m D i.succ u
        rw [← sourceVector_featureMap u] at he
        simpa [A, y, stageRadius] using he
      have herrB : ‖featureMap (d := d) (n := n)
          (WithLp.toLp 2 (sourceVector u)) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2
              (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B'
              (sourceVector u))) + z)‖ ≤
          stageRadius (d := d) (n := n) (p := p) (B := B) (R := R) m i.castSucc := by
        have he := stageOutput_error m D i.castSucc u
        rw [← sourceVector_featureMap u] at he
        simpa [B', z, stageRadius] using he
      have hmem := joint_stage_increment_mem_familyBallSource_of_two_radii
        (d := d) (n := n) (r₁ := m i.succ) (r₂ := m i.castSucc)
        (D i.succ).V (D i.castSucc).V (sourceVector u) A B' hA hBc y z hy hz
        (stageRadius_nonneg (d := d) (n := n) hB.le hR m i.succ)
        (stageRadius_nonneg (d := d) (n := n) hB.le hR m i.castSucc) herrA herrB
      simpa only [chainApproximant, stageStepSource, stageStepRadius,
        A, B', y, z, Fin.castSucc_succ, Fin.cases_zero, Fin.cases_succ] using hmem

end BrownianSharp.AlignmentPaperJointStageChain
