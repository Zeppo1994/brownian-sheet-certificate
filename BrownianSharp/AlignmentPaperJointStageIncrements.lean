import BrownianSharp.AlignmentPaperJointStageOutput
import BrownianSharp.AlignmentPaperJointSupportCount

/-! Actual adaptive increments lie in the finite support-labelled family
covered by the volumetric helper. -/

noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperJointStageIncrements

open BrownianSharp.AlignmentPaperJointAdaptiveEntropy
open BrownianSharp.AlignmentPaperJointStageOutput
open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperLpJointDvp

theorem joint_stage_increment_mem_familyBallSource_of_two_radii {d n r₁ r₂ : ℕ}
    (V W : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)))
    (x : Fin (JointSampleDimension d n) → ℝ)
    (A B : Finset (Fin (JointSampleDimension d n)))
    (hAc : A.card ≤ r₁) (hBc : B.card ≤ r₂)
    (y z : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ))
    (hy : y ∈ V) (hz : z ∈ W)
    {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (herrA : ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y)‖ ≤ R₁)
    (herrB : ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z)‖ ≤ R₂) :
    ((featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y) -
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z)) ∈
      AlignmentPaperNonlinearEntropyCover.familyBallSource
        (supportPairIncrementFamily (d := d) (n := n) (r₁ := r₁) (r₂ := r₂) V W)
        (R₁ + R₂) := by
  classical
  let L₁ := SupportLabel (D := JointSampleDimension d n) (r := r₁)
  let L₂ := SupportLabel (D := JointSampleDimension d n) (r := r₂)
  let P := L₁ × L₂
  let e : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  let i := e (⟨A, hAc⟩, ⟨B, hBc⟩)
  let inc := (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y) -
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z)
  have hAimage : featureMap (d := d) (n := n)
      (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) ∈
        supportHeadImage (d := d) (n := n) A :=
    thresholdHead_feature_mem_supportHeadImage A x
  have hBimage : featureMap (d := d) (n := n)
      (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) ∈
        supportHeadImage (d := d) (n := n) B :=
    thresholdHead_feature_mem_supportHeadImage B x
  have hinc : inc ∈ labelledIncrementSubspace (d := d) (n := n) A B V W :=
    labelledIncrement_mem_of_stage_outputs A B V W x y z hy hz hAimage hBimage
  have hnorm : ‖inc‖ ≤ R₁ + R₂ := by
    dsimp [inc]
    exact AlignmentPaperJointStageOutput.jointStage_increment_norm_le x A B y z herrA herrB
  change inc ∈ AlignmentPaperNonlinearEntropyCover.familyBallSource
    (supportPairIncrementFamily (d := d) (n := n) (r₁ := r₁) (r₂ := r₂) V W) (R₁ + R₂)
  rw [AlignmentPaperNonlinearEntropyCover.familyBallSource]
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  change inc ∈ HaarQuarter.TheoremF.FiniteDimensionalCovering.submoduleBallImage
    (supportPairIncrementFamily (d := d) (n := n) (r₁ := r₁) (r₂ := r₂) V W i)
      (R₁ + R₂)
  refine ⟨⟨inc, ?_⟩, ?_, rfl⟩
  · change inc ∈ labelledIncrementSubspace (d := d) (n := n)
      (e.symm i).1.1 (e.symm i).2.1 V W
    simpa [i, e, P] using hinc
  · simpa [Metric.mem_closedBall, dist_zero_right] using hnorm

end BrownianSharp.AlignmentPaperJointStageIncrements
