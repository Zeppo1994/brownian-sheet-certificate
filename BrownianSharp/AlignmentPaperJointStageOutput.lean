import BrownianSharp.AlignmentPaperJointAdaptiveEntropy

/-! Stage outputs packaged for multiscale chaining. -/

noncomputable section
open scoped BigOperators ENNReal
set_option maxHeartbeats 5000000

namespace BrownianSharp.AlignmentPaperJointStageOutput

open BrownianSharp.AlignmentPaperJointAdaptiveEntropy
open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperLpJointDvp

/-- With the KGG space fixed before the source point, select an adaptive sparse
head and a KGG center so their sum approximates the actual feature image. -/
theorem exists_joint_stage_center {d n m : ℕ}
    {p B : ℝ} (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B)
    (s : ℕ) (hs : 1 ≤ s)
    (hslo : (m : ℝ) / (400 * (Real.log ((DictionaryDimension d n : ℝ) + 1) +
      Real.log 129 + 1)) ≤ (s : ℝ))
    (V : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)))
    (hVrank : Module.rank ℝ V ≤ (m : Cardinal))
    (happrox : ∀ z : EuclideanSpace ℝ (Fin (JointSampleDimension d n)), ‖z‖ ≤ 1 →
      ∃ y ∈ V, ‖featureMap (d := d) (n := n) z - y‖ ≤
        2 * (Real.sqrt 50 *
          (Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
            ((25 / 4 : ℝ) ^ d)) + 1) / Real.sqrt (s : ℝ)))
    (x : Fin (JointSampleDimension d n) → ℝ)
    (hx : (∑ i, |x i| ^ p) ≤ B ^ p) (hmpos : 0 < m) :
    ∃ A : Finset (Fin (JointSampleDimension d n)), A.card ≤ m ∧
      ∃ y ∈ V,
        ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y)‖ ≤
          2 * Real.sqrt 50 *
            (Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
              ((25 / 4 : ℝ) ^ d)) + 1) / Real.sqrt (s : ℝ) *
            Real.sqrt ((B / (m : ℝ) ^ (1 / p)) ^ (2 - p) * B ^ p) := by
  obtain ⟨A, hA, y, hy, herr⟩ :=
    joint_lpball_head_kgg_approximation_of_dictionary hp hp2 hB s hs hslo V hVrank
      happrox x hx hmpos
  refine ⟨A, hA, y, hy, ?_⟩
  rw [sub_add_eq_sub_sub]
  exact herr

theorem jointStage_increment_norm_le {d n : ℕ}
    (x : Fin (JointSampleDimension d n) → ℝ)
    (A B : Finset (Fin (JointSampleDimension d n)))
    (y z : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ))
    {δ₁ δ₂ : ℝ}
    (hA : ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y)‖ ≤ δ₁)
    (hB : ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z)‖ ≤ δ₂) :
    ‖(featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y) -
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z)‖ ≤
      δ₁ + δ₂ := by
  have hiden :
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y) -
        (featureMap (d := d) (n := n)
          (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z) =
        (featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z)) -
        (featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y)) := by
    abel
  rw [hiden]
  calc
    _ ≤ ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
        (featureMap (d := d) (n := n)
          (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead B x)) + z)‖ +
        ‖featureMap (d := d) (n := n) (WithLp.toLp 2 x) -
          (featureMap (d := d) (n := n)
            (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead A x)) + y)‖ :=
          norm_sub_le _ _
    _ ≤ δ₂ + δ₁ := add_le_add hB hA
    _ = δ₁ + δ₂ := by ring

end BrownianSharp.AlignmentPaperJointStageOutput
