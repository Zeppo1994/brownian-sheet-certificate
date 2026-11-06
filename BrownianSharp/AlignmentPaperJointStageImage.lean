import BrownianSharp.AlignmentPaperJointStageRates

/-! Chosen adaptive stage approximants over the actual image of the finite
`ℓᵖ` ball under the common-grid DVP feature map. -/

noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperJointStageImage

open BrownianSharp.AlignmentPaperJointDictionary
open BrownianSharp.AlignmentPaperJointStageRates
open BrownianSharp.AlignmentPaperJointHeadOnly
open BrownianSharp.AlignmentPaperLpJointDvp

def jointLpFeatureImage {d n : ℕ} (p B : ℝ) :
    Set (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)) :=
  {f | ∃ x : Fin (JointSampleDimension d n) → ℝ,
    (∑ i, |x i| ^ p) ≤ B ^ p ∧
      featureMap (d := d) (n := n) (WithLp.toLp 2 x) = f}

noncomputable def sourceVector {d n : ℕ} {p B : ℝ}
    (u : {f : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) //
      f ∈ jointLpFeatureImage (d := d) (n := n) p B}) :
    Fin (JointSampleDimension d n) → ℝ :=
  Classical.choose u.property

theorem sourceVector_budget {d n : ℕ} {p B : ℝ}
    (u : {f : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) //
      f ∈ jointLpFeatureImage (d := d) (n := n) p B}) :
    (∑ i, |sourceVector u i| ^ p) ≤ B ^ p :=
  (Classical.choose_spec u.property).1

theorem sourceVector_featureMap {d n : ℕ} {p B : ℝ}
    (u : {f : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) //
      f ∈ jointLpFeatureImage (d := d) (n := n) p B}) :
    featureMap (d := d) (n := n) (WithLp.toLp 2 (sourceVector u)) = u.1 :=
  (Classical.choose_spec u.property).2

noncomputable def stageSupport {d n L : ℕ} {p B R : ℝ}
    (m : Fin L → ℕ)
    (D : ∀ j, JointStageData d n p B R (m j))
    (j : Fin L)
    (u : {f : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) //
      f ∈ jointLpFeatureImage (d := d) (n := n) p B}) :
    Finset (Fin (JointSampleDimension d n)) :=
  Classical.choose ((D j).approx (sourceVector u) (sourceVector_budget u))

theorem stageSupport_card_le {d n L : ℕ} {p B R : ℝ}
    (m : Fin L → ℕ)
    (D : ∀ j, JointStageData d n p B R (m j))
    (j : Fin L)
    (u : {f : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) //
      f ∈ jointLpFeatureImage (d := d) (n := n) p B}) :
    (stageSupport m D j u).card ≤ m j :=
  (Classical.choose_spec ((D j).approx (sourceVector u) (sourceVector_budget u))).1

noncomputable def stageOutput {d n L : ℕ} {p B R : ℝ}
    (m : Fin L → ℕ)
    (D : ∀ j, JointStageData d n p B R (m j))
    (j : Fin L)
    (u : {f : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) //
      f ∈ jointLpFeatureImage (d := d) (n := n) p B}) :
    PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) :=
  Classical.choose ((Classical.choose_spec
    ((D j).approx (sourceVector u) (sourceVector_budget u))).2)

theorem stageOutput_mem {d n L : ℕ} {p B R : ℝ}
    (m : Fin L → ℕ)
    (D : ∀ j, JointStageData d n p B R (m j))
    (j : Fin L)
    (u : {f : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) //
      f ∈ jointLpFeatureImage (d := d) (n := n) p B}) :
    stageOutput m D j u ∈ (D j).V :=
  (Classical.choose_spec (Classical.choose_spec
    ((D j).approx (sourceVector u) (sourceVector_budget u))).2).1

theorem stageOutput_error {d n L : ℕ} {p B R : ℝ}
    (m : Fin L → ℕ)
    (D : ∀ j, JointStageData d n p B R (m j))
    (j : Fin L)
    (u : {f : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) //
      f ∈ jointLpFeatureImage (d := d) (n := n) p B}) :
    ‖u.1 -
      (featureMap (d := d) (n := n)
        (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead
          (stageSupport m D j u) (sourceVector u))) + stageOutput m D j u)‖ ≤
      40 * Real.sqrt 50 * jointRowBound d n * B * Real.sqrt R *
        (m j : ℝ) ^ (-1 / p) := by
  rw [← sourceVector_featureMap u]
  exact (Classical.choose_spec (Classical.choose_spec
    ((D j).approx (sourceVector u) (sourceVector_budget u))).2).2

noncomputable def chainApproximant {d n L : ℕ} {p B R : ℝ}
    (m : Fin L → ℕ)
    (D : ∀ j, JointStageData d n p B R (m j))
    (j : Fin (L + 1))
    (u : {f : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) //
      f ∈ jointLpFeatureImage (d := d) (n := n) p B}) :
    PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) :=
  Fin.cases (0 : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)) (fun i =>
    featureMap (d := d) (n := n)
      (WithLp.toLp 2 (BrownianSharp.AlignmentPaperSparseHead.thresholdHead
        (stageSupport m D i u) (sourceVector u))) + stageOutput m D i u) j

theorem chainApproximant_start {d n L : ℕ} {p B R : ℝ}
    (m : Fin L → ℕ)
    (D : ∀ j, JointStageData d n p B R (m j))
    (u : {f : PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) //
      f ∈ jointLpFeatureImage (d := d) (n := n) p B}) :
    chainApproximant m D 0 u = 0 := by
  simp [chainApproximant]

end BrownianSharp.AlignmentPaperJointStageImage
