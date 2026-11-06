import BrownianSharp.AlignmentPaperLpJointDvp
import BrownianSharp.GaussianKGGDictionary
import BrownianSharp.AlignmentPaperKGGProbabilityBudget
import BrownianSharp.AlignmentPaperSparseHead

/-! A finite KGG dictionary for actual common-grid evaluations of the smooth
hyperbolic grade. -/

noncomputable section
open scoped BigOperators ENNReal
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000

namespace BrownianSharp.AlignmentPaperJointDictionary

open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.AlignmentPaperLpDvpBlockCover
open BrownianSharp.AlignmentPaperKGGProbabilityBudget

abbrev DictionaryDimension (d n : ℕ) :=
  Fintype.card (GradeCommonGrid d n) * 2

def outputEquivFin (d n : ℕ) :
    GradeCommonOutputIndex d n ≃ Fin (DictionaryDimension d n) :=
  gridRealIndexEquiv (gradeCommonBandwidth (d := d) (n := n))

def dictionaryRow {d n : ℕ} (i : Fin (DictionaryDimension d n)) :
    EuclideanSpace ℝ (Fin (JointSampleDimension d n)) :=
  jointGradeCommonRowVector (d := d) (n := n) ((outputEquivFin d n).symm i)

theorem dictionaryRow_norm_le {d n : ℕ}
    (i : Fin (DictionaryDimension d n)) :
    ‖dictionaryRow (d := d) (n := n) i‖ ≤
      Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
        ((25 / 4 : ℝ) ^ d)) + 1 := by
  have hC : 0 ≤ (((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
      ((25 / 4 : ℝ) ^ d) := by positivity
  have hsq : ‖dictionaryRow (d := d) (n := n) i‖ ^ 2 ≤
      (((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
        ((25 / 4 : ℝ) ^ d) := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [dictionaryRow] using
      jointGradeCommonRowVector_sq_sum_le ((outputEquivFin d n).symm i)
  have hn := norm_nonneg (dictionaryRow (d := d) (n := n) i)
  have hs := Real.sq_sqrt hC
  have hroot : 0 ≤ Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) * ((25 / 4 : ℝ) ^ d)) := Real.sqrt_nonneg _
  nlinarith

def dictionaryRows {d n : ℕ} :
    Fin (DictionaryDimension d n) →
      EuclideanSpace ℝ (Fin (JointSampleDimension d n)) :=
  dictionaryRow

noncomputable def featureMap {d n : ℕ} :
    EuclideanSpace ℝ (Fin (JointSampleDimension d n)) →L[ℝ]
      PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ) :=
  BrownianSharp.GaussianRIP.dictionaryFeatureMap (dictionaryRows (d := d) (n := n))

@[simp] theorem featureMap_apply {d n : ℕ}
    (z : EuclideanSpace ℝ (Fin (JointSampleDimension d n)))
    (i : Fin (DictionaryDimension d n)) :
    featureMap (d := d) (n := n) z i =
      jointGradeCommonGridFeatureCLM (d := d) (n := n) z
        ((outputEquivFin d n).symm i) := by
  change BrownianSharp.GaussianRIP.dictionaryFeatureMap
      (dictionaryRows (d := d) (n := n)) z i = _
  rw [BrownianSharp.GaussianRIP.dictionaryFeatureMap_apply_coord]
  simpa [dictionaryRows, dictionaryRow, outputEquivFin] using
    (jointGradeCommonGridFeature_eq_inner_row z ((outputEquivFin d n).symm i)).symm

theorem exists_joint_dictionary_subspace {d n m : ℕ}
    (hm : 400 * (Real.log ((DictionaryDimension d n : ℝ) + 1) +
      Real.log 129 + 1) ≤ (m : ℝ)) :
    ∃ s : ℕ, 1 ≤ s ∧
      (m : ℝ) / (400 * (Real.log ((DictionaryDimension d n : ℝ) + 1) +
        Real.log 129 + 1)) ≤ (s : ℝ) ∧
      ∃ V : Submodule ℝ (PiLp ∞ (fun _ : Fin (DictionaryDimension d n) => ℝ)),
        Module.rank ℝ V ≤ (m : Cardinal) ∧
        ∀ z : EuclideanSpace ℝ (Fin (JointSampleDimension d n)), ‖z‖ ≤ 1 →
          ∃ y ∈ V, ‖featureMap (d := d) (n := n) z - y‖ ≤
            2 * (Real.sqrt 50 *
              (Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
                ((25 / 4 : ℝ) ^ d)) + 1) / Real.sqrt (s : ℝ)) := by
  obtain ⟨s, hs, hslo, hbudget⟩ := exists_dictionary_budget_parameter hm
  have hR : 0 < Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
      ((25 / 4 : ℝ) ^ d)) + 1 := by positivity
  have hrow : ∀ i : Fin (DictionaryDimension d n),
      ‖dictionaryRows (d := d) (n := n) i‖ ≤
        Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
          ((25 / 4 : ℝ) ^ d)) + 1 := by
    intro i
    exact dictionaryRow_norm_le i
  have hMone : (1 : ℝ) ≤ (DictionaryDimension d n : ℝ) + 1 := by
    have hcard : 0 ≤ (DictionaryDimension d n : ℝ) := Nat.cast_nonneg _
    linarith
  have hlogM : 0 ≤ Real.log ((DictionaryDimension d n : ℝ) + 1) := Real.log_nonneg hMone
  have hmpos : 0 < (m : ℝ) := by
    have hlog129 : 0 < Real.log (129 : ℝ) := Real.log_pos (by norm_num)
    linarith
  have hmNat : 0 < m := by exact_mod_cast hmpos
  obtain ⟨V, hVrank, happrox⟩ :=
    BrownianSharp.GaussianRIP.exists_dictionary_width_subspace
      (m := m) (N := JointSampleDimension d n) (M := DictionaryDimension d n)
      (s := s) hmNat hs (dictionaryRows (d := d) (n := n))
      (Real.sqrt ((((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
        ((25 / 4 : ℝ) ^ d)) + 1) hR hrow hbudget
  refine ⟨s, hs, hslo, V, hVrank, ?_⟩
  intro z hz
  simpa [featureMap] using happrox z hz

end BrownianSharp.AlignmentPaperJointDictionary
