import BrownianSharp.AlignmentPaperJointDyadicBitBudget
import BrownianSharp.AlignmentPaperJointDyadicStages
import BrownianSharp.AlignmentPaperJointAdaptiveScalarSums

/-! Summation of the actual finite-grade dyadic mesh and coding costs. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperJointDyadicSums
open BrownianSharp.AlignmentPaperJointDyadicStages
open BrownianSharp.AlignmentPaperAdaptiveDyadicRadius
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperJointDyadicBitBudget

theorem mesh_sum_le {d n J : ℕ} {p B : ℝ} (hB : 0 < B) :
    (∑ j : Fin (J+1), mesh d n J p B j) ≤
      2 * dyadicRadius (stageScale d n B) p J := by
  let E := dyadicRadius (stageScale d n B) p J
  have hE : 0 ≤ E := (dyadicRadius_pos (stageScale_pos hB) J).le
  change (∑ j : Fin (J+1), E/(2:ℝ)^(J-j.val)) ≤ 2*E
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => E/(2:ℝ)^(J-j)) (J+1)]
  have hr := Finset.sum_range_reflect (fun j : ℕ => E/(2:ℝ)^j) (J+1)
  have hr' : (∑ j ∈ Finset.range (J+1), E/(2:ℝ)^(J-j)) =
      ∑ j ∈ Finset.range (J+1), E/(2:ℝ)^j := by
    simpa only [Nat.add_sub_cancel] using hr
  rw [hr']
  have heq : (∑ j ∈ Finset.range (J+1), E/(2:ℝ)^j) = dyadicRadiusSum J E := by
    apply Finset.sum_congr rfl
    intro j hj
    simp only [div_eq_mul_inv, inv_pow, one_div, one_mul, dyadicRadiusSum]
  rw [heq]
  exact dyadicRadiusSum_le J hE

theorem jointFeature_dyadic_entropy_radius {d n J : ℕ} {p B : ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B)
    (hJD : 2^J ≤ AlignmentPaperLpJointDvp.JointSampleDimension d n) :
    HaarQuarter.TheoremD.entropyNumber ((∑ j, bits d n J j)+1)
      (AlignmentPaperJointStageImage.jointLpFeatureImage (d := d) (n := n) p B) ≤
      ENNReal.ofReal (3 * dyadicRadius (stageScale d n B) p J) := by
  apply (jointFeature_dyadic_entropy hp hp2 hB hJD).trans
  apply ENNReal.ofReal_le_ofReal
  linarith [mesh_sum_le (d := d) (n := n) (J := J) (p := p) hB]
/-- The actual joint feature image has the finite-grade entropy bound at a
rank-logarithm budget. All approximation stages and their counts are chosen
internally; the domain size is the source dimension, not the output grid. -/
theorem jointFeature_dyadic_entropy_budgeted {d n J : ℕ} {p B : ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B)
    (hJD : 2^J ≤ AlignmentPaperLpJointDvp.JointSampleDimension d n) :
    HaarQuarter.TheoremD.entropyNumber
      (Nat.ceil ((6*codingConstant+1)*(2:ℝ)^J*
        logRatio (AlignmentPaperLpJointDvp.JointSampleDimension d n) J))
      (AlignmentPaperJointStageImage.jointLpFeatureImage (d := d) (n := n) p B) ≤
      ENNReal.ofReal (3*stageScale d n B*((2:ℝ)^J)^(-1/p)) := by
  let D := AlignmentPaperLpJointDvp.JointSampleDimension d n
  let A := (6*codingConstant+1)*(2:ℝ)^J*logRatio D J
  have hL : 1 ≤ logRatio D J := logRatio_one_le hJD
  have hr : 1 ≤ (2:ℝ)^J := one_le_pow₀ (by norm_num)
  have hrL : 1 ≤ (2:ℝ)^J*logRatio D J := one_le_mul_of_one_le_of_one_le hr hL
  have hindex : (∑ j : Fin (J+1), bits d n J j)+1 ≤ Nat.ceil A := by
    have hsum := bits_sum_le hJD
    have hkreal : (((∑ j : Fin (J+1), bits d n J j)+1 : ℕ) : ℝ) ≤ A := by
      rw [Nat.cast_add, Nat.cast_one]
      dsimp [A]
      nlinarith
    exact_mod_cast hkreal.trans (Nat.le_ceil A)
  simpa only [A, D, dyadicRadius, mul_assoc] using
    (AlignmentIsometricEntropy.entropyNumber_antitone
      (AlignmentPaperJointStageImage.jointLpFeatureImage (d := d) (n := n) p B) hindex).trans
        (jointFeature_dyadic_entropy_radius hp hp2 hB hJD)
end BrownianSharp.AlignmentPaperJointDyadicSums
