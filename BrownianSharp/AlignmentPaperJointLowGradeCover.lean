import BrownianSharp.AlignmentPaperJointGradeRefinement
import Mathlib.Data.Nat.Log

/-! Coarse covers at the maximal admissible dyadic source rank. The coding
cost is linear in the joint source dimension; the enclosing output grid does
not enter that dimension cost. -/
noncomputable section
open scoped ENNReal NNReal
namespace BrownianSharp.AlignmentPaperJointLowGradeCover
open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperJointDyadicBitBudget
open BrownianSharp.AlignmentPaperJointDyadicStages
open BrownianSharp.AlignmentPaperLpJointDvp

def lowGradeCodingConstant : ℝ := (6*codingConstant+1)*(1+Real.log 2)

theorem lowGradeCodingConstant_pos : 0 < lowGradeCodingConstant := by
  have hc := codingConstant_pos
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<2)
  unfold lowGradeCodingConstant
  positivity

theorem maximalDyadicRank_bounds {D : ℕ} (hD : 0 < D) :
    2^(Nat.log2 D) ≤ D ∧ D < 2*2^(Nat.log2 D) := by
  constructor
  · rw [Nat.log2_eq_log_two]
    exact Nat.pow_le_of_le_log hD.ne' le_rfl
  · have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2:ℕ)) D
    simpa [← Nat.log2_eq_log_two, pow_succ, mul_comm] using h

theorem maximalDyadicRank_logRatio_le {D : ℕ} (hD : 0 < D) :
    logRatio D (Nat.log2 D) ≤ 1+Real.log 2 := by
  have hb := maximalDyadicRank_bounds hD
  have hD0 : (0:ℝ)<D := by exact_mod_cast hD
  have hhalf : (D:ℝ) ≤ 2*(2:ℝ)^(Nat.log2 D) := by exact_mod_cast hb.2.le
  have hratio : Real.exp 1*(D:ℝ)/(2:ℝ)^(Nat.log2 D) ≤ Real.exp 1*2 := by
    apply (div_le_iff₀ (by positivity : (0:ℝ)<2^(Nat.log2 D))).2
    nlinarith [mul_le_mul_of_nonneg_left hhalf (Real.exp_nonneg 1)]
  have hpos : 0 < Real.exp 1*(D:ℝ)/(2:ℝ)^(Nat.log2 D) := by positivity
  have h := Real.log_le_log hpos hratio
  simpa only [logRatio, Real.log_mul (Real.exp_ne_zero _) (by norm_num : (2:ℝ)≠0),
    Real.log_exp] using h

theorem maximalDyadicRank_coding_le {D : ℕ} (hD : 0 < D) :
    (6*codingConstant+1)*(2:ℝ)^(Nat.log2 D)*logRatio D (Nat.log2 D) ≤
      lowGradeCodingConstant*(D:ℝ) := by
  have hlog := maximalDyadicRank_logRatio_le hD
  have hrank : (2:ℝ)^(Nat.log2 D) ≤ (D:ℝ) := by
    exact_mod_cast (maximalDyadicRank_bounds hD).1
  have hc : 0 ≤ 6*codingConstant+1 := by linarith [codingConstant_pos]
  have hlog0 : 0 ≤ 1+Real.log 2 := by linarith [Real.log_pos (by norm_num : (1:ℝ)<2)]
  calc
    _ ≤ (6*codingConstant+1)*(2:ℝ)^(Nat.log2 D)*(1+Real.log 2) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ ≤ (6*codingConstant+1)*(D:ℝ)*(1+Real.log 2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrank hc) hlog0
    _ = lowGradeCodingConstant*(D:ℝ) := by unfold lowGradeCodingConstant; ring

/-- An actual finite decoded cover with at most an exponential in the true
source dimension, with all covering stages selected internally. -/
theorem exists_maximalDyadic_decodedGrade_cover {d n : ℕ} {p B : ℝ}
    (hp : 1 < p) (hp2 : p < 2) (hB : 0 < B)
    (hD : 0 < JointSampleDimension d n) :
    ∃ C : Set C(UnitAddTorus (Fin d),ℂ), C.Finite ∧
      Metric.IsCover (decodedGradeDyadicRadius d n p B
        (Nat.log2 (JointSampleDimension d n)))
        (decodedJointLpFeatureImage (d := d) (n := n) p B) C ∧
      C.encard ≤ ((2 ^ Nat.ceil
        (lowGradeCodingConstant*(JointSampleDimension d n:ℝ)) : ℕ) : ℕ∞) := by
  obtain ⟨C,hC,hcover,hcard⟩ := exists_decodedJointLpFeatureImage_dyadic_cover
    hp hp2 hB (maximalDyadicRank_bounds hD).1
  refine ⟨C,hC,hcover,hcard.trans ?_⟩
  apply ENat.coe_le_coe.mpr
  apply Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ))
  exact (Nat.sub_le _ 1).trans (Nat.ceil_mono (maximalDyadicRank_coding_le hD))

/-- The maximal-rank radius is within a fixed factor of the sharp full-rank
radius, uniformly over every grade. -/
theorem maximalDyadic_decodedGrade_radius_le {d n : ℕ} {p B : ℝ}
    (hp : 1 < p) (hB : 0 < B) (hD : 0 < JointSampleDimension d n) :
    (decodedGradeDyadicRadius d n p B (Nat.log2 (JointSampleDimension d n)) : ℝ) ≤
      (24*(5:ℝ)^d) * (2:ℝ)^(1/p) * stageScale d n B *
        (JointSampleDimension d n:ℝ)^(-1/p) := by
  let D := JointSampleDimension d n
  have hp0 : 0 < p := by linarith
  have hDreal : (0:ℝ)<D := by exact_mod_cast hD
  have hhalf : (D:ℝ)/2 ≤ (2:ℝ)^(Nat.log2 D) := by
    have h := (maximalDyadicRank_bounds hD).2.le
    have hr : (D:ℝ) ≤ 2*(2:ℝ)^(Nat.log2 D) := by exact_mod_cast h
    linarith
  have hnegative : -1/p ≤ (0:ℝ) :=
    div_nonpos_of_nonpos_of_nonneg (by norm_num : (-1:ℝ) ≤ 0) hp0.le
  have hpow := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ)<(D:ℝ)/2)
    hhalf hnegative
  have hfactor : ((D:ℝ)/2)^(-1/p) = (2:ℝ)^(1/p)*(D:ℝ)^(-1/p) := by
    rw [Real.div_rpow hDreal.le (by norm_num : (0:ℝ)≤2), div_eq_mul_inv,
      ← Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
    have he : -(-1/p) = 1/p := by ring
    rw [he, mul_comm]
  rw [hfactor] at hpow
  have hs : 0 < stageScale d n B := stageScale_pos hB
  have hradius :
      (decodedGradeDyadicRadius d n p B (Nat.log2 D) : ℝ) =
        (24*(5:ℝ)^d)*stageScale d n B*((2:ℝ)^(Nat.log2 D))^(-1/p) := by
    change ((NNReal.mk (2*(5:ℝ)^d) (by positivity) *
      (2 * Real.toNNReal (2*(3*stageScale d n B*
        ((2:ℝ)^(Nat.log2 D))^(-1/p)))) : ℝ≥0) : ℝ) = _
    rw [NNReal.coe_mul, NNReal.coe_mul,
      Real.coe_toNNReal _ (by positivity)]
    norm_num
    ring
  rw [hradius]
  nlinarith [mul_le_mul_of_nonneg_left hpow
    (by positivity : 0 ≤ (24*(5:ℝ)^d)*stageScale d n B)]

end BrownianSharp.AlignmentPaperJointLowGradeCover
