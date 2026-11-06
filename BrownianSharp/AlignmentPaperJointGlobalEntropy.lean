import BrownianSharp.AlignmentPaperJointGlobalWindowSplit
import BrownianSharp.AlignmentPaperJointGlobalHighRadiusSum
import BrownianSharp.AlignmentPaperJointGlobalTailRadius
import BrownianSharp.AlignmentPaperJointLowGradeRefinedFamily
import BrownianSharp.AlignmentPaperJointLowGradeCostSum
import BrownianSharp.AlignmentPaperJointLowGradeRadiusSum
import BrownianSharp.AlignmentPaperJointHighGradeCovers
import BrownianSharp.AlignmentPaperJointHighGradeCostSum
import BrownianSharp.AlignmentPaperJointGradeEntropyInversion

/-! Actual global entropy upper bound for the decoded grade-series class. -/

noncomputable section
open scoped BigOperators ENNReal NNReal

namespace BrownianSharp.AlignmentPaperJointGlobalEntropy

set_option maxHeartbeats 1000000

open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperJointGlobalWindowSplit
open BrownianSharp.AlignmentPaperJointGlobalHighRadiusSum
open BrownianSharp.AlignmentPaperJointGlobalTailRadius
open BrownianSharp.AlignmentPaperJointLowGradeRefinedFamily
open BrownianSharp.AlignmentPaperJointLowGradeCostSum
open BrownianSharp.AlignmentPaperJointLowGradeRadiusSum
open BrownianSharp.AlignmentPaperJointHighGradeCovers
open BrownianSharp.AlignmentPaperJointHighGradeCostSum
open BrownianSharp.AlignmentPaperJointDyadicBitBudget
open BrownianSharp.AlignmentPaperJointGradeCoverConcatenation
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperJointGlobalWindow
open BrownianSharp.AlignmentPaperJointGradeEntropyInversion
open BrownianSharp.AlignmentPaperJointGlobalRankProfile
open BrownianSharp.AlignmentPaperJointStageImage
open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.Torus

theorem gradeSeriesClass_entropy_stage_bound {d : ℕ} {p A : ℝ}
    (hd : 2 ≤ d) (hp1 : 1 < p) (hp2 : p < 2) (hA : 0 < A) :
    ∃ Cbudget Cerror : ℝ, 0 < Cbudget ∧ 0 < Cerror ∧
      ∀ N : ℕ,
        HaarQuarter.TheoremD.entropyNumber (stageEntropyIndex Cbudget d N)
          (GradeSeriesClass d p A) ≤
          ENNReal.ofReal (Cerror*(2:ℝ)^(-(N:ℝ))*Real.sqrt (N+1:ℝ)) := by
  obtain ⟨Cbit,hCbit,hLowFamily⟩ :=
    exists_lowGrade_refined_cover_family hd hp1 hp2 hA
  obtain ⟨Ctail,hCtail,hTailRadius⟩ :=
    exists_windowTail_radius_envelope hd hp1 hp2 hA
  obtain ⟨ChighRad,hChighRad,hHighRadius⟩ :=
    exists_high_window_radius_envelope hd hp1 hp2 hA
  obtain ⟨ChighBits,hChighBits,hHighCount⟩ :=
    highProfile_count_cost_sum_le hd hp1 hp2
  let ClowBits : ℝ := Cbit *
      (4*(2:ℝ)^(3*d+1) / ((2:ℝ)^(3*d+1)/(Nat.factorial (d-1):ℝ))) + 1
  let Cbudget : ℝ := ClowBits + ChighBits + 1
  let Cerror : ℝ := 2 + ChighRad + Ctail
  have hClow : 0 < ClowBits := by
    dsimp [ClowBits]
    positivity
  have hCb : 0 < Cbudget := by dsimp [Cbudget]; positivity
  have hCe : 0 < Cerror := by dsimp [Cerror]; positivity
  refine ⟨Cbudget,Cerror,hCb,hCe,?_⟩
  intro N
  let W : ℕ := highProfileWindow p N
  let E : ℝ := (2:ℝ)^(-(N:ℝ))*Real.sqrt (N+1:ℝ)
  obtain ⟨lowC,hLow⟩ := hLowFamily N
  obtain ⟨highC,hHigh⟩ := exists_highGrade_cover_family hd hp1 hp2 hA (by rfl)
  let lowR : Fin (N+1) → ℝ≥0 := fun i =>
    ⟨lowTargetRadius N i.val, (lowTargetRadius_pos N i.val).le⟩
  let highR : Fin W → ℝ≥0 := fun j =>
    decodedGradeDyadicRadius d (N+1+j.val) p
      (gradeSeriesSourceRadius d p A (N+1+j.val))
      (highProfileRank d p N (j.val+1))
  let lowB : Fin (N+1) → ℕ := fun i =>
    Nat.ceil (Cbit*(JointSampleDimension d i.val:ℝ)*((N-i.val:ℕ)+1:ℝ))
  let highB : Fin W → ℕ := fun j =>
    Nat.ceil ((6*codingConstant+1) *
      (2:ℝ)^highProfileRank d p N (j.val+1) *
      logRatio (JointSampleDimension d (N+1+j.val))
        (highProfileRank d p N (j.val+1)))
  have hLowCover : ∀ i, Metric.IsCover (lowR i)
      (decodedJointLpFeatureImage (d := d) (n := i.val) p
        (gradeSeriesSourceRadius d p A i.val)) (lowC i) := by
    intro i
    change Metric.IsCover (lowR i) _ _
    exact (hLow i).2.1
  have hHighCover : ∀ j, Metric.IsCover (highR j)
      (decodedJointLpFeatureImage (d := d) (n := N+1+j.val) p
        (gradeSeriesSourceRadius d p A (N+1+j.val))) (highC j) := by
    intro j
    simpa [highR] using (hHigh j).2.1
  have hLowFinite : ∀ i, (lowC i).Finite := fun i => (hLow i).1
  have hHighFinite : ∀ j, (highC j).Finite := fun j => (hHigh j).1
  have hLowCard : ∀ i, (lowC i).encard ≤ ((2^(lowB i):ℕ):ℕ∞) := by
    intro i
    simpa [lowB] using (hLow i).2.2
  have hHighCard : ∀ j, (highC j).encard ≤ ((2^(highB j):ℕ):ℕ∞) := by
    intro j
    have hcard := (hHigh j).2.2
    change (highC j).encard ≤ ((2^(highB j - 1:ℕ):ℕ):ℕ∞) at hcard
    exact hcard.trans (by
      exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ))
        (Nat.sub_le (highB j) 1)))
  have hLowBits : (∑ i : Fin (N+1), (lowB i:ℝ)) ≤
      ClowBits*(JointSampleDimension d N:ℝ) := by
    have hsum := joint_low_grade_ceil_bit_sum_le (d:=d) (N:=N)
      (by omega : 1≤d) Cbit hCbit.le
    have hfin : (∑ i : Fin (N+1), (lowB i:ℝ)) =
        ∑ n ∈ Finset.range (N+1),
          (Nat.ceil (Cbit*(JointSampleDimension d n:ℝ)*(((N-n:ℕ):ℝ)+1):ℝ):ℝ) := by
      change (∑ i : Fin (N+1),
        (Nat.ceil (Cbit*(JointSampleDimension d i.val:ℝ)*
          ((N-i.val:ℕ)+1:ℝ):ℝ):ℝ)) = _
      rw [Fin.sum_univ_eq_sum_range (fun n : ℕ =>
        (Nat.ceil (Cbit*(JointSampleDimension d n:ℝ)*(((N-n:ℕ):ℝ)+1):ℝ):ℝ))]
    rw [hfin]
    simpa only [ClowBits] using hsum
  have hHighBits : (∑ j : Fin W, (highB j:ℝ)) ≤
      ChighBits*(JointSampleDimension d N:ℝ) := by
    change (∑ j : Fin (highProfileWindow p N),
      (Nat.ceil ((6*codingConstant+1) *
        (2:ℝ)^highProfileRank d p N (j.val+1) *
        logRatio (JointSampleDimension d (N+1+j.val))
          (highProfileRank d p N (j.val+1)):ℝ):ℝ)) ≤ _
    exact hHighCount N
  have hdim1 : 1 ≤ (JointSampleDimension d N:ℝ) := by
    have hgrade := joint_low_grade_dimension_cost_le (d:=d) (N:=N)
      (by omega : 1≤d)
    have hcount := grade_count_le_joint_dimension (d:=d) (N:=N)
      (by omega : 1≤d)
    nlinarith
  have hbitsReal :
      (((∑ i : Fin (N+1), lowB i) + ∑ j : Fin W, highB j + 1 : ℕ) : ℝ) ≤
        Cbudget*(JointSampleDimension d N:ℝ) := by
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, Nat.cast_sum, Nat.cast_sum]
    dsimp [Cbudget]
    nlinarith [hLowBits,hHighBits,hdim1]
  have hbits :
      (∑ i : Fin (N+1), lowB i) + ∑ j : Fin W, highB j + 1 ≤
        stageEntropyIndex Cbudget d N := by
    have hceil :
        (((∑ i : Fin (N+1), lowB i) + ∑ j : Fin W, highB j + 1 : ℕ) : ℝ) ≤
          (Nat.ceil (Cbudget*(JointSampleDimension d N:ℝ)):ℕ):= by
      exact hbitsReal.trans (Nat.le_ceil _)
    have hn :
        (∑ i : Fin (N+1), lowB i) + ∑ j : Fin W, highB j + 1 ≤
          Nat.ceil (Cbudget*(JointSampleDimension d N:ℝ)) := by exact_mod_cast hceil
    unfold stageEntropyIndex
    omega
  let T : ℝ := Ctail*E
  have hT : 0 ≤ T := by dsimp [T,E]; positivity
  have hTail : (∑' n : ℕ, gradeSeriesNormEnvelope d p A (n+(N+1+W))) ≤ T := by
    simpa [T,E,W, mul_assoc] using hTailRadius N
  have hsplit := gradeSeriesClass_entropy_le_of_split_window
    hd hp1 hp2 hA hT lowC highC lowR highR lowB highB
    hLowCover hHighCover hLowFinite hHighFinite hLowCard hHighCard hbits hTail
  let pieces := indexedGradeCoverPieces
    (fun i : Fin (N+1+W) => decodedJointLpFeatureImage (d:=d) (n:=i.val) p
      (gradeSeriesSourceRadius d p A i.val))
    (concatGradeFamily lowC highC) (concatGradeRadius lowR highR)
    (concatGradeFamily_isCover
      (fun n => decodedJointLpFeatureImage (d:=d) (n:=n) p
        (gradeSeriesSourceRadius d p A n)) lowC highC lowR highR
      hLowCover hHighCover)
    (concatGradeFamily_finite lowC highC hLowFinite hHighFinite) ++
    [gradeSeriesTailPiece T hT]
  have hlowrad : (∑ i : Fin (N+1), (lowR i:ℝ)) ≤ 2*E := by
    change (∑ i : Fin (N+1), lowTargetRadius N i.val) ≤ 2*E
    simpa [E, lowTargetRadius, mul_assoc] using low_target_radius_sum_le N
  have hhighrad : (∑ j : Fin W, (highR j:ℝ)) ≤ ChighRad*E := by
    simpa [highR,W,E, mul_assoc] using hHighRadius N
  have hsumrad : (Carl.sumRadii pieces : ℝ) ≤ Cerror*E := by
    have hsumid : (Carl.sumRadii pieces : ℝ) =
        (∑ i : Fin (N+1), (lowR i:ℝ)) +
          (∑ j : Fin W, (highR j:ℝ)) + T := by
      rw [Carl.sumRadii_eq_list_sum]
      simp [pieces, indexedGradeCoverPieces, List.map_append, List.sum_append,
        List.map_ofFn, List.sum_ofFn, List.map_singleton, List.sum_singleton,
        concatGradeRadius_sum, NNReal.coe_add, NNReal.coe_sum, gradeSeriesTailPiece,
        Real.coe_toNNReal, hT]
    rw [hsumid]
    dsimp [Cerror,T,E]
    nlinarith [hlowrad,hhighrad]
  have hradENN : (Carl.sumRadii pieces : ℝ≥0∞) ≤ ENNReal.ofReal (Cerror*E) := by
    have h := ENNReal.ofReal_le_ofReal hsumrad
    simpa only [ENNReal.ofReal_coe_nnreal] using h
  have hradENN' : (Carl.sumRadii pieces : ℝ≥0∞) ≤
      ENNReal.ofReal (Cerror*(2:ℝ)^(-(N:ℝ))*Real.sqrt (N+1:ℝ)) := by
    simpa [E, mul_assoc] using hradENN
  exact hsplit.trans (by simpa only [pieces] using hradENN')

theorem gradeSeriesClass_entropy_upper {d : ℕ} {p A : ℝ}
    (hd : 2 ≤ d) (hp1 : 1 < p) (hp2 : p < 2) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      HaarQuarter.TheoremD.entropyNumber k (GradeSeriesClass d p A) ≤
        ENNReal.ofReal (C*(k:ℝ)⁻¹*Real.rpow (Real.log (k:ℝ)) ((d:ℝ)-1/2)) := by
  obtain ⟨Cbudget,Cerror,hCb,hCe,hstage⟩ :=
    gradeSeriesClass_entropy_stage_bound hd hp1 hp2 hA
  exact eventually_entropy_powerlog_of_joint_stage_bounds hd
    (GradeSeriesClass d p A) hCb hCe 0 (fun N _ => by
      simpa only [Nat.cast_add, Nat.cast_one] using hstage N)

end BrownianSharp.AlignmentPaperJointGlobalEntropy
