import BrownianSharp.AlignmentPaperJointGlobalWindow
import BrownianSharp.AlignmentPaperJointGradeCoverConcatenation

/-! A split low/high allocation is one actual finite grade-series cover. -/

noncomputable section
open scoped BigOperators ENNReal NNReal

namespace BrownianSharp.AlignmentPaperJointGlobalWindowSplit

open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperJointGlobalWindow
open BrownianSharp.AlignmentPaperJointGradeCoverConcatenation
open BrownianSharp.AlignmentPaperJointStageImage
open BrownianSharp.Torus

theorem gradeSeriesClass_entropy_le_of_split_window
    {d N W k : ℕ} {p A T : ℝ}
    (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2) (hA : 0 < A) (hT : 0 ≤ T)
    (lowC : Fin (N+1) → Set C(UnitAddTorus (Fin d),ℂ))
    (highC : Fin W → Set C(UnitAddTorus (Fin d),ℂ))
    (lowR : Fin (N+1) → ℝ≥0) (highR : Fin W → ℝ≥0)
    (lowB : Fin (N+1) → ℕ) (highB : Fin W → ℕ)
    (hLowCover : ∀ i, Metric.IsCover (lowR i)
      (decodedJointLpFeatureImage (d := d) (n := i.val) p
        (gradeSeriesSourceRadius d p A i.val)) (lowC i))
    (hHighCover : ∀ j, Metric.IsCover (highR j)
      (decodedJointLpFeatureImage (d := d) (n := N+1+j.val) p
        (gradeSeriesSourceRadius d p A (N+1+j.val))) (highC j))
    (hLowFinite : ∀ i, (lowC i).Finite)
    (hHighFinite : ∀ j, (highC j).Finite)
    (hLowCard : ∀ i, (lowC i).encard ≤ ((2^(lowB i):ℕ):ℕ∞))
    (hHighCard : ∀ j, (highC j).encard ≤ ((2^(highB j):ℕ):ℕ∞))
    (hbits : (∑ i : Fin (N+1), lowB i) +
      ∑ j : Fin W, highB j + 1 ≤ k)
    (hTail : (∑' n : ℕ, gradeSeriesNormEnvelope d p A (n+(N+1+W))) ≤ T) :
    HaarQuarter.TheoremD.entropyNumber k (GradeSeriesClass d p A) ≤
      Carl.sumRadii
        (indexedGradeCoverPieces
          (fun i : Fin (N+1+W) => decodedJointLpFeatureImage
            (d := d) (n := i.val) p (gradeSeriesSourceRadius d p A i.val))
          (concatGradeFamily lowC highC)
          (concatGradeRadius lowR highR)
          (concatGradeFamily_isCover
            (fun n => decodedJointLpFeatureImage (d := d) (n := n) p
              (gradeSeriesSourceRadius d p A n)) lowC highC lowR highR
            hLowCover hHighCover)
          (concatGradeFamily_finite lowC highC hLowFinite hHighFinite) ++
          [gradeSeriesTailPiece T hT]) := by
  let G : Fin (N+1+W) → Set C(UnitAddTorus (Fin d),ℂ) := fun i =>
    decodedJointLpFeatureImage (d := d) (n := i.val) p
      (gradeSeriesSourceRadius d p A i.val)
  let C := concatGradeFamily lowC highC
  let r := concatGradeRadius lowR highR
  let b := concatGradeBits lowB highB
  have hcover : ∀ i, Metric.IsCover (r i) (G i) (C i) := by
    simpa [G,C,r] using concatGradeFamily_isCover
      (fun n => decodedJointLpFeatureImage (d := d) (n := n) p
        (gradeSeriesSourceRadius d p A n)) lowC highC lowR highR
      hLowCover hHighCover
  have hfinite : ∀ i, (C i).Finite := by
    simpa [C] using concatGradeFamily_finite lowC highC hLowFinite hHighFinite
  have hcard : ∀ i, (C i).encard ≤ ((2^(b i):ℕ):ℕ∞) := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [C,b,concatGradeFamily,concatGradeBits] using hLowCard j
    · intro j
      simpa [C,b,concatGradeFamily,concatGradeBits] using hHighCard j
  have hbits' : (∑ i : Fin (N+1+W), b i) + 1 ≤ k := by
    rw [concatGradeBits_sum]
    omega
  simpa [G,C,r] using
    gradeSeriesClass_entropy_le_of_window_bits hd hp hp2 hA hT
      C r hcover hfinite b hcard hbits' hTail

end BrownianSharp.AlignmentPaperJointGlobalWindowSplit
