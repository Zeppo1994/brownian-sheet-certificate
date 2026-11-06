import BrownianSharp.AlignmentPaperJointGlobalWindow
import BrownianSharp.AlignmentPaperJointGlobalRankProfile

/-! Fixed input-independent finite cover families for the high grade window. -/

noncomputable section
open scoped ENNReal NNReal
set_option maxHeartbeats 600000

namespace BrownianSharp.AlignmentPaperJointHighGradeCovers

open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperJointDyadicStages
open BrownianSharp.AlignmentPaperJointGlobalRankProfile
open BrownianSharp.AlignmentPaperJointStageImage
open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.Torus

theorem exists_highGrade_cover_family
    {d N W : ℕ} {p A : ℝ} (hd : 2 ≤ d) (hp : 1 < p) (hp2 : p < 2)
    (hA : 0 < A) (hW : W = highProfileWindow p N) :
    ∃ C : Fin W → Set C(UnitAddTorus (Fin d), ℂ),
      ∀ j : Fin W,
        (C j).Finite ∧
        Metric.IsCover
          (decodedGradeDyadicRadius d (N + 1 + j.val) p
            (gradeSeriesSourceRadius d p A (N + 1 + j.val))
            (highProfileRank d p N (j.val + 1)))
          (decodedJointLpFeatureImage (d := d) (n := N + 1 + j.val) p
            (gradeSeriesSourceRadius d p A (N + 1 + j.val))) (C j) ∧
        (C j).encard ≤ decodedGradeDyadicBudget d (N + 1 + j.val)
          (highProfileRank d p N (j.val + 1)) := by
  classical
  choose C hC using fun j : Fin W =>
    exists_decodedJointLpFeatureImage_dyadic_cover
      (d := d) (n := N + 1 + j.val)
      (J := highProfileRank d p N (j.val + 1))
      (p := p) (B := gradeSeriesSourceRadius d p A (N + 1 + j.val))
      hp hp2 (by
        unfold gradeSeriesSourceRadius
        positivity)
      (by
        have hj : j.val + 1 ≤ highProfileWindow p N := by
          rw [← hW]
          exact Nat.succ_le_iff.mpr j.isLt
        have hf := (highProfileRank_feasible hd hp hp2 hj).2.1
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf)
  exact ⟨C, fun j => hC j⟩

end BrownianSharp.AlignmentPaperJointHighGradeCovers
