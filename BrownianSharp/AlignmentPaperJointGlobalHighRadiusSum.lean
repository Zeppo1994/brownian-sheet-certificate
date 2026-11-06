import BrownianSharp.AlignmentPaperJointHighGradeRadiusTerm
import BrownianSharp.AlignmentPaperJointHighRadiusProfileSum
import BrownianSharp.AlignmentPaperJointGlobalHighScalar
import BrownianSharp.AlignmentPaperJointGlobalRankProfile

/-! Sum the actual high-grade cover radii over the finite allocation window. -/

noncomputable section
open scoped BigOperators NNReal

namespace BrownianSharp.AlignmentPaperJointGlobalHighRadiusSum

open BrownianSharp.AlignmentPaperJointHighGradeRadiusTerm
open BrownianSharp.AlignmentPaperJointHighRadiusProfileSum
open BrownianSharp.AlignmentPaperJointGlobalRankProfile
open BrownianSharp.AlignmentPaperJointGlobalCover
open BrownianSharp.AlignmentPaperJointGlobalHighScalar

theorem exists_high_window_radius_envelope {d : ℕ} {p A : ℝ}
    (hd : 2 ≤ d) (hp1 : 1 < p) (hp2 : p < 2) (hA : 0 < A) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      (∑ j : Fin (highProfileWindow p N),
        (decodedGradeDyadicRadius d (N+1+j.val) p
          (gradeSeriesSourceRadius d p A (N+1+j.val))
          (highProfileRank d p N (j.val+1)) : ℝ)) ≤
        K*(2:ℝ)^(-(N:ℝ))*Real.sqrt (N+1:ℝ) := by
  obtain ⟨Kt,hKt,hterm⟩ := exists_high_decoded_radius_term_le_profile hd hp1 hp2 hA
  let b : ℝ := ((d:ℝ)-1)/p + 1/2
  have hb : 0 ≤ b := by
    have hp0 : 0 < p := by linarith
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast (show 1 ≤ d by omega)
    dsimp [b]
    positivity
  obtain ⟨Ks,hKs,hsum⟩ := exists_high_radius_profile_sum_bound hp1 hp2 hb
  refine ⟨Kt*Ks,mul_pos hKt hKs,?_⟩
  intro N
  let E : ℝ := (2:ℝ)^(-(N:ℝ))*Real.sqrt (N+1:ℝ)
  calc
    (∑ j : Fin (highProfileWindow p N),
        (decodedGradeDyadicRadius d (N+1+j.val) p
          (gradeSeriesSourceRadius d p A (N+1+j.val))
          (highProfileRank d p N (j.val+1)) : ℝ)) ≤
      ∑ j : Fin (highProfileWindow p N),
        Kt*E*((2:ℝ)^(-((1-1/p)*(j.val+1:ℝ))) *
          Real.exp (highProfileEta p*(j.val+1:ℝ)/p) *
          (j.val+2:ℝ)^b) := by
      apply Finset.sum_le_sum
      intro j hj
      have hjW : j.val+1 ≤ highProfileWindow p N := by omega
      have h := hterm N j.val hjW
      simpa [E, b, mul_assoc, mul_left_comm, mul_comm] using h
    _ = Kt*E * ∑ j : Fin (highProfileWindow p N),
          (2:ℝ)^(-((1-1/p)*(j.val+1:ℝ))) *
            Real.exp (highProfileEta p*(j.val+1:ℝ)/p) *
            (j.val+2:ℝ)^b := by
      rw [Finset.mul_sum]
    _ ≤ Kt*E*Ks := by
      exact mul_le_mul_of_nonneg_left (hsum (highProfileWindow p N))
        (by positivity)
    _ = Kt*Ks*(2:ℝ)^(-(N:ℝ))*Real.sqrt (N+1:ℝ) := by
      dsimp [E]
      ring

end BrownianSharp.AlignmentPaperJointGlobalHighRadiusSum
