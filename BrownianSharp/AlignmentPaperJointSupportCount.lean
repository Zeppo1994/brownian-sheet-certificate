import BrownianSharp.AlignmentPaperJointAdaptiveEntropy
import BrownianSharp.AlignmentPaperSparseSupportCount

/-! Cardinality bounds for the adaptive sparse-support labels used by the
joint DVP entropy chain. -/

noncomputable section

namespace BrownianSharp.AlignmentPaperJointSupportCount

open BrownianSharp.AlignmentPaperJointAdaptiveEntropy

theorem supportLabel_card_eq {D r : ℕ} :
    Fintype.card (SupportLabel (D := D) (r := r)) =
      ((Finset.univ : Finset (Finset (Fin D))).filter
        (fun A => A.card ≤ r)).card := by
  classical
  let S : Finset (Finset (Fin D)) := Finset.univ.filter fun A => A.card ≤ r
  have hS : ∀ A : Finset (Fin D), A ∈ S ↔ A.card ≤ r := by
    intro A
    simp [S]
  simpa [SupportLabel] using (Fintype.card_of_subtype S hS)

theorem supportLabel_card_le_exp {D r : ℕ} (hr : 1 ≤ r) (hrD : r ≤ D) :
    (Fintype.card (SupportLabel (D := D) (r := r)) : ℝ) ≤
      Real.exp (r : ℝ) * ((D : ℝ) / (r : ℝ)) ^ r := by
  rw [supportLabel_card_eq]
  exact BrownianSharp.AlignmentPaperSparseSupportCount.sparse_support_count_le hr hrD

end BrownianSharp.AlignmentPaperJointSupportCount
