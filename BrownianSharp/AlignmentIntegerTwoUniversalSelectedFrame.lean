import BrownianSharp.AlignmentIntegerTwoSelectedBlock

/-! A single globally orthonormal source family assembled from the dyadic
selected order-two RL blocks. -/

noncomputable section
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentIntegerTwoUniversalSelectedFrame

open BrownianSharp.AlignmentIntegerTwoSelectedBlock
open BrownianSharp.AlignmentIntegerFractionalApproximationLower
open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentOrdinaryIntegrationLower

abbrev SelectedIndex := Σ s : ℕ, Fin (2^s)

def selectedSource (a : SelectedIndex) : UnitL2 :=
  selectedBlockFrame a.1 a.2

def selectedImage (a : SelectedIndex) : UnitL2 :=
  integerTwoL2Operator (selectedSource a)

theorem selectedSource_orthonormal : Orthonormal ℝ selectedSource := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  rcases a with ⟨s, i⟩
  rcases b with ⟨t, j⟩
  by_cases hst : s = t
  · subst t
    have h := orthonormal_iff_ite.mp (selectedBlockFrame_orthonormal s) i j
    simpa [selectedSource] using h
  · have hneq : (Sigma.mk s i : SelectedIndex) ≠ Sigma.mk t j := by
      intro h
      exact hst (congrArg Sigma.fst h)
    have hz := selectedBlockFrame_source_cross_orthogonal hst i j
    simpa [selectedSource, hneq] using hz

theorem selectedImage_pairwise_orthogonal :
    ∀ a b : SelectedIndex, a ≠ b → inner ℝ (selectedImage a) (selectedImage b) = 0 := by
  intro a b hab
  rcases a with ⟨s, i⟩
  rcases b with ⟨t, j⟩
  by_cases hst : s = t
  · subst t
    have hij : i ≠ j := by
      intro h
      apply hab
      cases h
      rfl
    change inner ℝ
      (integerTwoL2Operator (selectedBlockFrame s i))
      (integerTwoL2Operator (selectedBlockFrame s j)) = 0
    change inner ℝ
      (profileToL2 (integerTwoOperator (selectedBlockFrame s i)))
      (profileToL2 (integerTwoOperator (selectedBlockFrame s j))) = 0
    exact selectedBlockFrame_image_pairwise s i j hij
  · exact selectedBlockFrame_image_cross_orthogonal hst i j

theorem selectedImage_norm_lower (a : SelectedIndex) :
    ((halfFrequency (2^(a.1+2)))^2)⁻¹ ≤ ‖selectedImage a‖ := by
  exact selectedBlockFrame_image_norm_lower a.1 a.2

end BrownianSharp.AlignmentIntegerTwoUniversalSelectedFrame
