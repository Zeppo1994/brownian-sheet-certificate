import BrownianSharp.AlignmentIntegerEvenOrderSelectedFrame
import BrownianSharp.AlignmentIntegerEvenBlockOrthogonality
import Mathlib.Tactic

/-! A global Sigma-indexed source frame for the iterated integer-order RL
operators.  Local frames come from the finite-dimensional Gram diagonalization;
the sine-block adapter makes both the sources and their images orthogonal
across dyadic blocks. -/

noncomputable section
open scoped RealInnerProductSpace BigOperators

namespace BrownianSharp.AlignmentIntegerEvenOrderUniversalFrame

open BrownianSharp.AlignmentIntegerFractionalApproximationLower
open BrownianSharp.AlignmentIntegerEvenOrderSelectedFrame
open BrownianSharp.AlignmentIntegerEvenOrderJetConstraints
open BrownianSharp.AlignmentFiniteConstraintKernel
open BrownianSharp.AlignmentIntegerEvenBlockOrthogonality
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentOrdinaryIntegrationLower
open BrownianSharp.AlignmentIntegerTwoUniversalSelectedFrame

abbrev EvenOrderSelectedIndex := SelectedIndex

def evenOrderBlockSize (m s : ℕ) : ℕ := (m+2)*2^s

noncomputable def localEvenOrderFrameSub (m : ℕ) (hm : 1 ≤ m) (s : ℕ) :
    Fin (2^s) → evenOrderGoodSource (evenOrderBlockSize m s) (evenOrderBlockSize m s) (m+1) :=
  Classical.choose (exists_evenOrder_selected_frame m s hm)

noncomputable def localEvenOrderFrame (m : ℕ) (hm : 1 ≤ m) (s : ℕ) :
    Fin (2^s) → UnitL2 := fun i => (localEvenOrderFrameSub m hm s i : UnitL2)

private theorem localEvenOrderFrame_orthonormal (m : ℕ) (hm : 1 ≤ m) (s : ℕ) :
    Orthonormal ℝ (localEvenOrderFrame m hm s) := by
  have h := Classical.choose_spec (exists_evenOrder_selected_frame m s hm)
  rcases h with ⟨horth, hrest⟩
  exact horth

private theorem localEvenOrderFrame_image_orthogonal
    (m : ℕ) (hm : 1 ≤ m) (s : ℕ) :
    ∀ i j, i ≠ j →
      inner ℝ (integerTwoL2Iterate m (localEvenOrderFrame m hm s i))
        (integerTwoL2Iterate m (localEvenOrderFrame m hm s j)) = 0 := by
  have h := Classical.choose_spec (exists_evenOrder_selected_frame m s hm)
  rcases h with ⟨horth, hrest⟩
  rcases hrest with ⟨hpair, hnorm⟩
  exact hpair

private theorem localEvenOrderFrame_norm_lower
    (m : ℕ) (hm : 1 ≤ m) (s : ℕ) (i : Fin (2^s)) :
    ((halfFrequency (evenOrderBlockSize m s + evenOrderBlockSize m s))^2)⁻¹^m ≤
      ‖integerTwoL2Iterate m (localEvenOrderFrame m hm s i)‖ := by
  have h := Classical.choose_spec (exists_evenOrder_selected_frame m s hm)
  rcases h with ⟨horth, hrest⟩
  rcases hrest with ⟨hpair, hnorm⟩
  simpa [evenOrderBlockSize, localEvenOrderFrame, localEvenOrderFrameSub] using hnorm i

private theorem localEvenOrderFrame_source_mem_block
    (m : ℕ) (hm : 1 ≤ m) (s : ℕ) (i : Fin (2^s)) :
    localEvenOrderFrame m hm s i ∈ sineModeBlock (evenOrderBlockSize m s) (evenOrderBlockSize m s) := by
  classical
  let K := evenOrderBlockSize m s
  let D := evenOrderBlockSize m s
  have hsource := (localEvenOrderFrameSub m hm s i).property
  change (localEvenOrderFrame m hm s i : UnitL2) ∈
    LinearMap.range ((sineSecondSourceMap K D).comp
      (finiteConstraintMap (evenOrderJetConstraints K D (m+1))).ker.subtype) at hsource
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hsource
  have hcsource : sineSecondSourceMap K D c.val = localEvenOrderFrame m hm s i := by
    simpa [Function.comp_def, LinearMap.comp_apply] using hc
  change (localEvenOrderFrame m hm s i : UnitL2) ∈ sineModeBlock K D
  rw [← hcsource]
  exact sineSecondSourceMap_mem_sineModeBlock K D c.val

private theorem localEvenOrderFrame_image_mem_block
    (m : ℕ) (hm : 1 ≤ m) (s : ℕ) (i : Fin (2^s)) :
    integerTwoL2Iterate m (localEvenOrderFrame m hm s i) ∈
      sineModeBlock (evenOrderBlockSize m s) (evenOrderBlockSize m s) := by
  classical
  let K := evenOrderBlockSize m s
  let D := evenOrderBlockSize m s
  have hsource := (localEvenOrderFrameSub m hm s i).property
  change (localEvenOrderFrame m hm s i : UnitL2) ∈
    LinearMap.range ((sineSecondSourceMap K D).comp
      (finiteConstraintMap (evenOrderJetConstraints K D (m+1))).ker.subtype) at hsource
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hsource
  have hcsource : sineSecondSourceMap K D c.val = localEvenOrderFrame m hm s i := by
    simpa [Function.comp_def, LinearMap.comp_apply] using hc
  change integerTwoL2Iterate m (localEvenOrderFrame m hm s i) ∈ sineModeBlock K D
  rw [← hcsource]
  exact integerTwoL2Iterate_source_mem_sineModeBlock K D m c.val c.property

private theorem evenOrderBlockSize_separated (m : ℕ) {s t : ℕ} (hst : s < t) :
    evenOrderBlockSize m s + evenOrderBlockSize m s ≤ evenOrderBlockSize m t := by
  simpa [evenOrderBlockSize, two_mul, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using
    (dyadicBlock_window_separated (m+2) hst)

/-- A globally orthonormal Sigma-indexed source family whose m-fold RL images
are mutually orthogonal.  This is the reusable all-even-orders scalar frame
input for tensor LayerIndex arguments. -/
theorem exists_evenOrder_universal_sigma_frame (m : ℕ) (hm : 1 ≤ m) :
    ∃ e : EvenOrderSelectedIndex → UnitL2,
      Orthonormal ℝ e ∧
      (∀ a b, a ≠ b →
        inner ℝ (integerTwoL2Iterate m (e a))
          (integerTwoL2Iterate m (e b)) = 0) ∧
      ∀ a, ((halfFrequency (evenOrderBlockSize m a.1 + evenOrderBlockSize m a.1))^2)⁻¹^m ≤
        ‖integerTwoL2Iterate m (e a)‖ := by
  classical
  let e : (s : ℕ) → Fin (2^s) → UnitL2 := localEvenOrderFrame m hm
  have hsource := sigmaFrame_orthonormal e (evenOrderBlockSize m) (evenOrderBlockSize m)
    (localEvenOrderFrame_orthonormal m hm)
    (localEvenOrderFrame_source_mem_block m hm)
    (by intro s t hst; exact evenOrderBlockSize_separated m hst)
  have himage := sigmaFrame_images_pairwise_orthogonal
    (fun s i => integerTwoL2Iterate m (e s i))
    (evenOrderBlockSize m) (evenOrderBlockSize m)
    (by
      intro s i j hij
      exact localEvenOrderFrame_image_orthogonal m hm s i j hij)
    (localEvenOrderFrame_image_mem_block m hm)
    (by intro s t hst; exact evenOrderBlockSize_separated m hst)
  refine ⟨sigmaFrame e, hsource, ?_, ?_⟩
  · intro a b hab
    exact himage a b hab
  · intro a
    exact localEvenOrderFrame_norm_lower m hm a.1 a.2

end BrownianSharp.AlignmentIntegerEvenOrderUniversalFrame
