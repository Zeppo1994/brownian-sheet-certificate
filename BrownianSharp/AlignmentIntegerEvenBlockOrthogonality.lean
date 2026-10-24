import BrownianSharp.AlignmentIntegerEvenOrderJetConstraints
import BrownianSharp.AlignmentIntegerTwoUniversalSelectedFrame
import BrownianSharp.AlignmentFractionalL2
import Mathlib.Tactic

/-! Sine blocks with disjoint frequency windows are orthogonal, including
their spans. The Sigma-frame adapters globalize blockwise ON families and
blockwise orthogonal image families without dependent-profile casts. -/

noncomputable section
open scoped RealInnerProductSpace BigOperators

namespace BrownianSharp.AlignmentIntegerEvenBlockOrthogonality

open BrownianSharp
open BrownianSharp.AlignmentIntegerFractionalApproximationLower
open BrownianSharp.AlignmentIntegerEvenOrderJetConstraints
open BrownianSharp.AlignmentIntegerTwoUniversalSelectedFrame
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentOrdinaryIntegrationLower

/-- The span of the shifted sine modes in the half-open frequency block
`[K,K+D)`. -/
def sineModeBlock (K D : ℕ) : Submodule ℝ UnitL2 :=
  Submodule.span ℝ (Set.range (fun i : Fin D => shiftedSineMode K i.val))

/-- The finite weighted sine synthesis defining the order-two good-source map
always lies in its underlying sine block. -/
theorem sineSecondSourceMap_mem_sineModeBlock (K D : ℕ) (c : Fin D → ℝ) :
    sineSecondSourceMap K D c ∈ sineModeBlock K D := by
  classical
  change (∑ i : Fin D,
      (c i * (halfFrequency (K+i.val))^2) • shiftedSineMode K i.val) ∈ _
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Any two finite sine-block spans are orthogonal if their frequency windows
are disjoint and ordered. -/
theorem sineModeBlock_orthogonal {K D L E : ℕ} (hwindow : K+D ≤ L)
    {u v : UnitL2} (hu : u ∈ sineModeBlock K D)
    (hv : v ∈ sineModeBlock L E) : inner ℝ u v = 0 := by
  classical
  change u ∈ Submodule.span ℝ
      (Set.range (fun i : Fin D => shiftedSineMode K i.val)) at hu
  change v ∈ Submodule.span ℝ
      (Set.range (fun j : Fin E => shiftedSineMode L j.val)) at hv
  have hgen (i : Fin D) (j : Fin E) :
      inner ℝ (shiftedSineMode K i.val) (shiftedSineMode L j.val) = 0 := by
    have hfreq : K+i.val ≠ L+j.val := by omega
    have h := sineSource_orthonormal.inner_eq_zero hfreq
    simpa [shiftedSineMode] using h
  have hspan (i : Fin D) {w : UnitL2}
      (hw : w ∈ Submodule.span ℝ
        (Set.range (fun j : Fin E => shiftedSineMode L j.val))) :
      inner ℝ (shiftedSineMode K i.val) w = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw
    · rintro z ⟨j, rfl⟩
      exact hgen i j
    · simp
    · intro x y hx hy hpx hpy
      rw [inner_add_right, hpx, hpy]
      simp
    · intro a x hx hpx
      rw [inner_smul_right, hpx]
      simp
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
  · rintro z ⟨i, rfl⟩
    exact hspan i hv
  · simp
  · intro x y hx hy hpx hpy
    rw [inner_add_left, hpx, hpy]
    simp
  · intro a x hx hpx
    rw [inner_smul_left, hpx]
    simp

/-- The standard dyadic windows `[q·2^s,2q·2^s)` are disjoint and ordered
for every positive block-size multiplier `q`. -/
theorem dyadicBlock_window_separated (q : ℕ) {s t : ℕ} (hst : s < t) :
    q * 2^s + q * 2^s ≤ q * 2^t := by
  have hexp : s+1 ≤ t := by omega
  have hpow : 2^(s+1) ≤ 2^t :=
    Nat.pow_le_pow_right (by norm_num : 0 < 2) hexp
  calc
    q * 2^s + q * 2^s = q * (2^s + 2^s) := by ring
    _ = q * 2^(s+1) := by rw [show 2^s + 2^s = 2^s * 2 by omega, pow_succ]
    _ ≤ q * 2^t := Nat.mul_le_mul_left q hpow

/-- Every actual iterated order-two image of a jet-admissible source remains
inside the same finite sine-frequency block. -/
theorem integerTwoL2Iterate_source_mem_sineModeBlock
    (K D m : ℕ) (c : Fin D → ℝ)
    (hc : c ∈ (BrownianSharp.AlignmentFiniteConstraintKernel.finiteConstraintMap
      (evenOrderJetConstraints K D (m+1))).ker) :
    integerTwoL2Iterate m (sineSecondSourceMap K D c) ∈ sineModeBlock K D := by
  rw [integerTwoL2Iterate_source_apply K D m c hc]
  exact Submodule.smul_mem _ _ (sineSecondSourceMap_mem_sineModeBlock K D _)

/-- A blockwise selected family, globally indexed by its dyadic block depth. -/
def sigmaFrame (e : (s : ℕ) → Fin (2^s) → UnitL2) :
    SelectedIndex → UnitL2 := fun a => e a.1 a.2

/-- Blockwise orthonormal families are globally orthonormal when their source
frequency windows are ordered and disjoint. -/
theorem sigmaFrame_orthonormal
    (e : (s : ℕ) → Fin (2^s) → UnitL2)
    (K D : ℕ → ℕ)
    (he : ∀ s, Orthonormal ℝ (e s))
    (hmem : ∀ s (i : Fin (2^s)), e s i ∈ sineModeBlock (K s) (D s))
    (hsep : ∀ s t, s < t → K s + D s ≤ K t) :
    Orthonormal ℝ (sigmaFrame e) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  by_cases hab : a = b
  · subst b
    have hnorm := (he a.1).norm_eq_one a.2
    simp [sigmaFrame, real_inner_self_eq_norm_sq, hnorm]
  · rw [if_neg hab]
    rcases a with ⟨s,i⟩
    rcases b with ⟨t,j⟩
    by_cases hst : s = t
    · subst t
      have hij : i ≠ j := by
        intro h
        apply hab
        cases h
        rfl
      have h := (orthonormal_iff_ite.mp (he s) i j)
      simpa [sigmaFrame, hij] using h
    · rcases lt_or_gt_of_ne hst with hst' | hts'
      · exact sineModeBlock_orthogonal (hsep s t hst') (hmem s i) (hmem t j)
      · rw [real_inner_comm]
        exact sineModeBlock_orthogonal (hsep t s hts') (hmem t j) (hmem s i)

/-- Blockwise orthogonal image families are globally pairwise orthogonal under
the same disjoint-window hypothesis. -/
theorem sigmaFrame_images_pairwise_orthogonal
    (g : (s : ℕ) → Fin (2^s) → UnitL2)
    (K D : ℕ → ℕ)
    (hlocal : ∀ s i j, i ≠ j → inner ℝ (g s i) (g s j) = 0)
    (hmem : ∀ s (i : Fin (2^s)), g s i ∈ sineModeBlock (K s) (D s))
    (hsep : ∀ s t, s < t → K s + D s ≤ K t) :
    ∀ a b : SelectedIndex, a ≠ b →
      inner ℝ (sigmaFrame g a) (sigmaFrame g b) = 0 := by
  intro a b hab
  rcases a with ⟨s,i⟩
  rcases b with ⟨t,j⟩
  change inner ℝ (g s i) (g t j) = 0
  by_cases hst : s = t
  · subst t
    have hij : i ≠ j := by
      intro h
      apply hab
      cases h
      rfl
    exact hlocal s i j hij
  · rcases lt_or_gt_of_ne hst with hst' | hts'
    · exact sineModeBlock_orthogonal (hsep s t hst') (hmem s i) (hmem t j)
    · rw [real_inner_comm]
      exact sineModeBlock_orthogonal (hsep t s hts') (hmem t j) (hmem s i)

end BrownianSharp.AlignmentIntegerEvenBlockOrthogonality
