import BrownianSharp.AlignmentIntegerTwoHomogeneousLower
import BrownianSharp.AlignmentFiniteOrthogonalImageSubframe
import Mathlib.Tactic

/-! Selected orthogonal-image frames in the common-jet sine block for an
arbitrary number of order-two iterations. -/

noncomputable section

namespace BrownianSharp.AlignmentIntegerEvenOrderSelectedFrame

open BrownianSharp.AlignmentIntegerFractionalApproximationLower
open BrownianSharp.AlignmentIntegerEvenOrderJetConstraints
open BrownianSharp.AlignmentFiniteConstraintKernel
open BrownianSharp.AlignmentIntegerTwoHomogeneousLower
open BrownianSharp.AlignmentFiniteOrthogonalImageSubframe
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentOrdinaryIntegrationLower

def evenOrderGoodSource (K D m : ℕ) : Submodule ℝ UnitL2 :=
  LinearMap.range ((sineSecondSourceMap K D).comp
    (finiteConstraintMap (evenOrderJetConstraints K D m)).ker.subtype)

theorem evenOrderGoodSource_finrank_lower (K D m : ℕ) :
    D-m ≤ Module.finrank ℝ (evenOrderGoodSource K D m) := by
  classical
  let f := (sineSecondSourceMap K D).comp
    (finiteConstraintMap (evenOrderJetConstraints K D m)).ker.subtype
  have hinj : Function.Injective f := by
    intro c e h
    apply Subtype.ext
    have hz : sineSecondSourceMap K D (c.val-e.val) = 0 := by
      rw [map_sub]
      change f c-f e=0
      rw [h, sub_self]
    exact sub_eq_zero.mp ((sineSecondSourceMap_eq_zero_iff K D (c.val-e.val)).1 hz)
  have hrange := LinearMap.finrank_range_of_inj hinj
  have hker := finiteConstraintKernel_finrank_lower
    (evenOrderJetConstraints K D m)
  change D-m ≤ Module.finrank ℝ (LinearMap.range f)
  exact hker.trans_eq hrange.symm

noncomputable def integerTwoL2IterateCLM : ℕ → UnitL2 →L[ℝ] UnitL2
  | 0 => ContinuousLinearMap.id ℝ UnitL2
  | n+1 => integerTwoL2Operator.comp (integerTwoL2IterateCLM n)

theorem integerTwoL2IterateCLM_apply (m : ℕ) (x : UnitL2) :
    integerTwoL2IterateCLM m x = integerTwoL2Iterate m x := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp [integerTwoL2IterateCLM, integerTwoL2Iterate, ih]

/-- The common m-jet block contains a `2^s`-dimensional subspace on which the
m-fold order-two operator has a uniform lower bound. Diagonalizing its output
Gram matrix gives an orthonormal family with pairwise orthogonal images. -/
theorem exists_evenOrder_selected_frame
    (m s : ℕ) (hm : 1 ≤ m) :
    let D := (m+2)*2^s
    let K := D
    ∃ e : Fin (2^s) → evenOrderGoodSource K D (m+1),
      Orthonormal ℝ (fun i => (e i : UnitL2)) ∧
      (∀ i j, i ≠ j →
        inner ℝ (integerTwoL2Iterate m (e i : UnitL2))
          (integerTwoL2Iterate m (e j : UnitL2)) = 0) ∧
      ∀ i, ((halfFrequency (K+D))^2)⁻¹^m ≤
        ‖integerTwoL2Iterate m (e i : UnitL2)‖ := by
  classical
  dsimp
  let D : ℕ := (m+2)*2^s
  let K : ℕ := D
  have hpow : 1 ≤ 2^s := Nat.one_le_pow s 2 (by omega)
  have hmul : m+1 ≤ (m+1)*2^s := by
    simpa using Nat.mul_le_mul_left (m+1) hpow
  have hdecomp : (m+2)*2^s = (m+1)*2^s + 2^s := by
    rw [show m+2=(m+1)+1 by omega, Nat.add_mul, one_mul]
  have hdimker : 2^s ≤ D-(m+1) := by
    have hDlarge : m+1+2^s ≤ D := by
      dsimp [D]
      rw [hdecomp]
      exact Nat.add_le_add_right hmul (2^s)
    omega
  have hfiniteKernel : FiniteDimensional ℝ
      (finiteConstraintMap (evenOrderJetConstraints K D (m+1))).ker := inferInstance
  let V := evenOrderGoodSource K D (m+1)
  haveI : FiniteDimensional ℝ V :=
    Module.Finite.range ((sineSecondSourceMap K D).comp
      (finiteConstraintMap (evenOrderJetConstraints K D (m+1))).ker.subtype)
  letI : FiniteDimensional ℝ V := inferInstance
  let T' : V →L[ℝ] UnitL2 := (integerTwoL2IterateCLM m).comp V.subtypeL
  have hdim : 2^s ≤ Module.finrank ℝ V := by
    exact hdimker.trans (evenOrderGoodSource_finrank_lower K D (m+1))
  have hσ : 0 ≤ ((halfFrequency (K+D))^2)⁻¹ ^ m := by positivity
  have hlower : ∀ x : V, ‖x‖ = 1 →
      ((halfFrequency (K+D))^2)⁻¹^m ≤ ‖T' x‖ := by
    intro x hx
    have hxrange : (x : UnitL2) ∈ LinearMap.range
        ((sineSecondSourceMap K D).comp
          (finiteConstraintMap (evenOrderJetConstraints K D (m+1))).ker.subtype) := x.property
    obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hxrange
    have hcsource : sineSecondSourceMap K D c.val = (x : UnitL2) := by
      simpa [Function.comp_def, LinearMap.comp_apply] using hc
    have hall := (evenOrderJetKernel_mem_iff K D (m+1) c.val).mp c.property
    have hcommon : c.val ∈
        (finiteConstraintMap (evenOrderJetConstraints K D m)).ker :=
      (evenOrderJetKernel_mem_iff K D m c.val).mpr (fun j => hall j.castSucc)
    have hbound := integerTwoL2Iterate_homogeneous_lower_of_common_jet
      K D m (by dsimp [D]; positivity) c.val hcommon
    rw [hcsource, ← integerTwoL2IterateCLM_apply] at hbound
    have hxval : ‖(x : UnitL2)‖ = 1 := by exact hx
    change ((halfFrequency (K+D))^2)⁻¹^m * ‖(x : UnitL2)‖ ≤
      ‖integerTwoL2IterateCLM m (x : UnitL2)‖ at hbound
    rw [hxval] at hbound
    simpa [T', ContinuousLinearMap.comp_apply] using hbound
  obtain ⟨e, heorth, hepair, henorm⟩ :=
    exists_orthogonal_image_subframe T' hdim (((halfFrequency (K+D))^2)⁻¹^m) hlower
  refine ⟨e, ?_, ?_, ?_⟩
  · exact heorth
  · intro i j hij
    have h := hepair i j hij
    change inner ℝ (integerTwoL2IterateCLM m (e i : UnitL2))
      (integerTwoL2IterateCLM m (e j : UnitL2)) = 0 at h
    simpa only [integerTwoL2IterateCLM_apply] using h
  · intro i
    have h := henorm i
    change ((halfFrequency (K+D))^2)⁻¹^m ≤
      ‖integerTwoL2IterateCLM m (e i : UnitL2)‖ at h
    simpa only [integerTwoL2IterateCLM_apply] using h

end BrownianSharp.AlignmentIntegerEvenOrderSelectedFrame
