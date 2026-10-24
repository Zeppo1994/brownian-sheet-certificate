import BrownianSharp.AlignmentIntegerFractionalApproximationLower
import BrownianSharp.AlignmentFiniteConstraintKernel
import Mathlib.Tactic

/-! Finite boundary-jet constraints for iterating the integer order-two
Riemann--Liouville inverse on sine blocks. This is the scalar algebraic part of
the higher-even-order block construction. -/

noncomputable section
open scoped BigOperators

namespace BrownianSharp.AlignmentIntegerEvenOrderJetConstraints

open BrownianSharp.AlignmentIntegerFractionalApproximationLower
open BrownianSharp.AlignmentOrdinaryIntegrationLower

/-- Coefficient rescaling by the inverse square frequency, used between
successive order-two integrations. -/
def inverseFrequencySquared (K D : ℕ) :
    (Fin D → ℝ) →ₗ[ℝ] (Fin D → ℝ) where
  toFun c i := c i / (halfFrequency (K+i.val))^2
  map_add' c e := by
    funext i
    simp [add_div]
  map_smul' a c := by
    funext i
    simp [mul_div_assoc]

/-- The first boundary jet after `j` inverse-frequency rescalings. -/
def evenOrderJetFunctional (K D : ℕ) (j : ℕ) :
    (Fin D → ℝ) →ₗ[ℝ] ℝ :=
  (sineFirstJet K D).comp ((inverseFrequencySquared K D)^j)

/-- All `m` endpoint constraints needed for `m` repeated order-two integrations.
The j-th coordinate is the first jet after `j` inverse-frequency rescalings. -/
def evenOrderJetConstraints (K D m : ℕ) :
    Fin m → (Fin D → ℝ) →ₗ[ℝ] ℝ :=
  fun j => evenOrderJetFunctional K D j.val

theorem evenOrderJetConstraints_apply (K D m : ℕ)
    (c : Fin D → ℝ) (j : Fin m) :
    evenOrderJetConstraints K D m j c =
      sineFirstJet K D (((inverseFrequencySquared K D)^j.val) c) := rfl

theorem evenOrderJetFunctional_zero (K D : ℕ) (c : Fin D → ℝ) :
    evenOrderJetFunctional K D 0 c = sineFirstJet K D c := by
  simp [evenOrderJetFunctional]

theorem evenOrderJetFunctional_succ (K D j : ℕ) (c : Fin D → ℝ) :
    evenOrderJetFunctional K D (j+1) c =
      evenOrderJetFunctional K D j (inverseFrequencySquared K D c) := by
  simp [evenOrderJetFunctional, pow_succ, LinearMap.comp_apply]

/-- Vanishing of the finite bundled constraint map is exactly vanishing of
each intermediate endpoint jet. -/
theorem evenOrderJetKernel_mem_iff (K D m : ℕ) (c : Fin D → ℝ) :
    c ∈ (BrownianSharp.AlignmentFiniteConstraintKernel.finiteConstraintMap
      (evenOrderJetConstraints K D m)).ker ↔
      ∀ j : Fin m, evenOrderJetFunctional K D j.val c = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h j
    have hj := congrFun h j
    simpa [BrownianSharp.AlignmentFiniteConstraintKernel.finiteConstraintMap,
      evenOrderJetConstraints] using hj
  · intro h
    funext j
    exact h j

/-- A coefficient vector in the common jet kernel has every intermediate
rescaled vector in the one-jet kernel required by `integerTwoL2Operator`'s
recovery theorem. -/
theorem evenOrderJetKernel_iterates_mem (K D m : ℕ)
    (c : Fin D → ℝ)
    (hc : c ∈ (BrownianSharp.AlignmentFiniteConstraintKernel.finiteConstraintMap
      (evenOrderJetConstraints K D m)).ker)
    (j : Fin m) :
    ((inverseFrequencySquared K D)^j.val) c ∈ sineJetKernel K D := by
  rw [sineJetKernel, LinearMap.mem_ker]
  have hj := (evenOrderJetKernel_mem_iff K D m c).mp hc j
  exact hj

/-- Rescaling a coefficient vector once undoes the second derivative's
frequency-squared factor. -/
theorem sineSecondSourceMap_inverseFrequencySquared (K D : ℕ)
    (c : Fin D → ℝ) :
    sineSecondSourceMap K D (inverseFrequencySquared K D c) =
      ∑ i : Fin D, c i • shiftedSineMode K i.val := by
  classical
  change (∑ i : Fin D,
      (((c i / (halfFrequency (K+i.val))^2) *
        (halfFrequency (K+i.val))^2) • shiftedSineMode K i.val)) = _
  apply Finset.sum_congr rfl
  intro i hi
  have hω : halfFrequency (K + i.val) ≠ 0 := by
    dsimp [halfFrequency]
    positivity
  congr 1
  field_simp [hω]

/-- One order-two integration advances the inverse-frequency coefficient
rescaling, whenever its boundary jet vanishes. -/
theorem integerTwoL2Operator_rescale_apply (K D : ℕ)
    (c : Fin D → ℝ) (hc : c ∈ sineJetKernel K D) :
    integerTwoL2Operator (sineSecondSourceMap K D c) =
      -sineSecondSourceMap K D (inverseFrequencySquared K D c) := by
  rw [integerTwoL2Operator_source_apply K D c hc,
    sineSecondSourceMap_inverseFrequencySquared]

/-- Iteration of the actual order-two L² operator. -/
noncomputable def integerTwoL2Iterate : ℕ →
    BrownianSharp.AlignmentFractionalL2.UnitL2 →
      BrownianSharp.AlignmentFractionalL2.UnitL2
  | 0, x => x
  | n+1, x => integerTwoL2Operator (integerTwoL2Iterate n x)

/-- The common jet kernel makes every successive order-two integration an
exact frequency rescaling on the selected sine block. -/
theorem integerTwoL2Iterate_source_apply (K D m : ℕ)
    (c : Fin D → ℝ)
    (hc : c ∈ (BrownianSharp.AlignmentFiniteConstraintKernel.finiteConstraintMap
      (evenOrderJetConstraints K D (m+1))).ker) :
    integerTwoL2Iterate m (sineSecondSourceMap K D c) =
      (-1 : ℝ)^m • sineSecondSourceMap K D (((inverseFrequencySquared K D)^m) c) := by
  induction m generalizing c with
  | zero => simp [integerTwoL2Iterate]
  | succ m ih =>
      have hall := (evenOrderJetKernel_mem_iff K D (m+2) c).mp hc
      have hsmall : c ∈ (BrownianSharp.AlignmentFiniteConstraintKernel.finiteConstraintMap
          (evenOrderJetConstraints K D (m+1))).ker := by
        exact (evenOrderJetKernel_mem_iff K D (m+1) c).mpr (fun j => hall j.castSucc)
      have hprev := ih c hsmall
      have hj : ((inverseFrequencySquared K D) ^ m) c ∈ sineJetKernel K D :=
        evenOrderJetKernel_iterates_mem K D (m+2) c hc ⟨m, by omega⟩
      rw [integerTwoL2Iterate, hprev, map_smul,
        integerTwoL2Operator_rescale_apply K D
          (((inverseFrequencySquared K D)^m) c) hj]
      have hpow : inverseFrequencySquared K D (((inverseFrequencySquared K D)^m) c) =
          ((inverseFrequencySquared K D)^(m+1)) c := by
        rw [pow_succ']
        rfl
      rw [hpow]
      simp [pow_succ, mul_comm]

/-- Each added even-order boundary condition costs at most one dimension. -/
theorem evenOrderJetKernel_finrank_lower (K D m : ℕ) :
    D-m ≤ Module.finrank ℝ
      (BrownianSharp.AlignmentFiniteConstraintKernel.finiteConstraintMap
        (evenOrderJetConstraints K D m)).ker := by
  exact BrownianSharp.AlignmentFiniteConstraintKernel.finiteConstraintKernel_finrank_lower
    (evenOrderJetConstraints K D m)

end BrownianSharp.AlignmentIntegerEvenOrderJetConstraints
