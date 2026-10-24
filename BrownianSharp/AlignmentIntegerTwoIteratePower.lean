import BrownianSharp.AlignmentFractionalIntegerSemigroup
import BrownianSharp.AlignmentIntegerEvenOrderJetConstraints
import BrownianSharp.AlignmentIntegerFractionalApproximationLower
import Mathlib.Tactic

/-! Connect the recursive order-two action used by the jet construction to the
actual bounded-operator power of the scalar R₂ L² map. This adapter deliberately
imports only the jet-constraint layer, avoiding the selected-frame module. -/

noncomputable section

namespace BrownianSharp.AlignmentIntegerTwoIteratePower

open BrownianSharp.AlignmentFractionalIntegerSemigroup
open BrownianSharp.AlignmentIntegerEvenOrderJetConstraints
open BrownianSharp.AlignmentIntegerFractionalApproximationLower
open BrownianSharp.AlignmentFractionalL2

/-- The named order-two scalar operator is definitionally the actual RL L²
operator used by the semigroup theorem. -/
theorem scalarR2L2_eq_integerTwoL2Operator :
    scalarR2L2 = integerTwoL2Operator := by
  rfl

/-- Bounded-linear-map presentation of the recursively defined iterate. -/
noncomputable def integerTwoL2IterateCLM : ℕ → UnitL2 →L[ℝ] UnitL2
  | 0 => ContinuousLinearMap.id ℝ UnitL2
  | n+1 => integerTwoL2Operator.comp (integerTwoL2IterateCLM n)

theorem integerTwoL2IterateCLM_apply (m : ℕ) (x : UnitL2) :
    integerTwoL2IterateCLM m x = integerTwoL2Iterate m x := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp [integerTwoL2IterateCLM, integerTwoL2Iterate, ih]

/-- The CLM presentation of the recursive iterate equals the actual R₂
operator power. -/
theorem integerTwoL2IterateCLM_eq_pow (m : ℕ) :
    integerTwoL2IterateCLM m = scalarR2L2 ^ m := by
  induction m with
  | zero =>
      ext x
      simp [integerTwoL2IterateCLM, scalarR2L2]
  | succ m ih =>
      rw [integerTwoL2IterateCLM, ih, scalarR2L2_eq_integerTwoL2Operator]
      ext x
      simp [pow_succ', ContinuousLinearMap.mul_def]

/-- Pointwise form used by the common-jet lower-bound construction. -/
theorem integerTwoL2Iterate_eq_pow (m : ℕ) (x : UnitL2) :
    integerTwoL2Iterate m x = (scalarR2L2 ^ m) x := by
  rw [← integerTwoL2IterateCLM_apply, integerTwoL2IterateCLM_eq_pow]

/-- The recursive common-jet iterate is the actual order-`2m`
Riemann--Liouville operator on the whole scalar L² source. -/
theorem integerTwoL2Iterate_eq_actual_even_RL {m : ℕ} (hm : 1 ≤ m)
    (x : UnitL2) :
    integerTwoL2Iterate m x =
      scalarRLOnL2 (2 * (m:ℝ)) (by
        have hm' : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
        linarith) x := by
  rw [integerTwoL2Iterate_eq_pow, scalarRLOnL2_even_order_nat hm]


end BrownianSharp.AlignmentIntegerTwoIteratePower
