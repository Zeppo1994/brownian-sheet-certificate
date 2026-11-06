/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import TauCeti.Analysis.Normed.Module.DoubleDual

/-!
# Weak compactness in reflexive spaces

Pruned to the declarations used by the brownian-sheet certificate.

In a reflexive real or complex seminormed space, every bounded set has weakly compact closure,
and every norm-closed bounded real-convex set, in particular every closed ball, is weakly
compact.

Reflexivity means surjectivity of `NormedSpace.inclusionInDoubleDual`. The topology changes are
explicit, using `toWeakSpace` and `NormedSpace.inclusionInDoubleDualWeak`.

## Main results

* `TauCeti.isCompact_closure_toWeakSpace`: bounded sets have weakly compact closure.
* `TauCeti.isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded`: closed bounded convex sets
  are weakly compact.
* `TauCeti.isCompact_toWeakSpace_closedBall`: closed balls are weakly compact.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.6.
-/

public section

open Bornology Function Metric Set Topology
open NormedSpace

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- In a reflexive seminormed space, every norm-bounded set has weakly compact closure. -/
theorem isCompact_closure_toWeakSpace
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) {s : Set E} (hs : IsBounded s) :
    IsCompact (closure (toWeakSpace 𝕜 E '' s)) := by
  apply NormedSpace.isCompact_closure_weakSpace_of_isBounded 𝕜 E
  · simpa only [preimage_image_eq _ (toWeakSpace 𝕜 E).injective] using hs
  · intro φ _
    obtain ⟨x, hx⟩ := hE (WeakDual.toStrongDual φ)
    refine ⟨toWeakSpace 𝕜 E x, ?_⟩
    apply WeakDual.toStrongDual.injective
    simpa only [inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
      StrongDual.toStrongDual_toWeakDual] using hx

/-- Norm-closed bounded real-convex subsets of a reflexive seminormed space are weakly compact.
Convexity over real scalars also covers complex seminormed spaces. -/
theorem isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded
    (hE : Surjective (inclusionInDoubleDual 𝕜 E))
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] {s : Set E}
    (hclosed : IsClosed s) (hconv : Convex ℝ s) (hbound : IsBounded s) :
    IsCompact (toWeakSpace 𝕜 E '' s) := by
  have : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
  rw [← hclosed.closure_eq, hconv.toWeakSpace_closure 𝕜]
  exact isCompact_closure_toWeakSpace hE hbound

/-- Every closed ball in a reflexive seminormed space is weakly compact, including balls
of zero or negative radius. -/
theorem isCompact_toWeakSpace_closedBall
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) (x : E) (r : ℝ) :
    IsCompact (toWeakSpace 𝕜 E '' closedBall x r) := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .of_algebraMap_smul fun _ _ ↦ rfl
  exact isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded hE
    isClosed_closedBall (convex_closedBall x r) isBounded_closedBall

end TauCeti
