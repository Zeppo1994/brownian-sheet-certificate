/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Norm identities in `Lᵖ` spaces

Pruned to the declarations used by the brownian-sheet certificate.

## Main declarations

* `MeasureTheory.Lp.integral_norm_rpow_eq_norm_rpow`: for `0 < p < ∞`, the integral of the `p`-th
  power of the pointwise norm of an `Lᵖ` function is the `p`-th power of its `Lᵖ` norm.
-/

public section

namespace MeasureTheory

open scoped ENNReal

/-- For `0 < p < ∞`, the integral of the `p`-th power of the pointwise norm of an `Lᵖ` function
is the `p`-th power of its `Lᵖ` norm. -/
theorem Lp.integral_norm_rpow_eq_norm_rpow {alpha F : Type*} [MeasurableSpace alpha]
    {m : Measure alpha} [NormedAddCommGroup F] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (f : Lp F p m) :
    ∫ x, ‖f x‖ ^ p.toReal ∂m = ‖f‖ ^ p.toReal := by
  have h_nonneg : 0 ≤ ∫ x, ‖f x‖ ^ p.toReal ∂m :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [Lp.norm_def, toReal_eLpNorm,
    lpNorm_eq_integral_norm_rpow_toReal hp0 hp (Lp.aestronglyMeasurable f),
    ← Real.rpow_mul h_nonneg, inv_mul_cancel₀ (ENNReal.toReal_pos hp0 hp).ne', Real.rpow_one]

end MeasureTheory
