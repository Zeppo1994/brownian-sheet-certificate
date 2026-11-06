/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

/-!
# Scalar power mean inequalities

Pruned to the declarations used by the brownian-sheet certificate.

For `1 < q`, the power mean inequality `u ^ q ≤ 2 ^ (q - 1) * (s ^ q + t ^ q)` for
`0 ≤ u ≤ s + t` improves by a uniform factor `1 - κ` once `u` is also bounded away from `2 * s`,
say `u ≤ (2 - δ) * s` with `0 ≤ t ≤ s`. Strict convexity of `t ↦ t ^ q` gives the improvement
for each ratio `t / s`, and compactness of `[0, 1]` makes it uniform. This is the scalar step in
showing that `q`-th powers of norms on a uniformly convex space are uniformly convex.

## Main results

* `Real.min_rpow_lt_two_rpow_sub_one_mul`: `min (1 + r) (2 - δ) ^ q < 2 ^ (q - 1) * (1 + r ^ q)`
  for `1 < q`, `0 < δ ≤ 1` and `0 ≤ r ≤ 1`.
* `Real.exists_rpow_le_of_le_add_of_le_two_sub_mul`: the uniform strict power mean inequality.
-/

public section

namespace Real

/-- For `1 < q`, `0 < δ ≤ 1` and `0 ≤ r ≤ 1`,
`min (1 + r) (2 - δ) ^ q < 2 ^ (q - 1) * (1 + r ^ q)`: for `r < 1` by strict convexity of
`t ↦ t ^ q`, and for `r = 1` because `0 ≤ 2 - δ < 2`. -/
theorem min_rpow_lt_two_rpow_sub_one_mul {q δ r : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    min (1 + r) (2 - δ) ^ q < 2 ^ (q - 1) * (1 + r ^ q) := by
  have hq0 : 0 < q := by linarith
  have h2sub : (2 : ℝ) ^ (q - 1) = 2 ^ q / 2 := rpow_sub_one two_ne_zero q
  have hmin0 : 0 ≤ min (1 + r) (2 - δ) := le_min (by linarith) (by linarith)
  rcases hr1.lt_or_eq with hr1 | rfl
  · have hstrict := (strictConvexOn_rpow hq).2 (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 hr0)
      hr1.ne' (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simp only [smul_eq_mul, one_rpow] at hstrict
    have hle : min (1 + r) (2 - δ) ^ q ≤ (1 + r) ^ q :=
      rpow_le_rpow hmin0 (min_le_left _ _) hq0.le
    have hhalf : (1 + r) ^ q = 2 ^ q * (1 / 2 * 1 + 1 / 2 * r) ^ q := by
      rw [← mul_rpow zero_le_two (by positivity)]
      ring_nf
    have := mul_lt_mul_of_pos_left hstrict (by positivity : (0 : ℝ) < 2 ^ q)
    rw [h2sub]
    nlinarith
  · have hlt : min (1 + 1) (2 - δ) ^ q < 2 ^ q :=
      rpow_lt_rpow hmin0 ((min_le_right _ _).trans_lt (by linarith)) hq0
    have h2 : (2 : ℝ) ^ q / 2 * (1 + 1) = 2 ^ q := by ring
    rwa [one_rpow, h2sub, h2]

/-- **A uniform strict power mean inequality.** For `1 < q` and `0 < δ ≤ 1` there is `κ > 0`
such that `u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q)` whenever
`0 ≤ t ≤ s` and `0 ≤ u ≤ min (s + t) ((2 - δ) * s)`. After rescaling to `s = 1`, the gap
between the two sides is a continuous positive function of `t ∈ [0, 1]`, so it has a positive
minimum. This is the scalar part of `TauCeti.exists_forall_norm_add_rpow_le`. -/
theorem exists_rpow_le_of_le_add_of_le_two_sub_mul {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) :
    ∃ κ, 0 < κ ∧ ∀ s t u : ℝ, 0 ≤ t → t ≤ s → 0 ≤ u → u ≤ s + t → u ≤ (2 - δ) * s →
      u ^ q ≤ (1 - κ) * 2 ^ (q - 1) * (s ^ q + t ^ q) := by
  have hq0 : 0 < q := by linarith
  have h2sub : (2 : ℝ) ^ (q - 1) = 2 ^ q / 2 := rpow_sub_one two_ne_zero q
  -- The gap between the two sides after rescaling to `s = 1`.
  set φ : ℝ → ℝ := fun r ↦ 2 ^ (q - 1) * (1 + r ^ q) - min (1 + r) (2 - δ) ^ q with hφ
  have hφc : Continuous φ := by
    have := continuous_rpow_const hq0.le
    fun_prop
  obtain ⟨r₀, hr₀, hmin⟩ :=
    isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one) hφc.continuousOn
  have hm : 0 < φ r₀ := sub_pos.2 (min_rpow_lt_two_rpow_sub_one_mul hq hδ hδ1 hr₀.1 hr₀.2)
  refine ⟨φ r₀ / 2 ^ q, by positivity, fun s t u ht hts hu hus hu2 ↦ ?_⟩
  rcases (ht.trans hts).eq_or_lt with rfl | hs
  · obtain rfl : t = 0 := le_antisymm hts ht
    obtain rfl : u = 0 := le_antisymm (by simpa using hus) hu
    simp [zero_rpow hq0.ne']
  set r := t / s with hr_def
  have hr : r ∈ Set.Icc (0 : ℝ) 1 := ⟨div_nonneg ht hs.le, div_le_one_of_le₀ hts hs.le⟩
  have hv : u / s ≤ min (1 + r) (2 - δ) := by
    refine le_min ?_ ?_ <;> rw [div_le_iff₀ hs]
    · rw [hr_def, add_mul, div_mul_cancel₀ _ hs.ne', one_mul]
      exact hus
    · linarith
  have hrq : r ^ q ≤ 1 := rpow_le_one hr.1 hr.2 hq0.le
  have hgap : φ r₀ ≤ φ r := hmin hr
  have hvq : (u / s) ^ q ≤ min (1 + r) (2 - δ) ^ q :=
    rpow_le_rpow (div_nonneg hu hs.le) hv hq0.le
  have key : (u / s) ^ q ≤ (1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (1 + r ^ q) := by
    simp only [hφ] at hgap
    have hrq0 : 0 ≤ r ^ q := rpow_nonneg hr.1 q
    have : (1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (1 + r ^ q) =
        2 ^ (q - 1) * (1 + r ^ q) - φ r₀ * ((1 + r ^ q) / 2) := by
      rw [h2sub]
      field_simp
    rw [this]
    nlinarith
  have hsq : 0 < s ^ q := rpow_pos_of_pos hs q
  calc u ^ q = s ^ q * (u / s) ^ q := by
        rw [div_rpow hu hs.le, mul_div_cancel₀ _ hsq.ne']
    _ ≤ s ^ q * ((1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (1 + r ^ q)) := by gcongr
    _ = (1 - φ r₀ / 2 ^ q) * 2 ^ (q - 1) * (s ^ q + t ^ q) := by
        rw [hr_def, div_rpow ht hs.le]
        field_simp


end Real
