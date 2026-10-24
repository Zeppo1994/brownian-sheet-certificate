import BrownianSharp.NativeLayerSummability
import BrownianSharp.ScalarVariancePointwise

/-! Explicit scalar geometric budget and its upgrade to the actual native
layer's full target-block series. The only scale restriction is the displayed
strict inequality `2r < 2K-1`, which makes the inverse-frequency tail
geometric. -/

noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.NativeLayerBudget

open BrownianSharp.LayerBlockSummability
open BrownianSharp.NativeLayerSummability
open BrownianSharp.ScalarVariancePointwise

/-- The scalar decay ratio, written in real arithmetic for later comparison
with the regularity gap. -/
def scalarTailRatio (r : ℝ) (K : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * r - (2 * (K : ℝ) - 1)) /
    (1 - (2 : ℝ) ^ (2 * r - (2 * (K : ℝ) - 1)))

/-- Explicit dimension-free scalar budget from summing low and high target
frequencies. -/
def scalarLayerBudget (C r : ℝ) (K : ℕ) : ℝ :=
  10 + C ^ 2 * (2 : ℝ) ^ (2 * (K : ℝ) + 3) * scalarTailRatio r K

theorem scalarWeightedVariance_tsum_le {r C : ℝ} {K s : ℕ}
    (hK : 1 ≤ K) (hr : 0 ≤ r)
    (hgap : 2 * r < 2 * (K : ℝ) - 1) :
    (∑' k : ℕ, scalarWeightedVariance r K C s k) ≤
      ENNReal.ofReal
        (scalarLayerBudget C r K * (2 : ℝ) ^ (2 * r * (s : ℝ))) := by
  let qR : ℝ := (2 : ℝ) ^ (2 * r - (2 * (K : ℝ) - 1))
  let q : ℝ≥0∞ := ENNReal.ofReal qR
  let A : ℝ≥0∞ := ENNReal.ofReal (5 * (2 : ℝ) ^ (2 * r * (s : ℝ)))
  let H : ℝ≥0∞ := ENNReal.ofReal
    (C ^ 2 * (2 : ℝ) ^ (2 * (K : ℝ) + 3 + 2 * r * (s : ℝ)))
  have hqRpos : 0 < qR := by positivity [qR]
  have hqRlt : qR < 1 := by
    dsimp [qR]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    have : 2 * r - (2 * (K : ℝ) - 1) < 0 := by linarith
    exact this
  have hqpos : 0 ≤ q := by positivity
  have hq_lt : q < 1 := by
    dsimp [q]
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
    exact ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1) |>.2 hqRlt
  have hlow : ∀ k, k ≤ s → scalarWeightedVariance r K C s k ≤
      A * (1 / 2 : ℝ≥0∞) ^ (s - k) := by
    intro k hk
    simpa [A] using scalar_low_bound (C := C) (K := K) hr hk
  have hhigh : ∀ k, s < k → scalarWeightedVariance r K C s k ≤
      H * q ^ (k - s) := by
    intro k hk
    simpa [H, q, qR] using scalar_high_bound (C := C) (r := r) hK hk
  have hsplit := scalarTsum_le_of_pointwise_split s q A H hqpos hq_lt
    (scalarWeightedVariance r K C s) hlow hhigh
  have hratio : q * (1 - q)⁻¹ = ENNReal.ofReal (scalarTailRatio r K) := by
    change ENNReal.ofReal qR * (1 - ENNReal.ofReal qR)⁻¹ =
      ENNReal.ofReal (qR / (1 - qR))
    have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal qR =
        ENNReal.ofReal (1 - qR) := by
      rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
      rw [← ENNReal.ofReal_sub 1 hqRpos.le]
    rw [hsub, ← ENNReal.ofReal_inv_of_pos (sub_pos.mpr hqRlt)]
    rw [← ENNReal.ofReal_mul hqRpos.le]
    simp [div_eq_mul_inv]
  have hH : H = ENNReal.ofReal
      ((C ^ 2 * (2 : ℝ) ^ (2 * (K : ℝ) + 3)) *
        (2 : ℝ) ^ (2 * r * (s : ℝ))) := by
    dsimp [H]
    congr 1
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    ring
  have htail : H * (q * (1 - q)⁻¹) = ENNReal.ofReal
      ((C ^ 2 * (2 : ℝ) ^ (2 * (K : ℝ) + 3) *
        scalarTailRatio r K) * (2 : ℝ) ^ (2 * r * (s : ℝ))) := by
    rw [hH, hratio, ← ENNReal.ofReal_mul]
    · congr 1
      ring
    · positivity
  have hlow_sum : A * 2 = ENNReal.ofReal
      (10 * (2 : ℝ) ^ (2 * r * (s : ℝ))) := by
    dsimp [A]
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  have hbudget : A * 2 + H * (q * (1 - q)⁻¹) =
      ENNReal.ofReal
        (scalarLayerBudget C r K * (2 : ℝ) ^ (2 * r * (s : ℝ))) := by
    rw [hlow_sum, htail, ← ENNReal.ofReal_add]
    · congr 1
      dsimp [scalarLayerBudget, scalarTailRatio]
      ring
    · positivity
    · have hden : 0 < 1 - (2 : ℝ) ^
          (2 * r - (2 * (K : ℝ) - 1)) := sub_pos.mpr hqRlt
      dsimp [scalarLayerBudget, scalarTailRatio]
      positivity
  exact hsplit.trans_eq hbudget

/-- The actual native grade has a summable weighted variance over all target
blocks, with its exact weak-composition factor. -/
theorem nativeLayerVarianceEnvelope_weighted_tsum_le
    (d n K : ℕ) (C r : ℝ) (hK : 1 ≤ K) (hr : 0 ≤ r)
    (hgap : 2 * r < 2 * (K : ℝ) - 1) :
    (∑' t : Fin d → ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i : Fin d, (t i : ℝ)) *
        LayerBlockVariance.nativeLayerVarianceEnvelope d n K C t)) ≤
      (Fintype.card (Shape d n) : ℝ≥0∞) *
        ENNReal.ofReal
          (scalarLayerBudget C r K ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ))) := by
  apply BrownianSharp.NativeLayerSummability.nativeLayerVarianceEnvelope_weighted_tsum_le
    d n K C r (scalarLayerBudget C r K) ?_ ?_
  · have hexp : 2 * r - (2 * (K : ℝ) - 1) < 0 := by linarith
    have hq : (2 : ℝ) ^ (2 * r - (2 * (K : ℝ) - 1)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) hexp
    have hden : 0 < 1 - (2 : ℝ) ^
        (2 * r - (2 * (K : ℝ) - 1)) := sub_pos.mpr hq
    have hratio : 0 ≤ scalarTailRatio r K := by
      apply div_nonneg
      · positivity
      · exact hden.le
    unfold scalarLayerBudget
    positivity
  · intro s
    exact scalarWeightedVariance_tsum_le hK hr hgap

end BrownianSharp.NativeLayerBudget
