import BrownianSharp.LayerBlockSummability
import Mathlib.Basic.ENNReal.BigOperators

/-! Summation of the rectangular tensor envelopes over every source shape
and every target block. The scalar geometric estimate remains explicit as a
one-dimensional hypothesis, supplied separately by `ScalarVariancePointwise`.
-/

noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.NativeLayerSummability

open BrownianSharp.LayerBlockSummability
open BrownianSharp.LayerBlockVariance
open BrownianSharp.AtomicTensorFactorization

/-- The grade constraint turns the product of coordinate dilation budgets
into exactly one grade-`n` dilation, rather than a dimension-times-grade loss. -/
theorem shape_budget_eq (d n : ℕ) (B r : ℝ) (hB : 0 ≤ B)
    (s : Shape d n) :
    (∏ i : Fin d,
      ENNReal.ofReal (B * (2 : ℝ) ^ (2 * r * (s.1 i : ℝ)))) =
      ENNReal.ofReal (B ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ))) := by
  have hshape : (∑ i : Fin d, (s.1 i : ℝ)) = n := by
    have hh := (Finset.mem_finsuppAntidiag'.mp s.2).1
    have hh' : (∑ i : Fin d, s.1 i) = n := by
      simpa [Finsupp.sum_fintype] using hh
    exact_mod_cast hh'
  have hprod_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin d)),
      0 ≤ B * (2 : ℝ) ^ (2 * r * (s.1 i : ℝ)) := by
    intro i hi
    positivity
  rw [← ENNReal.ofReal_prod_of_nonneg hprod_nonneg]
  congr 1
  rw [Finset.prod_mul_distrib]
  rw [show (∏ i : Fin d, (2 : ℝ) ^ (2 * r * (s.1 i : ℝ))) =
      (2 : ℝ) ^ (∑ i : Fin d, 2 * r * (s.1 i : ℝ)) by
        symm
        exact Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2)
          (fun i : Fin d => 2 * r * (s.1 i : ℝ)) Finset.univ]
  have hexp : (∑ i : Fin d, 2 * r * (s.1 i : ℝ)) = 2 * r * (n : ℝ) := by
    calc
      (∑ i : Fin d, 2 * r * (s.1 i : ℝ)) =
          2 * ∑ i : Fin d, r * (s.1 i : ℝ) := by
            calc
              _ = ∑ i : Fin d, 2 * (r * (s.1 i : ℝ)) := by
                congr 1
                funext i
                ring
              _ = 2 * ∑ i : Fin d, r * (s.1 i : ℝ) := by
                rw [← Finset.mul_sum]
      _ = 2 * (r * ∑ i : Fin d, (s.1 i : ℝ)) := by
            rw [← Finset.mul_sum]
      _ = 2 * r * (n : ℝ) := by rw [hshape]; ring
  rw [hexp]
  simp

/-- The coordinatewise weighted sum of shape envelopes is exactly the
weighted native-layer envelope. This is the bridge from the factorized
variance estimates to the literal block variance used by the Gaussian
energy theorem. -/
theorem nativeLayerWeightedEnvelope_eq
    (d n K : ℕ) (C r : ℝ) (t : Fin d → ℕ) :
    (∑ a : Shape d n, ∏ i : Fin d,
      scalarWeightedVariance r K C (a.1 i) (t i)) =
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i : Fin d, (t i : ℝ)) *
        nativeLayerVarianceEnvelope d n K C t) := by
  classical
  have hweight :
      (∏ i : Fin d, (2 : ℝ) ^ (2 * r * (t i : ℝ))) =
        (2 : ℝ) ^ (2 * r * ∑ i : Fin d, (t i : ℝ)) := by
    calc
      _ = (2 : ℝ) ^ (∑ i : Fin d, 2 * r * (t i : ℝ)) := by
        symm
        exact Real.rpow_sum_of_pos (by norm_num : (0:ℝ) < 2)
          (fun i : Fin d => 2 * r * (t i : ℝ)) Finset.univ
      _ = _ := by
        have hexp : (∑ i : Fin d, 2 * r * (t i : ℝ)) =
            2 * r * ∑ i : Fin d, (t i : ℝ) := by
          calc
            _ = 2 * ∑ i : Fin d, r * (t i : ℝ) := by
              calc
                _ = ∑ i : Fin d, 2 * (r * (t i : ℝ)) := by
                  congr 1
                  funext i
                  ring
                _ = _ := by rw [← Finset.mul_sum]
            _ = _ := by rw [← Finset.mul_sum]; ring
        rw [hexp]
  have henv (s : ℕ) (k : ℕ) : 0 ≤ scalarVarianceEnvelope K C s k := by
    unfold scalarVarianceEnvelope
    split_ifs <;> positivity
  have hterm (a : Shape d n) :
      (∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i)) =
        ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i : Fin d, (t i : ℝ)) *
          ∏ i : Fin d, scalarVarianceEnvelope K C (a.1 i) (t i)) := by
    unfold scalarWeightedVariance
    rw [← ENNReal.ofReal_prod_of_nonneg]
    · congr 1
      rw [Finset.prod_mul_distrib, hweight]
    · intro i hi
      apply mul_nonneg
      · positivity
      · exact henv (a.1 i) (t i)
  rw [show nativeLayerVarianceEnvelope d n K C t =
      ∑ a : Shape d n, ∏ i : Fin d,
        scalarVarianceEnvelope K C (a.1 i) (t i) by rfl]
  simp_rw [hterm]
  rw [← ENNReal.ofReal_sum_of_nonneg]
  · apply congrArg ENNReal.ofReal
    exact (Finset.mul_sum (Finset.univ : Finset (Shape d n))
      (fun a : Shape d n =>
        ∏ i : Fin d, scalarVarianceEnvelope K C (a.1 i) (t i))
      ((2 : ℝ) ^ (2 * r * ∑ i : Fin d, (t i : ℝ)))).symm
  · intro a ha
    apply mul_nonneg
    · positivity
    · exact Finset.prod_nonneg fun i hi => henv (a.1 i) (t i)

/-- Full target-scale series of the actual native layer variance envelope,
with an exact finite shape count and the explicit scalar budget `B`. -/
theorem nativeLayerWeightedVarianceEnvelope_tsum_le
    (d n K : ℕ) (C r B : ℝ) (hB : 0 ≤ B)
    (hscalar : ∀ s : ℕ,
      ∑' k : ℕ, scalarWeightedVariance r K C s k ≤
        ENNReal.ofReal (B * (2 : ℝ) ^ (2 * r * (s : ℝ)))) :
    (∑' t : Fin d → ℕ,
      ∑ a : Shape d n, ∏ i : Fin d,
        scalarWeightedVariance r K C (a.1 i) (t i)) ≤
      (Fintype.card (Shape d n) : ℝ≥0∞) *
        ENNReal.ofReal (B ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ))) := by
  classical
  have hswap :
      (∑' t : Fin d → ℕ,
        ∑ a : Shape d n, ∏ i : Fin d,
          scalarWeightedVariance r K C (a.1 i) (t i)) =
      ∑' a : Shape d n, ∑' t : Fin d → ℕ,
        ∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i) := by
    have hfin (t : Fin d → ℕ) :
        (∑ a : Shape d n, ∏ i : Fin d,
          scalarWeightedVariance r K C (a.1 i) (t i)) =
        ∑' a : Shape d n, ∏ i : Fin d,
          scalarWeightedVariance r K C (a.1 i) (t i) := by
      exact (tsum_fintype (L := .unconditional _)
        (fun a : Shape d n => ∏ i : Fin d,
          scalarWeightedVariance r K C (a.1 i) (t i))).symm
    simp_rw [hfin]
    rw [ENNReal.tsum_comm]
  rw [hswap]
  calc
    (∑' a : Shape d n, ∑' t : Fin d → ℕ,
        ∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i))
      ≤ ∑' a : Shape d n,
          ∏ i : Fin d,
            ENNReal.ofReal (B * (2 : ℝ) ^ (2 * r * (a.1 i : ℝ))) := by
          apply ENNReal.tsum_le_tsum
          intro a
          exact shapeWeightedVariance_tsum_le d K C r B hB
            (fun s => hscalar s) a.1
    _ = ∑' a : Shape d n,
          ENNReal.ofReal (B ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ))) := by
          congr 1
          funext a
          exact shape_budget_eq d n B r hB a
    _ = (Fintype.card (Shape d n) : ℝ≥0∞) *
          ENNReal.ofReal (B ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ))) := by
          simp

/-- Same summability theorem stated directly for the actual, unweighted
native-layer block variance envelope. -/
theorem nativeLayerVarianceEnvelope_weighted_tsum_le
    (d n K : ℕ) (C r B : ℝ) (hB : 0 ≤ B)
    (hscalar : ∀ s : ℕ,
      ∑' k : ℕ, scalarWeightedVariance r K C s k ≤
        ENNReal.ofReal (B * (2 : ℝ) ^ (2 * r * (s : ℝ)))) :
    (∑' t : Fin d → ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i : Fin d, (t i : ℝ)) *
        nativeLayerVarianceEnvelope d n K C t)) ≤
      (Fintype.card (Shape d n) : ℝ≥0∞) *
        ENNReal.ofReal (B ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ))) := by
  calc
    _ = ∑' t : Fin d → ℕ,
        ∑ a : Shape d n, ∏ i : Fin d,
          scalarWeightedVariance r K C (a.1 i) (t i) := by
      congr 1
      funext t
      exact (nativeLayerWeightedEnvelope_eq d n K C r t).symm
    _ ≤ _ := nativeLayerWeightedVarianceEnvelope_tsum_le
      d n K C r B hB hscalar

end BrownianSharp.NativeLayerSummability
