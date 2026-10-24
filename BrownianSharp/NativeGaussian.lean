import BrownianSharp.NativeVariance
import BrownianSharp.NativeProjection
import BrownianSharp.GaussianRows

/-!
The native evaluation rows, their true Gaussian laws, and their normalized
correlations. All covariances are calculated from the full coordinate rows.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BrownianSharp

/-- Actual standardized evaluation at a deterministic midpoint. -/
def standardizedNativeRow {d n : ℕ} {Ω : Type*}
    (G : LayerIndex d n → Ω → ℝ) (q : MidpointGridIndex d n) (ω : Ω) : ℝ :=
  GaussianRows.row G (nativeLayerRowCoefficient q) ω / Real.sqrt (nativeLayerRowVariance q)

/-- Normalized dot product of the actual two native evaluation rows. -/
def nativeRowCorrelation {d n : ℕ} (q q' : MidpointGridIndex d n) : ℝ :=
  (∑ a, nativeLayerRowCoefficient q a * nativeLayerRowCoefficient q' a) /
    (Real.sqrt (nativeLayerRowVariance q) * Real.sqrt (nativeLayerRowVariance q'))

theorem nativeLayerRowVariance_nonneg {d n : ℕ} (q : MidpointGridIndex d n) :
    0 ≤ nativeLayerRowVariance q := Finset.sum_nonneg fun a _ => sq_nonneg _

theorem nativeLayerEvaluation_midpoint_eq {d n : ℕ} {Ω : Type*}
    (G : LayerIndex d n → Ω → ℝ) (q : MidpointGridIndex d n) (ω : Ω) :
    nativeLayerEvaluation G (nativeMidpointBrownianAnchor q) ω =
      GaussianRows.row G (nativeLayerRowCoefficient q) ω := rfl

section Probability
variable {d n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : LayerIndex d n → Ω → ℝ) (hG : ∀ a, Measurable (G a))
    (hIndep : iIndepFun G P) (hLaw : ∀ a, P.map (G a) = gaussianReal 0 1)
include hG hIndep hLaw

theorem nativeLayerEvaluation_variance (q : MidpointGridIndex d n) :
    ProbabilityTheory.variance (nativeLayerEvaluation G (nativeMidpointBrownianAnchor q)) P =
      nativeLayerRowVariance q := by
  exact GaussianRows.row_variance G hG hLaw hIndep (nativeLayerRowCoefficient q)

theorem standardizedNativeRow_law (q : MidpointGridIndex d n)
    (hv : 0 < nativeLayerRowVariance q) :
    P.map (standardizedNativeRow G q) = gaussianReal 0 1 := by
  exact GaussianRows.normalized_row_law G hG hLaw hIndep (nativeLayerRowCoefficient q) hv

theorem standardizedNativeRow_covariance (q q' : MidpointGridIndex d n) :
    cov[standardizedNativeRow G q, standardizedNativeRow G q'; P] =
      nativeRowCorrelation q q' := by
  unfold standardizedNativeRow nativeRowCorrelation
  rw [covariance_fun_div_left, covariance_fun_div_right,
    GaussianRows.row_covariance G hG hLaw hIndep]
  ring
end Probability

theorem nativeRowCorrelation_nonneg {d n : ℕ} (q q' : MidpointGridIndex d n) :
    0 ≤ nativeRowCorrelation q q' := by
  unfold nativeRowCorrelation
  apply div_nonneg
  · exact Finset.sum_nonneg fun a _ =>
      mul_nonneg (nativeLayerRowCoefficient_nonneg q a) (nativeLayerRowCoefficient_nonneg q' a)
  · positivity

/-- Cauchy--Schwarz supplies the actual correlation cap, including degenerate
zero rows (where the displayed total quotient is defined to be zero). -/
theorem nativeRowCorrelation_le_one {d n : ℕ} (q q' : MidpointGridIndex d n) :
    nativeRowCorrelation q q' ≤ 1 := by
  let A : ℝ := ∑ a, nativeLayerRowCoefficient q a * nativeLayerRowCoefficient q' a
  let s := Real.sqrt (nativeLayerRowVariance q)
  let t := Real.sqrt (nativeLayerRowVariance q')
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = nativeLayerRowVariance q :=
    Real.sq_sqrt (nativeLayerRowVariance_nonneg q)
  have ht2 : t ^ 2 = nativeLayerRowVariance q' :=
    Real.sq_sqrt (nativeLayerRowVariance_nonneg q')
  have hCS : A ^ 2 ≤ nativeLayerRowVariance q * nativeLayerRowVariance q' := by
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (nativeLayerRowCoefficient q) (nativeLayerRowCoefficient q')
  rw [← hs2, ← ht2] at hCS
  have hAle : A ≤ s * t := by
    have hnonneg : 0 ≤ s * t := mul_nonneg hs ht
    nlinarith [sq_nonneg (A - s * t)]
  change A / (s * t) ≤ 1
  by_cases hz : s * t = 0
  · simp [hz]
  · exact (div_le_one (lt_of_le_of_ne (mul_nonneg hs ht) (Ne.symm hz))).2 hAle

/-- The exact shell overlap bound transfers to the true normalized Gaussian
correlation on any deterministic set of rows with a fixed variance floor. -/
theorem nativeRowCorrelation_le_prefix {d n h : ℕ} (hd : 0 < d)
    (q q' : MidpointGridIndex d n) (c : Fin d →₀ ℕ)
    (hc : c.sum (fun _ x => x) = n + h)
    (hp : MidpointCommonPrefixProfile q q' c)
    {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hq : v₀ ≤ nativeLayerRowVariance q) (hq' : v₀ ≤ nativeLayerRowVariance q') :
    nativeRowCorrelation q q' ≤
      (1 / (2 : ℝ) ^ (n + 2 * d)) *
        min (Nat.choose (n + d - 1) (d - 1))
          (Nat.choose (h + d - 1) (d - 1)) / v₀ := by
  have hs : 0 < Real.sqrt (nativeLayerRowVariance q) :=
    Real.sqrt_pos.mpr (hv₀.trans_le hq)
  have ht : 0 < Real.sqrt (nativeLayerRowVariance q') :=
    Real.sqrt_pos.mpr (hv₀.trans_le hq')
  have hprod : v₀ ≤ Real.sqrt (nativeLayerRowVariance q) *
      Real.sqrt (nativeLayerRowVariance q') := by
    have hrootq := Real.sqrt_le_sqrt hq
    have hrootq' := Real.sqrt_le_sqrt hq'
    have hmul := mul_le_mul hrootq hrootq' (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
    rwa [Real.mul_self_sqrt hv₀.le] at hmul
  have hA : 0 ≤ ∑ a : LayerIndex d n,
      nativeLayerRowCoefficient q a * nativeLayerRowCoefficient q' a :=
    Finset.sum_nonneg fun a _ => mul_nonneg (nativeLayerRowCoefficient_nonneg q a)
      (nativeLayerRowCoefficient_nonneg q' a)
  unfold nativeRowCorrelation
  calc
    _ ≤ (∑ a : LayerIndex d n,
        nativeLayerRowCoefficient q a * nativeLayerRowCoefficient q' a) / v₀ :=
      div_le_div_of_nonneg_left hA hv₀ hprod
    _ ≤ _ := div_le_div_of_nonneg_right
      (nativeMidpointRowCovariance_le hd q q' c hc hp) hv₀.le

end BrownianSharp
