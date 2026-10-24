import BrownianSharp.NativeLayerThetaBudget

/-! The concave finite-theta branch of the actual native layer variance
envelope. This sums the powered source-normalized profile over all target
blocks, then over the actual weak-composition source shapes. -/

noncomputable section
open scoped BigOperators ENNReal
set_option maxHeartbeats 500000

namespace BrownianSharp.NativeLayerThetaLow

open BrownianSharp.NativeLayerThetaBudget
open BrownianSharp.NativeLayerSummability
open BrownianSharp.NativeLayerBudget
open BrownianSharp.LayerBlockSummability
open BrownianSharp.LayerBlockVariance
open BrownianSharp.AtomicTensorFactorization

def sourceNormalizedVarianceBudget (C r : ℝ) (K : ℕ) (theta : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal 5)^(theta/2) * (1-(1/2:ℝ≥0∞)^(theta/2))⁻¹ +
    (ENNReal.ofReal (C^2*(2:ℝ)^(2*(K:ℝ)+3)))^(theta/2) *
      ((ENNReal.ofReal ((2:ℝ)^(2*r-(2*(K:ℝ)-1)))^(theta/2)) *
        (1-(ENNReal.ofReal ((2:ℝ)^(2*r-(2*(K:ℝ)-1)))^(theta/2)))⁻¹)

theorem sourceNormalizedVarianceBudget_ne_top
    {C r theta : ℝ} {K : ℕ} (hK : 1 ≤ K) (hr : 0 ≤ r)
    (hgap : 2*r < 2*(K:ℝ)-1) (htheta : 1 ≤ theta) :
    sourceNormalizedVarianceBudget C r K theta ≠ ∞ := by
  have hu : 0 < theta/2 := by linarith
  have hqR : (2:ℝ)^(2*r-(2*(K:ℝ)-1)) < 1 := by
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  have hq : ENNReal.ofReal ((2:ℝ)^(2*r-(2*(K:ℝ)-1))) < 1 := by
    rw [show (1:ℝ≥0∞) = ENNReal.ofReal 1 by norm_num]
    exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0:ℝ)<1)).2 hqR
  have hlow : (1/2:ℝ≥0∞)^(theta/2) < 1 :=
    ENNReal.rpow_lt_one (by norm_num) hu
  have hhigh :
      (ENNReal.ofReal ((2:ℝ)^(2*r-(2*(K:ℝ)-1))))^(theta/2) < 1 :=
    ENNReal.rpow_lt_one hq hu
  have hdenlow : 1-(1/2:ℝ≥0∞)^(theta/2) ≠ 0 :=
    ne_of_gt (tsub_pos_of_lt hlow)
  have hdenhigh :
      1-(ENNReal.ofReal ((2:ℝ)^(2*r-(2*(K:ℝ)-1))))^(theta/2) ≠ 0 :=
    ne_of_gt (tsub_pos_of_lt hhigh)
  unfold sourceNormalizedVarianceBudget
  finiteness

theorem nativeLayerVarianceEnvelope_theta_tsum_le_of_one_le_and_le_two
    (d n K : ℕ) (C r theta : ℝ) (hK : 1 ≤ K) (hr : 0 ≤ r)
    (hgap : 2*r < 2*(K:ℝ)-1) (htheta : 1 ≤ theta) (htheta' : theta ≤ 2) :
    (∑' t : Fin d → ℕ,
      ENNReal.ofReal ((2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) *
        (nativeLayerVarianceEnvelope d n K C t)^(theta/2))) ≤
      (Fintype.card (Shape d n) : ℝ≥0∞) *
        (ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
          (sourceNormalizedVarianceBudget C r K theta) ^ d) := by
  classical
  let u : ℝ := theta / 2
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have htheta0 : 0 ≤ theta := le_trans (by norm_num) htheta
  have hscalar (s : ℕ) :
      (∑' k : ℕ, (sourceNormalizedVariance r K C s k)^u) ≤
        sourceNormalizedVarianceBudget C r K theta := by
    simpa [u, sourceNormalizedVarianceBudget] using
      (sourceNormalizedVariance_rpow_tsum_le (r:=r) (C:=C) (K:=K) (s:=s)
        hK hr hgap hu0 hu1)

  have hterm (t : Fin d → ℕ) :
      ENNReal.ofReal ((2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) *
        (nativeLayerVarianceEnvelope d n K C t)^u) =
      (∑ a : Shape d n, ∏ i : Fin d,
        scalarWeightedVariance r K C (a.1 i) (t i))^u := by
    have hv : 0 ≤ nativeLayerVarianceEnvelope d n K C t := by
      unfold nativeLayerVarianceEnvelope
      apply Finset.sum_nonneg
      intro a ha
      apply Finset.prod_nonneg
      intro i hi
      unfold scalarVarianceEnvelope
      split_ifs <;> positivity
    rw [nativeLayerWeightedEnvelope_eq d n K C r t]
    rw [ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (by positivity) hv) hu0.le]
    congr 1
    rw [Real.mul_rpow (by positivity) hv]
    have he : ((2:ℝ)^(2*r*∑ i : Fin d, (t i:ℝ)))^u =
        (2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) := by
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2)]
      congr 1
      dsimp [u]
      ring
    rw [he]

  have hshapeTerm (a : Shape d n) :
      (∑' t : Fin d → ℕ,
        (∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i))^u) ≤
      ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
          (sourceNormalizedVarianceBudget C r K theta)^d := by
    let f : Fin d → ℕ → ℝ≥0∞ := fun i k =>
      sourceNormalizedVariance r K C (a.1 i) k
    have hfactor (t : Fin d → ℕ) :
        (∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i))^u =
        ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
          (∏ i : Fin d, f i (t i)^u) := by
      rw [shape_targetWeighted_eq_sourceNormalized d n K C r a t]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hu0.le]
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hu0.le]
      rw [ENNReal.prod_rpow_of_nonneg hu0.le]
      congr 1
      have hgrade : ((2:ℝ)^(2*r*(n:ℝ)))^u = (2:ℝ)^(r*theta*(n:ℝ)) := by
        rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2)]
        congr 1
        dsimp [u]
        ring
      rw [hgrade]
    calc
      _ = ∑' t : Fin d → ℕ,
          ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
            ∏ i : Fin d, f i (t i)^u := by
          congr 1
          funext t
          exact hfactor t
      _ = ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
          ∑' t : Fin d → ℕ, ∏ i : Fin d, f i (t i)^u :=
            ENNReal.tsum_mul_left
      _ = ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
          ∏ i : Fin d, ∑' k : ℕ, f i k^u := by
          rw [ennreal_tsum_pi_prod d (fun i k => f i k ^ u)]
      _ ≤ ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
          (sourceNormalizedVarianceBudget C r K theta)^d := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc
            _ ≤ ∏ i : Fin d, sourceNormalizedVarianceBudget C r K theta :=
              Finset.prod_le_prod (fun i hi => hscalar (a.1 i))
            _ = sourceNormalizedVarianceBudget C r K theta ^ d := by simp
      _ = _ := rfl

  have hconcave (t : Fin d → ℕ) :
      (∑ a : Shape d n, ∏ i : Fin d,
        scalarWeightedVariance r K C (a.1 i) (t i))^u ≤
        ∑ a : Shape d n,
          (∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i))^u :=
    finset_sum_rpow_le_sum_rpow Finset.univ _ hu0 hu1
  have hpoint (t : Fin d → ℕ) :
      ENNReal.ofReal ((2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) *
        (nativeLayerVarianceEnvelope d n K C t)^u) ≤
      ∑ a : Shape d n,
        (∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i))^u := by
    rw [hterm t]
    exact hconcave t
  have hsum := ENNReal.tsum_le_tsum hpoint
  have hswap :
      (∑' t : Fin d → ℕ,
        ∑ a : Shape d n,
          (∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i))^u) =
      ∑' a : Shape d n,
        ∑' t : Fin d → ℕ,
          (∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i))^u := by
    have hfin (t : Fin d → ℕ) :
        (∑ a : Shape d n,
          (∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i))^u) =
        ∑' a : Shape d n,
          (∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i))^u := by
      exact (tsum_fintype (L := .unconditional _) _).symm
    simp_rw [hfin]
    rw [ENNReal.tsum_comm]
  have hfinite :
      (∑' a : Shape d n,
        ∑' t : Fin d → ℕ,
          (∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i))^u) ≤
        ∑' a : Shape d n,
          ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
            sourceNormalizedVarianceBudget C r K theta ^ d := by
    apply ENNReal.tsum_le_tsum
    intro a
    have := hshapeTerm a
    exact this
  have hcard :
      (∑' a : Shape d n,
        ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
          sourceNormalizedVarianceBudget C r K theta ^ d) =
      (Fintype.card (Shape d n) : ℝ≥0∞) *
        (ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
          sourceNormalizedVarianceBudget C r K theta ^ d) := by
    calc
      _ = ∑ a : Shape d n,
          ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
            sourceNormalizedVarianceBudget C r K theta ^ d := by
          exact tsum_fintype (L := .unconditional _)
            (fun a : Shape d n => ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
              sourceNormalizedVarianceBudget C r K theta ^ d)
      _ = _ := by simp
  calc
    _ ≤ ∑' t : Fin d → ℕ,
          ∑ a : Shape d n,
            (∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i))^u := by
          simpa [u] using hsum
    _ = ∑' a : Shape d n,
          ∑' t : Fin d → ℕ,
            (∏ i : Fin d, scalarWeightedVariance r K C (a.1 i) (t i))^u := hswap
    _ ≤ _ := hfinite
    _ = _ := by rw [hcard]

end BrownianSharp.NativeLayerThetaLow
