import BrownianSharp.NativeLayerThetaLow
import BrownianSharp.NativeSmoothBesovMean
import BrownianSharp.NativeClassReindex

/-! Numeric assembly of the actual theta≤2 native-layer variance profile into
the diagonal finite-theta Gaussian Besov energy. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.NativeLayerThetaMean

open BrownianSharp.NativeLayerThetaLow
open BrownianSharp.NativeLayerThetaBudget
open BrownianSharp.NativeLayerBudget
open BrownianSharp.LayerBlockVariance
open BrownianSharp.AtomicTensorFactorization
open BrownianSharp.PeriodicCover
open BrownianSharp.SmoothResolution

theorem nativeLayerBesov_theta_le_two_summability
    (d n K : ℕ) (C r theta : ℝ) (hK : 1 ≤ K) (hr : 0 ≤ r)
    (hgap : 2*r < 2*(K:ℝ)-1) (htheta : 1 ≤ theta) (htheta' : theta ≤ 2) :
    (∑' t : Fin d → ℕ,
      ENNReal.ofReal (((2:ℝ)^(r*∑ i : Fin d, (t i:ℝ)))^theta *
        (2^theta * (nativeLayerVarianceEnvelope d n K C t)^(theta/2) *
          gaussianAbsoluteMoment theta))) ≤
      ENNReal.ofReal (2^theta * gaussianAbsoluteMoment theta) *
        (Fintype.card (Shape d n) : ℝ≥0∞) *
        ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
          sourceNormalizedVarianceBudget C r K theta ^ d := by
  classical
  let u : ℝ := theta/2
  have hu : 0 < u := by dsimp [u]; linarith
  have hv (t : Fin d → ℕ) : 0 ≤ nativeLayerVarianceEnvelope d n K C t := by
    unfold nativeLayerVarianceEnvelope
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.prod_nonneg
    intro i hi
    unfold scalarVarianceEnvelope
    split_ifs <;> positivity
  have hbudget := nativeLayerVarianceEnvelope_theta_tsum_le_of_one_le_and_le_two
    d n K C r theta hK hr hgap htheta htheta'
  have hterm (t : Fin d → ℕ) :
      ENNReal.ofReal (((2:ℝ)^(r*∑ i : Fin d, (t i:ℝ)))^theta *
        (2^theta * (nativeLayerVarianceEnvelope d n K C t)^u *
          gaussianAbsoluteMoment theta)) =
      ENNReal.ofReal (2^theta * gaussianAbsoluteMoment theta) *
        ENNReal.ofReal ((2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) *
          (nativeLayerVarianceEnvelope d n K C t)^u) := by
    have hmoment : 0 ≤ gaussianAbsoluteMoment theta :=
      BrownianSharp.gaussianAbsoluteMoment_nonneg theta
    have hrexp : ((2:ℝ)^(r*∑ i : Fin d, (t i:ℝ)))^theta =
        (2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) := by
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2)]
      congr 1
      ring
    rw [hrexp]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤
      (2:ℝ)^theta * gaussianAbsoluteMoment theta)]
    congr 1
    ring
  calc
    _ = ENNReal.ofReal (2^theta * gaussianAbsoluteMoment theta) *
        ∑' t : Fin d → ℕ,
          ENNReal.ofReal ((2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) *
            (nativeLayerVarianceEnvelope d n K C t)^u) := by
          calc
            _ = ∑' t : Fin d → ℕ,
                ENNReal.ofReal (2^theta * gaussianAbsoluteMoment theta) *
                  ENNReal.ofReal ((2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) *
                    (nativeLayerVarianceEnvelope d n K C t)^u) := by
                  congr 1
                  funext t
                  exact hterm t
            _ = _ := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (2^theta * gaussianAbsoluteMoment theta) *
        ((Fintype.card (Shape d n) : ℝ≥0∞) *
          (ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
            sourceNormalizedVarianceBudget C r K theta ^ d)) := by
          apply mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by ac_rfl

/-- Actual expected Besov energy for the native layer when the spatial and
scale exponents agree and `1 ≤ theta ≤ 2`. The scale dependence is exactly
the weak-composition count times `2^(r theta n)`; all remaining factors are
uniform in the grade. -/
theorem nativeSmoothBesov_equalExponent_expected_energy_le_of_theta_le_two
    (d n K : ℕ) (hK : 1 ≤ K) (C : ℝ)
    (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (theta r : ℝ) (htheta : 1 ≤ theta) (htheta' : theta ≤ 2)
    (hr : 0 ≤ r) (hgap : 2*r < 2*(K:ℝ)-1) :
    (∫⁻ z : Fin (Fintype.card (LayerIndex d n)) → ℝ,
      smoothBesovEnergy (ENNReal.ofReal theta) r (ENNReal.ofReal theta)
        (gaussianSynthesis (BrownianSharp.nativeFinAtoms d n) z)
      ∂productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) ≤
      ENNReal.ofReal (2^theta * gaussianAbsoluteMoment theta) *
        (Fintype.card (Shape d n) : ℝ≥0∞) *
        ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
          sourceNormalizedVarianceBudget C r K theta ^ d := by
  have hsum := nativeLayerBesov_theta_le_two_summability
    d n K C r theta hK hr hgap htheta htheta'
  have hmean := BrownianSharp.nativeSmoothBesov_equalExponent_expected_energy_le
    d n K hK C hC theta r htheta hsum
  convert hmean using 1 <;> rfl

end BrownianSharp.NativeLayerThetaMean
