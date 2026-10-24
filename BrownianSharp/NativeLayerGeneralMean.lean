import BrownianSharp.NativeLayerThetaMean
import BrownianSharp.SmoothBesovGeneralMean
import BrownianSharp.NativeClassReindex

/-! Actual arbitrary-p, finite-theta Besov energy for the native Gaussian
layer. The finite-theta moment theorem reduces its numerical hypothesis to
the powered native variance tsum, whose low- and high-theta branches are
proved in the preceding modules. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.NativeLayerGeneralMean

open BrownianSharp.NativeLayerThetaLow
open BrownianSharp.NativeLayerThetaBudget
open BrownianSharp.NativeLayerBudget
open BrownianSharp.LayerBlockVariance
open BrownianSharp.AtomicTensorFactorization
open BrownianSharp.PeriodicCover
open BrownianSharp.SmoothResolution

def nativeThetaVarianceBound (d n K : ℕ) (C r theta : ℝ) : ℝ≥0∞ :=
  if theta ≤ 2 then
    (Fintype.card (Shape d n) : ℝ≥0∞) *
      (ENNReal.ofReal ((2:ℝ)^(r*theta*(n:ℝ))) *
        sourceNormalizedVarianceBudget C r K theta ^ d)
  else
    (Fintype.card (Shape d n) : ℝ≥0∞) *
      ENNReal.ofReal
        ((scalarLayerBudget C r K ^ d * (2:ℝ)^(2*r*(n:ℝ)))^(theta/2))

theorem nativeLayerVarianceEnvelope_theta_tsum_le_all
    (d n K : ℕ) (C r theta : ℝ) (hK : 1 ≤ K) (hr : 0 ≤ r)
    (hgap : 2*r < 2*(K:ℝ)-1) (htheta : 1 ≤ theta) :
    (∑' t : Fin d → ℕ,
      ENNReal.ofReal ((2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) *
        (nativeLayerVarianceEnvelope d n K C t)^(theta/2))) ≤
      nativeThetaVarianceBound d n K C r theta := by
  by_cases hsmall : theta ≤ 2
  · simpa [nativeThetaVarianceBound, hsmall] using
      nativeLayerVarianceEnvelope_theta_tsum_le_of_one_le_and_le_two
        d n K C r theta hK hr hgap htheta hsmall
  · have hlarge : 2 ≤ theta := le_of_not_ge hsmall
    simpa [nativeThetaVarianceBound, hsmall] using
      nativeLayerVarianceEnvelope_theta_tsum_le_of_two_le
        d n K C r theta hK hr hgap hlarge

/-- Numeric Gaussian-moment series for the general p/theta Besov adapter.
Its only n-dependent factor is the actual native variance budget above. -/
theorem nativeLayerGeneralBesov_summability
    (d n K : ℕ) (C r p theta : ℝ) (hK : 1 ≤ K) (hr : 0 ≤ r)
    (hgap : 2*r < 2*(K:ℝ)-1) (hp : 1 ≤ p) (htheta : 1 ≤ theta) :
    (∑' t : Fin d → ℕ,
      ENNReal.ofReal (((2:ℝ)^(r*∑ i : Fin d, (t i:ℝ)))^theta) *
        (ENNReal.ofReal (2 ^ max p theta *
          (nativeLayerVarianceEnvelope d n K C t)^(max p theta/2) *
          gaussianAbsoluteMoment (max p theta))^(theta/max p theta))) ≤
      (ENNReal.ofReal ((2 ^ max p theta *
        gaussianAbsoluteMoment (max p theta))^(theta/max p theta))) *
        nativeThetaVarianceBound d n K C r theta := by
  classical
  let q : ℝ := max p theta
  let a : ℝ := theta/q
  let momentConst : ℝ := 2^q * gaussianAbsoluteMoment q
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have htheta0 : 0 < theta := lt_of_lt_of_le zero_lt_one htheta
  have hq1 : 1 ≤ q := le_trans hp (le_max_left p theta)
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq1
  have ha0 : 0 < a := by dsimp [a,q]; positivity
  have ha1 : a ≤ 1 := by dsimp [a,q]; exact (div_le_one hqpos).2 (le_max_right p theta)
  have haeq : a*q = theta := by dsimp [a]; field_simp
  have hv (t : Fin d → ℕ) : 0 ≤ nativeLayerVarianceEnvelope d n K C t := by
    unfold nativeLayerVarianceEnvelope
    apply Finset.sum_nonneg
    intro s hs
    apply Finset.prod_nonneg
    intro i hi
    unfold scalarVarianceEnvelope
    split_ifs <;> positivity
  have hmomentNonneg : 0 ≤ momentConst := by
    dsimp [momentConst, q]
    apply mul_nonneg
    · positivity
    · exact BrownianSharp.gaussianAbsoluteMoment_nonneg _
  have hweight (t : Fin d → ℕ) :
      ((2:ℝ)^(r*∑ i : Fin d, (t i:ℝ)))^theta =
        (2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) := by
    rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2)]
    congr 1
    ring
  have hmoment (t : Fin d → ℕ) :
      (ENNReal.ofReal (2^q *
        (nativeLayerVarianceEnvelope d n K C t)^(q/2) *
        gaussianAbsoluteMoment q))^a =
      ENNReal.ofReal (momentConst^a) *
        ENNReal.ofReal ((nativeLayerVarianceEnvelope d n K C t)^(theta/2)) := by
    have hbase : 0 ≤ momentConst *
        (nativeLayerVarianceEnvelope d n K C t)^(q/2) :=
      mul_nonneg hmomentNonneg (Real.rpow_nonneg (hv t) _)
    have hpower :
        (momentConst *
          (nativeLayerVarianceEnvelope d n K C t)^(q/2))^a =
        momentConst^a * (nativeLayerVarianceEnvelope d n K C t)^(theta/2) := by
      rw [Real.mul_rpow hmomentNonneg (Real.rpow_nonneg (hv t) _)]
      rw [← Real.rpow_mul (hv t)]
      rw [show (q/2)*a = theta/2 by dsimp [a]; field_simp]
    have hinside :
        2^q * (nativeLayerVarianceEnvelope d n K C t)^(q/2) *
          gaussianAbsoluteMoment q =
        momentConst * (nativeLayerVarianceEnvelope d n K C t)^(q/2) := by
      dsimp [momentConst, q]
      ring
    rw [hinside, ENNReal.ofReal_rpow_of_nonneg hbase (by positivity), hpower]
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hmomentNonneg _)]

  have hterm (t : Fin d → ℕ) :
      ENNReal.ofReal (((2:ℝ)^(r*∑ i : Fin d, (t i:ℝ)))^theta) *
        (ENNReal.ofReal (2 ^ max p theta *
          (nativeLayerVarianceEnvelope d n K C t)^(max p theta/2) *
          gaussianAbsoluteMoment (max p theta))^a) =
      ENNReal.ofReal (momentConst^a) *
        ENNReal.ofReal ((2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) *
          (nativeLayerVarianceEnvelope d n K C t)^(theta/2)) := by
    rw [hweight t, hmoment t]
    rw [ENNReal.ofReal_mul (by positivity :
      0 ≤ (2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)))]
    ac_rfl
  have hseries := nativeLayerVarianceEnvelope_theta_tsum_le_all
    d n K C r theta hK hr hgap htheta
  calc
    _ = ENNReal.ofReal (momentConst^a) *
        ∑' t : Fin d → ℕ,
          ENNReal.ofReal ((2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) *
            (nativeLayerVarianceEnvelope d n K C t)^(theta/2)) := by
          calc
            _ = ∑' t : Fin d → ℕ,
                ENNReal.ofReal (momentConst^a) *
                  ENNReal.ofReal ((2:ℝ)^(r*theta*∑ i : Fin d, (t i:ℝ)) *
                    (nativeLayerVarianceEnvelope d n K C t)^(theta/2)) := by
                  congr 1
                  funext t
                  exact hterm t
            _ = _ := ENNReal.tsum_mul_left
    _ ≤ ENNReal.ofReal (momentConst^a) * nativeThetaVarianceBound d n K C r theta :=
      mul_le_mul_of_nonneg_left hseries (by positivity)
    _ = _ := by rfl

/-- The expected Besov energy of the actual native finite Gaussian layer,
for arbitrary finite spatial and scale exponents `p,theta≥1`. -/
theorem nativeSmoothBesov_general_expected_energy_le
    (d n K : ℕ) (hK : 1 ≤ K) (C : ℝ)
    (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (p theta r : ℝ) (hp : 1 ≤ p) (htheta : 1 ≤ theta)
    (hr : 0 ≤ r) (hgap : 2*r < 2*(K:ℝ)-1) :
    (∫⁻ z : Fin (Fintype.card (LayerIndex d n)) → ℝ,
      smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal theta)
        (gaussianSynthesis (nativeFinAtoms d n) z)
      ∂productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) ≤
      (ENNReal.ofReal ((2 ^ max p theta *
        gaussianAbsoluteMoment (max p theta))^(theta/max p theta))) *
        nativeThetaVarianceBound d n K C r theta := by
  classical
  let V := nativeLayerVarianceEnvelope d n K C
  have hV : ∀ t : Fin d → ℕ, 0 ≤ V t := by
    intro t
    unfold V nativeLayerVarianceEnvelope
    apply Finset.sum_nonneg
    intro s hs
    apply Finset.prod_nonneg
    intro i hi
    unfold scalarVarianceEnvelope
    split_ifs <;> positivity
  have hvariance : ∀ (t : Fin d → ℕ) (x : UnitAddTorus (Fin d)),
      (∑ i : Fin (Fintype.card (LayerIndex d n)),
        ‖SmoothResolution.block t (nativeFinAtoms d n i) x‖^2) ≤ V t := by
    intro t x
    let e := Fintype.equivFin (LayerIndex d n)
    have hnative := nativeLayer_block_variance_le d n K hK C hC t x
    have hreindex :
        (∑ i : Fin (Fintype.card (LayerIndex d n)),
          ‖SmoothResolution.block t (nativeFinAtoms d n i) x‖^2) =
          ∑ a : LayerIndex d n,
            ‖SmoothResolution.block t (periodicNativeAtom a) x‖^2 := by
      exact e.symm.sum_comp (fun a =>
        ‖SmoothResolution.block t (periodicNativeAtom a) x‖^2)
    rw [hreindex]
    simpa [V] using hnative
  have hsummable := nativeLayerGeneralBesov_summability
    d n K C r p theta hK hr hgap hp htheta
  have hmean := BrownianSharp.smoothBesov_general_expected_energy_le
    p theta r hp htheta (nativeFinAtoms d n) V hV hvariance hsummable
  simpa [V] using hmean

end BrownianSharp.NativeLayerGeneralMean
