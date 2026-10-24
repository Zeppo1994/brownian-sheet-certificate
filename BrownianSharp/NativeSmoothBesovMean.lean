import BrownianSharp.LayerBlockVariance
import BrownianSharp.SmoothBesovGaussianMean
import BrownianSharp.SmoothClassMeasurability

/-! Diagonal finite-theta Besov bound for the actual native Brownian layer
family, using its proved tensor variance envelope. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.PeriodicCover
open BrownianSharp.SmoothResolution
open BrownianSharp.LayerBlockVariance
open BrownianSharp.AtomicTensorFactorization

private def nativeBesovAtomsFin (d n : ℕ) :
    Fin (Fintype.card (LayerIndex d n)) → RealPeriodic d :=
  fun i => periodicNativeAtom ((Fintype.equivFin (LayerIndex d n)).symm i)

/-- Expected literal finite-theta Besov energy for the exact native layer
family in the diagonal case `theta = p >= 1`. The only numeric input is
summability of the explicit native variance-moment envelope. -/
theorem nativeSmoothBesov_equalExponent_expected_energy_le
    (d n K : ℕ) (hK : 1 ≤ K) (C : ℝ)
    (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (p r : ℝ) (hp : 1 ≤ p) {M : ℝ≥0∞}
    (hsummable : (∑' t : Fin d → ℕ,
      ENNReal.ofReal (((2 : ℝ) ^ (r * ∑ i, (t i : ℝ))) ^ p *
        (2 ^ p *
          (nativeLayerVarianceEnvelope d n K C t) ^ (p / 2) *
          gaussianAbsoluteMoment p))) ≤ M) :
    (∫⁻ z : Fin (Fintype.card (LayerIndex d n)) → ℝ,
      smoothBesovEnergy (ENNReal.ofReal p) r (ENNReal.ofReal p)
        (gaussianSynthesis (nativeBesovAtomsFin d n) z)
      ∂productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) ≤ M := by
  have hV : ∀ t : Fin d → ℕ, 0 ≤ nativeLayerVarianceEnvelope d n K C t := by
    intro t
    unfold nativeLayerVarianceEnvelope
    apply Finset.sum_nonneg
    intro s hs
    apply Finset.prod_nonneg
    intro i hi
    unfold scalarVarianceEnvelope
    split_ifs <;> positivity
  have hvariance : ∀ (t : Fin d → ℕ) (x : UnitAddTorus (Fin d)),
      (∑ i : Fin (Fintype.card (LayerIndex d n)),
        ‖block t (nativeBesovAtomsFin d n i) x‖ ^ 2) ≤
        nativeLayerVarianceEnvelope d n K C t := by
    intro t x
    let e := Fintype.equivFin (LayerIndex d n)
    have hnative := nativeLayer_block_variance_le d n K hK C hC t x
    have hreindex :
        (∑ i : Fin (Fintype.card (LayerIndex d n)),
          ‖block t (nativeBesovAtomsFin d n i) x‖ ^ 2) =
        ∑ a : LayerIndex d n, ‖block t (periodicNativeAtom a) x‖ ^ 2 := by
      classical
      unfold nativeBesovAtomsFin
      exact e.symm.sum_comp (fun a => ‖block t (periodicNativeAtom a) x‖ ^ 2)
    rw [hreindex]
    exact hnative
  have hmeas : ∀ t : Fin d → ℕ, Measurable (fun z :
      Fin (Fintype.card (LayerIndex d n)) → ℝ =>
        (SmoothResolution.weightedBlockNorm (ENNReal.ofReal p) r t
          (gaussianSynthesis (nativeBesovAtomsFin d n) z)) ^ p) := by
    intro t
    have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
    have hpenn0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
    have hpennTop : ENNReal.ofReal p ≠ ∞ := by simp
    have hnorm := smoothBlock_eLpNorm_gaussian_measurable t
      (nativeBesovAtomsFin d n) (ENNReal.ofReal p) hpenn0 hpennTop
    dsimp [SmoothResolution.weightedBlockNorm]
    exact (measurable_const.mul hnorm).pow_const p
  have hspatialMeas : ∀ t : Fin d → ℕ, Measurable (fun z :
      Fin (Fintype.card (LayerIndex d n)) → ℝ =>
        ∫⁻ x : UnitAddTorus (Fin d),
          ENNReal.ofReal (‖block t
            (gaussianSynthesis (nativeBesovAtomsFin d n) z) x‖ ^ p)
          ∂(volume : Measure (UnitAddTorus (Fin d)))) := by
    intro t
    have hjoint := smoothBlock_gaussian_joint_measurable t
      (nativeBesovAtomsFin d n)
    apply Measurable.lintegral_prod_right
    exact ENNReal.measurable_ofReal.comp
      (hjoint.norm.pow_const p)
  exact smoothBesov_equalExponent_expected_energy_le p r hp
    (nativeBesovAtomsFin d n) (nativeLayerVarianceEnvelope d n K C)
    hV hvariance hmeas hspatialMeas hsummable

end BrownianSharp
