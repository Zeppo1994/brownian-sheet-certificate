import BrownianSharp.LayerBlockVariance
import BrownianSharp.SmoothSobolevLowerPMean

/-! Native-layer specialization of the Jensen transfer from p=2 to
`1≤p<2` for the literal smooth Sobolev square function. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.PeriodicCover
open BrownianSharp.SmoothResolution
open BrownianSharp.LayerBlockVariance
open BrownianSharp.AtomicTensorFactorization

private def nativeLowerPAtomsFin (d n : ℕ) :
    Fin (Fintype.card (LayerIndex d n)) → RealPeriodic d :=
  fun i => periodicNativeAtom ((Fintype.equivFin (LayerIndex d n)).symm i)

private theorem nativeLayerVarianceEnvelope_nonneg (d n K : ℕ) (C : ℝ)
    (t : Fin d → ℕ) : 0 ≤ nativeLayerVarianceEnvelope d n K C t := by
  unfold nativeLayerVarianceEnvelope
  apply Finset.sum_nonneg
  intro s hs
  apply Finset.prod_nonneg
  intro i hi
  unfold scalarVarianceEnvelope
  split_ifs <;> positivity

private theorem nativeLowerP_variance (d n K : ℕ) (hK : 1 ≤ K) (C : ℝ)
    (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (t : Fin d → ℕ) (x : UnitAddTorus (Fin d)) :
    (∑ i : Fin (Fintype.card (LayerIndex d n)),
      ‖block t (nativeLowerPAtomsFin d n i) x‖ ^ 2) ≤
      nativeLayerVarianceEnvelope d n K C t := by
  let e := Fintype.equivFin (LayerIndex d n)
  have hnative := nativeLayer_block_variance_le d n K hK C hC t x
  have hreindex :
      (∑ i : Fin (Fintype.card (LayerIndex d n)),
        ‖block t (nativeLowerPAtomsFin d n i) x‖ ^ 2) =
      ∑ a : LayerIndex d n, ‖block t (periodicNativeAtom a) x‖ ^ 2 := by
    classical
    unfold nativeLowerPAtomsFin
    exact e.symm.sum_comp (fun a => ‖block t (periodicNativeAtom a) x‖ ^ 2)
  rw [hreindex]
  exact hnative

/-- Expected literal Sobolev energy for the native Brownian layer family at
`1≤p<2`, by Jensen from the p=2 native variance budget. -/
theorem nativeSmoothSobolev_lowerP_expected_energy_le
    (d n K : ℕ) (hK : 1 ≤ K) (C : ℝ)
    (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (p r : ℝ) (hp : 1 ≤ p) (hp2 : p < 2) {M : ℝ≥0∞}
    (hsummable : (∑' t : Fin d → ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (t i : ℝ)) *
        (4 * nativeLayerVarianceEnvelope d n K C t * gaussianAbsoluteMoment 2))) ≤ M) :
    (∫⁻ z : Fin (Fintype.card (LayerIndex d n)) → ℝ,
      ∫⁻ x : UnitAddTorus (Fin d),
        (squareFunctionSquared r
          (gaussianSynthesis (nativeLowerPAtomsFin d n) z) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d)))
      ∂productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) ≤ M ^ (p / 2) := by
  apply smoothSobolev_lowerP_expected_energy_le p r hp hp2
    (nativeLowerPAtomsFin d n) (nativeLayerVarianceEnvelope d n K C)
    (nativeLayerVarianceEnvelope_nonneg d n K C)
    (fun t x => nativeLowerP_variance d n K hK C hC t x) hsummable

/-- Half-mass for the literal native smooth Sobolev p-unit ball when the
rescaled p=2 native variance budget is at most one half. -/
theorem nativeSmoothSobolev_lowerP_unitBall_mass
    (d n K : ℕ) (hK : 1 ≤ K) (C : ℝ)
    (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (p r : ℝ) (hp : 1 ≤ p) (hp2 : p < 2) {M : ℝ≥0∞}
    (hsummable : (∑' t : Fin d → ℕ,
      ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (t i : ℝ)) *
        (4 * nativeLayerVarianceEnvelope d n K C t * gaussianAbsoluteMoment 2))) ≤ M)
    (hsmall : M ^ (p / 2) ≤ 1 / 2) :
    (1 / 2 : ℝ≥0∞) ≤
      (productStandardGaussian (Fin (Fintype.card (LayerIndex d n))))
        {z | SobolevUnitBall p r (gaussianSynthesis (nativeLowerPAtomsFin d n) z)} := by
  have hV : ∀ t : Fin d → ℕ, 0 ≤ nativeLayerVarianceEnvelope d n K C t :=
    nativeLayerVarianceEnvelope_nonneg d n K C
  have hvariance : ∀ (t : Fin d → ℕ) (x : UnitAddTorus (Fin d)),
      (∑ i : Fin (Fintype.card (LayerIndex d n)),
        ‖block t (nativeLowerPAtomsFin d n i) x‖ ^ 2) ≤
        nativeLayerVarianceEnvelope d n K C t :=
    fun t x => nativeLowerP_variance d n K hK C hC t x
  have hmeas := smoothSobolevEnergy_gaussian_measurable p r
    (nativeLowerPAtomsFin d n)
  have hmean := nativeSmoothSobolev_lowerP_expected_energy_le
    d n K hK C hC p r hp hp2 hsummable
  exact smoothSobolevUnitBall_mass_of_mean_le_half
    (productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) p r
    (fun z => gaussianSynthesis (nativeLowerPAtomsFin d n) z) hmeas
    (hmean.trans hsmall)

end BrownianSharp
