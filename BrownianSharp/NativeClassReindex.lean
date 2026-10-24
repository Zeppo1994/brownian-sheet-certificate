import BrownianSharp.PeriodicNativeCover
import BrownianSharp.SmoothScaledClassEvents

/-! Exact native coefficient reindexing for arbitrary actual function-class
events, using measurable equivalences so no Borel premise on the class is
needed for the outer-measure identity. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace BrownianSharp
open Torus PeriodicCover

def nativeFinAtoms (d n : ℕ) : Fin (Fintype.card (LayerIndex d n)) → RealPeriodic d :=
  fun i => periodicNativeAtom ((Fintype.equivFin (LayerIndex d n)).symm i)

theorem reindexNative_measure_preimage_any {d n : ℕ}
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (E : Set (LayerIndex d n → ℝ)) :
    productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))
      (CameronMartinCover.reindexNative e ⁻¹' E) =
      productStandardGaussian (LayerIndex d n) E := by
  have hf : CameronMartinCover.reindexNative e =
      (MeasurableEquiv.piCongrLeft (fun _ : LayerIndex d n => ℝ) e) := by
    funext x a
    simp [CameronMartinCover.reindexNative, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft, Equiv.piCongrLeft']
  have hemb : MeasurableEmbedding (CameronMartinCover.reindexNative e) := by
    rw [hf]
    exact (MeasurableEquiv.piCongrLeft (fun _ : LayerIndex d n => ℝ) e).measurableEmbedding
  have h := hemb.map_apply (productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) E
  rw [(reindexNative_measurePreserving e).map_eq] at h
  exact h.symm

theorem nativeFinSynthesis_reindex {d n : ℕ}
    (z : Fin (Fintype.card (LayerIndex d n)) → ℝ) :
    gaussianSynthesis (nativeFinAtoms d n) z = periodicNativeSynthesisLinear
      (CameronMartinCover.reindexNative (Fintype.equivFin (LayerIndex d n)).symm z) := by
  have h := periodicNativeSynthesis_reindex_scaled
    (Fintype.equivFin (LayerIndex d n)).symm 1 z
  change gaussianSynthesis (fun i => periodicNativeAtom
    ((Fintype.equivFin (LayerIndex d n)).symm i)) z = _
  simpa only [one_smul] using h

theorem native_scaled_class_mass_reindex {d n : ℕ} (A : ℝ) (K : Set (RealPeriodic d)) :
    productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))
      {z | A • gaussianSynthesis (nativeFinAtoms d n) z ∈ K} =
    productStandardGaussian (LayerIndex d n)
      {x | A • periodicNativeSynthesisLinear x ∈ K} := by
  have hset : {z | A • gaussianSynthesis (nativeFinAtoms d n) z ∈ K} =
      CameronMartinCover.reindexNative (Fintype.equivFin (LayerIndex d n)).symm ⁻¹'
        {x | A • periodicNativeSynthesisLinear x ∈ K} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_preimage, nativeFinSynthesis_reindex]
  rw [hset, reindexNative_measure_preimage_any]

/-- A literal Sobolev energy bound for the finite Gaussian synthesis gives
actual native class mass after exact normalization. -/
theorem nativeSobolev_scaled_unitBall_mass_of_mean {d n : ℕ}
    (p r : ℝ) (hp : 0 ≤ p) {A : ℝ} (hA : 0 < A)
    {M : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hmean : (∫⁻ z : Fin (Fintype.card (LayerIndex d n)) → ℝ,
      (∫⁻ x : UnitAddTorus (Fin d),
        (SmoothResolution.squareFunctionSquared r
          (gaussianSynthesis (nativeFinAtoms d n) z) x)^(p/2))
      ∂productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) ≤ M)
    (hscale : ENNReal.ofReal (A^p)*(2*M) ≤ 1) :
    (1/2:ℝ≥0∞) ≤ productStandardGaussian (LayerIndex d n)
      {x | SmoothResolution.SobolevUnitBall p r (A • periodicNativeSynthesisLinear x)} := by
  change (1/2:ℝ≥0∞) ≤ productStandardGaussian (LayerIndex d n)
    {x | A • periodicNativeSynthesisLinear x ∈
      {f : RealPeriodic d | SmoothResolution.SobolevUnitBall p r f}}
  rw [← native_scaled_class_mass_reindex (d:=d) (n:=n) A
    {f : RealPeriodic d | SmoothResolution.SobolevUnitBall p r f}]
  exact smoothSobolev_scaled_unitBall_mass _ p r hp
    (fun z => gaussianSynthesis (nativeFinAtoms d n) z) hA hM hMtop
    (smoothSobolevEnergy_gaussian_measurable p r _) hmean hscale

theorem nativeBesov_scaled_unitBall_mass_of_mean {d n : ℕ}
    (p : ℝ≥0∞) (hp0 : p ≠ 0) (hpTop : p ≠ ∞) (r : ℝ)
    {θ : ℝ≥0∞} (hθ : θ ≠ ∞) {A : ℝ} (hA : 0 < A)
    {M : ℝ≥0∞} (hM : 0 < M) (hMtop : M ≠ ∞)
    (hmean : (∫⁻ z : Fin (Fintype.card (LayerIndex d n)) → ℝ,
      smoothBesovEnergy p r θ (gaussianSynthesis (nativeFinAtoms d n) z)
      ∂productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) ≤ M)
    (hscale : ENNReal.ofReal (A^θ.toReal)*(2*M) ≤ 1) :
    (1/2:ℝ≥0∞) ≤ productStandardGaussian (LayerIndex d n)
      {x | SmoothResolution.BesovUnitBall p r θ (A • periodicNativeSynthesisLinear x)} := by
  change (1/2:ℝ≥0∞) ≤ productStandardGaussian (LayerIndex d n)
    {x | A • periodicNativeSynthesisLinear x ∈
      {f : RealPeriodic d | SmoothResolution.BesovUnitBall p r θ f}}
  rw [← native_scaled_class_mass_reindex (d:=d) (n:=n) A
    {f : RealPeriodic d | SmoothResolution.BesovUnitBall p r θ f}]
  exact smoothBesov_scaled_unitBall_mass _ p r hθ
    (fun z => gaussianSynthesis (nativeFinAtoms d n) z) hA hM hMtop
    (smoothBesovEnergy_gaussian_measurable _ p hp0 hpTop r θ) hmean hscale

end BrownianSharp
