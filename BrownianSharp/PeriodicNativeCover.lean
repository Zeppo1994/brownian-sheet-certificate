import BrownianSharp.SmoothGridConfinement
import BrownianSharp.CameronMartinNativeConfinement

/-! Actual finite periodic synthesis and its translated-ball cover obstruction. -/
set_option maxHeartbeats 1800000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp
open Torus HaarQuarter

/-- Continuous periodic native synthesis with the original layer indexing. -/
def periodicNativeSynthesisLinear {d n : ℕ} :
    (LayerIndex d n → ℝ) →ₗ[ℝ] RealPeriodic d where
  toFun x := ∑ a, x a • periodicNativeAtom a
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.smul_sum, smul_smul, mul_comm]

theorem periodicNativeSynthesisLinear_apply {d n : ℕ}
    (x : LayerIndex d n → ℝ) (z : UnitAddTorus (Fin d)) :
    periodicNativeSynthesisLinear x z = smoothPeriodicSynthesis x z := by
  simp [periodicNativeSynthesisLinear, smoothPeriodicSynthesis]

theorem periodicNativeSynthesis_reindex_scaled {d n : ℕ}
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (A : ℝ) (x : Fin (Fintype.card (LayerIndex d n)) → ℝ) :
    PeriodicCover.gaussianSynthesis (fun i => A • periodicNativeAtom (e i)) x =
      A • periodicNativeSynthesisLinear (CameronMartinCover.reindexNative e x) := by
  change (∑ i, x i • (A • periodicNativeAtom (e i))) = _
  rw [show A • periodicNativeSynthesisLinear (CameronMartinCover.reindexNative e x) =
      ∑ a, A • (CameronMartinCover.reindexNative e x a • periodicNativeAtom a) by
        simp [periodicNativeSynthesisLinear, Finset.smul_sum]]
  apply Fintype.sum_equiv e
  intro i
  simp [CameronMartinCover.reindexNative, smul_smul, mul_comm]

/-- The scaled finite periodic grid cube has exactly its unscaled good-grid
Gaussian mass, after both index equivalences are accounted for. -/
theorem periodicNative_scaled_good_event_mass {d n : ℕ}
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (v : Fin (Fintype.card (SmoothGoodGrid d n)) ≃ SmoothGoodGrid d n)
    {A ε : ℝ} (hA : 0 < A) (hε : 0 ≤ ε) :
    productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))
      {x | ‖PeriodicCover.synthesisGridMap (fun i => A • periodicNativeAtom (e i))
        (fun j => periodicMidpoint (v j).val) x‖ ≤ A*ε} =
    productStandardGaussian (LayerIndex d n) (smoothGoodUniformEvent d n ε) := by
  classical
  have hE : MeasurableSet (smoothGoodUniformEvent d n ε) := by
    unfold smoothGoodUniformEvent
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun q => measurableSet_le (by fun_prop) measurable_const)
  have hset : {x | ‖PeriodicCover.synthesisGridMap (fun i => A • periodicNativeAtom (e i))
        (fun j => periodicMidpoint (v j).val) x‖ ≤ A*ε} =
      (CameronMartinCover.reindexNative e) ⁻¹' smoothGoodUniformEvent d n ε := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [pi_norm_le_iff_of_nonneg (mul_nonneg hA.le hε)]
    have hrow : ∀ j, PeriodicCover.synthesisGridMap (fun i => A • periodicNativeAtom (e i))
        (fun j => periodicMidpoint (v j).val) x j =
        A * ∑ a, smoothLayerAtom smoothAtom (v j).val a * CameronMartinCover.reindexNative e x a := by
      intro j
      change (PeriodicCover.gaussianSynthesis _ x) _ = _
      rw [periodicNativeSynthesis_reindex_scaled]
      simp only [ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
        periodicNativeSynthesisLinear_apply, smoothPeriodicSynthesis_midpoint_eq]
    simp only [Real.norm_eq_abs, hrow, abs_mul, abs_of_pos hA,
      smoothGoodUniformEvent, Set.mem_setOf_eq]
    constructor
    · intro h q
      have hh : A * |∑ a, smoothLayerAtom smoothAtom q.val a * CameronMartinCover.reindexNative e x a| ≤ A*ε := by simpa using h (v.symm q)
      exact (mul_le_mul_iff_right₀ hA).mp hh
    · intro h j
      exact mul_le_mul_of_nonneg_left (h (v j)) hA.le
  rw [hset]
  exact (reindexNative_measurePreserving e).measure_preimage hE.nullMeasurableSet

/-- Every translated uniform ball has mass controlled by the actual centered
finite good-grid cube, including singular synthesis maps. -/
theorem periodicNative_ball_mass_le {d n : ℕ} (hd : 0<d)
    {A ε ρ : ℝ} (hA : 0<A) (hε : 0<ε) (hρ : 0≤ρ) (hρε : ρ≤A*ε)
    (Q : ℝ≥0∞)
    (hconf : productStandardGaussian (LayerIndex d n) (smoothGoodUniformEvent d n ε) ≤ Q)
    (f : RealPeriodic d) :
    productStandardGaussian (LayerIndex d n)
      {x | edist (A • periodicNativeSynthesisLinear x) f ≤ ENNReal.ofReal ρ} ≤ Q := by
  classical
  let e := (Fintype.equivFin (LayerIndex d n)).symm
  let v := (Fintype.equivFin (SmoothGoodGrid d n)).symm
  have hN : 0 < Fintype.card (LayerIndex d n) :=
    Fintype.card_pos_iff.mpr (nativeLayerIndex_nonempty d n hd)
  have hgrid : productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))
      {x | ‖PeriodicCover.synthesisGridMap (fun i => A • periodicNativeAtom (e i))
        (fun j => periodicMidpoint (v j).val) x‖ ≤ A*ε} ≤ Q := by
    rw [periodicNative_scaled_good_event_mass e v hA hε.le]
    exact hconf
  have hball := PeriodicCover.gaussianSynthesis_ball_mass_le hN
    (fun i => A • periodicNativeAtom (e i)) (fun j => periodicMidpoint (v j).val)
    ρ (A*ε) hρ hρε (mul_pos hA hε) Q hgrid f
  let E : Set (LayerIndex d n → ℝ) :=
    {x | edist (A • periodicNativeSynthesisLinear x) f ≤ ENNReal.ofReal ρ}
  have hF : Continuous (fun x : LayerIndex d n → ℝ => A • periodicNativeSynthesisLinear x) :=
    (LinearMap.continuous_of_finiteDimensional
      (periodicNativeSynthesisLinear (d := d) (n := n))).const_smul A
  have hE : MeasurableSet E := measurableSet_le (hF.measurable.edist measurable_const) measurable_const
  have hset : {x | edist (PeriodicCover.gaussianSynthesis
      (fun i => A • periodicNativeAtom (e i)) x) f ≤ ENNReal.ofReal ρ} =
      CameronMartinCover.reindexNative e ⁻¹' E := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, E]
    rw [periodicNativeSynthesis_reindex_scaled]
  rw [hset, (reindexNative_measurePreserving e).measure_preimage hE.nullMeasurableSet] at hball
  exact hball

/-- The periodic cover obstruction for any actual admissible coefficient
event. Class membership and its mass are displayed exactly; no L2 cutoff is
silently substituted for a smooth Besov or Sobolev norm event. -/
theorem periodicNative_externalCover_gt_of_class_mass {d n k : ℕ} (hd : 0<d)
    {A ε ρ : ℝ} (hA : 0<A) (hε : 0<ε) (hρ : 0≤ρ) (hρε : ρ≤A*ε)
    (K : Set (RealPeriodic d)) (E : Set (LayerIndex d n → ℝ)) (Q : ℝ≥0∞)
    (hclass : ∀ x ∈ E, A • periodicNativeSynthesisLinear x ∈ K)
    (hconf : productStandardGaussian (LayerIndex d n) (smoothGoodUniformEvent d n ε) ≤ Q)
    (hmass : ((2^(k-1):ℕ):ℝ≥0∞)*Q < productStandardGaussian (LayerIndex d n) E) :
    ((2^(k-1):ℕ):ℕ∞) < Metric.externalCoveringNumber ⟨ρ,hρ⟩ K := by
  apply externalCoveringNumber_gt_of_admissible_mass
    (productStandardGaussian (LayerIndex d n)) (fun x => A • periodicNativeSynthesisLinear x)
    E K ⟨ρ,hρ⟩ Q (2^(k-1)) hclass
  · intro f
    convert periodicNative_ball_mass_le (d := d) (n := n) hd hA hε hρ hρε Q hconf f using 1 <;>
      simp only [ENNReal.ofReal_eq_coe_nnreal hρ]
    congr 1
  · exact hmass

end BrownianSharp
