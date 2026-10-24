import BrownianSharp.GaussianUniformEvent
import BrownianSharp.CameronMartinRate
import BrownianSharp.ExtendedStatements

/-! Exact coefficient reindexing and scale identification for applying the
native confinement estimate to the Cameron--Martin entropy cover. -/
set_option maxHeartbeats 1600000
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp
open HaarQuarter

/-- The ambient Cameron--Martin evaluation coefficient is exactly the native
integrated Haar coefficient on the midpoint grid. -/
theorem nativeGridMatrix_midpoint {d n M : ℕ}
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (q : Fin M → MidpointGridIndex d n) (j : Fin M)
    (i : Fin (Fintype.card (LayerIndex d n))) :
    CameronMartinCover.nativeGridMatrix e (fun j => nativeMidpointBrownianAnchor (q j)) j i =
      nativeLayerRowCoefficient (q j) (e i) := rfl

/-- Reindexing the actual coefficient Gaussian preserves its full law. -/
theorem reindexNative_measurePreserving {d n : ℕ}
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n) :
    MeasurePreserving (CameronMartinCover.reindexNative e)
      (productStandardGaussian (Fin (Fintype.card (LayerIndex d n))))
      (productStandardGaussian (LayerIndex d n)) := by
  have hf : CameronMartinCover.reindexNative e =
      (MeasurableEquiv.piCongrLeft (fun _ : LayerIndex d n => ℝ) e) := by
    funext x a
    simp [CameronMartinCover.reindexNative, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft, Equiv.piCongrLeft']
  rw [hf]
  exact measurePreserving_piCongrLeft (α := fun _ : LayerIndex d n => ℝ)
    (fun _ => gaussianReal 0 1) e

/-- Exact equality of the finite evaluation-cube mass after the two finite
index equivalences. -/
theorem nativeGridMatrix_good_event_mass {d n : ℕ}
    (e : Fin (Fintype.card (LayerIndex d n)) ≃ LayerIndex d n)
    (v : Fin (Fintype.card (NativeGoodGrid d n)) ≃ NativeGoodGrid d n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))
      {x | ‖rowEvaluation (CameronMartinCover.nativeGridMatrix e
        (fun j => nativeMidpointBrownianAnchor (v j).val)) x‖ ≤ ε} =
    productStandardGaussian (LayerIndex d n) (nativeGoodUniformEvent d n ε) := by
  classical
  have hE : MeasurableSet (nativeGoodUniformEvent d n ε) := by
    unfold nativeGoodUniformEvent
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter (fun q => measurableSet_le (by fun_prop) measurable_const)
  have hset : {x | ‖rowEvaluation (CameronMartinCover.nativeGridMatrix e
        (fun j => nativeMidpointBrownianAnchor (v j).val)) x‖ ≤ ε} =
      (CameronMartinCover.reindexNative e) ⁻¹' nativeGoodUniformEvent d n ε := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [pi_norm_le_iff_of_nonneg hε]
    have hsum : ∀ j, rowEvaluation (CameronMartinCover.nativeGridMatrix e
        (fun j => nativeMidpointBrownianAnchor (v j).val)) x j =
        ∑ a, nativeLayerRowCoefficient (v j).val a * CameronMartinCover.reindexNative e x a := by
      intro j
      change (∑ i, nativeLayerRowCoefficient (v j).val (e i) * x i) = _
      apply Fintype.sum_equiv e
      intro i
      simp [CameronMartinCover.reindexNative]
    simp only [Real.norm_eq_abs, hsum, nativeGoodUniformEvent, Set.mem_setOf_eq]
    constructor
    · intro h q; simpa using h (v.symm q)
    · intro h j; exact h (v j)
  rw [hset]
  exact (reindexNative_measurePreserving e).measure_preimage hE.nullMeasurableSet

/-- The entropy application's notation is exactly the sharp native radius
at even total grade, with no change in the power of the shell count. -/
theorem sharpRadius_even_eq_periodicNativeRadius (d q : ℕ) (a : ℝ) :
    sharpRadius d a (2*q) = a * periodicNativeRadius d q (1/2) (1/2) := by
  have hpow : (2:ℝ)^(2*q) = ((2:ℝ)^q)^2 := by rw [mul_comm 2 q, pow_mul]
  have hroot : Real.sqrt ((2:ℝ)^(2*q)) = (2:ℝ)^q := by
    rw [hpow, Real.sqrt_sq (by positivity)]
  have hS : 0 ≤ hyperbolicCount d (2*q) := by unfold hyperbolicCount; positivity
  unfold sharpRadius periodicNativeRadius
  rw [Real.sqrt_div (mul_nonneg (Nat.cast_nonneg _) hS),
    Real.sqrt_mul (Nat.cast_nonneg _), hroot]
  have hexp : (-2:ℝ)*(1/2)*(q:ℝ) = -(q:ℝ) := by ring
  rw [hexp, Real.rpow_neg (by norm_num), Real.rpow_natCast]
  simp only [Real.sqrt_eq_rpow, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- The actual Cameron--Martin entropy lower order, conditional only on
Gaussian Ehrhard. All coefficient cutoff, covering, and index inputs are
proved for the restricted-cube integration image. -/
theorem cameronMartinEntropyLower_of_productGaussianEhrhard
    (hEhrhard : ProductGaussianEhrhard) {d : ℕ} (hd : 2 ≤ d) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k →
      ENNReal.ofReal (c * cmIndexRate d k) ≤
        HaarQuarter.TheoremD.entropyNumber k (CameronMartin.KdUnitCube d) := by
  obtain ⟨b, hb, hbound⟩ := nativeGoodUniform_confinement_all_grades_of_ehrhard hEhrhard hd
  let η := nativeRadiusConstant d (1/2) (nativeMomentSlope d)
  have hη : 0 < η := nativeRadiusConstant_pos d (by norm_num) (nativeMomentSlope_pos d)
  let M : ℕ → ℕ := fun q => Fintype.card (NativeGoodGrid d (2*q))
  let t : ∀ q : ℕ, Fin (M q) → BrownianCubeAnchor d := fun q j =>
    nativeMidpointBrownianAnchor
      (((Fintype.equivFin (NativeGoodGrid d (2*q))).symm j).val)
  have hconf : ∀ q : ℕ, 0 < q →
      productStandardGaussian (Fin (Fintype.card (LayerIndex d (2*q))))
        {x | ‖rowEvaluation (CameronMartinCover.nativeGridMatrix
          (Fintype.equivFin (LayerIndex d (2*q))).symm (t q)) x‖ ≤
          η * periodicNativeRadius d q (1/2) (1/2)} ≤
        ENNReal.ofReal (Real.exp (-b*(Fintype.card (LayerIndex d (2*q)):ℝ))) := by
    intro q hq
    have hε : 0 ≤ sharpRadius d η (2*q) := (sharpRadius_pos hd hη (by omega)).le
    rw [← sharpRadius_even_eq_periodicNativeRadius d q η]
    change productStandardGaussian _
      {x | ‖rowEvaluation (CameronMartinCover.nativeGridMatrix
        (Fintype.equivFin (LayerIndex d (2*q))).symm
        (fun j => nativeMidpointBrownianAnchor
          (((Fintype.equivFin (NativeGoodGrid d (2*q))).symm j).val))) x‖ ≤
        sharpRadius d η (2*q)} ≤ _
    rw [nativeGridMatrix_good_event_mass _ _ hε]
    have h := ENNReal.ofReal_le_ofReal (hbound (2*q) (by omega))
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
    have hcard : (Fintype.card (LayerIndex d (2*q)):ℝ) = nativeDimension d (2*q) := by
      rw [layerIndex_card d (2*q) (by omega)]
      simp [nativeDimension, hyperbolicCount]
    rw [hcard]
    exact h
  have hrate := CameronMartinRate.native_entropy_rate_of_exponential_confinement
    hd b hb η hη M t hconf
  refine ⟨(η/(2*(max 1 ⌈(2/b)⌉₊:ℝ))) * periodicNativeRateConstant d 1 0, ?_, ?_⟩
  · exact mul_pos (div_pos hη (by positivity)) (periodicNativeRateConstant_pos hd 1 0)
  · intro k hk
    simpa [cmIndexRate, logarithmicIndexRate, mul_assoc] using hrate k hk

end BrownianSharp
