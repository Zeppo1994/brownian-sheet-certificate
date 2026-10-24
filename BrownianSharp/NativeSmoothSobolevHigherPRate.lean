import BrownianSharp.NativeEnergyRate
import BrownianSharp.NativeLayerBudget
import BrownianSharp.NativeSmoothSobolevLowerPMean
import BrownianSharp.SmoothSobolevHigherPMean
import Mathlib.Basic.Denumerable

/-! Native expected-energy rates for every Sobolev exponent p>1. The only
stochastic input beyond the proved native variance envelope is the actual
Gaussian block moment; the scale-lattice series is handled by Minkowski. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BrownianSharp

open Torus PeriodicCover SmoothResolution LayerBlockVariance NativeLayerBudget
open AtomicTensorFactorization

private def nativeHigherAtomsFin (d n : ℕ) :
    Fin (Fintype.card (LayerIndex d n)) → RealPeriodic d := nativeFinAtoms d n

private theorem nativeHigherVarianceEnvelope_nonneg (d n K : ℕ) (C : ℝ)
    (t : Fin d → ℕ) : 0 ≤ nativeLayerVarianceEnvelope d n K C t := by
  unfold nativeLayerVarianceEnvelope
  apply Finset.sum_nonneg
  intro s hs
  apply Finset.prod_nonneg
  intro i hi
  unfold scalarVarianceEnvelope
  split_ifs <;> positivity

private theorem nativeHigherVariance (d n K : ℕ) (hK : 1 ≤ K) (C : ℝ)
    (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (t : Fin d → ℕ) (x : UnitAddTorus (Fin d)) :
    (∑ i : Fin (Fintype.card (LayerIndex d n)),
      ‖block t (nativeHigherAtomsFin d n i) x‖ ^ 2) ≤
        nativeLayerVarianceEnvelope d n K C t := by
  let e := Fintype.equivFin (LayerIndex d n)
  have hnative := nativeLayer_block_variance_le d n K hK C hC t x
  have hreindex :
      (∑ i : Fin (Fintype.card (LayerIndex d n)),
        ‖block t (nativeHigherAtomsFin d n i) x‖ ^ 2) =
      ∑ a : LayerIndex d n, ‖block t (periodicNativeAtom a) x‖ ^ 2 := by
    classical
    unfold nativeHigherAtomsFin nativeFinAtoms
    exact e.symm.sum_comp (fun a => ‖block t (periodicNativeAtom a) x‖ ^ 2)
  rw [hreindex]
  exact hnative

/-- The native literal Sobolev square-function moment at p≥2, with an
explicit constant depending on the smooth-atom derivative order but not on
the layer grade n. -/
theorem nativeSmoothSobolev_higherP_expected_energy_rate
    (d n K : ℕ) (hd : 1 ≤ d) (hK : 1 ≤ K) (C : ℝ)
    (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (p r : ℝ) (hp2 : 2 ≤ p) (hr : 0 ≤ r)
    (hgap : 2 * r < 2 * (K : ℝ) - 1) :
    (∫⁻ z : Fin (Fintype.card (LayerIndex d n)) → ℝ,
      ∫⁻ x : UnitAddTorus (Fin d),
        (squareFunctionSquared r
          (gaussianSynthesis (nativeHigherAtomsFin d n) z) x) ^ (p / 2)
        ∂(volume : Measure (UnitAddTorus (Fin d)))
      ∂productStandardGaussian (Fin (Fintype.card (LayerIndex d n)))) ≤
      ENNReal.ofReal ((4 * gaussianAbsoluteMoment p ^ (2 / p) *
        scalarLayerBudget C r K ^ d) ^ (p / 2) *
        (nativeClassNormScale d n r (1 / 2)) ^ p) := by
  classical
  let atoms := nativeHigherAtomsFin d n
  let V := nativeLayerVarianceEnvelope d n K C
  have hV : ∀ t, 0 ≤ V t := nativeHigherVarianceEnvelope_nonneg d n K C
  have hvariance := fun t x => nativeHigherVariance d n K hK C hC t x
  have hbase := nativeLayerVarianceEnvelope_weighted_tsum_le d n K C r hK hr hgap
  let A : ℝ := 4 * gaussianAbsoluteMoment p ^ (2 / p)
  have hBnonneg : 0 ≤ scalarLayerBudget C r K := by
    unfold scalarLayerBudget scalarTailRatio
    have hq : (2 : ℝ) ^ (2 * r - (2 * (K : ℝ) - 1)) < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      linarith
    have hden : 0 < 1 - (2 : ℝ) ^ (2 * r - (2 * (K : ℝ) - 1)) := sub_pos.mpr hq
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    have hm : 0 ≤ gaussianAbsoluteMoment p := by
      unfold gaussianAbsoluteMoment
      exact integral_nonneg fun _ => by positivity
    positivity
  have hsummable :
      (∑' t : Fin d → ℕ, ENNReal.ofReal
        ((2 : ℝ) ^ (2 * r * ∑ i, (t i : ℝ)) *
          (4 * V t * gaussianAbsoluteMoment p ^ (2 / p)))) ≤
        ENNReal.ofReal (A * (Fintype.card (Shape d n) : ℝ) *
          (scalarLayerBudget C r K ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ)))) := by
    have hterm (t : Fin d → ℕ) :
        ENNReal.ofReal ((2 : ℝ) ^ (2 * r * ∑ i, (t i : ℝ)) *
          (4 * V t * gaussianAbsoluteMoment p ^ (2 / p))) =
        ENNReal.ofReal A * ENNReal.ofReal
          ((2 : ℝ) ^ (2 * r * ∑ i, (t i : ℝ)) * V t) := by
      rw [← ENNReal.ofReal_mul hA]
      congr 1
      dsimp [A]
      ring
    calc
      _ = ENNReal.ofReal A *
          (∑' t : Fin d → ℕ, ENNReal.ofReal
            ((2 : ℝ) ^ (2 * r * ∑ i, (t i : ℝ)) * V t)) := by
          simp_rw [hterm]
          rw [ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal A *
          ((Fintype.card (Shape d n) : ℝ≥0∞) *
            ENNReal.ofReal (scalarLayerBudget C r K ^ d * (2 : ℝ) ^
              (2 * r * (n : ℝ)))) := by gcongr
      _ = ENNReal.ofReal (A * (Fintype.card (Shape d n) : ℝ) *
          (scalarLayerBudget C r K ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ)))) := by
          rw [show (Fintype.card (Shape d n) : ℝ≥0∞) =
            ENNReal.ofReal (Fintype.card (Shape d n) : ℝ) by norm_num]
          let X : ℝ := (Fintype.card (Shape d n) : ℝ) *
            (scalarLayerBudget C r K ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ)))
          have hX : 0 ≤ X := by dsimp [X]; positivity [hBnonneg]
          calc
            ENNReal.ofReal A *
                (ENNReal.ofReal (Fintype.card (Shape d n) : ℝ) *
                  ENNReal.ofReal (scalarLayerBudget C r K ^ d *
                    (2 : ℝ) ^ (2 * r * (n : ℝ))))
              = ENNReal.ofReal A * ENNReal.ofReal X := by
                  change ENNReal.ofReal A *
                    (ENNReal.ofReal (Fintype.card (Shape d n) : ℝ) *
                      ENNReal.ofReal (scalarLayerBudget C r K ^ d *
                        (2 : ℝ) ^ (2 * r * (n : ℝ)))) = _
                  rw [← ENNReal.ofReal_mul (by positivity :
                    0 ≤ (Fintype.card (Shape d n) : ℝ))]
            _ = ENNReal.ofReal (A * X) := (ENNReal.ofReal_mul hA).symm
            _ = ENNReal.ofReal (A * (Fintype.card (Shape d n) : ℝ) *
                (scalarLayerBudget C r K ^ d * (2 : ℝ) ^
                  (2 * r * (n : ℝ)))) := by congr 1 <;> dsimp [X] <;> ring
  letI : Infinite (Fin d → ℕ) := Infinite.of_injective
    (fun m : ℕ => fun _ : Fin d => m) (by
      intro a b h
      have i : Fin d := ⟨0, by omega⟩
      exact congrFun h i)
  letI : Denumerable (Fin d → ℕ) := Denumerable.ofEncodableOfInfinite _
  let enum : ℕ ≃ (Fin d → ℕ) := (Denumerable.eqv (Fin d → ℕ)).symm
  have henergy := smoothSobolev_higherP_expected_energy_le p r hp2 atoms V hV
    hvariance enum hsummable
  have hshapeCard : (Fintype.card (Shape d n) : ℝ) = hyperbolicCount d n := by
    unfold hyperbolicCount
    exact_mod_cast shape_card d n (by omega)
  have hmom : 0 ≤ gaussianAbsoluteMoment p := by
    unfold gaussianAbsoluteMoment
    exact integral_nonneg fun _ => by positivity
  have hApos : 0 ≤ 4 * gaussianAbsoluteMoment p ^ (2 / p) := by positivity
  have hcount_nonneg : 0 ≤ hyperbolicCount d n := by rw [← hshapeCard]; positivity
  have hreal_nonneg : 0 ≤ A * hyperbolicCount d n *
      (scalarLayerBudget C r K ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ))) := by
    dsimp [A]
    apply mul_nonneg
    · apply mul_nonneg
      · exact mul_nonneg (by norm_num) (Real.rpow_nonneg hmom _)
      · exact hcount_nonneg
    · exact mul_nonneg (pow_nonneg hBnonneg _) (by positivity)
  have hreal_nonneg' : 0 ≤ A * (Fintype.card (Shape d n) : ℝ) *
      (scalarLayerBudget C r K ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ))) := by
    rw [hshapeCard]
    exact hreal_nonneg
  have hscale_sq : (nativeClassNormScale d n r (1 / 2)) ^ 2 =
      hyperbolicCount d n * (2 : ℝ) ^ (2 * r * (n : ℝ)) := by
    unfold nativeClassNormScale
    have hpow : (hyperbolicCount d n ^ (1 / 2 : ℝ)) ^ 2 = hyperbolicCount d n := by
      rw [show (hyperbolicCount d n ^ (1 / 2 : ℝ)) ^ 2 =
        (hyperbolicCount d n ^ (1 / 2 : ℝ)) ^ (2 : ℝ) by
          rw [← Real.rpow_natCast]; norm_num]
      rw [← Real.rpow_mul hcount_nonneg]
      norm_num
    have hpow2 : ((2 : ℝ) ^ (r * (n : ℝ))) ^ 2 =
        (2 : ℝ) ^ (2 * r * (n : ℝ)) := by
      rw [show ((2 : ℝ) ^ (r * (n : ℝ))) ^ 2 =
        ((2 : ℝ) ^ (r * (n : ℝ))) ^ (2 : ℝ) by
          rw [← Real.rpow_natCast]; norm_num]
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (2 : ℝ))]
      congr 1 <;> ring
    rw [mul_pow, hpow, hpow2]
    ring
  have hM_eq : A * (Fintype.card (Shape d n) : ℝ) *
      (scalarLayerBudget C r K ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ))) =
      (4 * gaussianAbsoluteMoment p ^ (2 / p) * scalarLayerBudget C r K ^ d) *
        (nativeClassNormScale d n r (1 / 2)) ^ 2 := by
    rw [hshapeCard, hscale_sq]
    dsimp [A]
    ring
  have hpow :
      ENNReal.ofReal (A * (Fintype.card (Shape d n) : ℝ) *
        (scalarLayerBudget C r K ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ)))) ^ (p / 2) =
      ENNReal.ofReal ((A * (Fintype.card (Shape d n) : ℝ) *
        (scalarLayerBudget C r K ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ)))) ^ (p / 2)) :=
    ENNReal.ofReal_rpow_of_nonneg hreal_nonneg' (by linarith)
  calc
    _ ≤ (ENNReal.ofReal (A * (Fintype.card (Shape d n) : ℝ) *
      (scalarLayerBudget C r K ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ))))) ^ (p / 2) := by
        simpa [atoms, V] using henergy
    _ = ENNReal.ofReal ((A * (Fintype.card (Shape d n) : ℝ) *
        (scalarLayerBudget C r K ^ d * (2 : ℝ) ^ (2 * r * (n : ℝ)))) ^ (p / 2)) := hpow
    _ = ENNReal.ofReal ((4 * gaussianAbsoluteMoment p ^ (2 / p) *
        scalarLayerBudget C r K ^ d) ^ (p / 2) *
        (nativeClassNormScale d n r (1 / 2)) ^ p) := by
          congr 1
          rw [hM_eq]
          rw [Real.mul_rpow (by positivity : 0 ≤
            4 * gaussianAbsoluteMoment p ^ (2 / p) * scalarLayerBudget C r K ^ d)
            (sq_nonneg (nativeClassNormScale d n r (1 / 2)))]
          have hL : 0 < nativeClassNormScale d n r (1 / 2) :=
            nativeClassNormScale_pos hd r (1 / 2)
          have hLpow : (nativeClassNormScale d n r (1 / 2) ^ 2) ^ (p / 2) =
              nativeClassNormScale d n r (1 / 2) ^ p := by
            rw [show nativeClassNormScale d n r (1 / 2) ^ 2 =
              nativeClassNormScale d n r (1 / 2) ^ (2 : ℝ) by
                rw [← Real.rpow_natCast]; norm_num]
            rw [← Real.rpow_mul (le_of_lt hL)]
            congr 1 <;> ring
          rw [hLpow]

end BrownianSharp
