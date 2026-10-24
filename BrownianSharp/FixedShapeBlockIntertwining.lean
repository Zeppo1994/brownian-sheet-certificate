import BrownianSharp.FixedShapeDerivativeLp
import BrownianSharp.FixedShapeBlockLp
import BrownianSharp.AtomicTensorFactorization
import BrownianSharp.PeriodicAtomDerivatives
import BrownianSharp.ScalarHighFrequency
import Mathlib.Analysis.Fourier.AddCircleMulti

/-! Exact coefficient identity for coordinatewise inverse derivatives on a
fixed rectangular atom family. This is the deterministic Fourier bridge from
the original synthesis to its mixed derivative synthesis. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AtomicTensorFactorization
open BrownianSharp.AtomicTensorVariance
open BrownianSharp.ScalarAtomVariance
open BrownianSharp.PeriodicCover
open BrownianSharp.ScalarHighFrequency
open UnitAddTorus

/-- Fourier coefficients of a tensor derivative atom factor coordinatewise. -/
theorem fixedShapeDerivativeAtom_fourierCoeff_eq_prod {d : ℕ}
    (s k : Fin d → ℕ) (j : DyadicShapeCell d s) (n : Fin d → ℤ) :
    realPeriodicFourierCoeff
        ⟨dyadicShapeDerivativeAtom s k j,
          by
            change Continuous (fun x : UnitAddTorus (Fin d) =>
              ∏ i : Fin d, periodizedDyadicAtomDerivative1
                (s i) (j i).val (j i).isLt (k i) (x i))
            exact continuous_finsetProd Finset.univ fun i hi =>
              (periodizedDyadicAtomDerivative1 (s i) (j i).val
                (j i).isLt (k i)).continuous.comp (continuous_apply i)⟩ n =
      ∏ i : Fin d,
        fourierCoeff
          (fun x : UnitAddCircle =>
            (periodizedDyadicAtomDerivative1 (s i) (j i).val
              (j i).isLt (k i) x : ℂ)) (n i) := by
  classical
  unfold realPeriodicFourierCoeff complexifyRealPeriodic UnitAddTorus.mFourierCoeff
  simp only [ContinuousMap.coe_mk]
  have hfun :
      (fun x : UnitAddTorus (Fin d) =>
        UnitAddTorus.mFourier (-n) x •
          (dyadicShapeDerivativeAtom s k j x : ℂ)) =
      fun x => ∏ i : Fin d,
        (fourier (-(n i)) (x i) •
          (periodizedDyadicAtomDerivative1 (s i) (j i).val
            (j i).isLt (k i) (x i) : ℂ)) := by
    funext x
    simp [UnitAddTorus.mFourier, dyadicShapeDerivativeAtom,
      smul_eq_mul, Finset.prod_mul_distrib]
  rw [hfun]
  change (∫ x : (i : Fin d) → UnitAddCircle,
      ∏ i : Fin d,
        (fourier (-(n i)) (x i) •
          (periodizedDyadicAtomDerivative1 (s i) (j i).val
            (j i).isLt (k i) (x i) : ℂ))
      ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) = _
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun i y => fourier (-(n i)) y •
      (periodizedDyadicAtomDerivative1 (s i) (j i).val
        (j i).isLt (k i) y : ℂ))]
  apply Finset.prod_congr rfl
  intro i hi
  simp [fourierCoeff, fourier, smul_eq_mul]

/-- The Fourier coefficient of a finite fixed-shape derivative synthesis is
the corresponding finite coefficient sum. -/
theorem fixedShapeDerivativeSynthesis_fourierCoeff_eq_sum {d : ℕ}
    (s k : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ) (n : Fin d → ℤ) :
    realPeriodicFourierCoeff (fixedShapeDerivativeSynthesis s k c) n =
      ∑ j : DyadicShapeCell d s,
        (c j : ℂ) *
          ∏ i : Fin d,
            fourierCoeff
              (fun x : UnitAddCircle =>
                (periodizedDyadicAtomDerivative1 (s i) (j i).val
                  (j i).isLt (k i) x : ℂ)) (n i) := by
  classical
  unfold realPeriodicFourierCoeff complexifyRealPeriodic UnitAddTorus.mFourierCoeff
  change (∫ x : UnitAddTorus (Fin d),
      UnitAddTorus.mFourier (-n) x •
        ((∑ j : DyadicShapeCell d s,
          c j * dyadicShapeDerivativeAtom s k j x : ℝ) : ℂ)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) = _
  have hfun :
      (fun x : UnitAddTorus (Fin d) =>
        UnitAddTorus.mFourier (-n) x •
          ((∑ j : DyadicShapeCell d s,
            c j * dyadicShapeDerivativeAtom s k j x : ℝ) : ℂ)) =
      fun x => ∑ j : DyadicShapeCell d s,
        (c j : ℂ) *
          (UnitAddTorus.mFourier (-n) x *
            (dyadicShapeDerivativeAtom s k j x : ℂ)) := by
    funext x
    simp only [smul_eq_mul, Complex.ofReal_sum, Complex.ofReal_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hfun, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [show (fun x : UnitAddTorus (Fin d) =>
      (c j : ℂ) * (UnitAddTorus.mFourier (-n) x *
        (dyadicShapeDerivativeAtom s k j x : ℂ))) =
        fun x => (c j : ℂ) *
          (UnitAddTorus.mFourier (-n) x *
            (dyadicShapeDerivativeAtom s k j x : ℂ)) by rfl]
    rw [integral_const_mul]
    change (c j : ℂ) *
      realPeriodicFourierCoeff
        ⟨dyadicShapeDerivativeAtom s k j, by
          change Continuous (fun x : UnitAddTorus (Fin d) =>
            ∏ i : Fin d, periodizedDyadicAtomDerivative1
              (s i) (j i).val (j i).isLt (k i) (x i))
          exact continuous_finsetProd Finset.univ fun i hi =>
            (periodizedDyadicAtomDerivative1 (s i) (j i).val
              (j i).isLt (k i)).continuous.comp (continuous_apply i)⟩ n = _
    rw [fixedShapeDerivativeAtom_fourierCoeff_eq_prod]
  · intro j hj
    have hc : Continuous (fun x : UnitAddTorus (Fin d) =>
      UnitAddTorus.mFourier (-n) x *
        (dyadicShapeDerivativeAtom s k j x : ℂ)) := by
      exact (UnitAddTorus.mFourier (-n)).continuous.mul
        (Complex.continuous_ofReal.comp (continuous_finsetProd Finset.univ fun i hi =>
          (periodizedDyadicAtomDerivative1 (s i) (j i).val
            (j i).isLt (k i)).continuous.comp (continuous_apply i)))
    exact (continuous_const.mul hc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/-- Mixed multiplier coefficient: low coordinates retain their block
multiplier; differentiated coordinates use the inverse derivative symbol. -/
def fixedShapeMixedSymbol {d : ℕ} (t k : Fin d → ℕ) (n : Fin d → ℤ) : ℂ :=
  ∏ i : Fin d, if k i = 0 then
    (scalarBlock (t i) (n i : ℝ) : ℂ)
  else inverseMultiplier (t i) (k i) (n i)

/-- The original block multiplier times the original synthesis coefficient is
exactly the mixed inverse-derivative multiplier times the derivative
synthesis coefficient. -/
theorem fixedShapeMixed_fourierCoeff_identity {d : ℕ}
    (s t k : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ) (n : Fin d → ℤ)
    (hscale : ∀ i, k i = 0 ∨ (0 < t i ∧ 0 < k i ∧ Even (k i))) :
    tensorMultiplier t n * realPeriodicFourierCoeff (fixedShapeSynthesis s c) n =
      fixedShapeMixedSymbol t k n *
        realPeriodicFourierCoeff (fixedShapeDerivativeSynthesis s k c) n := by
  classical
  rw [fixedShapeDerivativeSynthesis_fourierCoeff_eq_sum]
  have hbase :
      realPeriodicFourierCoeff (fixedShapeSynthesis s c) n =
        ∑ j : DyadicShapeCell d s,
          (c j : ℂ) * ∏ i : Fin d,
            fourierCoeff
              (fun x : UnitAddCircle =>
                (periodizedDyadicAtomDerivative1 (s i) (j i).val
                  (j i).isLt 0 x : ℂ)) (n i) := by
    simpa [fixedShapeSynthesis, fixedShapeDerivativeSynthesis,
      dyadicShapeDerivativeAtom] using
      (fixedShapeDerivativeSynthesis_fourierCoeff_eq_sum
        s (fun _ => 0) c n)
  rw [hbase]
  rw [tensorMultiplier, fixedShapeMixedSymbol]
  rw [Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hcoord (i : Fin d) :
      (scalarBlock (t i) (n i : ℝ) : ℂ) *
          fourierCoeff
            (fun x : UnitAddCircle =>
              (periodizedDyadicAtomDerivative1 (s i) (j i).val
                (j i).isLt 0 x : ℂ)) (n i) =
        (if k i = 0 then (scalarBlock (t i) (n i : ℝ) : ℂ)
          else inverseMultiplier (t i) (k i) (n i)) *
          fourierCoeff
            (fun x : UnitAddCircle =>
              (periodizedDyadicAtomDerivative1 (s i) (j i).val
                (j i).isLt (k i) x : ℂ)) (n i) := by
    rcases hscale i with hk | ⟨hti, hki_pos, hki⟩
    · simp [hk]
    · have hk0 : k i ≠ 0 := by omega
      by_cases hn : n i = 0
      · simp [hn, hk0, inverseMultiplier, scalarBlock_zero (t i) hti]
      · rw [periodizedDyadicAtomDerivative1_fourier_eq_pow
        (s i) (j i).val (j i).isLt (k i) (n i) hn]
        simp only [if_neg hn, if_neg hk0]
        have hden : (2 * Real.pi * Complex.I * ((n i : ℤ) : ℂ)) ^ (k i) ≠ 0 := by
          apply pow_ne_zero
          apply mul_ne_zero
          · apply mul_ne_zero
            · norm_num [Real.pi_ne_zero]
            · exact Complex.I_ne_zero
          · exact_mod_cast hn
        simp only [inverseMultiplier, if_neg hn]
        field_simp [hden]
        <;> ring
  have hprod :
      (∏ i : Fin d, ((scalarBlock (t i) (n i : ℝ) : ℂ) *
          fourierCoeff
            (fun x : UnitAddCircle =>
              (periodizedDyadicAtomDerivative1 (s i) (j i).val
                (j i).isLt 0 x : ℂ)) (n i))) =
        ∏ i : Fin d, (((if k i = 0 then
            (scalarBlock (t i) (n i : ℝ) : ℂ)
          else inverseMultiplier (t i) (k i) (n i)) *
            fourierCoeff
              (fun x : UnitAddCircle =>
                (periodizedDyadicAtomDerivative1 (s i) (j i).val
                  (j i).isLt (k i) x : ℂ)) (n i))) := by
    apply Finset.prod_congr rfl
    intro i hi
    exact hcoord i
  calc
      ((∏ i : Fin d, scalarBlock (t i) (n i : ℝ) : ℝ) : ℂ) *
          ((c j : ℂ) * ∏ i : Fin d,
            fourierCoeff
              (fun x : UnitAddCircle =>
                (periodizedDyadicAtomDerivative1 (s i) (j i).val
                  (j i).isLt 0 x : ℂ)) (n i)) =
        (∏ i : Fin d, (scalarBlock (t i) (n i : ℝ) : ℂ)) *
          ((c j : ℂ) * ∏ i : Fin d,
            fourierCoeff
              (fun x : UnitAddCircle =>
                (periodizedDyadicAtomDerivative1 (s i) (j i).val
                  (j i).isLt 0 x : ℂ)) (n i)) := by
            simp only [Complex.ofReal_prod]
      _ =
        (c j : ℂ) * ∏ i : Fin d,
          ((scalarBlock (t i) (n i : ℝ) : ℂ) *
            fourierCoeff
              (fun x : UnitAddCircle =>
                (periodizedDyadicAtomDerivative1 (s i) (j i).val
                  (j i).isLt 0 x : ℂ)) (n i)) := by
            calc
              _ = (c j : ℂ) *
                  ((∏ i : Fin d, (scalarBlock (t i) (n i : ℝ) : ℂ)) *
                    ∏ i : Fin d, fourierCoeff
                      (fun x : UnitAddCircle =>
                        (periodizedDyadicAtomDerivative1 (s i) (j i).val
                          (j i).isLt 0 x : ℂ)) (n i)) := by ring
              _ = _ := by rw [← Finset.prod_mul_distrib]
      _ = (c j : ℂ) * ∏ i : Fin d,
          ((if k i = 0 then (scalarBlock (t i) (n i : ℝ) : ℂ)
            else inverseMultiplier (t i) (k i) (n i)) *
            fourierCoeff
              (fun x : UnitAddCircle =>
                (periodizedDyadicAtomDerivative1 (s i) (j i).val
                  (j i).isLt (k i) x : ℂ)) (n i)) := by
            rw [hprod]
      _ = (∏ i : Fin d,
          (if k i = 0 then (scalarBlock (t i) (n i : ℝ) : ℂ)
            else inverseMultiplier (t i) (k i) (n i))) *
          ((c j : ℂ) * ∏ i : Fin d,
            fourierCoeff
              (fun x : UnitAddCircle =>
                (periodizedDyadicAtomDerivative1 (s i) (j i).val
                  (j i).isLt (k i) x : ℂ)) (n i)) := by
            rw [Finset.prod_mul_distrib]
            ring

end BrownianSharp
