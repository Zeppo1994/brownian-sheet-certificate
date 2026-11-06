import BrownianSharp.AlignmentPaperAnchoredLpScalarKernelFormula
import Mathlib.Analysis.Complex.Trigonometric

noncomputable section
open MeasureTheory

namespace BrownianSharp.AlignmentPaperAnchoredLpFaceCoefficients

open BrownianSharp.AlignmentPaperAnchoredLpScalarKernelFormula
open BrownianSharp.AlignmentPaperAnchoredLpSourceFourier
open BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentPaperAnchoredLpReflectionTensor
open BrownianSharp.AlignmentFractionalTensor
open HaarQuarter

/-- The active-coordinate derivative multiplier in the scalar anchored source
kernel is exactly the sine factor carried by the parity-twisted face source. -/
theorem twoPiI_mul_anchoredScalarFourierKernel_eq_sine
    (n : ℤ) (v : ℝ) (hn : n ≠ 0) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (2 * Real.pi * Complex.I * (n : ℂ)) * anchoredScalarFourierKernel n v =
      -2 * Complex.I * (Real.sin (Real.pi * (n : ℝ) * v) : ℂ) := by
  rw [anchoredScalarFourierKernel_nonzero_formula n v hn hv0 hv1]
  let θ : ℝ := Real.pi * (n : ℝ) * v
  have hden : -2 * Real.pi * Complex.I * (n : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero
        · norm_num
        · exact_mod_cast Real.pi_ne_zero
      · exact Complex.I_ne_zero
    · exact_mod_cast hn
  have hfirst : Complex.exp
      ((-2 * Real.pi * Complex.I * (n : ℂ)) * (1-v/2)) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
    have hexp : (-2 * Real.pi * Complex.I * (n : ℂ)) * (1-v/2) =
        (n : ℂ) * (-2 * Real.pi * Complex.I) + (θ : ℂ) * Complex.I := by
      dsimp [θ]
      push_cast
      ring
    rw [hexp, Complex.exp_add]
    have hperiod : Complex.exp ((n : ℂ) * (-2 * Real.pi * Complex.I)) = 1 := by
      convert Complex.exp_int_mul_two_pi_mul_I (-n) using 1 <;> push_cast <;> ring_nf
    rw [hperiod, one_mul]
  have hsecond : Complex.exp
      ((-2 * Real.pi * Complex.I * (n : ℂ)) * (v/2)) =
        Complex.exp ((-(θ) : ℝ) * Complex.I) := by
    congr 1
    dsimp [θ]
    push_cast
    ring
  rw [hfirst, hsecond, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  have hsin : Real.sin (-θ) = -Real.sin θ := Real.sin_neg θ
  have hcos : Real.cos (-θ) = Real.cos θ := Real.cos_neg θ
  rw [hsin, hcos]
  field_simp [hden]
  dsimp [θ]
  push_cast
  ring

/-- Multiplying the actual path coefficient by the derivative multipliers on
its nonzero face replaces every active scalar kernel by its parity sine
factor. Zero coordinates retain their lower-face weights. -/
theorem periodicIntegrationPath_derivativeFourierCoeff_sine {d : ℕ} {p : ℝ}
    (hp : 1 < p)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d))
    (k : Fin d → ℤ) (J : Finset (Fin d))
    (hJ : ∀ i, i ∈ J ↔ k i ≠ 0) :
    (∏ i ∈ J, (2 * Real.pi * Complex.I * (k i : ℂ))) *
        UnitAddTorus.mFourierCoeff
          (fun x : UnitAddTorus (Fin d) =>
            ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ)) k =
      ∫ v, (∏ i, if k i = 0 then ((1-v i:ℝ):ℂ)
          else -2 * Complex.I *
            (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ)) * (g v : ℂ)
        ∂cubeMeasure d := by
  classical
  let m : Fin d → ℂ := fun i => 2 * Real.pi * Complex.I * (k i : ℂ)
  let b : Fin d → (Fin d → ℝ) → ℂ := fun i v =>
    if k i = 0 then ((1-v i:ℝ):ℂ) else anchoredScalarFourierKernel (k i) (v i)
  rw [periodicIntegrationPath_fourierCoeff_mixedKernel hp g k]
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  have hmeasure : cubeMeasure d =
      Measure.pi (fun _ : Fin d => unitIntervalMeasure) := by
    simp [cubeMeasure, AlignmentFractionalTensor.unitCube_measure_eq_pi,
      unitIntervalMeasure]
  have hbounds : ∀ᵐ v ∂cubeMeasure d, ∀ i, v i ∈ Set.Icc (0:ℝ) 1 := by
    rw [hmeasure]
    exact BrownianSharp.AlignmentPaperAnchoredLpSourceFourier.ae_unitCube_coordinates d
  filter_upwards [hbounds] with v hv
  have hprod : (∏ i ∈ J, m i) * (∏ i, b i v) =
      ∏ i, if k i = 0 then ((1-v i:ℝ):ℂ)
        else -2 * Complex.I * (Real.sin (Real.pi * (k i : ℝ) * v i) : ℂ) := by
    have hm : (∏ i ∈ J, m i) = ∏ i, if i ∈ J then m i else 1 := by
      simp
    rw [hm, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hij : i ∈ J
    · have hki : k i ≠ 0 := (hJ i).mp hij
      simp [hij, b, m, hki,
        twoPiI_mul_anchoredScalarFourierKernel_eq_sine (k i) (v i) hki
          (hv i).1 (hv i).2]
    · have hki : k i = 0 := by
        by_contra hne
        exact hij ((hJ i).mpr hne)
      simp [hij, b, hki]
  rw [← mul_assoc, hprod]

end BrownianSharp.AlignmentPaperAnchoredLpFaceCoefficients
