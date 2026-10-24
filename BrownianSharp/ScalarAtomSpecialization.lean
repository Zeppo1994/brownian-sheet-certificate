import BrownianSharp.ScalarHighFrequency
import BrownianSharp.AtomicSynthesisLp

/-! The scalar Bessel inequalities applied to the actual periodized smooth
dyadic cells. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.ScalarAtomSpecialization

open BrownianSharp.ScalarBlockBessel
open BrownianSharp.ScalarAtomVariance
open BrownianSharp.ScalarHighFrequency
open AddCircle

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- Complex-valued continuous form of the real periodized derivative atom. -/
def atomComplex (s K : ℕ) (j : Fin (2 ^ s)) : C(UnitAddCircle, ℂ) where
  toFun x := (periodizedDyadicAtomDerivative1 s j.1 j.2 K x : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp
    (periodizedDyadicAtomDerivative1 s j.1 j.2 K).continuous

/-- Convert a squared Haar-integral estimate for a continuous scalar function
to the corresponding L² norm-square estimate. -/
theorem continuousLp_norm_sq_eq_integral (f : C(UnitAddCircle, ℂ)) :
    ‖continuousLp1 f‖ ^ 2 =
      ∫ x : UnitAddCircle, ‖f x‖ ^ 2 ∂AddCircle.haarAddCircle := by
  rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ _ _ _]
  rw [continuousLp1, ContinuousMap.inner_toLp]
  have hintOn : IntegrableOn (fun x : UnitAddCircle => f x * star (f x))
      Set.univ AddCircle.haarAddCircle := by
    have hc : Continuous (fun x : UnitAddCircle => f x * star (f x)) := by fun_prop
    exact hc.continuousOn.integrableOn_compact isCompact_univ
  have hint : Integrable (fun x : UnitAddCircle => f x * star (f x))
      AddCircle.haarAddCircle := by
    simpa [integrableOn_univ] using hintOn
  change Complex.re (∫ x : UnitAddCircle, f x * star (f x)
    ∂AddCircle.haarAddCircle) = _
  calc
    _ = ∫ x : UnitAddCircle, Complex.re (f x * star (f x))
        ∂AddCircle.haarAddCircle := (integral_re hint).symm
    _ = ∫ x : UnitAddCircle, ‖f x‖ ^ 2 ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [RCLike.star_def, RCLike.mul_conj]
      change Complex.re ((Complex.ofReal ‖f x‖) ^ 2) = _
      rw [← Complex.ofReal_pow, Complex.ofReal_re]

/-- Actual fixed-depth scalar derivative atoms are pairwise orthogonal. -/
theorem atomComplex_orthogonal (s K : ℕ) :
    ∀ i j : Fin (2 ^ s), i ≠ j →
      inner ℂ (continuousLp1 (atomComplex s K i))
        (continuousLp1 (atomComplex s K j)) = 0 := by
  intro i j hij
  rw [continuousLp1, continuousLp1, ContinuousMap.inner_toLp]
  have hpair := periodizedDyadicAtomDerivative1_pairwise_inner_eq_zero
    s j.1 i.1 j.2 i.2 (Ne.symm (by intro heq; exact hij (Fin.ext heq))) K
  simpa [atomComplex] using hpair

theorem atomComplex_norm_sq_le (s K : ℕ) (hK : 1 ≤ K)
    {C : ℝ} (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (j : Fin (2 ^ s)) :
    ‖continuousLp1 (atomComplex s K j)‖ ^ 2 ≤
      C ^ 2 * (2 : ℝ) ^ ((2 * K - 1) * s) := by
  rw [continuousLp_norm_sq_eq_integral]
  exact periodizedDyadicAtomDerivative1_L2_sq_le s j.1 j.2 K hK hC

theorem atomComplex_zero_norm_sq_le (s : ℕ) {C : ℝ}
    (hC : ∀ x : ℝ, |smoothAtom x| ≤ C) (j : Fin (2 ^ s)) :
    ‖continuousLp1 (atomComplex s 0 j)‖ ^ 2 ≤
      C ^ 2 * ((2 : ℝ) ^ s)⁻¹ := by
  rw [continuousLp_norm_sq_eq_integral]
  simpa [atomComplex] using
    periodizedDyadicAtomDerivative1_L2_sq_le_zero s j.1 j.2 hC

/-- The actual atom-family low-frequency variance bound, with the bump
supremum as the only atom constant. -/
theorem actual_scalar_low_frequency_variance (s t : ℕ)
    {C : ℝ} (hC : ∀ x : ℝ, |smoothAtom x| ≤ C)
    (x : UnitAddCircle) :
    (∑ j : Fin (2 ^ s),
      ‖∑ n ∈ scalarFrequencyBox t,
        (BrownianSharp.SmoothResolution.scalarBlock t (n : ℝ) : ℂ) *
          fourierCoeff (atomComplex s 0 j) n * fourier n x‖ ^ 2) ≤
      (C ^ 2 * ((2 : ℝ) ^ s)⁻¹) * ((2 : ℝ) ^ (t + 2) + 1) := by
  apply scalarBlock_atoms_sum_sq_le t (fun j : Fin (2 ^ s) => atomComplex s 0 j)
    x (mul_nonneg (sq_nonneg C) (by positivity))
    (by
      intro i j hij
      exact atomComplex_orthogonal s 0 i j hij)
    (by
      intro j
      exact atomComplex_zero_norm_sq_le s hC j)

/-- In the low-frequency regime `t ≤ s`, the pointwise variance decays like
the ratio of the number of retained frequencies to the dyadic cell count. -/
theorem actual_scalar_low_frequency_variance_ratio (s t : ℕ) (hts : t ≤ s)
    {C : ℝ} (hC : ∀ x : ℝ, |smoothAtom x| ≤ C)
    (x : UnitAddCircle) :
    (∑ j : Fin (2 ^ s),
      ‖∑ n ∈ scalarFrequencyBox t,
        (BrownianSharp.SmoothResolution.scalarBlock t (n : ℝ) : ℂ) *
          fourierCoeff (atomComplex s 0 j) n * fourier n x‖ ^ 2) ≤
      5 * C ^ 2 * ((2 : ℝ) ^ t / (2 : ℝ) ^ s) := by
  have hbase := actual_scalar_low_frequency_variance s t hC x
  have hfactor : 0 ≤ C ^ 2 * ((2 : ℝ) ^ s)⁻¹ :=
    mul_nonneg (sq_nonneg C) (inv_nonneg.mpr (by positivity))
  have hcount : (2 : ℝ) ^ (t + 2) + 1 ≤ 5 * (2 : ℝ) ^ t := by
    have hpow : (2 : ℝ) ^ (t + 2) = 4 * (2 : ℝ) ^ t := by
      rw [pow_add]
      norm_num
      ring
    rw [hpow]
    have ht0 : 1 ≤ (2 : ℝ) ^ t := one_le_pow₀ (by norm_num)
    nlinarith
  calc
    _ ≤ (C ^ 2 * ((2 : ℝ) ^ s)⁻¹) * ((2 : ℝ) ^ (t + 2) + 1) := hbase
    _ ≤ (C ^ 2 * ((2 : ℝ) ^ s)⁻¹) * (5 * (2 : ℝ) ^ t) :=
      mul_le_mul_of_nonneg_left hcount hfactor
    _ = 5 * C ^ 2 * ((2 : ℝ) ^ t / (2 : ℝ) ^ s) := by ring

/-- The actual atom-family high-frequency variance bound.  It exposes only the
explicit derivative norm constant and uses the integration-by-parts identity
to place the inverse multiplier on the kernel. -/
theorem actual_scalar_high_frequency_variance (s t K : ℕ)
    (ht : 0 < t) (hK : 1 ≤ K)
    {C : ℝ} (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (x : UnitAddCircle) :
    (∑ j : Fin (2 ^ s),
      ‖∑ n ∈ scalarFrequencyBox t,
        (BrownianSharp.SmoothResolution.scalarBlock t (n : ℝ) : ℂ) *
          fourierCoeff (atomComplex s 0 j) n * fourier n x‖ ^ 2) ≤
      (C ^ 2 * (2 : ℝ) ^ ((2 * K - 1) * s)) *
        ‖kernelLp (scalarFrequencyBox t) (inverseMultiplier t K) x‖ ^ 2 := by
  apply scalarBlock_derivative_atoms_sum_sq_le t K ht
    (fun j : Fin (2 ^ s) => atomComplex s 0 j)
    (fun j : Fin (2 ^ s) => atomComplex s K j)
    (by
      intro j n hn
      simpa [atomComplex] using
        periodizedDyadicAtomDerivative1_fourier_eq_pow s j.1 j.2 K n hn)
    x (mul_nonneg (sq_nonneg C) (by positivity))
    (by
      intro i j hij
      exact atomComplex_orthogonal s K i j hij)
    (by
      intro j
      exact atomComplex_norm_sq_le s K hK hC j)

/-- Substituting the inverse-kernel tail estimate gives the explicit
one-dimensional high-frequency decay bound for the actual cell family. -/
theorem actual_scalar_high_frequency_variance_card (s t K : ℕ)
    (ht : 0 < t) (hK : 1 ≤ K)
    {C : ℝ} (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (x : UnitAddCircle) :
    (∑ j : Fin (2 ^ s),
      ‖∑ n ∈ scalarFrequencyBox t,
        (BrownianSharp.SmoothResolution.scalarBlock t (n : ℝ) : ℂ) *
          fourierCoeff (atomComplex s 0 j) n * fourier n x‖ ^ 2) ≤
      (C ^ 2 * (2 : ℝ) ^ ((2 * K - 1) * s)) *
        ((2 : ℝ) ^ (t + 2) + 1) *
          (((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹) ^ 2 := by
  have hfactor : 0 ≤ C ^ 2 * (2 : ℝ) ^ ((2 * K - 1) * s) :=
    mul_nonneg (sq_nonneg C) (by positivity)
  have hkernel := scalarBlock_inverse_kernel_energy_le
    (scalarFrequencyBox t) t K ht x
  have hcard : ((scalarFrequencyBox t).card : ℝ) ≤
      (2 : ℝ) ^ (t + 2) + 1 := by
    exact_mod_cast scalarFrequencyBox_card_le t
  calc
    _ ≤ (C ^ 2 * (2 : ℝ) ^ ((2 * K - 1) * s)) *
        ‖kernelLp (scalarFrequencyBox t) (inverseMultiplier t K) x‖ ^ 2 :=
          actual_scalar_high_frequency_variance s t K ht hK hC x
    _ ≤ (C ^ 2 * (2 : ℝ) ^ ((2 * K - 1) * s)) *
        ((scalarFrequencyBox t).card : ℝ) *
          (((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹) ^ 2 := by
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hkernel hfactor
    _ ≤ (C ^ 2 * (2 : ℝ) ^ ((2 * K - 1) * s)) *
        ((2 : ℝ) ^ (t + 2) + 1) *
          (((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹) ^ 2 := by
          have hη : 0 ≤ (((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹) ^ 2 := sq_nonneg _
          calc
            _ = (C ^ 2 * (2 : ℝ) ^ ((2 * K - 1) * s)) *
                (((scalarFrequencyBox t).card : ℝ) *
                  (((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹) ^ 2) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hη) hfactor
            _ = _ := by ring

end BrownianSharp.ScalarAtomSpecialization
