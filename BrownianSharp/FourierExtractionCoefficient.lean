import BrownianSharp.FourierExtractionKernel

noncomputable section
open MeasureTheory
namespace HaarQuarter.FourierExtractionCoefficient
open HaarQuarter.FourierExtractionKernel

theorem circleBlockKernel_fourierCoeff (m : ℝ) (hm : 0 < m) (n : ℤ) :
    fourierCoeff (circleBlockKernel m hm) n =
      blockQuotientSchwartz ((n : ℝ) / m) := by
  classical
  letI : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  let s := sampledBlockSupport m hm
  have hterm (k : ℤ) (hk : k ∈ s) :
      Integrable (fun x : UnitAddCircle =>
        (blockQuotientSchwartz ((k : ℝ) / m) : ℂ) *
          fourier (T := (1 : ℝ)) k x)
        AddCircle.haarAddCircle := by
    have hc : Continuous (fun x : UnitAddCircle =>
        (blockQuotientSchwartz ((k : ℝ) / m) : ℂ) *
          fourier (T := (1 : ℝ)) k x) := by fun_prop
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hrep : (circleBlockKernel m hm : UnitAddCircle → ℂ) =
      ∑ k ∈ s, fun x : UnitAddCircle =>
        (blockQuotientSchwartz ((k : ℝ) / m) : ℂ) *
          fourier (T := (1 : ℝ)) k x := by
    funext x
    simp [circleBlockKernel, s, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
  rw [hrep]
  have hcoeff_sum :
      fourierCoeff (∑ k ∈ s, fun x : UnitAddCircle =>
        (blockQuotientSchwartz ((k : ℝ) / m) : ℂ) * fourier k x) =
      ∑ k ∈ s, fourierCoeff (fun x : UnitAddCircle =>
        (blockQuotientSchwartz ((k : ℝ) / m) : ℂ) *
          fourier (T := (1 : ℝ)) k x) :=
    fourierCoeff.sum s
      (fun k x => (blockQuotientSchwartz ((k : ℝ) / m) : ℂ) *
        fourier (T := (1 : ℝ)) k x)
      hterm
  rw [hcoeff_sum]
  have hfourierCoeff_mode (k : ℤ) :
      fourierCoeff (T := (1 : ℝ)) (fourier (T := (1 : ℝ)) k) n =
        if n = k then (1 : ℂ) else 0 := by
    have h := congrFun (fourierCoeff_fourier (T := (1 : ℝ)) k) n
    simpa [Pi.single_apply] using h
  have hmode (k : ℤ) :
      fourierCoeff (fun x : UnitAddCircle =>
        (blockQuotientSchwartz ((k : ℝ) / m) : ℂ) * fourier (T := (1 : ℝ)) k x) n =
        if n = k then blockQuotientSchwartz ((k : ℝ) / m) else 0 := by
    rw [fourierCoeff.const_mul, hfourierCoeff_mode]
    simp only [mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_apply]
  simp_rw [hmode]
  simp only [Finset.sum_ite_eq]
  by_cases hn : n ∈ s
  · simpa [hn]
  · have hzero : blockQuotientSchwartz ((n : ℝ) / m) = 0 := by
      by_contra hne
      apply hn
      simpa [s, sampledBlockSupport, hne]
    simp [hn, hzero]

/-- The polynomial with the averaged adjacent-scale detail multipliers is
exactly the average of the genuine translated-grid detail of the input
polynomial. -/
theorem finiteCircleFourierPolynomial_eq_average_translatedDetail
    (m : ℕ) (hm : 0 < m) (s : Finset ℤ) (a : ℤ → ℂ) (x : ℝ) :
    finiteCircleFourierPolynomial s
        (fun n => a n * (detailMultiplier ((n : ℝ) / (m : ℝ)) : ℂ))
        (x : UnitAddCircle) =
      ∫ β in (0 : ℝ)..1, translatedDetailPolynomialResponse m s a x β := by
  rw [translatedDetailPolynomialResponse_average m hm s a x]
  unfold finiteCircleFourierPolynomial
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdouble : (((2 * m : ℕ) : ℝ)⁻¹) = ((m : ℝ)⁻¹) / 2 := by
    have htwo : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by norm_num
    rw [htwo]
    field_simp [hmR.ne']
  have hhalf : Real.pi * (n : ℝ) * (((2 * m : ℕ) : ℝ)⁻¹) =
      Real.pi * ((n : ℝ) / (m : ℝ)) / 2 := by
    rw [hdouble]
    field_simp [hmR.ne']
  have hone : Real.pi * (n : ℝ) * ((m : ℝ)⁻¹) =
      Real.pi * ((n : ℝ) / (m : ℝ)) := by
    field_simp [hmR.ne']
  have hcoef :
      ((Real.sinc (Real.pi * ((n : ℝ) / (m : ℝ)) / 2) : ℂ) ^ 2 -
        (Real.sinc (Real.pi * ((n : ℝ) / (m : ℝ))) : ℂ) ^ 2) =
        (detailMultiplier ((n : ℝ) / (m : ℝ)) : ℂ) := by
    rw [detailMultiplier]
    push_cast
    ring
  rw [hhalf, hone, hcoef]
  have hchar : fourier (T := (1 : ℝ)) n (x : UnitAddCircle) =
      TrigonometricHaarExtraction.character n x := by
    rw [fourier_coe_apply]
    unfold TrigonometricHaarExtraction.character
    congr 1
    push_cast
    ring
  rw [hchar]
  ring

/-- Convolution of the averaged scalar Haar detail by the actual periodized
kernel is precisely the smooth cutoff Fourier projection. -/
theorem circleBlockKernel_convolution_average_translatedDetail
    (m : ℕ) (hm : 0 < m) (s : Finset ℤ) (a : ℤ → ℂ)
    (x : UnitAddCircle) :
    circleConvolution (circleBlockKernel (m : ℝ) (by exact_mod_cast hm))
      (finiteCircleFourierPolynomial s
        (fun n => a n * (detailMultiplier ((n : ℝ) / (m : ℝ)) : ℂ))) x =
      ∑ n ∈ s,
        (a n * (blockCutoff ((n : ℝ) / (m : ℝ)) : ℂ)) * fourier n x := by
  rw [circleConvolution_finiteFourierPolynomial]
  apply Finset.sum_congr rfl
  intro n hn
  rw [circleBlockKernel_fourierCoeff (m : ℝ) (by exact_mod_cast hm)]
  calc
    (a n * (detailMultiplier ((n : ℝ) / (m : ℝ)) : ℂ) *
        blockQuotientSchwartz ((n : ℝ) / (m : ℝ))) * fourier n x =
      (a n * ((detailMultiplier ((n : ℝ) / (m : ℝ)) : ℂ) *
        blockQuotientSchwartz ((n : ℝ) / (m : ℝ)))) * fourier n x := by ring
    _ = (a n * (blockCutoff ((n : ℝ) / (m : ℝ) : ℝ) : ℂ)) * fourier n x := by
      rw [detailMultiplier_mul_blockQuotientSchwartz]

end HaarQuarter.FourierExtractionCoefficient
