import BrownianSharp.TrigonometricHaarExtraction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Tensorization of translated Haar detail multipliers

The product-grid detail on a product character is the product of its
one-dimensional details.  Averaging each translation independently over the
unit circle factors by Fubini, so the resulting multiplier is the product of
the scalar `sinc²` differences.
-/

noncomputable section

open MeasureTheory
open scoped Real

namespace HaarQuarter.TrigonometricTensorExtraction

open HaarQuarter.TrigonometricHaarExtraction

/-- Lebesgue probability measure on one circle represented by `[0,1]`. -/
def unitCircleMeasure : Measure ℝ := MeasureTheory.volume.restrict (Set.Ioc 0 1)

instance unitCircleMeasure_isFinite : IsFiniteMeasure unitCircleMeasure := by
  rw [unitCircleMeasure, isFiniteMeasure_restrict]
  simp

theorem integral_unitCircleMeasure_eq_interval (f : ℝ → ℂ) :
    (∫ t, f t ∂unitCircleMeasure) = ∫ t in 0..1, f t := by
  rw [unitCircleMeasure, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- The one-dimensional translated Haar-detail response at scale `m`. -/
def translatedDetailComponent (m : ℕ) (k : ℤ) (x β : ℝ) : ℂ :=
  translatedGridCellProjection k (((2 * m : ℕ) : ℝ)⁻¹) x β -
    translatedGridCellProjection k ((m : ℝ)⁻¹) x β

/-- Product of the coordinatewise one-dimensional Haar details, the tensor
product detail applied to a product character. -/
def translatedTensorDetail {d : ℕ} (m : Fin d → ℕ)
    (k : Fin d → ℤ) (x β : Fin d → ℝ) : ℂ :=
  ∏ i, translatedDetailComponent (m i) (k i) (x i) (β i)

/-- Independent uniform translations in each coordinate factor the average of
the tensor detail into the product of the scalar detail averages. -/
theorem translatedTensorDetail_average {d : ℕ} (m : Fin d → ℕ)
    (hm : ∀ i, 0 < m i) (k : Fin d → ℤ) (x : Fin d → ℝ) :
    (∫ β : Fin d → ℝ, translatedTensorDetail m k x β
      ∂Measure.pi (fun _ : Fin d => unitCircleMeasure)) =
      ∏ i, (∫ β, translatedDetailComponent (m i) (k i) (x i) β
        ∂unitCircleMeasure) := by
  change (∫ β : Fin d → ℝ,
      ∏ i, translatedDetailComponent (m i) (k i) (x i) (β i)
      ∂Measure.pi (fun _ : Fin d => unitCircleMeasure)) = _
  exact MeasureTheory.integral_fintype_prod_eq_prod
    (fun i β => translatedDetailComponent (m i) (k i) (x i) β)

/-- Exact tensorized Fourier multiplier for the averaged shifted-grid detail.
This is the product-circle version of the scalar `sinc²` difference. -/
theorem translatedTensorDetail_character_multiplier {d : ℕ}
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (k : Fin d → ℤ) (x : Fin d → ℝ) :
    (∫ β : Fin d → ℝ, translatedTensorDetail m k x β
      ∂Measure.pi (fun _ : Fin d => unitCircleMeasure)) =
      ∏ i, (((Real.sinc (Real.pi * (k i : ℝ) * (((2 * m i : ℕ) : ℝ)⁻¹)) : ℂ) ^ 2 -
        (Real.sinc (Real.pi * (k i : ℝ) * ((m i : ℝ)⁻¹)) : ℂ) ^ 2) *
          character (k i) (x i)) := by
  rw [translatedTensorDetail_average]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [integral_unitCircleMeasure_eq_interval]
    exact translatedGridHaarDetailMultiplier (m i) (hm i) (k i) (x i)
  · exact hm

/-- A finite trigonometric polynomial acted on by the tensor product of the
translated one-dimensional details. -/
def translatedTensorPolynomialResponse {d : ℕ} (m : Fin d → ℕ)
    (s : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (x : Fin d → ℝ) (β : Fin d → ℝ) : ℂ :=
  ∑ k ∈ s, a k * translatedTensorDetail m k x β

/-- Each scalar shifted-grid detail is integrable over the unit translation
parameter. -/
theorem translatedDetailComponent_integrable (m : ℕ) (hm : 0 < m)
    (k : ℤ) (x : ℝ) :
    Integrable (fun β => translatedDetailComponent m k x β) unitCircleMeasure := by
  have h1 := translatedGridCellProjection_intervalIntegrable
    (h := (((2 * m : ℕ) : ℝ)⁻¹)) k (by positivity) x
    (a := 0) (b := 1) (by norm_num)
  have h2 := translatedGridCellProjection_intervalIntegrable
    (h := ((m : ℝ)⁻¹)) k (by positivity) x
    (a := 0) (b := 1) (by norm_num)
  have hdiff : IntervalIntegrable
      (fun β : ℝ => translatedDetailComponent m k x β) volume 0 1 := by
    exact h1.sub h2
  have hOn : IntegrableOn
      (fun β : ℝ => translatedDetailComponent m k x β) (Set.Ioc (0 : ℝ) 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le
      (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)).mp hdiff
  simpa [unitCircleMeasure, IntegrableOn] using hOn

/-- Finite-sum integration extends the character multiplier formula to every
finite product-circle Fourier polynomial. -/
theorem translatedTensorPolynomialResponse_average {d : ℕ}
    (m : Fin d → ℕ) (hm : ∀ i, 0 < m i)
    (s : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) → ℂ)
    (x : Fin d → ℝ) :
    (∫ β : Fin d → ℝ,
      translatedTensorPolynomialResponse m s a x β
      ∂Measure.pi (fun _ : Fin d => unitCircleMeasure)) =
      ∑ k ∈ s, a k * ∏ i,
        (((Real.sinc (Real.pi * (k i : ℝ) * (((2 * m i : ℕ) : ℝ)⁻¹) : ℝ) : ℂ) ^ 2 -
          (Real.sinc (Real.pi * (k i : ℝ) * ((m i : ℝ)⁻¹) : ℝ) : ℂ) ^ 2) *
          character (k i) (x i)) := by
  unfold translatedTensorPolynomialResponse
  have hterm (k : Fin d → ℤ) :
      Integrable (fun β : Fin d → ℝ =>
        translatedTensorDetail m k x β)
        (Measure.pi (fun _ : Fin d => unitCircleMeasure)) := by
    change Integrable (fun β : Fin d → ℝ =>
      ∏ i, translatedDetailComponent (m i) (k i) (x i) (β i)) _
    apply Integrable.fintype_prod
    intro i
    exact translatedDetailComponent_integrable (m i) (hm i) (k i) (x i)
  have hsum (k : Fin d → ℤ) (hk : k ∈ s) :
      Integrable (fun β : Fin d → ℝ =>
        a k * translatedTensorDetail m k x β)
        (Measure.pi (fun _ : Fin d => unitCircleMeasure)) :=
    (hterm k).const_mul (a k)
  rw [MeasureTheory.integral_finsetSum s hsum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [integral_const_mul]
  rw [translatedTensorDetail_character_multiplier m hm k x]

end HaarQuarter.TrigonometricTensorExtraction
