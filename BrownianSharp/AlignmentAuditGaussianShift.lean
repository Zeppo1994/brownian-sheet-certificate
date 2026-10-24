import BrownianSharp.GaussianDensity
import BrownianSharp.GaussianGridStatistics
import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
open scoped Pointwise

namespace BrownianSharp.AlignmentAuditGaussianShift

variable {ι : Type*} [Fintype ι]

private noncomputable def productVolume : Measure (ι → ℝ) := volume

private theorem productVolume_neg_preserving :
    MeasurePreserving (fun x : ι → ℝ => -x) (productVolume (ι := ι))
      (productVolume (ι := ι)) := by
  classical
  constructor
  · fun_prop
  · change Measure.map (fun x : ι → ℝ => -x) volume = volume
    let f : (ι → ℝ) →ₗ[ℝ] ι → ℝ := (-1 : ℝ) • LinearMap.id
    have hf : (fun x : ι → ℝ => -x) = f := by
      ext x i
      simp [f]
    have hdet : LinearMap.det f ≠ 0 := by
      change LinearMap.det ((-1 : ℝ) • LinearMap.id) ≠ 0
      simp only [LinearMap.det_smul, LinearMap.det_id, mul_one]
      exact pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)
    have hdetval : LinearMap.det f = (-1 : ℝ) ^ Module.finrank ℝ (ι → ℝ) := by
      change LinearMap.det ((-1 : ℝ) • LinearMap.id) = _
      simp only [LinearMap.det_smul, LinearMap.det_id, mul_one]
    have habs : |(LinearMap.det f)⁻¹| = 1 := by
      rw [hdetval, abs_inv, abs_pow]
      simp
    rw [hf, Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet]
    simp [habs]

private theorem productVolume_add_preserving (h : ι → ℝ) :
    MeasurePreserving (fun x : ι → ℝ => x + h) (productVolume (ι := ι))
      (productVolume (ι := ι)) := by
  classical
  constructor
  · fun_prop
  · change Measure.map (fun x : ι → ℝ => x + h) volume = volume
    exact map_add_right_eq_self volume h

private theorem density_neg (x : ι → ℝ) :
    BrownianSharp.GaussianDensity.density (-x) =
      BrownianSharp.GaussianDensity.density x := by
  classical
  unfold BrownianSharp.GaussianDensity.density
  apply Finset.prod_congr rfl
  intro i hi
  rw [Pi.neg_apply]
  unfold gaussianPDFReal
  congr 2 <;> ring

private theorem density_translate (x h : ι → ℝ) :
    BrownianSharp.GaussianDensity.density (x + h) =
      Real.exp (-(∑ i, (h i)^2) / 2 - ∑ i, x i * h i) *
        BrownianSharp.GaussianDensity.density x := by
  classical
  unfold BrownianSharp.GaussianDensity.density
  calc
    _ = ∏ i, (Real.exp (-(h i)^2 / 2 - x i * h i) *
        gaussianPDFReal 0 1 (x i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hpdf (u v : ℝ) : gaussianPDFReal 0 1 (u + v) =
          Real.exp (-v^2 / 2 - u * v) * gaussianPDFReal 0 1 u := by
        unfold gaussianPDFReal
        simp only [sub_zero, mul_one]
        have hexp : -(u + v) ^ 2 / 2 =
            (-v ^ 2 / 2 - u * v) + (-u ^ 2 / 2) := by ring
        norm_num
        rw [hexp, Real.exp_add]
        ring
      simpa using hpdf (x i) (h i)
    _ = (∏ i, Real.exp (-(h i)^2 / 2 - x i * h i)) *
        (∏ i, gaussianPDFReal 0 1 (x i)) := Finset.prod_mul_distrib
    _ = Real.exp (∑ i, (-(h i)^2 / 2 - x i * h i)) *
        (∏ i, gaussianPDFReal 0 1 (x i)) := by rw [← Real.exp_sum]
    _ = _ := by
      congr 1
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_div, ← Finset.sum_neg_distrib]

def shiftEnergy (h : ι → ℝ) : ℝ :=
  ∑ i, (h i)^2

private noncomputable def shiftPairing (x h : ι → ℝ) : ℝ :=
  ∑ i, x i * h i

private theorem density_shift_pair_lower (x h : ι → ℝ) :
    BrownianSharp.GaussianDensity.density (x + h) +
        BrownianSharp.GaussianDensity.density (-x + h) ≥
      2 * Real.exp (-shiftEnergy h / 2) *
        BrownianSharp.GaussianDensity.density x := by
  rw [density_translate x h, density_translate (-x) h, density_neg]
  have hpair : shiftPairing (-x) h = -shiftPairing x h := by
    simp [shiftPairing, Finset.sum_neg_distrib]
  have hexp : Real.exp (-shiftEnergy h / 2 - shiftPairing x h) =
      Real.exp (-shiftEnergy h / 2) * Real.exp (-shiftPairing x h) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  have hexp' : Real.exp (-shiftEnergy h / 2 - shiftPairing (-x) h) =
      Real.exp (-shiftEnergy h / 2) * Real.exp (shiftPairing x h) := by
    rw [hpair, sub_neg_eq_add, Real.exp_add]
  rw [show (∑ i, (h i) ^ 2) = shiftEnergy h by rfl,
    show (∑ i, x i * h i) = shiftPairing x h by rfl,
    show (∑ i, (-x) i * h i) = shiftPairing (-x) h by rfl,
    hexp, hexp']
  have hcosh : 2 ≤ Real.exp (-shiftPairing x h) + Real.exp (shiftPairing x h) := by
    have h₁ := Real.add_one_le_exp (shiftPairing x h)
    have h₂ := Real.add_one_le_exp (-shiftPairing x h)
    linarith
  have hnonneg : 0 ≤ Real.exp (-shiftEnergy h / 2) *
      BrownianSharp.GaussianDensity.density x :=
    mul_nonneg (Real.exp_nonneg _) (BrownianSharp.GaussianDensity.density_nonneg _)
  calc
    _ = Real.exp (-shiftEnergy h / 2) *
        BrownianSharp.GaussianDensity.density x *
        (Real.exp (-shiftPairing x h) + Real.exp (shiftPairing x h)) := by ring
    _ ≥ Real.exp (-shiftEnergy h / 2) *
        BrownianSharp.GaussianDensity.density x * 2 :=
      mul_le_mul_of_nonneg_left hcosh hnonneg
    _ = 2 * Real.exp (-shiftEnergy h / 2) *
        BrownianSharp.GaussianDensity.density x := by ring

private theorem density_measurable :
    Measurable (BrownianSharp.GaussianDensity.density : (ι → ℝ) → ℝ) := by
  unfold BrownianSharp.GaussianDensity.density
  fun_prop

private theorem translated_image_measurable (A : Set (ι → ℝ)) (h : ι → ℝ)
    (hA : MeasurableSet A) : MeasurableSet ((fun x : ι → ℝ => x + h) '' A) := by
  exact (MeasurableEquiv.addRight h).measurableSet_image.mpr hA

private theorem standardGaussian_image_eq_lintegral (A : Set (ι → ℝ))
    (h : ι → ℝ) (hA : MeasurableSet A) :
    BrownianSharp.productStandardGaussian ι ((fun x : ι → ℝ => x + h) '' A) =
      ∫⁻ x in A, ENNReal.ofReal
        (BrownianSharp.GaussianDensity.density (x + h)) ∂(volume : Measure (ι → ℝ)) := by
  unfold BrownianSharp.productStandardGaussian
  rw [BrownianSharp.GaussianDensity.standardGaussian_eq_withDensity,
    withDensity_apply _ (translated_image_measurable A h hA)]
  symm
  exact (productVolume_add_preserving h).setLIntegral_comp_emb
    (MeasurableEquiv.addRight h).measurableEmbedding
    (fun y => ENNReal.ofReal (BrownianSharp.GaussianDensity.density y)) A

private theorem standardGaussian_eq_lintegral (A : Set (ι → ℝ))
    (hA : MeasurableSet A) :
    BrownianSharp.productStandardGaussian ι A =
      ∫⁻ x in A, ENNReal.ofReal (BrownianSharp.GaussianDensity.density x)
        ∂(volume : Measure (ι → ℝ)) := by
  unfold BrownianSharp.productStandardGaussian
  rw [BrownianSharp.GaussianDensity.standardGaussian_eq_withDensity,
    withDensity_apply _ hA]

private theorem translated_reflected_lintegral_eq (A : Set (ι → ℝ))
    (h : ι → ℝ) (hA : MeasurableSet A)
    (hsymm : ∀ x, x ∈ A ↔ -x ∈ A) :
    ∫⁻ x in A, ENNReal.ofReal
        (BrownianSharp.GaussianDensity.density (-x + h)) ∂(volume : Measure (ι → ℝ)) =
      ∫⁻ x in A, ENNReal.ofReal
        (BrownianSharp.GaussianDensity.density (x + h)) ∂(volume : Measure (ι → ℝ)) := by
  have himage : (fun x : ι → ℝ => -x) '' A = A := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hsymm x).mp hx
    · intro hy
      exact ⟨-y, (hsymm y).mp hy, by simp⟩
  have hchange := (productVolume_neg_preserving (ι := ι)).setLIntegral_comp_emb
    (MeasurableEquiv.neg (ι → ℝ)).measurableEmbedding
    (fun y => ENNReal.ofReal (BrownianSharp.GaussianDensity.density (y + h))) A
  rw [himage] at hchange
  simpa [productVolume] using hchange

private theorem pointwise_ennreal_pair_lower (x h : ι → ℝ) :
    ENNReal.ofReal (BrownianSharp.GaussianDensity.density (x + h)) +
      ENNReal.ofReal (BrownianSharp.GaussianDensity.density (-x + h)) ≥
    ENNReal.ofReal (2 * Real.exp (-shiftEnergy h / 2) *
      BrownianSharp.GaussianDensity.density x) := by
  rw [← ENNReal.ofReal_add
    (BrownianSharp.GaussianDensity.density_nonneg _)
    (BrownianSharp.GaussianDensity.density_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (density_shift_pair_lower x h)

/-- Finite-dimensional Cameron--Martin shift lower bound for every measurable
centrally symmetric set.  The energy is the Euclidean squared norm written as
the finite coordinate sum. -/
theorem productGaussian_symmetric_translate_lower
    (A : Set (ι → ℝ)) (hA : MeasurableSet A)
    (hsymm : ∀ x, x ∈ A ↔ -x ∈ A) (h : ι → ℝ) :
    BrownianSharp.productStandardGaussian ι ((fun x : ι → ℝ => x + h) '' A) ≥
      ENNReal.ofReal (Real.exp (-shiftEnergy h / 2)) *
        BrownianSharp.productStandardGaussian ι A := by
  let c : ℝ := Real.exp (-shiftEnergy h / 2)
  have hc : 0 < c := by positivity
  have hc2 : 0 ≤ 2 * c := by positivity
  have hshiftMeas : Measurable (fun x : ι → ℝ =>
      ENNReal.ofReal (BrownianSharp.GaussianDensity.density (x + h))) :=
    (density_measurable.comp (by fun_prop)).ennreal_ofReal
  have hrefMeas : Measurable (fun x : ι → ℝ =>
      ENNReal.ofReal (BrownianSharp.GaussianDensity.density (-x + h))) :=
    (density_measurable.comp (by fun_prop)).ennreal_ofReal
  have hupperMeas : Measurable (fun x : ι → ℝ =>
      ENNReal.ofReal (BrownianSharp.GaussianDensity.density (x + h)) +
      ENNReal.ofReal (BrownianSharp.GaussianDensity.density (-x + h))) := by
    exact hshiftMeas.add hrefMeas
  have hmono := MeasureTheory.setLIntegral_mono
    (μ := (volume : Measure (ι → ℝ))) (s := A)
    (f := fun x => ENNReal.ofReal (2 * c *
      BrownianSharp.GaussianDensity.density x))
    (g := fun x => ENNReal.ofReal (BrownianSharp.GaussianDensity.density (x + h)) +
      ENNReal.ofReal (BrownianSharp.GaussianDensity.density (-x + h)))
    hupperMeas (by
      intro x hx
      have hp := pointwise_ennreal_pair_lower x h
      simpa [c] using hp)
  have hsum :
      (∫⁻ x in A, ENNReal.ofReal
          (BrownianSharp.GaussianDensity.density (x + h)) +
          ENNReal.ofReal (BrownianSharp.GaussianDensity.density (-x + h))
          ∂(volume : Measure (ι → ℝ))) =
        2 * BrownianSharp.productStandardGaussian ι
          ((fun x : ι → ℝ => x + h) '' A) := by
    rw [lintegral_add_left hshiftMeas]
    rw [standardGaussian_image_eq_lintegral A h hA,
      translated_reflected_lintegral_eq A h hA hsymm]
    simp [two_mul]
  have hlower :
      (∫⁻ x in A, ENNReal.ofReal
          (2 * c * BrownianSharp.GaussianDensity.density x)
          ∂(volume : Measure (ι → ℝ))) =
        ENNReal.ofReal (2 * c) * BrownianSharp.productStandardGaussian ι A := by
    rw [show (fun x : ι → ℝ => ENNReal.ofReal
        (2 * c * BrownianSharp.GaussianDensity.density x)) =
      fun x => ENNReal.ofReal (2 * c) *
        ENNReal.ofReal (BrownianSharp.GaussianDensity.density x) by
      funext x
      rw [ENNReal.ofReal_mul hc2]]
    rw [lintegral_const_mul (ENNReal.ofReal (2 * c))
      ((density_measurable.ennreal_ofReal)),
      standardGaussian_eq_lintegral A hA]
  have hineq : ENNReal.ofReal (2 * c) *
      BrownianSharp.productStandardGaussian ι A ≤
      2 * BrownianSharp.productStandardGaussian ι
        ((fun x : ι → ℝ => x + h) '' A) := by
    calc
      _ = ∫⁻ x in A, ENNReal.ofReal
          (2 * c * BrownianSharp.GaussianDensity.density x)
          ∂(volume : Measure (ι → ℝ)) := hlower.symm
      _ ≤ ∫⁻ x in A, ENNReal.ofReal
          (BrownianSharp.GaussianDensity.density (x + h)) +
          ENNReal.ofReal (BrownianSharp.GaussianDensity.density (-x + h))
          ∂(volume : Measure (ι → ℝ)) := hmono
      _ = 2 * BrownianSharp.productStandardGaussian ι
          ((fun x : ι → ℝ => x + h) '' A) := hsum
  have hineq' : (ENNReal.ofReal c * BrownianSharp.productStandardGaussian ι A) * 2 ≤
      (BrownianSharp.productStandardGaussian ι
        ((fun x : ι → ℝ => x + h) '' A)) * 2 := by
    simpa [ENNReal.ofReal_mul hc2, ENNReal.ofReal_ofNat,
      mul_assoc, mul_comm, mul_left_comm] using hineq
  have hcancel := (ENNReal.mul_le_mul_iff_left
    (show (2 : ℝ≥0∞) ≠ 0 by norm_num)
    (show (2 : ℝ≥0∞) ≠ ∞ by norm_num)).mp hineq'
  simpa [c, mul_comm, mul_left_comm, mul_assoc] using hcancel

/-- The same bound written using pointwise set addition by a singleton. -/
theorem productGaussian_symmetric_add_singleton_lower
    (A : Set (ι → ℝ)) (hA : MeasurableSet A)
    (hsymm : ∀ x, x ∈ A ↔ -x ∈ A) (h : ι → ℝ) :
    BrownianSharp.productStandardGaussian ι (A + {h}) ≥
      ENNReal.ofReal (Real.exp (-shiftEnergy h / 2)) *
        BrownianSharp.productStandardGaussian ι A := by
  have himage : Set.image (fun x : ι → ℝ => x + h) A = A + {h} := by
    ext y
    simp
  rw [← himage]
  exact productGaussian_symmetric_translate_lower A hA hsymm h

end BrownianSharp.AlignmentAuditGaussianShift
