import BrownianSharp.AlignmentExponential
import BrownianSharp.GaussianDensity
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace BrownianSharp.AlignmentExponentialDiagonalDilation

private noncomputable def expandedDensity {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∏ i, gaussianPDFReal 0 ⟨(a i)⁻¹ ^ 2, by positivity⟩ (x i)

private theorem expandedDensity_nonneg {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (x : ι → ℝ) : 0 ≤ expandedDensity a x := by
  unfold expandedDensity
  exact Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _

private theorem expandedDensity_integrable {ι : Type*} [Fintype ι]
    (a : ι → ℝ) : Integrable (expandedDensity (ι := ι) a) volume := by
  unfold expandedDensity
  exact Integrable.fintype_prod fun i => integrable_gaussianPDFReal _ _

private theorem pi_expandedGaussian_eq_withDensity {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    Measure.pi (fun i : ι => gaussianReal 0 ⟨(a i)⁻¹ ^ 2, by positivity⟩) =
      volume.withDensity (fun x => ENNReal.ofReal (expandedDensity a x)) := by
  classical
  let v : ι → ℝ≥0 := fun i => ⟨(a i)⁻¹ ^ 2, sq_nonneg _⟩
  letI : ∀ i : ι, IsProbabilityMeasure (gaussianReal 0 (v i)) := fun i =>
    instIsProbabilityMeasureGaussianReal 0 (v i)
  letI : ∀ i : ι, SigmaFinite (gaussianReal 0 (v i)) := fun i =>
    (inferInstance : SigmaFinite (gaussianReal 0 (v i)))
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hInt : Integrable (expandedDensity (ι := ι) a)
      (volume.restrict (Set.univ.pi s)) := expandedDensity_integrable a |>.restrict
  rw [← ofReal_integral_eq_lintegral_ofReal hInt
    (ae_of_all _ (expandedDensity_nonneg a))]
  change ENNReal.ofReal (∫ x, ∏ i,
      gaussianPDFReal 0 ⟨(a i)⁻¹ ^ 2, by positivity⟩ (x i)
      ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  calc
    _ = ∏ i, ENNReal.ofReal (∫ x in s i,
          gaussianPDFReal 0 ⟨(a i)⁻¹ ^ 2, by positivity⟩ x) :=
      ENNReal.ofReal_prod_of_nonneg (fun i _ =>
        integral_nonneg fun x => gaussianPDFReal_nonneg _ _ _)
    _ = _ := Finset.prod_congr rfl (fun i _ =>
      (gaussianReal_apply_eq_integral 0 (by
        intro hv
        have hval : ((v i : ℝ≥0) : ℝ) = 0 := congrArg (fun z : ℝ≥0 => (z : ℝ)) hv
        change ((a i)⁻¹ ^ 2 : ℝ) = 0 at hval
        exact (pow_ne_zero 2 (inv_ne_zero (ha i))) hval) (s i)).symm)

private theorem expandedPDF_ge {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (x : ℝ) :
    gaussianPDFReal 0 (⟨(a⁻¹)^2, by positivity⟩ : ℝ≥0) x ≥
      a * gaussianPDFReal 0 1 x := by
  have hscale : gaussianPDFReal 0 1 (a * x) ≥ gaussianPDFReal 0 1 x := by
    rw [gaussianPDFReal]
    apply mul_le_mul_of_nonneg_left
    · apply Real.exp_le_exp.mpr
      have hsq : a ^ 2 ≤ 1 := by nlinarith [sq_nonneg (a - 1)]
      have hx : 0 ≤ x ^ 2 := sq_nonneg x
      have hsqx : a ^ 2 * x ^ 2 ≤ x ^ 2 := by
        simpa using (mul_le_mul_of_nonneg_right hsq hx)
      simp only [sub_zero]
      norm_num
      nlinarith [hsqx]
    · positivity
  have hratio : gaussianPDFReal 0 (⟨(a⁻¹)^2, by positivity⟩ : ℝ≥0) x =
      a * gaussianPDFReal 0 1 (a * x) := by
    let v : ℝ≥0 := ⟨(a⁻¹)^2, sq_nonneg _⟩
    have h := gaussianPDFReal_inv_mul (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
      (c := a⁻¹) (by positivity) x
    have h' : gaussianPDFReal 0 1 (a * x) =
        a⁻¹ * gaussianPDFReal 0 v x := by
      have h1 : gaussianPDFReal 0 1 (a * x) =
          |a⁻¹| * gaussianPDFReal 0 v x := by
        simp only [inv_inv, mul_zero, mul_one] at h
        change gaussianPDFReal 0 1 (a * x) =
          |a⁻¹| * gaussianPDFReal 0 (⟨(a⁻¹)^2, sq_nonneg _⟩ : ℝ≥0) x at h
        exact h
      rw [abs_of_pos (inv_pos.mpr ha)] at h1
      exact h1
    calc
      gaussianPDFReal 0 (⟨(a⁻¹)^2, by positivity⟩ : ℝ≥0) x =
          a * (a⁻¹ * gaussianPDFReal 0 (⟨(a⁻¹)^2, by positivity⟩ : ℝ≥0) x) := by
            field_simp
      _ = a * gaussianPDFReal 0 1 (a * x) := by rw [← h']
  rw [hratio]
  exact mul_le_mul_of_nonneg_left hscale ha.le

private theorem expandedDensity_ge {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1)
    (x : ι → ℝ) :
    (∏ i, a i) * GaussianDensity.density x ≤ expandedDensity a x := by
  classical
  unfold expandedDensity GaussianDensity.density
  calc
    (∏ i, a i) * ∏ i, gaussianPDFReal 0 1 (x i) =
        ∏ i, (a i * gaussianPDFReal 0 1 (x i)) := by
          rw [Finset.prod_mul_distrib]
    _ ≤ ∏ i, gaussianPDFReal 0 (⟨((a i)⁻¹)^2, by positivity⟩ : ℝ≥0) (x i) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact mul_nonneg (ha i).le (gaussianPDFReal_nonneg _ _ _)
      · intro i hi
        exact expandedPDF_ge (ha i) (ha1 i) (x i)

private theorem expandedProductGaussian_ge_smul {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1) :
    Measure.pi (fun i : ι => gaussianReal 0
        ⟨(a i)⁻¹ ^ 2, by positivity⟩) ≥
      ENNReal.ofReal (∏ i, a i) • BrownianSharp.productStandardGaussian ι := by
  have hprod : 0 ≤ ∏ i, a i := Finset.prod_nonneg fun i _ => (ha i).le
  change Measure.pi (fun i : ι => gaussianReal 0
      ⟨(a i)⁻¹ ^ 2, by positivity⟩) ≥
    ENNReal.ofReal (∏ i, a i) •
      Measure.pi (fun _ : ι => gaussianReal 0 1)
  rw [pi_expandedGaussian_eq_withDensity a (fun i => (ha i).ne'),
    BrownianSharp.GaussianDensity.standardGaussian_eq_withDensity,
    ← withDensity_smul (μ := (volume : Measure (ι → ℝ)))
      (ENNReal.ofReal (∏ i, a i))
      (hf := (GaussianDensity.density_measurable.ennreal_ofReal))]
  apply withDensity_mono
  filter_upwards with x
  rw [Pi.smul_apply, smul_eq_mul, ← ENNReal.ofReal_mul hprod]
  exact ENNReal.ofReal_le_ofReal (expandedDensity_ge a ha ha1 x)

private theorem reciprocalScale_map_standardGaussian {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, a i ≠ 0) :
    (BrownianSharp.productStandardGaussian ι).map
        (fun x i => (a i)⁻¹ * x i) =
      Measure.pi (fun i : ι => gaussianReal 0
        ⟨(a i)⁻¹ ^ 2, by positivity⟩) := by
  have h := Measure.pi_map_pi
    (μ := fun _ : ι => gaussianReal 0 1)
    (f := fun i : ι => fun x : ℝ => (a i)⁻¹ * x)
    (hf := fun i => (by fun_prop : AEMeasurable (fun x : ℝ => (a i)⁻¹ * x)
      (gaussianReal 0 1)))
  calc
    (BrownianSharp.productStandardGaussian ι).map
        (fun x i => (a i)⁻¹ * x i) =
      Measure.pi (fun i => (gaussianReal 0 1).map (fun x => (a i)⁻¹ * x)) := h
    _ = Measure.pi (fun i : ι => gaussianReal 0
          ⟨(a i)⁻¹ ^ 2, by positivity⟩) := by
      congr 1
      funext i
      rw [gaussianReal_map_const_mul]
      congr 1
      · simp
      · apply Subtype.ext
        simp [pow_two, inv_pow, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- Product standard Gaussian gives the contracted preimage at least the
coordinate-volume factor times the original set mass. -/
theorem productGaussian_diagonal_dilation_preimage_ge {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1)
    {S : Set (ι → ℝ)} (hS : MeasurableSet S) :
    BrownianSharp.productStandardGaussian ι S ≥
      ENNReal.ofReal (∏ i, a i) * BrownianSharp.productStandardGaussian ι
        ((fun z i => a i * z i) ⁻¹' S) := by
  let C : (ι → ℝ) → (ι → ℝ) := fun x i => (a i)⁻¹ * x i
  have hmap : (BrownianSharp.productStandardGaussian ι).map C =
      Measure.pi (fun i : ι => gaussianReal 0 ⟨(a i)⁻¹ ^ 2, by positivity⟩) :=
    reciprocalScale_map_standardGaussian a (fun i => (ha i).ne')
  have hmeas : Measurable C := by
    change Measurable (fun (x : ι → ℝ) i => (a i)⁻¹ * x i)
    fun_prop
  have hle := expandedProductGaussian_ge_smul a ha ha1
  have hmeasure : (BrownianSharp.productStandardGaussian ι).map C ≥
      ENNReal.ofReal (∏ i, a i) • BrownianSharp.productStandardGaussian ι := by
    rw [hmap]
    exact hle
  let D : (ι → ℝ) → (ι → ℝ) := fun z i => a i * z i
  let A : Set (ι → ℝ) := D ⁻¹' S
  have hA : MeasurableSet A := hS.preimage (by
    change Measurable (fun (z : ι → ℝ) i => a i * z i)
    fun_prop)
  have hset : C ⁻¹' A = S := by
    ext x
    change D (C x) ∈ S ↔ x ∈ S
    constructor
    · intro hx
      have heq : D (C x) = x := by
        funext i
        dsimp [D, C]
        calc
          a i * ((a i)⁻¹ * x i) = (a i * (a i)⁻¹) * x i := (mul_assoc _ _ _).symm
          _ = x i := by rw [mul_inv_cancel₀ (ne_of_gt (ha i)), one_mul]
      rwa [heq] at hx
    · intro hx
      change D (C x) ∈ S
      have heq : D (C x) = x := by
        funext i
        dsimp [D, C]
        calc
          a i * ((a i)⁻¹ * x i) = (a i * (a i)⁻¹) * x i := (mul_assoc _ _ _).symm
          _ = x i := by rw [mul_inv_cancel₀ (ne_of_gt (ha i)), one_mul]
      rwa [heq]
  have hval := Measure.le_iff.mp hmeasure A hA
  rw [Measure.map_apply hmeas hA, Measure.coe_smul, Pi.smul_apply, smul_eq_mul] at hval
  rw [hset] at hval
  exact hval

end BrownianSharp.AlignmentExponentialDiagonalDilation
