import BrownianSharp.GaussianSquareMGF
import BrownianSharp.GaussianGridStatistics
import Mathlib.Probability.Moments.Basic

/-!
# Product Gaussian chi-square moments

This module lifts the proved one-coordinate Gaussian-square MGF to a finite
product.  It is the analytic probability input needed for the fixed-vector
part of the Gaussian RIP union bound.
-/

namespace BrownianSharp.GaussianRIP

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The exponential of a finite Gaussian squared norm is integrable below
the chi-square MGF singularity. -/
theorem integrable_exp_mul_productGaussian_sqNorm {κ : Type*} [Fintype κ]
    (t : ℝ) (ht : t < 1 / 2) :
    Integrable (fun x : κ → ℝ => Real.exp (t * ∑ i, x i ^ 2))
      (BrownianSharp.productStandardGaussian κ) := by
  let μ := BrownianSharp.productStandardGaussian κ
  let X : κ → (κ → ℝ) → ℝ := fun i x => x i ^ 2
  have hcoord : iIndepFun (fun i : κ => fun x : κ → ℝ => x i) μ :=
    BrownianSharp.productStandardGaussian_coordinates_independent κ
  have hsq : iIndepFun X μ :=
    hcoord.comp (fun (_ : κ) (z : ℝ) => z ^ 2) (fun _ => by fun_prop)
  have hInt : ∀ i ∈ Finset.univ, Integrable (fun x : κ → ℝ =>
      Real.exp (t * X i x)) μ := by
    intro i hi
    have hLaw : HasLaw (fun x : κ → ℝ => x i) (gaussianReal 0 1) μ :=
      ⟨(measurable_pi_apply i).aemeasurable,
        BrownianSharp.productStandardGaussian_coordinate_law i⟩
    simpa [X, Function.comp_def] using
      hLaw.integrable_comp (integrable_exp_mul_sq_gaussianReal t ht)
  have h := hsq.integrable_exp_mul_sum (fun i => by fun_prop) hInt
  simpa [X, Finset.sum_apply] using h

/-- The MGF of the squared Euclidean norm of a finite standard Gaussian vector. -/
theorem productGaussian_sqNorm_mgf {κ : Type*} [Fintype κ]
    (t : ℝ) (ht : t < 1 / 2) :
    ProbabilityTheory.mgf (fun x : κ → ℝ => ∑ i, x i ^ 2)
        (BrownianSharp.productStandardGaussian κ) t =
      (Real.sqrt (1 - 2 * t))⁻¹ ^ Fintype.card κ := by
  let μ := BrownianSharp.productStandardGaussian κ
  let X : κ → (κ → ℝ) → ℝ := fun i x => x i ^ 2
  have hcoord : iIndepFun (fun i : κ => fun x : κ → ℝ => x i) μ :=
    BrownianSharp.productStandardGaussian_coordinates_independent κ
  have hsq : iIndepFun X μ := by
    exact hcoord.comp (fun (_ : κ) (z : ℝ) => z ^ 2) (fun _ => by fun_prop)
  have hmgf : ∀ i : κ, ProbabilityTheory.mgf (X i) μ t =
      (Real.sqrt (1 - 2 * t))⁻¹ := by
    intro i
    rw [ProbabilityTheory.mgf]
    change (∫ x : κ → ℝ, Real.exp (t * (x i) ^ 2) ∂μ) = _
    have hmeas : AEMeasurable (fun x : κ → ℝ => x i) μ :=
      (measurable_pi_apply i).aemeasurable
    rw [← integral_map hmeas (by fun_prop : AEStronglyMeasurable
      (fun y : ℝ => Real.exp (t * y ^ 2)) (Measure.map (fun x : κ → ℝ => x i) μ))]
    rw [BrownianSharp.productStandardGaussian_coordinate_law]
    exact integral_exp_mul_sq_gaussianReal t ht
  rw [show (fun x : κ → ℝ => ∑ i, x i ^ 2) = fun x => ∑ i ∈ Finset.univ, X i x by
    funext x
    simp [X]]
  have hsumfun : (fun x : κ → ℝ => ∑ i ∈ Finset.univ, X i x) =
      ∑ i ∈ Finset.univ, X i := by
    funext x
    simp [Finset.sum_apply]
  rw [hsumfun]
  rw [hsq.mgf_sum (fun i => by fun_prop) Finset.univ]
  simp_rw [hmgf]
  rw [Finset.prod_const, Finset.card_univ]

private theorem sqrt_two_le_exp_three_fourths :
    Real.sqrt 2 ≤ Real.exp (3 / 4 : ℝ) := by
  have hs : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  have he := Real.add_one_le_exp (3 / 4 : ℝ)
  norm_num at he
  linarith

/-- A coarse but exponentially small upper tail for a standard Gaussian
squared norm. -/
theorem productGaussian_sqNorm_upper_tail {κ : Type*} [Fintype κ] :
    (BrownianSharp.productStandardGaussian κ).real
        {x : κ → ℝ | 4 * (Fintype.card κ : ℝ) ≤ ∑ i, x i ^ 2} ≤
      Real.exp (-(Fintype.card κ : ℝ) / 4) := by
  let μ := BrownianSharp.productStandardGaussian κ
  let S : (κ → ℝ) → ℝ := fun x => ∑ i, x i ^ 2
  have hInt := integrable_exp_mul_productGaussian_sqNorm (κ := κ) (1 / 4 : ℝ) (by norm_num)
  have hchern := ProbabilityTheory.measure_ge_le_exp_mul_mgf
    (X := S) (μ := μ) (ε := 4 * (Fintype.card κ : ℝ)) (t := (1 / 4 : ℝ))
    (by norm_num) hInt
  have hmgf : ProbabilityTheory.mgf S μ (1 / 4 : ℝ) =
      (Real.sqrt 2) ^ Fintype.card κ := by
    rw [show S = fun x : κ → ℝ => ∑ i, x i ^ 2 by rfl]
    rw [productGaussian_sqNorm_mgf (κ := κ) (1 / 4 : ℝ) (by norm_num)]
    congr 1
    norm_num
  rw [show (BrownianSharp.productStandardGaussian κ).real
      {x : κ → ℝ | 4 * (Fintype.card κ : ℝ) ≤ ∑ i, x i ^ 2} =
        μ.real {x | 4 * (Fintype.card κ : ℝ) ≤ S x} by rfl]
  calc
    μ.real {x | 4 * (Fintype.card κ : ℝ) ≤ S x} ≤
        Real.exp (-(1 / 4 : ℝ) * (4 * (Fintype.card κ : ℝ))) *
          ProbabilityTheory.mgf S μ (1 / 4 : ℝ) := hchern
    _ = Real.exp (-(Fintype.card κ : ℝ)) * (Real.sqrt 2) ^ Fintype.card κ := by
      rw [hmgf]
      congr 1
      ring
    _ ≤ Real.exp (-(Fintype.card κ : ℝ) / 4) := by
      have hn : (Real.sqrt 2) ^ Fintype.card κ ≤
          (Real.exp (3 / 4 : ℝ)) ^ Fintype.card κ := by
        gcongr
        exact sqrt_two_le_exp_three_fourths
      rw [← Real.exp_nat_mul] at hn
      have hsum : Real.exp (-(Fintype.card κ : ℝ)) *
          Real.exp ((Fintype.card κ : ℝ) * (3 / 4)) =
          Real.exp (-(Fintype.card κ : ℝ) / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ ≤ Real.exp (-(Fintype.card κ : ℝ)) *
            Real.exp ((Fintype.card κ : ℝ) * (3 / 4)) := by
          exact mul_le_mul_of_nonneg_left hn (Real.exp_nonneg _)
        _ = Real.exp (-(Fintype.card κ : ℝ) / 4) := hsum

private theorem exp_half_le_sqrt_three :
    Real.exp (1 / 2 : ℝ) ≤ Real.sqrt 3 := by
  have h := Real.exp_le_two_add_div_two_sub
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 2)
  have hs : (5 / 3 : ℝ) ≤ Real.sqrt 3 := by
    have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hnonneg := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  norm_num at h
  linarith

/-- A coarse lower tail bound for the squared norm.  The threshold `m/4`
is the one needed to verify the lower half of a norm RIP estimate. -/
theorem productGaussian_sqNorm_lower_tail {κ : Type*} [Fintype κ] :
    (BrownianSharp.productStandardGaussian κ).real
        {x : κ → ℝ | ∑ i, x i ^ 2 ≤ (Fintype.card κ : ℝ) / 4} ≤
      Real.exp (-(Fintype.card κ : ℝ) / 4) := by
  let μ := BrownianSharp.productStandardGaussian κ
  let S : (κ → ℝ) → ℝ := fun x => ∑ i, x i ^ 2
  have hInt := integrable_exp_mul_productGaussian_sqNorm (κ := κ) (-1 : ℝ) (by norm_num)
  have hchern := ProbabilityTheory.measure_le_le_exp_mul_mgf
    (X := S) (μ := μ) (ε := (Fintype.card κ : ℝ) / 4) (t := (-1 : ℝ))
    (by norm_num) hInt
  have hmgf : ProbabilityTheory.mgf S μ (-1 : ℝ) = (Real.sqrt 3)⁻¹ ^ Fintype.card κ := by
    rw [productGaussian_sqNorm_mgf (κ := κ) (-1 : ℝ) (by norm_num)]
    congr 1
    norm_num
  rw [show (BrownianSharp.productStandardGaussian κ).real
      {x : κ → ℝ | ∑ i, x i ^ 2 ≤ (Fintype.card κ : ℝ) / 4} =
        μ.real {x | S x ≤ (Fintype.card κ : ℝ) / 4} by rfl]
  calc
    μ.real {x | S x ≤ (Fintype.card κ : ℝ) / 4} ≤
        Real.exp (-(-1 : ℝ) * ((Fintype.card κ : ℝ) / 4)) *
          ProbabilityTheory.mgf S μ (-1 : ℝ) := hchern
    _ = Real.exp ((Fintype.card κ : ℝ) / 4) *
          (Real.sqrt 3)⁻¹ ^ Fintype.card κ := by
      rw [hmgf]
      congr 1
      congr 1 <;> ring
    _ ≤ Real.exp (-(Fintype.card κ : ℝ) / 4) := by
      have hn : (Real.exp (1 / 2 : ℝ)) ^ Fintype.card κ ≤
          (Real.sqrt 3) ^ Fintype.card κ := by
        gcongr
        exact exp_half_le_sqrt_three
      have hn' := mul_le_mul_of_nonneg_right hn
        (Real.exp_nonneg ((Fintype.card κ : ℝ) / 4))
      have hsqrtpos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
      have hrewrite : (Real.exp (1 / 2 : ℝ)) ^ Fintype.card κ =
          Real.exp ((Fintype.card κ : ℝ) / 2) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have hmul : Real.exp ((Fintype.card κ : ℝ) / 4) *
          (Real.sqrt 3)⁻¹ ^ Fintype.card κ ≤
          Real.exp ((Fintype.card κ : ℝ) / 4) *
            (Real.exp (1 / 2 : ℝ))⁻¹ ^ Fintype.card κ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        have hinv : (Real.sqrt 3)⁻¹ ≤ (Real.exp (1 / 2 : ℝ))⁻¹ :=
          (inv_le_inv₀ (Real.sqrt_pos.2 (by norm_num)) (Real.exp_pos _)).2
            exp_half_le_sqrt_three
        exact pow_le_pow_left₀ (by positivity) hinv _
      rw [hrewrite] at hn'
      have hpow : (Real.exp (1 / 2 : ℝ))⁻¹ ^ Fintype.card κ =
          Real.exp (-((Fintype.card κ : ℝ) / 2)) := by
        calc
          (Real.exp (1 / 2 : ℝ))⁻¹ ^ Fintype.card κ =
              ((Real.exp (1 / 2 : ℝ)) ^ Fintype.card κ)⁻¹ := by rw [inv_pow]
          _ = (Real.exp ((Fintype.card κ : ℝ) * (1 / 2)))⁻¹ := by
            rw [← Real.exp_nat_mul]
          _ = Real.exp (-((Fintype.card κ : ℝ) * (1 / 2))) := by rw [← Real.exp_neg]
          _ = Real.exp (-((Fintype.card κ : ℝ) / 2)) := by congr 1 <;> ring
      rw [hpow] at hmul
      rw [← Real.exp_add] at hmul
      have hfinal : (Fintype.card κ : ℝ) / 4 - (Fintype.card κ : ℝ) / 2 =
          -(Fintype.card κ : ℝ) / 4 := by ring
      convert hmul using 1 <;> congr 1 <;> ring

private theorem sqrt_two_le_exp_seven_sixteenths :
    Real.sqrt 2 ≤ Real.exp (7 / 16 : ℝ) := by
  have hs : Real.sqrt 2 ≤ (23 / 16 : ℝ) := by
    have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    have hnonneg := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have he := Real.add_one_le_exp (7 / 16 : ℝ)
  norm_num at he
  linarith

/-- A stronger upper tail threshold useful for extending a sphere net to an
operator norm estimate. -/
theorem productGaussian_sqNorm_upper_tail_two {κ : Type*} [Fintype κ] :
    (BrownianSharp.productStandardGaussian κ).real
        {x : κ → ℝ | 2 * (Fintype.card κ : ℝ) ≤ ∑ i, x i ^ 2} ≤
      Real.exp (-(Fintype.card κ : ℝ) / 16) := by
  let μ := BrownianSharp.productStandardGaussian κ
  let S : (κ → ℝ) → ℝ := fun x => ∑ i, x i ^ 2
  have hInt := integrable_exp_mul_productGaussian_sqNorm (κ := κ) (1 / 4 : ℝ) (by norm_num)
  have hchern := ProbabilityTheory.measure_ge_le_exp_mul_mgf
    (X := S) (μ := μ) (ε := 2 * (Fintype.card κ : ℝ)) (t := (1 / 4 : ℝ))
    (by norm_num) hInt
  have hmgf : ProbabilityTheory.mgf S μ (1 / 4 : ℝ) =
      (Real.sqrt 2) ^ Fintype.card κ := by
    rw [productGaussian_sqNorm_mgf (κ := κ) (1 / 4 : ℝ) (by norm_num)]
    congr 1
    norm_num
  rw [show (BrownianSharp.productStandardGaussian κ).real
      {x : κ → ℝ | 2 * (Fintype.card κ : ℝ) ≤ ∑ i, x i ^ 2} =
        μ.real {x | 2 * (Fintype.card κ : ℝ) ≤ S x} by rfl]
  calc
    μ.real {x | 2 * (Fintype.card κ : ℝ) ≤ S x} ≤
        Real.exp (-(1 / 4 : ℝ) * (2 * (Fintype.card κ : ℝ))) *
          ProbabilityTheory.mgf S μ (1 / 4 : ℝ) := hchern
    _ = Real.exp (-(Fintype.card κ : ℝ) / 2) *
          (Real.sqrt 2) ^ Fintype.card κ := by
      rw [hmgf]
      congr 1 <;> ring
    _ ≤ Real.exp (-(Fintype.card κ : ℝ) / 16) := by
      have hn : (Real.sqrt 2) ^ Fintype.card κ ≤
          (Real.exp (7 / 16 : ℝ)) ^ Fintype.card κ := by
        gcongr
        exact sqrt_two_le_exp_seven_sixteenths
      rw [← Real.exp_nat_mul] at hn
      have heq : (Fintype.card κ : ℝ) * (7 / 16) =
          (Fintype.card κ : ℝ) * (7 / 16) := rfl
      calc
        _ ≤ Real.exp (-(Fintype.card κ : ℝ) / 2) *
            Real.exp ((Fintype.card κ : ℝ) * (7 / 16)) :=
          mul_le_mul_of_nonneg_left hn (Real.exp_nonneg _)
        _ = Real.exp (-(Fintype.card κ : ℝ) / 16) := by
          rw [← Real.exp_add]
          congr 1
          ring

private theorem exp_fiftyone_hundredths_le_sqrt_three :
    Real.exp (51 / 100 : ℝ) ≤ Real.sqrt 3 := by
  have h := Real.exp_le_two_add_div_two_sub
    (by norm_num : (0 : ℝ) ≤ 51 / 100) (by norm_num : (51 / 100 : ℝ) < 2)
  have hs : (251 / 149 : ℝ) ≤ Real.sqrt 3 := by
    have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    have hnonneg := Real.sqrt_nonneg (3 : ℝ)
    nlinarith
  norm_num at h
  linarith

/-- A lower-tail estimate at squared radius `m/2`, with a conservative
exponential rate. -/
theorem productGaussian_sqNorm_lower_tail_half {κ : Type*} [Fintype κ] :
    (BrownianSharp.productStandardGaussian κ).real
        {x : κ → ℝ | ∑ i, x i ^ 2 ≤ (Fintype.card κ : ℝ) / 2} ≤
      Real.exp (-(Fintype.card κ : ℝ) / 100) := by
  let μ := BrownianSharp.productStandardGaussian κ
  let S : (κ → ℝ) → ℝ := fun x => ∑ i, x i ^ 2
  have hInt := integrable_exp_mul_productGaussian_sqNorm (κ := κ) (-1 : ℝ) (by norm_num)
  have hchern := ProbabilityTheory.measure_le_le_exp_mul_mgf
    (X := S) (μ := μ) (ε := (Fintype.card κ : ℝ) / 2) (t := (-1 : ℝ))
    (by norm_num) hInt
  have hmgf : ProbabilityTheory.mgf S μ (-1 : ℝ) = (Real.sqrt 3)⁻¹ ^ Fintype.card κ := by
    rw [productGaussian_sqNorm_mgf (κ := κ) (-1 : ℝ) (by norm_num)]
    congr 1
    norm_num
  rw [show (BrownianSharp.productStandardGaussian κ).real
      {x : κ → ℝ | ∑ i, x i ^ 2 ≤ (Fintype.card κ : ℝ) / 2} =
        μ.real {x | S x ≤ (Fintype.card κ : ℝ) / 2} by rfl]
  calc
    μ.real {x | S x ≤ (Fintype.card κ : ℝ) / 2} ≤
        Real.exp (-(-1 : ℝ) * ((Fintype.card κ : ℝ) / 2)) *
          ProbabilityTheory.mgf S μ (-1 : ℝ) := hchern
    _ = Real.exp ((Fintype.card κ : ℝ) / 2) *
          (Real.sqrt 3)⁻¹ ^ Fintype.card κ := by
      rw [hmgf]
      congr 1 <;> ring
    _ ≤ Real.exp (-(Fintype.card κ : ℝ) / 100) := by
      have hn : (Real.exp (51 / 100 : ℝ)) ^ Fintype.card κ ≤
          (Real.sqrt 3) ^ Fintype.card κ := by
        gcongr
        exact exp_fiftyone_hundredths_le_sqrt_three
      have hpow : (Real.exp (51 / 100 : ℝ))⁻¹ ^ Fintype.card κ =
          Real.exp (-((Fintype.card κ : ℝ) * (51 / 100))) := by
        calc
          _ = ((Real.exp (51 / 100 : ℝ)) ^ Fintype.card κ)⁻¹ := by rw [inv_pow]
          _ = (Real.exp ((Fintype.card κ : ℝ) * (51 / 100)))⁻¹ := by
            rw [← Real.exp_nat_mul]
          _ = Real.exp (-((Fintype.card κ : ℝ) * (51 / 100))) := by rw [← Real.exp_neg]
      have hinv : (Real.sqrt 3)⁻¹ ≤ (Real.exp (51 / 100 : ℝ))⁻¹ :=
        (inv_le_inv₀ (Real.sqrt_pos.2 (by norm_num)) (Real.exp_pos _)).2
          exp_fiftyone_hundredths_le_sqrt_three
      have hpowle : (Real.sqrt 3)⁻¹ ^ Fintype.card κ ≤
          (Real.exp (51 / 100 : ℝ))⁻¹ ^ Fintype.card κ :=
        pow_le_pow_left₀ (by positivity) hinv _
      rw [hpow] at hpowle
      calc
        _ ≤ Real.exp ((Fintype.card κ : ℝ) / 2) *
            Real.exp (-((Fintype.card κ : ℝ) * (51 / 100))) :=
          mul_le_mul_of_nonneg_left hpowle (Real.exp_nonneg _)
        _ = Real.exp (-(Fintype.card κ : ℝ) / 100) := by
          rw [← Real.exp_add]
          congr 1
          ring

end BrownianSharp.GaussianRIP
