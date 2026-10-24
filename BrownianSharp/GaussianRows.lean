import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic

/-!
Gaussian laws and covariance of finite evaluation rows from independent
standard coordinates. The covariance is the actual row dot product, including
all transverse overlaps.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BrownianSharp.GaussianRows

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ) (hG : ∀ i, Measurable (G i))
    (hLaw : ∀ i, P.map (G i) = gaussianReal 0 1)

include hG hLaw

/-- A native coordinate's law, with the measurability condition displayed. -/
theorem coordinate_hasLaw (i : ι) : HasLaw (G i) (gaussianReal 0 1) P :=
  ⟨(hG i).aemeasurable, hLaw i⟩

theorem coordinate_gaussian (i : ι) : HasGaussianLaw (G i) P :=
  (coordinate_hasLaw G hG hLaw i).hasGaussianLaw

theorem coordinate_mean (i : ι) : ∫ ω, G i ω ∂P = 0 := by
  rw [(coordinate_hasLaw G hG hLaw i).integral_eq, integral_id_gaussianReal]

theorem coordinate_variance (i : ι) : ProbabilityTheory.variance (G i) P = 1 := by
  rw [(coordinate_hasLaw G hG hLaw i).variance_eq, variance_id_gaussianReal]
  rfl

noncomputable def row (G : ι → Ω → ℝ) (c : ι → ℝ) (ω : Ω) : ℝ := ∑ i, c i * G i ω

theorem row_gaussian (hIndep : iIndepFun G P) (c : ι → ℝ) :
    HasGaussianLaw (row G c) P := by
  have hScaled : iIndepFun (fun i ω => c i * G i ω) P := by
    simpa [Function.comp_def] using
      hIndep.comp (fun i x => c i * x) (fun _ => measurable_const.mul measurable_id)
  apply hScaled.hasGaussianLaw_fun_sum
  intro i
  convert (coordinate_gaussian G hG hLaw i).smul (c i) using 1

theorem row_mean (c : ι → ℝ) : ∫ ω, row G c ω ∂P = 0 := by
  unfold row
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, coordinate_mean G hG hLaw]
    simp
  · intro i hi
    exact ((coordinate_gaussian G hG hLaw i).memLp_two.integrable (by norm_num)).const_mul _

theorem coordinates_covariance (hIndep : iIndepFun G P) [DecidableEq ι] (i j : ι) :
    cov[G i, G j; P] = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    rw [covariance_self (hG i).aemeasurable, coordinate_variance G hG hLaw]
    simp
  · rw [if_neg hij]
    exact (hIndep.indepFun hij).covariance_eq_zero
      (coordinate_gaussian G hG hLaw i).memLp_two
      (coordinate_gaussian G hG hLaw j).memLp_two

/-- All mixed row covariance is retained exactly. -/
theorem row_covariance (hIndep : iIndepFun G P) (c d : ι → ℝ) :
    cov[row G c, row G d; P] = ∑ i, c i * d i := by
  classical
  have hLc : ∀ i, MemLp (fun ω => c i * G i ω) 2 P :=
    fun i => (coordinate_gaussian G hG hLaw i).memLp_two.const_mul _
  have hLd : ∀ i, MemLp (fun ω => d i * G i ω) 2 P :=
    fun i => (coordinate_gaussian G hG hLaw i).memLp_two.const_mul _
  unfold row
  rw [covariance_fun_sum_fun_sum hLc hLd]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    coordinates_covariance G hG hLaw hIndep]
  simp

theorem row_variance (hIndep : iIndepFun G P) (c : ι → ℝ) :
    ProbabilityTheory.variance (row G c) P = ∑ i, c i ^ 2 := by
  rw [← covariance_self (row_gaussian G hG hLaw hIndep c).aemeasurable,
    row_covariance G hG hLaw hIndep]
  simp [pow_two]

/-- The finite row has its actual variance, with no scalar surrogate. -/
theorem row_law (hIndep : iIndepFun G P) (c : ι → ℝ) :
    P.map (row G c) = gaussianReal 0 (∑ i, c i ^ 2).toNNReal := by
  rw [(row_gaussian G hG hLaw hIndep c).map_eq_gaussianReal,
    row_mean G hG hLaw, row_variance G hG hLaw hIndep]

/-- Standardization uses the actual row variance, and requires precisely its
strict positivity. -/
theorem normalized_row_law (hIndep : iIndepFun G P) (c : ι → ℝ)
    (hv : 0 < ∑ i, c i ^ 2) :
    P.map (fun ω => row G c ω / Real.sqrt (∑ i, c i ^ 2)) = gaussianReal 0 1 := by
  let v : ℝ := ∑ i, c i ^ 2
  let s : ℝ := Real.sqrt v
  have hs : 0 < s := Real.sqrt_pos.mpr hv
  have hs2 : s ^ 2 = v := Real.sq_sqrt hv.le
  have hGaussian : HasGaussianLaw (fun ω => row G c ω / s) P := by
    convert (row_gaussian G hG hLaw hIndep c).smul s⁻¹ using 1
    funext ω
    change row G c ω / s = s⁻¹ * row G c ω
    ring
  have hmean : ∫ ω, row G c ω / s ∂P = 0 := by
    rw [integral_div, row_mean G hG hLaw]
    simp
  have hvariance : ProbabilityTheory.variance (fun ω => row G c ω / s) P = 1 := by
    simp_rw [div_eq_mul_inv, mul_comm (row G c _) s⁻¹]
    rw [variance_const_mul, row_variance G hG hLaw hIndep]
    change s⁻¹ ^ 2 * v = 1
    rw [← hs2]
    field_simp
  rw [hGaussian.map_eq_gaussianReal, hmean, hvariance]
  norm_num

end BrownianSharp.GaussianRows
