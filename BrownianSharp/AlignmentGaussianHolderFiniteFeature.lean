import BrownianSharp.AlignmentGaussianFiniteFeature
import BrownianSharp.AlignmentHolderGaussianChaining
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory HaarQuarter
open scoped BigOperators NNReal
namespace BrownianSharp.AlignmentGaussianHolderFiniteFeature

open BrownianSharp.AlignmentGaussianFiniteFeature
open BrownianSharp.AlignmentGaussianChaining
open BrownianSharp.AlignmentHolderGaussianChaining

/-- Expected continuum norm for a finite Gaussian feature sum with arbitrary
positive Hölder exponent. A squared increment bound by `R * dist^(2h)` gives
near-pair scale `sqrt R * 2^h * 2^(-hN)` on the dyadic chain. -/
theorem finiteGaussianFeaturePath_expected_norm_holder
    {d : ℕ} {ι : Type*} [Fintype ι]
    (h : ℝ) (hh : 0 < h)
    (v : ι → C(BrownianCubeAnchor d, ℝ)) (σ R : ℝ)
    (hσ : 0 ≤ σ) (hR : 0 ≤ R)
    (hvar : ∀ x, ∑ i, (v i x)^2 ≤ σ^2)
    (hincrement : ∀ x y, ∑ i, (v i x - v i y)^2 ≤ R * (dist x y)^(2*h))
    (n₀ : ℕ) :
    Integrable (fun z => ‖finiteGaussianFeaturePath v z‖)
        (productStandardGaussian ι) ∧
      (∫ z, ‖finiteGaussianFeaturePath v z‖ ∂productStandardGaussian ι) ≤
        holderChainingConstant d h * Real.sqrt ((n₀:ℝ)+1) *
          (σ + Real.sqrt R * (2:ℝ)^h * (2:ℝ)^(-h*(n₀:ℝ))) := by
  let vp : BrownianCubeAnchor d → ℝ≥0 := fun x =>
    (∑ i, (v i x)^2).toNNReal
  let vi : (N : ℕ) → CubeNearPairs d N → ℝ≥0 := fun N p =>
    (∑ i, (v i (cubeDyadicAnchor p.val.2) -
      v i (cubeDyadicAnchor p.val.1))^2).toNNReal
  apply gaussian_chaining_expected_norm_holder h hh (productStandardGaussian ι)
    (finiteGaussianFeaturePath v) (finiteGaussianFeaturePath_continuous v).measurable
    vp vi (finiteGaussianFeaturePath_eval_hasLaw v)
    (fun N p => finiteGaussianFeaturePath_increment_hasLaw v
      (cubeDyadicAnchor p.val.2) (cubeDyadicAnchor p.val.1))
    σ (Real.sqrt R * (2:ℝ)^h) hσ (by positivity)
  · intro x
    simpa only [vp, Real.coe_toNNReal _
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] using hvar x
  · intro N p
    have hd : dist (cubeDyadicAnchor p.val.2) (cubeDyadicAnchor p.val.1) ≤ 2*((2:ℝ)^N)⁻¹ := by
      simpa only [dist_comm] using p.property
    have hpow : (dist (cubeDyadicAnchor p.val.2) (cubeDyadicAnchor p.val.1))^(2*h) ≤
        (2*((2:ℝ)^N)⁻¹)^(2*h) :=
      Real.rpow_le_rpow (dist_nonneg) hd (by positivity)
    have hmesh : 2*((2:ℝ)^N)⁻¹ = (2:ℝ)^((1:ℝ)-(N:ℝ)) := by
      calc
        _ = 2*(2:ℝ)^(-(N:ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num : (0:ℝ)≤2)]
        _ = (2:ℝ)^(1:ℝ) * (2:ℝ)^(-(N:ℝ)) := by rw [Real.rpow_one]
        _ = (2:ℝ)^((1:ℝ)-(N:ℝ)) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ)<2)]
          congr 1 <;> ring
    have hmeshPow : ((2:ℝ)^((1:ℝ)-(N:ℝ)))^(2*h) =
        (2:ℝ)^(2*h) * (2:ℝ)^(-2*h*(N:ℝ)) := by
      rw [← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
      rw [show ((1:ℝ)-(N:ℝ))*(2*h) = 2*h + (-2*h*(N:ℝ)) by ring]
      rw [Real.rpow_add (by norm_num : (0:ℝ)<2)]
    have hsqH : ((2:ℝ)^h)^2 = (2:ℝ)^(2*h) := by
      calc
        _ = Real.rpow (Real.rpow 2 h) (2:ℝ) := (Real.rpow_natCast _ _).symm
        _ = Real.rpow 2 (h*2) := (Real.rpow_mul (by norm_num : (0:ℝ)≤2) h 2).symm
        _ = _ := by congr 1 <;> ring
    have hsqN : ((2:ℝ)^(-h*(N:ℝ)))^2 = (2:ℝ)^(-2*h*(N:ℝ)) := by
      calc
        _ = Real.rpow (Real.rpow 2 (-h*(N:ℝ))) (2:ℝ) := (Real.rpow_natCast _ _).symm
        _ = Real.rpow 2 ((-h*(N:ℝ))*2) :=
          (Real.rpow_mul (by norm_num : (0:ℝ)≤2) (-h*(N:ℝ)) 2).symm
        _ = _ := by congr 1 <;> ring
    have hLsq : (Real.sqrt R * (2:ℝ)^h * (2:ℝ)^(-h*(N:ℝ)))^2 =
        R * (2*((2:ℝ)^N)⁻¹)^(2*h) := by
      calc
        _ = R * (((2:ℝ)^h)^2 * ((2:ℝ)^(-h*(N:ℝ)))^2) := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hR]
          ring
        _ = R * ((2:ℝ)^(2*h) * (2:ℝ)^(-2*h*(N:ℝ))) := by
          rw [hsqH, hsqN]
        _ = R * (((2:ℝ)^((1:ℝ)-(N:ℝ)))^(2*h)) := by
          rw [hmeshPow]
        _ = _ := by rw [hmesh]
    have hbound : R * (dist (cubeDyadicAnchor p.val.2)
        (cubeDyadicAnchor p.val.1))^(2*h) ≤
        (Real.sqrt R * (2:ℝ)^h * (2:ℝ)^(-h*(N:ℝ)))^2 := by
      calc
        _ ≤ R * (2*((2:ℝ)^N)⁻¹)^(2*h) := mul_le_mul_of_nonneg_left hpow hR
        _ = _ := hLsq.symm
    have hincr_here := hincrement (cubeDyadicAnchor p.val.2) (cubeDyadicAnchor p.val.1)
    have hnonneg : 0 ≤ ∑ i,
        (v i (cubeDyadicAnchor p.val.2)-v i (cubeDyadicAnchor p.val.1))^2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hle : ∑ i,
        (v i (cubeDyadicAnchor p.val.2)-v i (cubeDyadicAnchor p.val.1))^2 ≤
        (Real.sqrt R * (2:ℝ)^h * (2:ℝ)^(-h*(N:ℝ)))^2 := hincr_here.trans hbound
    simpa only [vi, Real.coe_toNNReal _ hnonneg] using hle
end BrownianSharp.AlignmentGaussianHolderFiniteFeature
