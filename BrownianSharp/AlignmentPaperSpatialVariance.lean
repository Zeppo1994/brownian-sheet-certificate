import BrownianSharp.AlignmentPaperSpatialExponential
import BrownianSharp.SmoothGaussian
import BrownianSharp.ActualConcentration
import BrownianSharp.NativeShellSum
import BrownianSharp.GaussianPairMoments
import Mathlib.Probability.Moments.Covariance
import BrownianSharp.ShellVariance
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option maxHeartbeats 800000

/-! Literal spatial integration and variance control for the Lemma 2.4
observable. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open BrownianSharp

namespace BrownianSharp.AlignmentPaperSpatialVariance

instance smoothGoodGridMeasurableSpace (d n : ℕ) :
    MeasurableSpace (SmoothGoodGrid d n) := ⊤

instance smoothGoodGridMeasurableSingletonClass (d n : ℕ) :
    MeasurableSingletonClass (SmoothGoodGrid d n) := ⟨fun _ => by trivial⟩

theorem row_overlap_abs_le_one {κ : Type*} [Fintype κ]
    (a b : κ → ℝ) (ha : ∑ i, a i ^ 2 = 1) (hb : ∑ i, b i ^ 2 = 1) :
    |∑ i, a i * b i| ≤ 1 := by
  calc
    |∑ i, a i * b i| ≤ ∑ i, |a i * b i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (a i ^ 2 + b i ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      nlinarith [sq_nonneg (|a i| - |b i|), sq_abs (a i), sq_abs (b i)]
    _ = 1 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, ha, hb]
      norm_num

theorem variance_eq_spatial_remainder_integral
    {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (a : α → κ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (ha : ∀ x, ∑ i, a x i ^ 2 = 1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) :
    ProbabilityTheory.variance
      (AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a)
      (productStandardGaussian κ) =
      ∫ p : α × α,
        (Real.cosh (τ * ∑ i, a p.1 i * a p.2 i) - 1) ∂(μ.prod μ) := by
  let K : α × α → ℝ := fun p => Real.cosh (τ * ∑ i, a p.1 i * a p.2 i)
  have hKmeas : Measurable K := by
    dsimp [K]
    fun_prop (disch := exact haMeas _)
  have hKbound (p : α × α) : ‖K p‖ ≤ Real.exp τ := by
    have hrho := row_overlap_abs_le_one (a p.1) (a p.2) (ha p.1) (ha p.2)
    have harg : |τ * ∑ i, a p.1 i * a p.2 i| ≤ τ := by
      rw [abs_mul, abs_of_nonneg hτ]
      exact mul_le_of_le_one_right hτ hrho
    have hcosh : Real.cosh (τ * ∑ i, a p.1 i * a p.2 i) ≤
        Real.exp |τ * ∑ i, a p.1 i * a p.2 i| := by
      rw [Real.cosh_eq]
      let u := τ * ∑ i, a p.1 i * a p.2 i
      have h₁ := Real.exp_le_exp.mpr (le_abs_self u)
      have h₂ := Real.exp_le_exp.mpr (show -u ≤ |u| by simpa using le_abs_self (-u))
      nlinarith
    change |Real.cosh (τ * ∑ i, a p.1 i * a p.2 i)| ≤ Real.exp τ
    rw [abs_of_nonneg (by rw [Real.cosh_eq]; positivity)]
    exact hcosh.trans (Real.exp_le_exp.mpr harg)
  have hK : Integrable K (μ.prod μ) := by
    apply Integrable.mono' (integrable_const (Real.exp τ)) hKmeas.aestronglyMeasurable
    filter_upwards with p
    simpa [Real.norm_of_nonneg (Real.exp_pos τ).le] using hKbound p
  have hKsub : Integrable (fun p : α × α => K p - 1) (μ.prod μ) :=
    hK.sub (integrable_const (1 : ℝ))
  have hmain := AlignmentPaperSpatialExponential.productGaussian_spatialCoshAverage_variance
    μ a τ hτ ha haMeas
  calc
    ProbabilityTheory.variance
        (AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a)
        (productStandardGaussian κ) = (∫ p, K p ∂(μ.prod μ)) - 1 := by
          rw [hmain, MeasureTheory.integral_prod _ hK]
    _ = ∫ p, K p - 1 ∂(μ.prod μ) := by
          have hmass : ∫ _ : α × α, (1 : ℝ) ∂(μ.prod μ) = 1 := by
            simp [integral_const]
          calc
            (∫ p, K p ∂(μ.prod μ)) - 1 =
                (∫ p, K p ∂(μ.prod μ)) - ∫ _ : α × α, (1 : ℝ) ∂(μ.prod μ) := by rw [hmass]
            _ = ∫ p, K p - 1 ∂(μ.prod μ) := (integral_sub hK (integrable_const (1 : ℝ))).symm

theorem variance_le_spatial_overlap_remainder
    {α κ : Type*} [MeasurableSpace α] [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (a : α → κ → ℝ) (τ : ℝ) (hτ : 0 ≤ τ)
    (ha : ∀ x, ∑ i, a x i ^ 2 = 1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) :
    ProbabilityTheory.variance
      (AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a)
      (productStandardGaussian κ) ≤
      ∫ p : α × α, (τ ^ 2 * (∑ i, a p.1 i * a p.2 i) ^ 2 / 2 *
        Real.exp (τ * |∑ i, a p.1 i * a p.2 i|)) ∂(μ.prod μ) := by
  let R : α × α → ℝ := fun p => τ ^ 2 * (∑ i, a p.1 i * a p.2 i) ^ 2 / 2 *
      Real.exp (τ * |∑ i, a p.1 i * a p.2 i|)
  let K : α × α → ℝ := fun p =>
      Real.cosh (τ * ∑ i, a p.1 i * a p.2 i) - 1
  have hRmeas : Measurable R := by
    dsimp [R]
    fun_prop (disch := exact haMeas _)
  have hKmeas : Measurable K := by
    dsimp [K]
    fun_prop (disch := exact haMeas _)
  have hρ (p : α × α) : |∑ i, a p.1 i * a p.2 i| ≤ 1 :=
    row_overlap_abs_le_one (a p.1) (a p.2) (ha p.1) (ha p.2)
  have hKbound (p : α × α) : ‖K p‖ ≤ Real.exp τ + 1 := by
    have harg : |τ * ∑ i, a p.1 i * a p.2 i| ≤ τ := by
      rw [abs_mul, abs_of_nonneg hτ]
      exact mul_le_of_le_one_right hτ (hρ p)
    have hcosh : Real.cosh (τ * ∑ i, a p.1 i * a p.2 i) ≤
        Real.exp |τ * ∑ i, a p.1 i * a p.2 i| := by
      rw [Real.cosh_eq]
      let u := τ * ∑ i, a p.1 i * a p.2 i
      have h₁ := Real.exp_le_exp.mpr (le_abs_self u)
      have h₂ := Real.exp_le_exp.mpr (show -u ≤ |u| by simpa using le_abs_self (-u))
      nlinarith
    have hnorm : ‖K p‖ ≤ Real.cosh (τ * ∑ i, a p.1 i * a p.2 i) + 1 := by
      change |Real.cosh (τ * ∑ i, a p.1 i * a p.2 i) - 1| ≤ _
      calc
        |Real.cosh (τ * ∑ i, a p.1 i * a p.2 i) - 1| ≤
            |Real.cosh (τ * ∑ i, a p.1 i * a p.2 i)| + 1 :=
              by simpa using (abs_sub_le
                (Real.cosh (τ * ∑ i, a p.1 i * a p.2 i)) (0 : ℝ) (1 : ℝ))
        _ = Real.cosh (τ * ∑ i, a p.1 i * a p.2 i) + 1 := by
          rw [abs_of_nonneg (by rw [Real.cosh_eq]; positivity)]
    calc
      ‖K p‖ ≤ Real.cosh (τ * ∑ i, a p.1 i * a p.2 i) + 1 := hnorm
      _ ≤ Real.exp τ + 1 := by
        calc
          Real.cosh (τ * ∑ i, a p.1 i * a p.2 i) + 1 ≤
              Real.exp |τ * ∑ i, a p.1 i * a p.2 i| + 1 := by
                simpa [add_comm] using add_le_add_right hcosh 1
          _ ≤ Real.exp τ + 1 := by
                simpa [add_comm] using add_le_add_right (Real.exp_le_exp.mpr harg) 1
  have hK : Integrable K (μ.prod μ) := by
    apply Integrable.mono' (integrable_const (Real.exp τ + 1)) hKmeas.aestronglyMeasurable
    filter_upwards with p
    simpa [Real.norm_of_nonneg (by positivity)] using hKbound p
  have hKsub : Integrable (fun p : α × α => K p) (μ.prod μ) := hK
  have hRbound (p : α × α) : ‖R p‖ ≤ τ ^ 2 / 2 * Real.exp τ := by
    have hρsq : (∑ i, a p.1 i * a p.2 i) ^ 2 ≤ 1 := by
      have h := hρ p
      have hmul := mul_le_mul h h (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith [sq_abs (∑ i, a p.1 i * a p.2 i)]
    have hexp : Real.exp (τ * |∑ i, a p.1 i * a p.2 i|) ≤ Real.exp τ := by
      apply Real.exp_le_exp.mpr
      exact mul_le_of_le_one_right hτ (hρ p)
    have hcoef : τ ^ 2 * (∑ i, a p.1 i * a p.2 i) ^ 2 / 2 ≤ τ ^ 2 / 2 := by
      have hmul := mul_le_mul_of_nonneg_left hρsq (sq_nonneg τ)
      nlinarith
    dsimp [R]
    change |τ ^ 2 * (∑ i, a p.1 i * a p.2 i) ^ 2 / 2 *
      Real.exp (τ * |∑ i, a p.1 i * a p.2 i|)| ≤ _
    rw [abs_of_nonneg (by positivity)]
    calc
      (τ ^ 2 * (∑ i, a p.1 i * a p.2 i) ^ 2 / 2) *
          Real.exp (τ * |∑ i, a p.1 i * a p.2 i|) ≤
        (τ ^ 2 * (∑ i, a p.1 i * a p.2 i) ^ 2 / 2) * Real.exp τ :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ (τ ^ 2 / 2) * Real.exp τ :=
          mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg τ)
  have hR : Integrable R (μ.prod μ) := by
    apply Integrable.mono' (integrable_const (τ ^ 2 / 2 * Real.exp τ)) hRmeas.aestronglyMeasurable
    filter_upwards with p
    simpa [Real.norm_of_nonneg (by positivity)] using hRbound p
  have hKsubInt : Integrable K (μ.prod μ) := hK
  have hpoint (p : α × α) : K p ≤ R p := by
    dsimp [K, R]
    exact AlignmentPaperSpatialExponential.spatialOverlap_cosh_remainder_le hτ
  rw [variance_eq_spatial_remainder_integral μ a τ hτ ha haMeas]
  exact integral_mono_ae hKsubInt hR (ae_of_all _ hpoint)

end BrownianSharp.AlignmentPaperSpatialVariance
