import BrownianSharp.GaussianHeatDef
import BrownianSharp.NativeStatisticProperties

/-! Uniform spatial limits for Gaussian heat averages of compact perturbations
of a constant. These supply Borell's maximum principle at spatial infinity. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace BrownianSharp

/-- Every finite product standard Gaussian has integrable coefficient norm. -/
theorem productStandardGaussian_norm_integrable (κ : Type*) [Fintype κ] :
    Integrable (fun z : κ → ℝ => ‖z‖) (productStandardGaussian κ) :=
  (productStandardGaussian_coeff_memLp_two κ).norm.integrable (by norm_num)

theorem gaussianHeat_integrable_of_bounded {κ : Type*} [Fintype κ]
    (q : (κ → ℝ) → ℝ) (hq : Continuous q) (t : ℝ) (x : κ → ℝ)
    {M : ℝ} (hM : ∀ u, |q u| ≤ M) :
    Integrable (fun z => q (x + Real.sqrt t • z)) (productStandardGaussian κ) := by
  have hcont : Continuous (fun z : κ → ℝ => q (x + Real.sqrt t • z)) :=
    hq.comp (by fun_prop)
  apply (integrable_const M : Integrable (fun _ : κ → ℝ => M)
    (productStandardGaussian κ)).mono' hcont.aestronglyMeasurable
  exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hM _

/-- A direct first-moment tail estimate, uniform on a bounded time interval. -/
theorem gaussianHeat_sub_constant_le_norm_budget {κ : Type*} [Fintype κ]
    (q : (κ → ℝ) → ℝ) (hq : Continuous q)
    {δ M R T S t : ℝ} (hM : 0 ≤ M) (hT : 0 < T) (hS : 0 < S)
    (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hbounded : ∀ u, |q u - δ| ≤ M)
    (houtside : ∀ u, R < ‖u‖ → q u = δ)
    (x : κ → ℝ) (hx : R + Real.sqrt T * S < ‖x‖) :
    |gaussianHeat q t x - δ| ≤
      M / S * ∫ z : κ → ℝ, ‖z‖ ∂productStandardGaussian κ := by
  have hqBound : ∀ u, |q u| ≤ M + |δ| := by
    intro u
    calc
      |q u| = |(q u - δ) + δ| := by rw [sub_add_cancel]
      _ ≤ |q u - δ| + |δ| := abs_add_le _ _
      _ ≤ _ := add_le_add (hbounded u) (le_refl |δ|)
  have hqInt := gaussianHeat_integrable_of_bounded q hq t x hqBound
  have hdiffInt : Integrable (fun z => q (x + Real.sqrt t • z) - δ)
      (productStandardGaussian κ) := hqInt.sub (integrable_const δ)
  have hpoint : ∀ z : κ → ℝ,
      |q (x + Real.sqrt t • z) - δ| ≤ (M / S) * ‖z‖ := by
    intro z
    by_cases hz : R < ‖x + Real.sqrt t • z‖
    · rw [houtside _ hz, sub_self, abs_zero]
      positivity
    · have hzR : ‖x + Real.sqrt t • z‖ ≤ R := le_of_not_gt hz
      have htriangle : ‖x‖ ≤ ‖x + Real.sqrt t • z‖ + Real.sqrt t * ‖z‖ := by
        calc
          ‖x‖ = ‖(x + Real.sqrt t • z) - Real.sqrt t • z‖ := by congr 1; abel
          _ ≤ ‖x + Real.sqrt t • z‖ + ‖Real.sqrt t • z‖ := norm_sub_le _ _
          _ = _ := by rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg t)]
      have hsqrt := Real.sqrt_le_sqrt ht.2
      have hmul := mul_le_mul_of_nonneg_right hsqrt (norm_nonneg z)
      have hroot : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
      have hSz : S ≤ ‖z‖ := by nlinarith
      calc
        _ ≤ M := hbounded _
        _ = (M / S) * S := by field_simp
        _ ≤ (M / S) * ‖z‖ := mul_le_mul_of_nonneg_left hSz (div_nonneg hM hS.le)
  have heq : gaussianHeat q t x - δ =
      ∫ z, q (x + Real.sqrt t • z) - δ ∂productStandardGaussian κ := by
    rw [integral_sub hqInt (integrable_const δ)]
    simp [gaussianHeat]
  rw [heq]
  calc
    _ ≤ ∫ z, |q (x + Real.sqrt t • z) - δ| ∂productStandardGaussian κ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := productStandardGaussian κ) (fun z => q (x + Real.sqrt t • z) - δ)
    _ ≤ ∫ z, (M / S) * ‖z‖ ∂productStandardGaussian κ :=
      integral_mono hdiffInt.abs
        ((productStandardGaussian_norm_integrable κ).const_mul _) hpoint
    _ = _ := integral_const_mul _ _

/-- A compact perturbation tends uniformly to its exterior constant under
Gaussian heat averaging, for every bounded nonnegative time interval. -/
theorem gaussianHeat_uniform_limit_at_infinity {κ : Type*} [Fintype κ]
    (q : (κ → ℝ) → ℝ) (hq : Continuous q)
    {δ M R T : ℝ} (hM : 0 ≤ M) (hT : 0 < T)
    (hbounded : ∀ u, |q u - δ| ≤ M)
    (houtside : ∀ u, R < ‖u‖ → q u = δ) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : κ → ℝ, L < ‖x‖ →
        |gaussianHeat q t x - δ| < ε := by
  intro ε hε
  let m := ∫ z : κ → ℝ, ‖z‖ ∂productStandardGaussian κ
  have hm : 0 ≤ m := integral_nonneg fun _ => norm_nonneg _
  let S := (M * (m + 1) + 1) / ε
  have hS : 0 < S := by dsimp [S]; positivity
  refine ⟨R + Real.sqrt T * S, ?_⟩
  intro t ht x hx
  have h := gaussianHeat_sub_constant_le_norm_budget q hq hM hT hS ht hbounded houtside x hx
  refine h.trans_lt ?_
  change M / S * m < ε
  have hmul : M * m < ε * S := by
    dsimp [S]
    rw [mul_div_cancel₀ _ hε.ne']
    nlinarith
  rw [div_mul_eq_mul_div]
  exact (div_lt_iff₀ hS).2 hmul

end BrownianSharp
