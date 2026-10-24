import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
The scalar Riemann--Liouville kernel and its local L² integrability for every
order strictly above one half. This is the analytic kernel input for the
continuous point-evaluation map; it makes no entropy-rate claim.
-/

noncomputable section
open MeasureTheory

namespace BrownianSharp.AlignmentFractionalKernel

/-- Scalar Riemann--Liouville kernel `x^(α-1) / Γ(α)` on the positive half-line. -/
def kernel (α x : ℝ) : ℝ := (Real.Gamma α)⁻¹ * x ^ (α - 1)

theorem kernel_exponent_gt_minus_one {α : ℝ} (hα : 1/2 < α) :
    -1 < α - 1 := by linarith

theorem kernel_sq_exponent_gt_minus_one {α : ℝ} (hα : 1/2 < α) :
    -1 < 2 * (α - 1) := by linarith

/-- The singularity of the RL kernel is integrable on every bounded interval
starting at zero. -/
theorem kernel_intervalIntegrable {α t : ℝ} (hα : 1/2 < α) :
    IntervalIntegrable (kernel α) volume 0 t := by
  unfold kernel
  exact (intervalIntegral.intervalIntegrable_rpow'
    (kernel_exponent_gt_minus_one hα)).const_mul _

/-- Squaring the RL kernel still leaves an integrable singularity exactly
when `α > 1/2`, the threshold used for point evaluation on `L²`. -/
theorem kernel_sq_intervalIntegrable {α t : ℝ} (hα : 1/2 < α) (ht : 0 ≤ t) :
    IntervalIntegrable (fun x => (kernel α x) ^ 2) volume 0 t := by
  have hpow : IntervalIntegrable (fun x : ℝ => x ^ (2 * (α - 1))) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow'
      (kernel_sq_exponent_gt_minus_one hα)
  have hGamma : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos (by linarith : 0 < α)).ne'
  have hEq : Set.EqOn (fun x => (kernel α x) ^ 2)
      (fun x => ((Real.Gamma α)⁻¹) ^ 2 * x ^ (2 * (α - 1)))
      (Set.uIoo 0 t) := by
    intro x hx
    have hx0 : 0 < x := by
      have hx' : x ∈ Set.Ioo (0:ℝ) t := by
        simpa [Set.uIoo, min_eq_left ht, max_eq_right ht] using hx
      exact hx'.1
    simp only [kernel, mul_pow]
    have hid : (x ^ (α - 1)) ^ 2 = x ^ (2 * (α - 1)) := by
      calc
        (x ^ (α - 1)) ^ 2 = x ^ (α - 1) * x ^ (α - 1) := by rw [pow_two]
        _ = x ^ ((α - 1) + (α - 1)) := (Real.rpow_add hx0 _ _).symm
        _ = x ^ (2 * (α - 1)) := by congr 1; ring
    rw [hid]
  rw [intervalIntegrable_congr_uIoo hEq]
  exact hpow.const_mul _

/-- Riemann--Liouville integration on the anchored interval `[0,t]`. -/
def rlIntegral (α : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, kernel α (t - u) * g u

/-- For continuous data, the actual RL integrand is interval integrable on the
anchored unit interval whenever `α > 1/2`. -/
theorem rlIntegrand_intervalIntegrable {α t : ℝ} {g : ℝ → ℝ}
    (hα : 1/2 < α) (hg : Continuous g) :
    IntervalIntegrable (fun u => kernel α (t - u) * g u) volume 0 t := by
  have hk : IntervalIntegrable (fun u : ℝ => kernel α (t - u)) volume 0 t := by
    have hbase : IntervalIntegrable (kernel α) volume 0 t := kernel_intervalIntegrable hα
    have hshift := hbase.comp_sub_left t
    simpa using hshift.symm
  exact hk.mul_continuousOn hg.continuousOn

/-- Cauchy--Schwarz bounds the absolute RL integrand pairing by the product
of the two `L²` norms, for any measure on which the factors are square
integrable. The kernel-specific hypotheses are established above on each
anchored interval. -/
theorem kernel_pairing_cauchy_schwarz {α t : ℝ} {g : ℝ → ℝ} {μ : Measure ℝ}
    (hK : MemLp (fun u => kernel α (t - u)) 2 μ) (hg : MemLp g 2 μ) :
    (∫ u, |kernel α (t - u)| * |g u| ∂μ) ≤
      (∫ u, |kernel α (t - u)| ^ 2 ∂μ) ^ (1 / 2 : ℝ) *
        (∫ u, |g u| ^ 2 ∂μ) ^ (1 / 2 : ℝ) := by
  have hK' : MemLp (fun u => kernel α (t - u)) (ENNReal.ofReal 2) μ := by simpa using hK
  have hg' : MemLp g (ENNReal.ofReal 2) μ := by simpa using hg
  have h := integral_mul_norm_le_Lp_mul_Lq
    (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff]) hK' hg'
  simpa [Real.norm_eq_abs] using h

/-- Exact squared kernel norm on `[0,t]`; the order threshold is the condition
that the power integral at zero converges. -/
theorem kernel_sq_integral {α t : ℝ} (hα : 1/2 < α) (ht : 0 ≤ t) :
    (∫ u in (0:ℝ)..t, (kernel α (t - u)) ^ 2) =
      ((Real.Gamma α)⁻¹) ^ 2 * (t ^ (2 * α - 1) / (2 * α - 1)) := by
  have hExp : -1 < 2 * (α - 1) := kernel_sq_exponent_gt_minus_one hα
  have hP : 0 < 2 * α - 1 := by linarith
  have hEq : Set.EqOn
      (fun u => ((Real.Gamma α)⁻¹) ^ 2 * ((t - u) ^ (α - 1)) ^ 2)
      (fun u => ((Real.Gamma α)⁻¹) ^ 2 * (t - u) ^ (2 * (α - 1)))
      (Set.uIoo 0 t) := by
    intro u hu
    have hu' : u ∈ Set.Ioo (0:ℝ) t := by
      simpa [Set.uIoo, min_eq_left ht, max_eq_right ht] using hu
    have htu : 0 < t - u := by linarith [hu'.2]
    have hp : ((t - u) ^ (α - 1)) ^ 2 = (t-u) ^ (2 * (α - 1)) := by
      calc
        ((t-u) ^ (α - 1)) ^ 2 = (t-u) ^ (α - 1) * (t-u) ^ (α - 1) := by rw [pow_two]
        _ = (t-u) ^ ((α-1) + (α-1)) := (Real.rpow_add htu _ _).symm
        _ = (t-u) ^ (2 * (α-1)) := by congr 1; ring
    change ((Real.Gamma α)⁻¹) ^ 2 * ((t - u) ^ (α - 1)) ^ 2 =
      ((Real.Gamma α)⁻¹) ^ 2 * (t - u) ^ (2 * (α - 1))
    rw [hp]
  simp only [kernel, mul_pow]
  rw [intervalIntegral.integral_congr_uIoo hEq]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => x ^ (2 * (α - 1))) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl hExp)]
  have hplus : 2 * (α - 1) + 1 = 2 * α - 1 := by ring
  rw [hplus, Real.zero_rpow hP.ne']
  ring

end BrownianSharp.AlignmentFractionalKernel
