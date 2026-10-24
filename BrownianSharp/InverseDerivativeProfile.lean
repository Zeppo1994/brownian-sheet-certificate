import BrownianSharp.SmoothResolution
import BrownianSharp.ScalarKernelBudget
import Mathlib.Tactic

/-! Smooth compact profiles for inverse even-derivative multipliers. -/

noncomputable section
open Set
open scoped Topology

namespace BrownianSharp.InverseDerivativeProfile

open BrownianSharp.SmoothResolution

/-- The normalized real profile associated with the inverse K-th derivative
of the annular cutoff multiplier. The constant `(2π i)^(-K)` is kept outside
the profile; for even K it is real. -/
def profile (K : ℕ) (ξ : ℝ) : ℝ :=
  (cutoff ξ - cutoff (2 * ξ)) / ξ ^ K

theorem profile_eq_zero_near_zero (K : ℕ) {ξ : ℝ} (hξ : |ξ| ≤ 1 / 2) :
    profile K ξ = 0 := by
  have h1 : |ξ| ≤ 1 := by linarith [abs_nonneg ξ]
  have h2 : |2 * ξ| ≤ 1 := by rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]; linarith
  simp [profile, cutoff_eq_one h1, cutoff_eq_one h2]

theorem profile_eq_zero_of_two_le_abs (K : ℕ) {ξ : ℝ} (hξ : 2 ≤ |ξ|) :
    profile K ξ = 0 := by
  have h2ξ : 2 ≤ |2 * ξ| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2 : ℝ))]
    nlinarith
  simp [profile, cutoff_eq_zero hξ, cutoff_eq_zero h2ξ]

theorem profile_smooth (K : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (profile K) := by
  apply contDiff_iff_contDiffAt.mpr
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    have hevent : (fun y => profile K y) =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds (by norm_num : (-1 / 2 : ℝ) < 0)
        (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
      apply profile_eq_zero_near_zero
      have hylo : -(1 / 2 : ℝ) < y := by linarith [hy.1]
      have hyhi : y < (1 / 2 : ℝ) := by linarith [hy.2]
      have : |y| < 1 / 2 := abs_lt.mpr ⟨hylo, hyhi⟩
      exact this.le
    exact (contDiff_const.contDiffAt : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : ℝ)) 0)
      |>.congr_of_eventuallyEq hevent
  · have hnum : ContDiff ℝ (⊤ : ℕ∞) (fun y => cutoff y - cutoff (2 * y)) := by
      exact cutoff_smooth.sub (cutoff_smooth.comp (by fun_prop))
    have hden : ContDiff ℝ (⊤ : ℕ∞) (fun y : ℝ => y ^ K) := contDiff_id.pow K
    have hdenξ : ξ ^ K ≠ 0 := pow_ne_zero K hξ
    change ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y => (cutoff y - cutoff (2 * y)) / y ^ K) ξ
    exact hnum.contDiffAt.div hden.contDiffAt hdenξ

theorem profile_hasCompactSupport (K : ℕ) : HasCompactSupport (profile K) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ) 2)
  intro ξ hξ
  change profile K ξ ≠ 0 at hξ
  have hnorm : |ξ| ≤ 2 := by
    by_contra h
    have hzero : profile K ξ = 0 := profile_eq_zero_of_two_le_abs K (le_of_not_ge h)
    exact hξ hzero
  simpa [Metric.mem_closedBall, dist_eq_norm, Real.norm_eq_abs] using hnorm

theorem exists_profile_secondDerivative_bound (K : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ξ, |iteratedDeriv 2 (profile K) ξ| ≤ M := by
  exact BrownianSharp.exists_iteratedDeriv_two_bound_of_compactSupport
    ((profile_smooth K).of_le (by norm_num)) (profile_hasCompactSupport K)

end BrownianSharp.InverseDerivativeProfile

end
