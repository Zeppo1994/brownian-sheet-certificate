import BrownianSharp.AlignmentFractionalKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! Actual finite-interval removal of exponential damping in the
Riemann--Liouville preimage, using Mathlib dominated convergence. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace BrownianSharp.AlignmentPaperFractionalDampingLimit
open BrownianSharp.AlignmentFractionalKernel

def dampedRLIntegral (β ε : ℝ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0:ℝ)..t, Real.exp (-ε*(t-u)) * kernel β (t-u) * F u

theorem damped_rlIntegrand_intervalIntegrable {β ε t : ℝ} {F : ℝ → ℝ}
    (hβ : 1/2 < β) (hF : Continuous F) :
    IntervalIntegrable (fun u => Real.exp (-ε*(t-u))*kernel β (t-u)*F u)
      volume 0 t := by
  have hi := (rlIntegrand_intervalIntegrable hβ hF).mul_continuousOn
    (show ContinuousOn (fun u : ℝ => Real.exp (-ε*(t-u))) (Set.uIcc 0 t) by fun_prop)
  convert hi using 1
  funext u
  ring

/-- Every nonnegative sequence of damping parameters tending to zero yields
the genuine undamped RL integral at every nonnegative time. -/
theorem dampedRLIntegral_tendsto {β t : ℝ} (hβ : 1/2 < β) (ht : 0 ≤ t)
    (F : ℝ → ℝ) (hF : Continuous F) (ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n) (hεlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => dampedRLIntegral β (ε n) F t) atTop
      (𝓝 (rlIntegral β F t)) := by
  have hi := rlIntegrand_intervalIntegrable hβ hF (t := t)
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun u => Real.exp (-ε n*(t-u))*kernel β (t-u)*F u)
      (volume.restrict (Set.Ioc 0 t)) := by
    intro n
    exact (damped_rlIntegrand_intervalIntegrable hβ hF).1.aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ u ∂volume.restrict (Set.Ioc 0 t),
      ‖Real.exp (-ε n*(t-u))*kernel β (t-u)*F u‖ ≤
        ‖kernel β (t-u)*F u‖ := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have harg : -ε n*(t-u) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hε n)) (sub_nonneg.mpr hu.2)
    have he : Real.exp (-ε n*(t-u)) ≤ 1 := Real.exp_le_one_iff.mpr harg
    rw [mul_assoc, norm_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_right he (norm_nonneg _)).trans_eq (one_mul _)
  have hlim : ∀ᵐ u ∂volume.restrict (Set.Ioc 0 t),
      Tendsto (fun n => Real.exp (-ε n*(t-u))*kernel β (t-u)*F u)
        atTop (𝓝 (kernel β (t-u)*F u)) := by
    filter_upwards [] with u
    have hexp : Tendsto (fun n => Real.exp (-ε n*(t-u))) atTop (𝓝 1) := by
      have harglim : Tendsto (fun n => -ε n*(t-u)) atTop (𝓝 0) := by
        simpa using (hεlim.neg).mul_const (t-u)
      have h := (Real.continuous_exp.tendsto (0:ℝ)).comp harglim
      simpa only [Function.comp_def, Real.exp_zero] using h
    have h := (hexp.mul_const (kernel β (t-u))).mul_const (F u)
    simpa using h
  have h := tendsto_integral_of_dominated_convergence
    (fun u => ‖kernel β (t-u)*F u‖) hmeas hi.1.norm hbound hlim
  simpa only [dampedRLIntegral, rlIntegral, intervalIntegral.integral_of_le ht] using h

end BrownianSharp.AlignmentPaperFractionalDampingLimit
