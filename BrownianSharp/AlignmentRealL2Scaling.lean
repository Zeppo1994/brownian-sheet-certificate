import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Whole-line L² dilation identities for homogeneous Gaussian features. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace
namespace BrownianSharp.AlignmentRealL2Scaling

theorem memLp_two_comp_div {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfm : Measurable f) {a : ℝ} (ha : a ≠ 0) :
    MemLp (fun u : ℝ => f (u/a)) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    ((hfm.comp (measurable_id.div_const a)).aestronglyMeasurable)).2
  exact ((memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf).comp_div ha

theorem memLp_two_homogeneous_scale {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hfm : Measurable f) {a : ℝ} (ha : a ≠ 0) (p : ℝ) :
    MemLp (fun u : ℝ => a^p*f (u/a)) 2 volume :=
  (memLp_two_comp_div hf hfm ha).const_mul _

theorem homogeneous_square_integral_scale (f : ℝ → ℝ) {a : ℝ}
    (ha : 0 < a) (p : ℝ) :
    (∫ u : ℝ, (a^p*f (u/a))^2) =
      a^(2*p+1) * ∫ u : ℝ, (f u)^2 := by
  have hpoint : (fun u : ℝ => (a^p*f (u/a))^2) =
      (fun u : ℝ => (a^p)^2*(f (u/a))^2) := by funext u; ring
  rw [hpoint,integral_const_mul,Measure.integral_comp_div
    (fun u : ℝ => (f u)^2) a,abs_of_pos ha,smul_eq_mul]
  have hs : (a^p)^2 = a^(2*p) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul ha.le]
    congr 1
    ring
  have hp : (a^p)^2*a = a^(2*p+1) := by
    rw [hs]
    calc
      a^(2*p)*a = a^(2*p)*a^(1:ℝ) := by rw [Real.rpow_one]
      _ = a^(2*p+1) := (Real.rpow_add ha _ _).symm
  calc
    _ = ((a^p)^2*a)*(∫ u : ℝ, (f u)^2) := by ring
    _ = _ := by rw [hp]

theorem wholeLineL2_norm_sq (z : Lp ℝ 2 (volume : Measure ℝ)) :
    ‖z‖^2 = ∫ u : ℝ, (z u)^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  congr 1
  funext u
  simp [pow_two]

theorem toLp_norm_sq {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖^2 = ∫ u : ℝ, (f u)^2 := by
  rw [wholeLineL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with u hu
  rw [hu]

theorem homogeneous_toLp_norm_sq {f g : ℝ → ℝ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) {a : ℝ} (ha : 0 < a) (p : ℝ)
    (heq : ∀ u : ℝ, g u = a^p*f (u/a)) :
    ‖hg.toLp g‖^2 = a^(2*p+1)*‖hf.toLp f‖^2 := by
  rw [toLp_norm_sq hg,toLp_norm_sq hf]
  have hgfun : g = fun u : ℝ => a^p*f (u/a) := funext heq
  rw [hgfun]
  exact homogeneous_square_integral_scale f ha p

theorem translated_square_integral (f : ℝ → ℝ) (s : ℝ) :
    (∫ u : ℝ, (f (u-s))^2) = ∫ u : ℝ, (f u)^2 := by
  simpa only [sub_eq_add_neg] using
    (integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun u : ℝ => (f u)^2) (-s))

end BrownianSharp.AlignmentRealL2Scaling
