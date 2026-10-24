import BrownianSharp.AlignmentFractionalPastTailL2Approx
import BrownianSharp.AlignmentSigmaFiniteL2Tensor
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! Exact dilation of the actual past-source MvN tail on the positive half-line. -/
noncomputable section
open MeasureTheory Set
namespace BrownianSharp.AlignmentFractionalPastTailScaling
open AlignmentFractionalPastTail AlignmentFractionalPastTailL2Approx
open AlignmentSigmaFiniteL2Tensor

theorem pastTailPower_scale (p : ℝ) {t x : ℝ} (ht : 0<t) (hx : 0<x) :
    pastTailPower p t (t*x) = t^p*pastTailPower p 1 x := by
  have hfac : t*x+t=t*(x+1) := by ring
  simp only [pastTailPower,hfac,Real.mul_rpow ht.le (by positivity : 0≤x+1),
    Real.mul_rpow ht.le hx.le]
  ring

theorem pastTailPower_square_integral_scale (p : ℝ) {t : ℝ} (ht : 0<t) :
    (∫ x in Ioi (0:ℝ), (pastTailPower p t x)^2) =
      t^(2*p+1)*(∫ x in Ioi (0:ℝ), (pastTailPower p 1 x)^2) := by
  have hchange := integral_comp_mul_left_Ioi'
    (fun x : ℝ => (pastTailPower p t x)^2) 0 ht
  have hae : (fun x : ℝ => (pastTailPower p t (t*x))^2) =ᵐ[volume.restrict (Ioi 0)]
      (fun x => (t^p)^2*(pastTailPower p 1 x)^2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [pastTailPower_scale p ht (mem_Ioi.mp hx),mul_pow]
  have hfac : t*(t^p)^2=t^(2*p+1) := by
    have hpp : (t^p)^2=t^(2*p) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
      congr 1
      ring
    rw [hpp]
    calc
      t*t^(2*p) = t^((1:ℝ))*t^(2*p) := by rw [Real.rpow_one]
      _ = t^(1+2*p) := (Real.rpow_add ht _ _).symm
      _ = t^(2*p+1) := by congr 1; ring
  calc
    _ = t*(∫ x in Ioi (0:ℝ), (pastTailPower p t (t*x))^2) := by
      simpa using hchange.symm
    _ = t*((t^p)^2*(∫ x in Ioi (0:ℝ), (pastTailPower p 1 x)^2)) := by
      rw [integral_congr_ae hae,integral_const_mul]
    _ = _ := by rw [← mul_assoc,hfac]

theorem pastTail_toLp_norm_eq (p : ℝ) {t : ℝ} (ht : 0<t)
    (hf : MemLp (pastTailPower p 1) 2 (volume.restrict (Ioi 0)))
    (hg : MemLp (pastTailPower p t) 2 (volume.restrict (Ioi 0))) :
    ‖hg.toLp (pastTailPower p t)‖ = t^(p+1/2)*‖hf.toLp (pastTailPower p 1)‖ := by
  have hnorm (s : ℝ) (hs : MemLp (pastTailPower p s) 2 (volume.restrict (Ioi 0))) :
      ‖hs.toLp (pastTailPower p s)‖^2=∫x in Ioi (0:ℝ),(pastTailPower p s x)^2 := by
    rw [realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp hs] with x hx
    rw [hx]
  have hs := pastTailPower_square_integral_scale p ht
  rw [← hnorm t hg, ← hnorm 1 hf] at hs
  have hp : (t^(p+1/2))^2=t^(2*p+1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    ring
  have hnonneg : 0≤t^(p+1/2)*‖hf.toLp (pastTailPower p 1)‖ := by positivity
  have heq : ‖hg.toLp (pastTailPower p t)‖^2 =
      (t^(p+1/2)*‖hf.toLp (pastTailPower p 1)‖)^2 := by
    rw [mul_pow,hp]
    exact hs
  nlinarith [norm_nonneg (hg.toLp (pastTailPower p t))]

theorem pastTail_toLp_norm_le (p : ℝ) (hp0 : -(1/2:ℝ)<p) (hp1 : p<1/2)
    {t c : ℝ} (ht0 : 0≤t) (ht1 : t≤1) (htc : t≤c) (hc : 0≤c) :
    ‖(pastTailPower_memLp_two hp0 hp1 ht0 ht1).toLp (pastTailPower p t)‖ ≤
      c^(p+1/2)*
        ‖(pastTailPower_memLp_two hp0 hp1 (by norm_num) (by norm_num)).toLp
          (pastTailPower p 1)‖ := by
  by_cases ht : t=0
  · subst t
    have hz : (pastTailPower_memLp_two hp0 hp1 ht0 ht1).toLp
        (pastTailPower p 0)=0 := by
      apply Lp.ext
      filter_upwards [MemLp.coeFn_toLp (pastTailPower_memLp_two hp0 hp1 ht0 ht1),
        Lp.coeFn_zero ℝ 2 (volume.restrict (Ioi (0:ℝ)))] with x hx hz
      rw [hx,hz]
      simp [pastTailPower]
    rw [hz,norm_zero]
    positivity
  · have htpos : 0<t := lt_of_le_of_ne ht0 (Ne.symm ht)
    rw [pastTail_toLp_norm_eq p htpos]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow ht0 htc (by linarith)) (norm_nonneg _)

end BrownianSharp.AlignmentFractionalPastTailScaling
