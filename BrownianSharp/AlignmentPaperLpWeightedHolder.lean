import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Weighted Hölder/Jensen inequality for the convolution sampling argument. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperLpWeightedHolder

/-- For nonnegative weights, Hölder in the weighted measure gives the
power-form estimate used to sum samples against a reproducing kernel. The
MemLp hypotheses are for the two explicit Hölder factors. -/
theorem integral_weighted_mul_rpow_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {p q : ℝ} (hpq : p.HolderConjugate q)
    (w v : α → ℝ) (hw : 0 ≤ᵐ[μ] w) (hv : 0 ≤ᵐ[μ] v)
    (hU : MemLp (fun x => w x ^ (1/p) * v x) (ENNReal.ofReal p) μ)
    (hW : MemLp (fun x => w x ^ (1/q)) (ENNReal.ofReal q) μ) :
    (∫ x, w x * v x ∂μ) ^ p ≤
      (∫ x, w x * v x ^ p ∂μ) * (∫ x, w x ∂μ) ^ (p - 1) := by
  let U : α → ℝ := fun x => w x ^ (1/p) * v x
  let W : α → ℝ := fun x => w x ^ (1/q)
  have hU_nonneg : 0 ≤ᵐ[μ] U := by
    filter_upwards [hw, hv] with x hxw hxv
    exact mul_nonneg (Real.rpow_nonneg hxw _) hxv
  have hW_nonneg : 0 ≤ᵐ[μ] W := by
    filter_upwards [hw] with x hxw
    exact Real.rpow_nonneg hxw _
  have hInv : 1/p + 1/q = 1 := by simpa [one_div] using hpq.inv_add_inv_eq_one
  have hpowP : (1/p) * p = 1 := by
    simpa [one_div] using (inv_mul_cancel₀ hpq.ne_zero)
  have hpowQ : (1/q) * p = p - 1 := by
    have hp0 : p ≠ 0 := hpq.ne_zero
    have hq0 : q ≠ 0 := hpq.symm.ne_zero
    field_simp [hp0, hq0] at hInv ⊢
    nlinarith
  have hprod : (∫ x, U x * W x ∂μ) = ∫ x, w x * v x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hw, hv] with x hxw hxv
    dsimp [U, W]
    have hpInv : 0 < 1/p := one_div_pos.mpr hpq.pos
    have hqInv : 0 < 1/q := one_div_pos.mpr hpq.symm.pos
    by_cases hx : w x = 0
    · simp [hx, Real.zero_rpow hpInv.ne', Real.zero_rpow hqInv.ne', hpq.pos.ne']
    · have hxpos : 0 < w x := lt_of_le_of_ne hxw (Ne.symm hx)
      calc
        w x ^ (1/p) * v x * w x ^ (1/q) =
            w x ^ (1/p) * w x ^ (1/q) * v x := by ring
        _ = w x ^ (1/p + 1/q) * v x := by rw [← Real.rpow_add hxpos]
        _ = w x * v x := by rw [hInv, Real.rpow_one]
  have hUpow : (∫ x, U x ^ p ∂μ) = ∫ x, w x * v x ^ p ∂μ := by
    apply integral_congr_ae
    filter_upwards [hw, hv] with x hxw hxv
    dsimp [U]
    have hpInv : 0 < 1/p := one_div_pos.mpr hpq.pos
    by_cases hx : w x = 0
    · simp [hx, Real.zero_rpow hpInv.ne', hpq.pos.ne']
    · have hxpos : 0 < w x := lt_of_le_of_ne hxw (Ne.symm hx)
      calc
        (w x ^ (1/p) * v x) ^ p = (w x ^ (1/p)) ^ p * v x ^ p :=
          Real.mul_rpow (Real.rpow_nonneg hxw _) hxv
        _ = w x ^ ((1/p) * p) * v x ^ p := by rw [← Real.rpow_mul hxw]
        _ = w x * v x ^ p := by rw [hpowP, Real.rpow_one]
  have hWpow : (∫ x, W x ^ q ∂μ) = ∫ x, w x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hw] with x hxw
    dsimp [W]
    have hqInv : 0 < 1/q := one_div_pos.mpr hpq.symm.pos
    by_cases hx : w x = 0
    · simp [hx, Real.zero_rpow hqInv.ne', hpq.symm.pos.ne']
    · have hpowQ' : (1/q) * q = 1 := by
        simpa [one_div] using (inv_mul_cancel₀ hpq.symm.ne_zero)
      calc
        (w x ^ (1/q)) ^ q = w x ^ ((1/q) * q) := (Real.rpow_mul hxw _ _).symm
        _ = w x := by rw [hpowQ', Real.rpow_one]
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq hU_nonneg hW_nonneg hU hW
  rw [hprod, hUpow, hWpow] at hholder
  have hwv : 0 ≤ᵐ[μ] fun x => w x * v x := by
    filter_upwards [hw, hv] with x hxw hxv
    exact mul_nonneg hxw hxv
  have hI : 0 ≤ ∫ x, w x * v x ∂μ := integral_nonneg_of_ae hwv
  have hJ : 0 ≤ ∫ x, w x * v x ^ p ∂μ := by
    apply integral_nonneg_of_ae
    filter_upwards [hw, hv] with x hxw hxv
    exact mul_nonneg hxw (Real.rpow_nonneg hxv _)
  have hM : 0 ≤ ∫ x, w x ∂μ := integral_nonneg_of_ae hw
  have hpow := Real.rpow_le_rpow hI hholder hpq.pos.le
  rw [Real.mul_rpow (by positivity) (by positivity)] at hpow
  rw [← Real.rpow_mul hJ, hpowP, Real.rpow_one] at hpow
  rw [← Real.rpow_mul hM, hpowQ] at hpow
  simpa using hpow

end BrownianSharp.AlignmentPaperLpWeightedHolder
