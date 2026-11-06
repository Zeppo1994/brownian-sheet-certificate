import BrownianSharp.AlignmentPaperQuantizationUpperRates

noncomputable section
open Filter Topology
namespace BrownianSharp.AlignmentPaperEmpiricalRateBudget
open AlignmentPaperQuantizationUpperRates

/-- The concrete empirical coupling budget has the canonical quantization
order once the Gaussian net uses at most exp(9x/64)+1 representatives. -/
theorem eventually_empirical_budget_le_radius {α β c M K : ℝ}
    (hα : 0<α) (hβ : 0≤β) (hc : 0<c) (hM : 0≤M) :
    ∀ᶠ x : ℝ in atTop, ∀ N : ℝ, 0≤N → N≤Real.exp (9*x/64)+1 →
      Real.sqrt (3*(2*((3*canonicalPowerlogRadius α β c x)^2+
        Real.sqrt M*Real.exp (-x/64))+
        (x*K^2)*(1/2)*Real.sqrt (N/Real.exp x))) ≤
        8*canonicalPowerlogRadius α β c x := by
  have htail := eventually_exp_tail_le_radius_sq (c := c)
    (A := Real.sqrt M) (b := 1/64) (q := 0) hα hβ hc (Real.sqrt_nonneg _) (by norm_num)
  have hcell := eventually_exp_tail_le_radius_sq (c := c)
    (A := K^2) (b := 1/4) (q := 1) hα hβ hc (sq_nonneg _) (by norm_num)
  filter_upwards [htail,hcell,eventually_gt_atTop (1:ℝ)] with x htail hcell hx
  intro N hN hcard
  have hx0 : 0≤x := by linarith
  have hlogx : 0<Real.log x := Real.log_pos hx
  let ε := canonicalPowerlogRadius α β c x
  have hε : 0≤ε := by dsimp [ε,canonicalPowerlogRadius]; positivity
  have htail' : Real.sqrt M*Real.exp (-x/64)≤ε^2 := by
    simpa [ε,div_eq_mul_inv,mul_comm] using htail
  have hcell' : K^2*x*Real.exp (-x/4)≤ε^2 := by
    simpa [ε,div_eq_mul_inv,mul_comm] using hcell
  have he1 : 1≤Real.exp (x/4) := Real.one_le_exp_iff.mpr (by positivity)
  have he2 : Real.exp (9*x/64)≤Real.exp (x/4) :=
    Real.exp_le_exp.mpr (by linarith)
  have hcard' : N≤2*Real.exp (x/4) := by linarith
  have hfrac : N/Real.exp x≤4*Real.exp (-x/2) := by
    calc
      N/Real.exp x ≤ (2*Real.exp (x/4))/Real.exp x :=
        div_le_div_of_nonneg_right hcard' (Real.exp_pos _).le
      _ = 2*Real.exp (-3*x/4) := by
        rw [div_eq_mul_inv,←Real.exp_neg]
        calc
          _ = 2*(Real.exp (x/4)*Real.exp (-x)) := by ring
          _ = _ := by rw [←Real.exp_add]; congr 2 <;> ring
      _ ≤ 2*Real.exp (-x/2) := mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
      _ ≤ 4*Real.exp (-x/2) := by nlinarith [Real.exp_pos (-x/2)]
  have hsqrt : Real.sqrt (N/Real.exp x)≤2*Real.exp (-x/4) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    have he : (2*Real.exp (-x/4))^2=4*Real.exp (-x/2) := by
      rw [mul_pow]
      norm_num
      rw [pow_two,←Real.exp_add]
      congr 2 <;> ring
    rw [he]
    exact hfrac
  have herr : (x*K^2)*(1/2)*Real.sqrt (N/Real.exp x)≤ε^2 := by
    calc
      _ ≤ (x*K^2)*(1/2)*(2*Real.exp (-x/4)) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = K^2*x*Real.exp (-x/4) := by ring
      _ ≤ ε^2 := hcell'
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity,?_⟩
  change 3*(2*((3*ε)^2+Real.sqrt M*Real.exp (-x/64))+
    (x*K^2)*(1/2)*Real.sqrt (N/Real.exp x))≤(8*ε)^2
  nlinarith [sq_nonneg ε]

end BrownianSharp.AlignmentPaperEmpiricalRateBudget
