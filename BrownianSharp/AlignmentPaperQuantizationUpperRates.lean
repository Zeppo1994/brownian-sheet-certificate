import BrownianSharp.AlignmentPaperQuantizationRates
import BrownianSharp.AlignmentPaperGaussianQuantileBounds

noncomputable section
open Filter Topology MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentPaperQuantizationUpperRates

/-- The upper half of the small-ball scale inversion, for an arbitrary fixed
positive multiple of the canonical radius. -/
theorem eventually_powerlog_rate_upper {α β c : ℝ}
    (hα : 0<α) (hβ : 0≤β) (hc : 0<c) :
    ∀ᶠ x : ℝ in atTop,
      Latest.smallBallRate α β (canonicalPowerlogRadius α β c x) ≤
        c^(-α)*(2/α)^β*x := by
  have hconst : ∀ᶠ x : ℝ in atTop, -Real.log c ≤ Real.log x/α := by
    have h := Real.tendsto_log_atTop.eventually_ge_atTop (-α*Real.log c)
    filter_upwards [h] with x hx
    apply (le_div_iff₀ hα).2
    nlinarith
  have hwindow := eventually_powerlog_radius_le hα hβ hc (by norm_num : (0:ℝ)<1/2)
  filter_upwards [hconst,hwindow,eventually_gt_atTop (Real.exp 1)] with x hconst hwindow hx
  have hx1 : 1<x := by
    have : 1<Real.exp 1 := by rw [←Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num)
    exact this.trans hx
  have hx0 : 0<x := by linarith
  have hL1 : 1<Real.log x := by
    rw [←Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos _) hx
  have hL0 : 0<Real.log x := by linarith
  let ε := canonicalPowerlogRadius α β c x
  have hε : 0<ε := by dsimp [ε,canonicalPowerlogRadius]; positivity
  have hε1 : ε<1 := by dsimp [ε,canonicalPowerlogRadius]; linarith
  have hlogε : 0≤Real.log ε⁻¹ := Real.log_nonneg (by
    exact (one_le_inv₀ hε).2 hε1.le)
  have hlogId : Real.log ε⁻¹ = -Real.log c+(1/α)*Real.log x-
      (β/α)*Real.log (Real.log x) := by
    dsimp [ε,canonicalPowerlogRadius]
    rw [Real.log_inv,Real.log_mul (by positivity) (by positivity),
      Real.log_mul hc.ne' (by positivity),Real.log_rpow hx0,Real.log_rpow hL0]
    ring
  have hlogUpper : Real.log ε⁻¹ ≤ (2/α)*Real.log x := by
    rw [hlogId]
    have hll : 0≤Real.log (Real.log x) := Real.log_nonneg hL1.le
    have hb : 0≤(β/α)*Real.log (Real.log x) := by positivity
    have he : (2/α)*Real.log x=Real.log x/α+(1/α)*Real.log x := by ring
    rw [he]
    linarith
  have hid : ε⁻¹^α = c^(-α)*x*(Real.log x)^(-β) := by
    dsimp [ε,canonicalPowerlogRadius]
    rw [Real.inv_rpow (by positivity),←Real.rpow_neg (by positivity),
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow hc.le (by positivity),
      ←Real.rpow_mul hx0.le,←Real.rpow_mul hL0.le]
    have he1 : (-(1/α))*(-α)=1 := by field_simp
    have he2 : (β/α)*(-α) = -β := by field_simp
    rw [he1,he2,Real.rpow_one]
  have hcancel : (Real.log x)^(-β)*((2/α)*Real.log x)^β=(2/α)^β := by
    rw [Real.mul_rpow (by positivity) hL0.le]
    have he : (Real.log x)^(-β)*(Real.log x)^β=1 := by
      rw [←Real.rpow_add hL0]
      simp
    calc
      _ = ((Real.log x)^(-β)*(Real.log x)^β)*(2/α)^β := by ring
      _ = _ := by rw [he,one_mul]
  change ε⁻¹^α*(Real.log ε⁻¹)^β ≤ _
  rw [hid]
  calc
    c^(-α)*x*(Real.log x)^(-β)*(Real.log ε⁻¹)^β ≤
      c^(-α)*x*(Real.log x)^(-β)*((2/α)*Real.log x)^β := by
        gcongr
    _ = c^(-α)*(2/α)^β*x := by rw [mul_assoc, hcancel]; ring

/-- Enlarging the radius by a fixed factor makes the small-ball logarithm
any prescribed positive fraction of the logarithmic sample budget. -/
theorem exists_eventual_powerlog_upper_budget {α β C η : ℝ}
    (hα : 0<α) (hβ : 0≤β) (hC : 0<C) (hη : 0<η) :
    ∃ c : ℝ, 0<c ∧ ∀ᶠ x : ℝ in atTop,
      C*Latest.smallBallRate α β (canonicalPowerlogRadius α β c x) ≤ η*x := by
  let A : ℝ := C*(2/α)^β/η
  let c : ℝ := A^(1/α)
  have hA : 0<A := by dsimp [A]; positivity
  have hc : 0<c := Real.rpow_pos_of_pos hA _
  have hpow : c^(-α)=A⁻¹ := by
    dsimp [c]
    rw [←Real.rpow_mul hA.le]
    have he : (1/α)*(-α) = -1 := by field_simp
    rw [he,Real.rpow_neg_one]
  have hcoeff : C*(c^(-α)*(2/α)^β)=η := by
    rw [hpow]
    dsimp [A]
    have hpowpos : 0<(2/α)^β := by positivity
    field_simp
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_powerlog_rate_upper hα hβ hc] with x hx
  calc
    C*Latest.smallBallRate α β (canonicalPowerlogRadius α β c x) ≤
      C*(c^(-α)*(2/α)^β*x) := mul_le_mul_of_nonneg_left hx hC.le
    _ = η*x := by rw [←mul_assoc,hcoeff]

/-- Any fixed exponentially decaying tail, including a polynomial prefactor,
is negligible compared with the squared quantization radius. This uses
Mathlib's exponential-versus-real-power limit. -/
theorem eventually_exp_tail_le_radius_sq {α β c A b q : ℝ}
    (hα : 0<α) (hβ : 0≤β) (hc : 0<c) (hA : 0≤A) (hb : 0<b) :
    ∀ᶠ x : ℝ in atTop,
      A*x^q*Real.exp (-b*x) ≤ (canonicalPowerlogRadius α β c x)^2 := by
  have ht : Tendsto (fun x : ℝ => A*(x^(q+2/α)*Real.exp (-b*x)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
      (q+2/α) b hb).const_mul A
  have he := ht.eventually (Iic_mem_nhds (sq_pos_of_pos hc))
  filter_upwards [he,eventually_gt_atTop (Real.exp 1)] with x hx hxlarge
  have hx0 : 0<x := (Real.exp_pos _).trans hxlarge
  have hL1 : 1<Real.log x := by
    rw [←Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos _) hxlarge
  have hpowcancel : x^(q+2/α)*x^(-2/α)=x^q := by
    rw [←Real.rpow_add hx0]
    congr 1
    ring
  have hmain : A*x^q*Real.exp (-b*x) ≤ c^2*x^(-2/α) := by
    calc
      _ = (A*(x^(q+2/α)*Real.exp (-b*x)))*x^(-2/α) := by
        calc
          _ = A*(x^(q+2/α)*x^(-2/α))*Real.exp (-b*x) := by rw [hpowcancel]
          _ = _ := by ring
      _ ≤ c^2*x^(-2/α) := mul_le_mul_of_nonneg_right hx (by positivity)
  have hlogpow : 1≤(Real.log x)^(β/α) :=
    Real.one_le_rpow hL1.le (by positivity)
  have hrad : c*x^(-(1/α)) ≤ canonicalPowerlogRadius α β c x := by
    dsimp [canonicalPowerlogRadius]
    exact le_mul_of_one_le_right (by positivity) hlogpow
  have hsq : (c*x^(-(1/α)))^2=c^2*x^(-2/α) := by
    rw [mul_pow]
    congr 1
    rw [←Real.rpow_natCast (x^(-(1/α))) 2,←Real.rpow_mul hx0.le]
    congr 1
    norm_num
    ring
  apply hmain.trans
  rw [←hsq]
  exact pow_le_pow_left₀ (by positivity) hrad 2

end BrownianSharp.AlignmentPaperQuantizationUpperRates
