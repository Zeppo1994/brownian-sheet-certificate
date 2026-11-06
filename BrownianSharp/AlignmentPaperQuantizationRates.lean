import BrownianSharp.AlignmentPaperQuantization
import BrownianSharp.AlignmentFractionalSheetStatement
import BrownianSharp.AlignmentGaussianIntegratedReverse
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

open Filter Topology
open Asymptotics
open MeasureTheory HaarQuarter
open scoped ENNReal

namespace BrownianSharp

noncomputable section

/-- The logarithmic factor in the inverse of a power-log small-ball rate is
asymptotically negligible compared with `log x`. This is the scalar estimate
needed when selecting the quantization radius at sample size `m`. -/
theorem eventually_loglog_div_log_small
    {β : ℝ} (hβ : 0 ≤ β) :
    ∀ᶠ x : ℝ in atTop,
      1 < x ∧ 0 < Real.log x ∧
        β * Real.log (Real.log x) ≤ (Real.log x) / 2 := by
  have hratio : Tendsto (fun x : ℝ =>
      Real.log (Real.log x) / Real.log x) atTop (𝓝 0) := by
    have h := Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    exact h.tendsto_div_nhds_zero
  have hsmall : ∀ᶠ x : ℝ in atTop,
      β * (Real.log (Real.log x) / Real.log x) < 1 / 2 := by
    have ht : Tendsto (fun x : ℝ => β *
        (Real.log (Real.log x) / Real.log x)) atTop (𝓝 0) := by
      simpa using hratio.const_mul β
    exact ht.eventually (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  filter_upwards [eventually_gt_atTop (Real.exp 1), hsmall] with x hx hs
  have hx' : 1 < x := by
    have h1 : 1 < Real.exp 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr (by norm_num)
    exact lt_trans h1 hx
  have hL : 1 < Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hx
  have hLpos : 0 < Real.log x := by linarith
  have hmul : β * (Real.log (Real.log x) / Real.log x) < 1 / 2 := hs
  have hdiv : β * Real.log (Real.log x) < (Real.log x) / 2 := by
    have := mul_lt_mul_of_pos_right hmul hLpos
    field_simp [ne_of_gt hLpos] at this
    nlinarith
  exact ⟨hx', hLpos, hdiv.le⟩

/-- At the canonical inverse power-log radius, the reciprocal logarithm is at
least a fixed fraction of `log x`; this is the key scalar half of the
quantization-scale inversion. -/
theorem eventually_log_reciprocal_powerlog_radius
    {α β c : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) / (2 * α) ≤
        Real.log ((Real.sqrt 2 * (c * x ^ (-(1 / α)) *
          (Real.log x) ^ (β / α)))⁻¹) := by
  have hbeta : 0 ≤ 2 * β := by positivity
  have hloglog := eventually_loglog_div_log_small hbeta
  have hconst : ∀ᶠ x : ℝ in atTop,
      Real.log (Real.sqrt 2 * c) ≤ Real.log x / (4 * α) := by
    have hlogx := Real.tendsto_log_atTop.eventually_ge_atTop
      (4 * α * Real.log (Real.sqrt 2 * c))
    filter_upwards [hlogx] with x hx
    have : 0 < 4 * α := by positivity
    apply (le_div_iff₀ this).2
    nlinarith [hx]
  filter_upwards [hloglog, hconst, eventually_gt_atTop (Real.exp 1)] with x hll hconst hx
  rcases hll with ⟨hxgt, hLpos, hllbound⟩
  have hL : 1 < Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hx
  let L := Real.log x
  have hLog : Real.log ((Real.sqrt 2 * (c * x ^ (-(1 / α)) *
        (Real.log x) ^ (β / α)))⁻¹) =
      -Real.log (Real.sqrt 2 * c) + (1 / α) * L - (β / α) * Real.log L := by
    have hxpos : 0 < x := by linarith
    have hK : 0 < Real.sqrt 2 * c := mul_pos (Real.sqrt_pos.2 (by norm_num)) hc
    have hpowx : 0 < x ^ (-(1 / α)) := Real.rpow_pos_of_pos hxpos _
    have hpowL : 0 < L ^ (β / α) := Real.rpow_pos_of_pos hLpos _
    have hprod : Real.sqrt 2 * (c * x ^ (-(1 / α)) * L ^ (β / α)) =
        (Real.sqrt 2 * c) * (x ^ (-(1 / α)) * L ^ (β / α)) := by ring
    rw [Real.log_inv, hprod,
      Real.log_mul (ne_of_gt hK) (ne_of_gt (mul_pos hpowx hpowL)),
      Real.log_mul (ne_of_gt hpowx) (ne_of_gt hpowL),
      Real.log_rpow hxpos, Real.log_rpow hLpos]
    dsimp [L]
    ring
  rw [hLog]
  have hll' : (2 * β) * Real.log L ≤ L / 2 := by
    simpa [L] using hllbound
  have hbeta' : β * Real.log L ≤ L / 4 := by nlinarith [hll']
  have hconst' : Real.log (Real.sqrt 2 * c) ≤ L / (4 * α) := by simpa [L] using hconst
  field_simp [ne_of_gt hα] at hconst'
  have hmain := hLog
  dsimp [L] at hmain
  field_simp [ne_of_gt hα]
  nlinarith [hconst', hbeta', hmain]

/-- The canonical inverse power-log radius tends to zero. -/
theorem tendsto_powerlog_radius_zero
    {α β c : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hc : 0 < c) :
    Tendsto (fun x : ℝ => c * x ^ (-(1 / α)) *
      (Real.log x) ^ (β / α)) atTop (𝓝 0) := by
  let r : ℝ := β / α
  let s : ℝ := 1 / (2 * α)
  have hs : 0 < s := by dsimp [s]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsmall : Tendsto (fun x : ℝ => (Real.log x) ^ r / x ^ s)
      atTop (𝓝 0) := by
    have h := (isLittleO_log_rpow_rpow_atTop r hs).tendsto_div_nhds_zero
    simpa [div_eq_mul_inv] using h
  have hpow : Tendsto (fun x : ℝ => x ^ (-s)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hs
  have hprod : Tendsto (fun x : ℝ =>
      c * ((Real.log x) ^ r / x ^ s) * x ^ (-s)) atTop (𝓝 0) := by
    have hcT : Tendsto (fun _ : ℝ => c) atTop (𝓝 c) := tendsto_const_nhds
    have hmul := (hcT.mul hsmall).mul hpow
    simpa using hmul
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hxpos : 0 < x := by linarith
  have hsumm : -(1 / α) = -s + -s := by
    dsimp [s]
    ring
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hrpow : (Real.log x) ^ r = (Real.log x) ^ (β / α) := by rfl
  rw [hrpow, hsumm, Real.rpow_add hxpos]
  rw [Real.rpow_neg (le_of_lt hxpos)]
  ring

theorem eventually_powerlog_radius_le
    {α β c ε₀ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hc : 0 < c) (hε₀ : 0 < ε₀) :
    ∀ᶠ x : ℝ in atTop,
      c * x ^ (-(1 / α)) * (Real.log x) ^ (β / α) ≤ ε₀ := by
  have ht := tendsto_powerlog_radius_zero hα hβ hc
  exact ht.eventually (Iic_mem_nhds hε₀)

private theorem powerlog_radius_rpow_identity
    {α β c x : ℝ} (hα : 0 < α) (hc : 0 < c) (hx : 1 < x) :
    (Real.sqrt 2 * (c * x ^ (-(1 / α)) *
      (Real.log x) ^ (β / α))) ^ (-α) =
      (Real.sqrt 2 * c) ^ (-α) * x * (Real.log x) ^ (-β) := by
  have hxpos : 0 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx
  have hK : 0 ≤ Real.sqrt 2 * c := by positivity
  have hpowx : 0 ≤ x ^ (-(1 / α)) := by positivity
  have hpowL : 0 ≤ (Real.log x) ^ (β / α) := by positivity
  have hprod : 0 ≤ x ^ (-(1 / α)) * (Real.log x) ^ (β / α) := by positivity
  rw [show Real.sqrt 2 * (c * x ^ (-(1 / α)) *
        (Real.log x) ^ (β / α)) =
      (Real.sqrt 2 * c) * (x ^ (-(1 / α)) *
        (Real.log x) ^ (β / α)) by ring]
  rw [Real.mul_rpow hK hprod, Real.mul_rpow hpowx hpowL]
  rw [← Real.rpow_mul (le_of_lt hxpos),
    ← Real.rpow_mul (le_of_lt hLpos)]
  have he1 : (-(1 / α)) * (-α) = 1 := by field_simp
  have he2 : (β / α) * (-α) = -β := by field_simp
  rw [he1, he2, Real.rpow_one]
  ring

theorem eventually_powerlog_rate_lower
    {α β c : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      (Real.sqrt 2 * c) ^ (-α) * (1 / (2 * α)) ^ β * x ≤
        Latest.smallBallRate α β
          (Real.sqrt 2 * (c * x ^ (-(1 / α)) * (Real.log x) ^ (β / α))) := by
  have hlog := eventually_log_reciprocal_powerlog_radius hα hβ hc
  filter_upwards [hlog, eventually_gt_atTop (Real.exp 1)] with x hlog hx
  have hxpos : 0 < x := (Real.exp_pos 1).trans hx
  have hxgt : 1 < x := by
    have h1 : 1 < Real.exp 1 := by rw [← Real.exp_zero]; exact Real.exp_lt_exp.mpr (by norm_num)
    exact h1.trans hx
  have hLpos : 0 < Real.log x := Real.log_pos hxgt
  let eps := Real.sqrt 2 * (c * x ^ (-(1 / α)) * (Real.log x) ^ (β / α))
  have heps : 0 < eps := by dsimp [eps]; positivity
  have hRpos : 0 < Real.log eps⁻¹ := by
    have hbound : 0 < Real.log x / (2 * α) := by positivity
    change 0 < Real.log ((Real.sqrt 2 * (c * x ^ (-(1 / α)) *
      (Real.log x) ^ (β / α)))⁻¹)
    exact lt_of_lt_of_le hbound hlog
  have hRpow : (Real.log x / (2 * α)) ^ β ≤
      (Real.log eps⁻¹) ^ β := Real.rpow_le_rpow (by positivity) hlog hβ
  have hcancel : (Real.log x / (2 * α)) ^ β *
      (Real.log x) ^ (-β) = (1 / (2 * α)) ^ β := by
    rw [show Real.log x / (2 * α) = Real.log x * (1 / (2 * α)) by field_simp]
    rw [Real.mul_rpow hLpos.le (by positivity)]
    have hz : (Real.log x) ^ β * (Real.log x) ^ (-β) = 1 := by
      rw [← Real.rpow_add hLpos]
      simp
    calc
      (Real.log x) ^ β * (1 / (2 * α)) ^ β * (Real.log x) ^ (-β) =
          ((Real.log x) ^ β * (Real.log x) ^ (-β)) * (1 / (2 * α)) ^ β := by ring
      _ = (1 / (2 * α)) ^ β := by simpa [hz]
  have hidentity : eps ^ (-α) = (Real.sqrt 2 * c) ^ (-α) * x *
      (Real.log x) ^ (-β) := by
    simpa [eps] using powerlog_radius_rpow_identity (α := α) (β := β)
      (c := c) (x := x) hα hc hxgt
  have hconv : eps ^ (-α) = eps⁻¹ ^ α := by
    rw [Real.rpow_neg (le_of_lt heps), ← Real.inv_rpow (le_of_lt heps)]
  simp only [Latest.smallBallRate]
  rw [← hconv]
  change (Real.sqrt 2 * c) ^ (-α) * (1 / (2 * α)) ^ β * x ≤
      eps ^ (-α) * (Real.log eps⁻¹) ^ β
  calc
    (Real.sqrt 2 * c) ^ (-α) * (1 / (2 * α)) ^ β * x =
        (Real.sqrt 2 * c) ^ (-α) * x *
          ((Real.log x / (2 * α)) ^ β * (Real.log x) ^ (-β)) := by
            rw [hcancel]
            ring
    _ ≤ (Real.sqrt 2 * c) ^ (-α) * x *
          ((Real.log eps⁻¹) ^ β * (Real.log x) ^ (-β)) := by
            gcongr
    _ = eps ^ (-α) * (Real.log eps⁻¹) ^ β := by
            dsimp [eps]
            rw [hidentity]
            ring

theorem exists_powerlog_scale_for_coefficient
    {α β c₀ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hc₀ : 0 < c₀) :
    ∃ c : ℝ, 0 < c ∧
      c₀ * (Real.sqrt 2 * c) ^ (-α) * (1 / (2 * α)) ^ β = 4 := by
  let A : ℝ := (1 / (2 * α)) ^ β
  let T : ℝ := c₀ * A / 4
  let c : ℝ := (Real.sqrt 2)⁻¹ * T ^ (1 / α)
  have hA : 0 < A := by dsimp [A]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hroot : 0 < T ^ (1 / α) := Real.rpow_pos_of_pos hT _
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hc : 0 < c := by dsimp [c]; positivity
  have hsimpl : Real.sqrt 2 * c = T ^ (1 / α) := by
    dsimp [c]
    field_simp
  have hpow : (T ^ (1 / α)) ^ (-α) = T⁻¹ := by
    rw [← Real.rpow_mul hT.le]
    have he : (1 / α) * (-α) = -1 := by field_simp
    rw [he, Real.rpow_neg hT.le]
    simp
  refine ⟨c, hc, ?_⟩
  rw [hsimpl, hpow]
  dsimp [T, A]
  field_simp

theorem exists_eventual_powerlog_strength
    {α β c₀ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hc₀ : 0 < c₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      2 ≤ x ∧ 2 * Real.log (2 * Real.exp x) ≤ c₀ *
        Latest.smallBallRate α β
          (Real.sqrt 2 * (c * x ^ (-(1 / α)) * (Real.log x) ^ (β / α))) := by
  obtain ⟨c, hc, hcoeff⟩ := exists_powerlog_scale_for_coefficient hα hβ hc₀
  have hrate := eventually_powerlog_rate_lower hα hβ hc
  refine ⟨c, hc, ?_⟩
  filter_upwards [hrate, eventually_ge_atTop (2 : ℝ)]
    with x hrate hx
  have hxpos : 0 < x := by linarith
  have hmain : 4 * x ≤ c₀ * Latest.smallBallRate α β
      (Real.sqrt 2 * (c * x ^ (-(1 / α)) * (Real.log x) ^ (β / α))) := by
    calc
      4 * x = (c₀ * ((Real.sqrt 2 * c) ^ (-α) *
          (1 / (2 * α)) ^ β)) * x := by rw [← hcoeff]; ring
      _ = c₀ * (((Real.sqrt 2 * c) ^ (-α) *
          (1 / (2 * α)) ^ β) * x) := by ring
      _ ≤ c₀ * Latest.smallBallRate α β
          (Real.sqrt 2 * (c * x ^ (-(1 / α)) * (Real.log x) ^ (β / α))) := by
            gcongr
  have hlog : Real.log (2 * Real.exp x) = Real.log 2 + x := by
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos x)), Real.log_exp]
  rw [hlog]
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)) (by norm_num)
    linarith
  exact ⟨hx, by nlinarith⟩

theorem exists_eventual_powerlog_strength_nat
    {α β c₀ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hc₀ : 0 < c₀) :
    ∃ c : ℝ, 0 < c ∧ ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      2 ≤ Real.log (m : ℝ) ∧ 2 * Real.log (2 * (m : ℝ)) ≤ c₀ *
        Latest.smallBallRate α β
          (Real.sqrt 2 * (c * (Real.log (m : ℝ)) ^ (-(1 / α)) *
            (Real.log (Real.log (m : ℝ))) ^ (β / α))) := by
  obtain ⟨c, hc, hstrength⟩ := exists_eventual_powerlog_strength hα hβ hc₀
  have hcomp : ∀ᶠ m : ℕ in atTop,
      2 ≤ Real.log (m : ℝ) ∧ 2 * Real.log (2 * Real.exp (Real.log (m : ℝ))) ≤ c₀ *
        Latest.smallBallRate α β
          (Real.sqrt 2 * (c * (Real.log (m : ℝ)) ^ (-(1 / α)) *
            (Real.log (Real.log (m : ℝ))) ^ (β / α))) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hstrength
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hcomp
  refine ⟨c, hc, max M 2, ?_⟩
  intro m hm
  have h := hM m (le_trans (le_max_left M 2) hm)
  have hmpos : 0 < (m : ℝ) := by
    have hm2 : 2 ≤ m := le_trans (le_max_right M 2) hm
    exact_mod_cast (by omega : 0 < m)
  rcases h with ⟨hlogm, hstrength⟩
  rw [Real.exp_log hmpos] at hstrength
  exact ⟨hlogm, hstrength⟩

def canonicalPowerlogRadius (α β c x : ℝ) : ℝ :=
  c * x ^ (-(1 / α)) * (Real.log x) ^ (β / α)

theorem eventually_powerlog_radius_window_nat
    {α β c ε₀ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hc : 0 < c) (hε₀ : 0 < ε₀) :
    ∀ᶠ m : ℕ in atTop,
      Real.sqrt 2 * canonicalPowerlogRadius α β c (Real.log (m : ℝ)) ≤ ε₀ := by
  have hrad := tendsto_powerlog_radius_zero hα hβ hc
  have hsmall : ∀ᶠ m : ℕ in atTop,
      canonicalPowerlogRadius α β c (Real.log (m : ℝ)) ≤ ε₀ / Real.sqrt 2 := by
    have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    exact hlog.eventually
      (hrad.eventually (Iic_mem_nhds (div_pos hε₀ (Real.sqrt_pos.2 (by norm_num)))))
  filter_upwards [hsmall] with m hm
  calc
    Real.sqrt 2 * canonicalPowerlogRadius α β c (Real.log (m : ℝ)) ≤
        Real.sqrt 2 * (ε₀ / Real.sqrt 2) :=
          mul_le_mul_of_nonneg_left hm (le_of_lt (Real.sqrt_pos.2 (by norm_num)))
    _ = ε₀ := by
      have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
      field_simp [hsqrt]

theorem centeredGaussian_quantizationQ1_lower_of_powerlog_smallball
    {X Ω : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [LocallyCompactSpace X] [CompactSpace X] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(X, ℝ)) (hF : Measurable F)
    (hG : ProbabilityTheory.IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
    {α β c₀ ε₀ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) (hc₀ : 0 < c₀)
    (m : ℕ) (hm : 0 < m) (t : ℝ) (ht : 0 < t)
    (hwindow : Real.sqrt 2 * t ≤ ε₀)
    (hstrength : 2 * Real.log (2 * (m : ℝ)) ≤
      c₀ * Latest.smallBallRate α β (Real.sqrt 2 * t))
    (hlog : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      c₀ * Latest.smallBallRate α β ε ≤
        -Real.log (P.real {ω | ‖F ω‖ ≤ ε}))
    (hmeas : ∀ c : Fin m → C(X, ℝ),
      Measurable (fun x => finiteCodebookDistortion hm c x)) :
    ENNReal.ofReal t / 2 ≤ quantizationQ1 (P.map F) m hm := by
  let ε := Real.sqrt 2 * t
  have hε : 0 < ε := mul_pos (Real.sqrt_pos.2 (by norm_num)) ht
  have hlog' := hlog ε hε hwindow
  have hreal : P.real {ω | ‖F ω‖ ≤ ε} ≤
      Real.exp (-c₀ * Latest.smallBallRate α β ε) := by
    by_cases hp : P.real {ω | ‖F ω‖ ≤ ε} = 0
    · rw [hp]
      exact (Real.exp_pos _).le
    · let p := P.real {ω | ‖F ω‖ ≤ ε}
      have hp' : 0 < p := lt_of_le_of_ne (by positivity) (Ne.symm hp)
      have hlogp : Real.log p ≤ -c₀ * Latest.smallBallRate α β ε := by
        dsimp [p]
        linarith [hlog']
      calc
        P.real {ω | ‖F ω‖ ≤ ε} = Real.exp (Real.log p) := (Real.exp_log hp').symm
        _ ≤ Real.exp (-c₀ * Latest.smallBallRate α β ε) := Real.exp_le_exp.mpr hlogp
  have hmass : (P.map F) (Metric.closedBall 0 ε) ≤
      ENNReal.ofReal (1 / (2 * (m : ℝ))) ^ 2 := by
    have hmap : (P.map F) (Metric.closedBall 0 ε) =
        P {ω | ‖F ω‖ ≤ ε} := by
      rw [Measure.map_apply hF Metric.isClosed_closedBall.measurableSet]
      congr 1
    have hprobENN : P {ω | ‖F ω‖ ≤ ε} ≤
        ENNReal.ofReal (Real.exp (-c₀ * Latest.smallBallRate α β ε)) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
      exact ENNReal.ofReal_le_ofReal hreal
    rw [hmap]
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-c₀ * Latest.smallBallRate α β ε)) := hprobENN
      _ ≤ ENNReal.ofReal (1 / (2 * (m : ℝ))) ^ 2 := by
        rw [← ENNReal.ofReal_pow]
        have hmain : Real.exp (-c₀ * Latest.smallBallRate α β ε) ≤
            Real.exp (-2 * Real.log (2 * (m : ℝ))) :=
          Real.exp_le_exp.mpr (by linarith [hstrength])
        have hM : 0 < 2 * (m : ℝ) := by positivity
        have hEq : Real.exp (-2 * Real.log (2 * (m : ℝ))) =
            (1 / (2 * (m : ℝ))) ^ 2 := by
          calc
            _ = Real.exp (Real.log ((2 * (m : ℝ))⁻¹) +
                Real.log ((2 * (m : ℝ))⁻¹)) := by
                  congr 1
                  rw [Real.log_inv (2 * (m : ℝ))]
                  ring
            _ = Real.exp (Real.log ((2 * (m : ℝ))⁻¹)) ^ 2 := by
                  rw [Real.exp_add]
                  ring
            _ = (1 / (2 * (m : ℝ))) ^ 2 := by
                  rw [Real.exp_log (inv_pos.mpr hM)]
                  congr 1
                  field_simp
        refine ENNReal.ofReal_le_ofReal (hmain.trans_eq hEq)
        positivity
  have hbudget : (m : ℝ≥0∞) * ENNReal.ofReal (1 / (2 * (m : ℝ))) ≤ 1 / 2 := by
    have hmcast : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    have hbcast : ENNReal.ofReal (1 / (2 * (m : ℝ))) =
        (2 * (m : ℝ≥0∞))⁻¹ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 * (m : ℝ))]
      norm_num [ENNReal.ofReal_natCast]
    rw [hbcast]
    have hmE : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hmcast
    change (m : ℝ≥0∞) * (2 * (m : ℝ≥0∞))⁻¹ ≤ 1 / 2
    have hmul : (m : ℝ≥0∞) * (2 * (m : ℝ≥0∞))⁻¹ = 1 / 2 := by
      have h2 : (2 : ℝ≥0∞) ≠ 0 := by norm_num
      have h2top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
      rw [ENNReal.mul_inv (Or.inl h2) (Or.inl h2top)]
      calc
        (m : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞)⁻¹) =
            (m : ℝ≥0∞) * ((m : ℝ≥0∞)⁻¹ * (2 : ℝ≥0∞)⁻¹) := by
              rw [mul_comm ((2 : ℝ≥0∞)⁻¹) ((m : ℝ≥0∞)⁻¹)]
        _ = (2 : ℝ≥0∞)⁻¹ := ENNReal.mul_inv_cancel_left hmE (by simp)
      norm_num
    rw [hmul]
  exact centered_gaussian_quantizationQ1_lower F hF hG hmean m hm t
    (1 / (2 * (m : ℝ))) ht.le (by positivity) hmeas hmass hbudget

end
end BrownianSharp
