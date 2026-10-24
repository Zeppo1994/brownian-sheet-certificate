import BrownianSharp.YoungConvolutionLp
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-! Complex-valued Young convolution estimate from the positive real one. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Convolution of complex continuous functions on the circle obeys the
usual `L¹`-kernel to `Lᵖ` estimate for every real `p ≥ 1`. -/
theorem addCircle_complex_convolution_rpow_le
    (K u : C(UnitAddCircle, ℂ)) (p : ℝ) (hp : 1 ≤ p) :
    (∫ x : UnitAddCircle,
      ‖∫ y : UnitAddCircle, K y * u (x - y) ∂AddCircle.haarAddCircle‖ ^ p
        ∂AddCircle.haarAddCircle) ≤
      (∫ y : UnitAddCircle, ‖K y‖ ∂AddCircle.haarAddCircle) ^ p *
        (∫ x : UnitAddCircle, ‖u x‖ ^ p ∂AddCircle.haarAddCircle) := by
  classical
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  letI : IsProbabilityMeasure μ := by dsimp [μ]; infer_instance
  letI : IsFiniteMeasureOnCompacts μ := by dsimp [μ]; infer_instance
  let a : ℝ := ∫ y : UnitAddCircle, ‖K y‖ ∂μ
  let knorm : C(UnitAddCircle, ℝ) := ⟨fun y => ‖K y‖, K.continuous.norm⟩
  let unorm : C(UnitAddCircle, ℝ) := ⟨fun x => ‖u x‖, u.continuous.norm⟩
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hKint : Integrable (fun y : UnitAddCircle => ‖K y‖) μ :=
    K.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have huInt : Integrable (fun x : UnitAddCircle => ‖u x‖ ^ p) μ := by
    have hcont : Continuous (fun x : UnitAddCircle => ‖u x‖ ^ p) := by
      exact (Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp
        (continuous_norm.comp u.continuous)
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  by_cases ha : a = 0
  · have hKzero : (fun y : UnitAddCircle => ‖K y‖) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) hKint).mp (by simpa [a] using ha)
    have hconvzero (x : UnitAddCircle) :
        (∫ y : UnitAddCircle, K y * u (x-y) ∂μ) = 0 := by
      have hzero : (fun y : UnitAddCircle => K y * u (x-y)) =ᵐ[μ] 0 := by
        filter_upwards [hKzero] with y hy
        have hKy : K y = 0 := norm_eq_zero.mp (by simpa using hy)
        simp [hKy]
      rw [integral_congr_ae hzero]
      simp
    have hfun : (fun x : UnitAddCircle =>
        ‖∫ y : UnitAddCircle, K y * u (x-y) ∂AddCircle.haarAddCircle‖ ^ p) =
        fun _ => 0 := by
      funext x
      have hz := hconvzero x
      simpa [μ, Real.zero_rpow (by linarith : p ≠ 0)] using congrArg (fun z : ℂ => ‖z‖ ^ p) hz
    simp [μ, a, ha, hfun, Real.zero_rpow (by linarith : p ≠ 0)]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (Ne.symm ha)
    let kprob : C(UnitAddCircle, ℝ) := ⟨fun y => ‖K y‖ / a,
      K.continuous.norm.div_const a⟩
    have hkprob_nonneg : ∀ y, 0 ≤ kprob y := fun y => div_nonneg (norm_nonneg _) ha_pos.le
    have hknorm_eq (y : UnitAddCircle) : ‖K y‖ = a * kprob y := by
      dsimp [kprob]
      field_simp
    have hkprob_mass : (∫ y : UnitAddCircle, kprob y ∂μ) = 1 := by
      have : (∫ y : UnitAddCircle, kprob y ∂μ) = a⁻¹ * a := by
        dsimp [kprob]
        rw [show (fun y : UnitAddCircle => ‖K y‖ / a) =
          (fun y => a⁻¹ * ‖K y‖) by funext y; simp [div_eq_mul_inv, mul_comm]]
        rw [integral_const_mul]
      rw [this]
      exact inv_mul_cancel₀ ha
    have hconvNormBound (x : UnitAddCircle) :
        ‖∫ y : UnitAddCircle, K y * u (x-y) ∂μ‖ ≤
          a * (∫ y : UnitAddCircle, kprob y * ‖u (x-y)‖ ∂μ) := by
      have hsub : Continuous (fun y : UnitAddCircle => x-y) := continuous_const.sub continuous_id
      have hint : Integrable (fun y : UnitAddCircle => K y * u (x-y)) μ :=
        (K.continuous.mul (u.continuous.comp hsub)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      calc
        _ ≤ ∫ y : UnitAddCircle, ‖K y * u (x-y)‖ ∂μ := norm_integral_le_integral_norm _
        _ = ∫ y : UnitAddCircle, ‖K y‖ * ‖u (x-y)‖ ∂μ := by
          congr 1
          funext y
          rw [norm_mul]
        _ = ∫ y : UnitAddCircle, a * (kprob y * ‖u (x-y)‖) ∂μ := by
          congr 1
          funext y
          rw [hknorm_eq y]
          ring
        _ = a * (∫ y : UnitAddCircle, kprob y * ‖u (x-y)‖ ∂μ) := by
          rw [integral_const_mul]
    let cconv : UnitAddCircle → ℂ := fun x =>
      ∫ y : UnitAddCircle, K y * u (x-y) ∂μ
    let rconv : UnitAddCircle → ℝ := fun x =>
      ∫ y : UnitAddCircle, kprob y * ‖u (x-y)‖ ∂μ
    have hrconv_nonneg (x : UnitAddCircle) : 0 ≤ rconv x := by
      apply integral_nonneg
      intro y
      exact mul_nonneg (hkprob_nonneg y) (norm_nonneg _)
    have hpoint (x : UnitAddCircle) : ‖cconv x‖ ^ p ≤ (a * rconv x) ^ p := by
      exact Real.rpow_le_rpow (norm_nonneg _) (hconvNormBound x) (by linarith)
    have hjointSM : StronglyMeasurable (fun z : UnitAddCircle × UnitAddCircle =>
        K z.2 * u (z.1-z.2)) :=
      (K.continuous.comp continuous_snd).mul
        (u.continuous.comp (continuous_fst.sub continuous_snd)) |>.stronglyMeasurable
    have hcconvSM : StronglyMeasurable cconv := hjointSM.integral_prod_right
    have hcconvMeas : Measurable cconv := hcconvSM.measurable
    have hboundU : ∀ x, ‖u x‖ ≤ ‖u‖ := (u.norm_le (norm_nonneg _)).mp le_rfl
    have hrjointSM : StronglyMeasurable (fun z : UnitAddCircle × UnitAddCircle =>
        kprob z.2 * ‖u (z.1-z.2)‖) :=
      (kprob.continuous.comp continuous_snd).mul
        (continuous_norm.comp (u.continuous.comp (continuous_fst.sub continuous_snd))) |>.stronglyMeasurable
    have hrconvMeas : Measurable rconv := hrjointSM.integral_prod_right |>.measurable
    have hrconvBound (x : UnitAddCircle) : rconv x ≤ ‖u‖ := by
      calc
        _ ≤ ∫ y : UnitAddCircle, kprob y * ‖u‖ ∂μ := by
          have hsub : Continuous (fun y : UnitAddCircle => x-y) := continuous_const.sub continuous_id
          have hleft : Integrable (fun y : UnitAddCircle => kprob y * ‖u (x-y)‖) μ :=
            ((kprob.continuous.mul (continuous_norm.comp (u.continuous.comp hsub))).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _))
          have hright : Integrable (fun y : UnitAddCircle => kprob y * ‖u‖) μ :=
            (kprob.continuous.mul continuous_const).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
          apply integral_mono hleft hright
          intro y
          exact mul_le_mul_of_nonneg_left (hboundU (x-y)) (hkprob_nonneg y)
        _ = ‖u‖ := by
          calc
            _ = (∫ y : UnitAddCircle, kprob y ∂μ) * ‖u‖ := by rw [integral_mul_const]
            _ = ‖u‖ := by rw [hkprob_mass]; ring
    have hconvBound (x : UnitAddCircle) : ‖cconv x‖ ≤ a * ‖u‖ := by
      calc
        _ ≤ ∫ y : UnitAddCircle, ‖K y * u (x-y)‖ ∂μ := by
          have hsub : Continuous (fun y : UnitAddCircle => x-y) := continuous_const.sub continuous_id
          have hint : Integrable (fun y : UnitAddCircle => K y * u (x-y)) μ :=
            (K.continuous.mul (u.continuous.comp hsub)).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
          exact norm_integral_le_integral_norm _
        _ = ∫ y : UnitAddCircle, a * (kprob y * ‖u (x-y)‖) ∂μ := by
          congr 1
          funext y
          rw [norm_mul, hknorm_eq y]
          ring
        _ ≤ ∫ y : UnitAddCircle, a * (kprob y * ‖u‖) ∂μ := by
          apply integral_mono
          · have hsub : Continuous (fun y : UnitAddCircle => x-y) := continuous_const.sub continuous_id
            have hcont : Continuous (fun y : UnitAddCircle => a * (kprob y * ‖u (x-y)‖)) :=
              continuous_const.mul (kprob.continuous.mul (continuous_norm.comp (u.continuous.comp hsub)))
            exact (hcont.integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _))
          · have hcont : Continuous (fun y : UnitAddCircle => a * (kprob y * ‖u‖)) :=
              continuous_const.mul (kprob.continuous.mul continuous_const)
            exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
          · intro y
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hboundU (x-y)) (hkprob_nonneg y)) ha_pos.le
        _ = a * ‖u‖ := by
          calc
            _ = a * (∫ y : UnitAddCircle, kprob y * ‖u‖ ∂μ) := by rw [integral_const_mul]
            _ = a * ‖u‖ := by rw [integral_mul_const, hkprob_mass]; ring
    have hpowBound : ∀ x, ‖cconv x‖ ^ p ≤ (a * ‖u‖) ^ p := by
      intro x
      exact Real.rpow_le_rpow (norm_nonneg _) (hconvBound x) (by linarith)
    have hLHSint : Integrable (fun x : UnitAddCircle => ‖cconv x‖ ^ p) μ := by
      apply Integrable.of_bound
        ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).measurable.comp
          (continuous_norm.measurable.comp hcconvMeas)).aestronglyMeasurable
        ((a * ‖u‖) ^ p)
      filter_upwards [] with x
      change |‖cconv x‖ ^ p| ≤ (a * ‖u‖) ^ p
      rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hpowBound x
    have hRHSint : Integrable (fun x : UnitAddCircle => ‖u x‖ ^ p) μ := huInt
    have hpos := addCircle_positive_convolution_rpow_le kprob unorm hkprob_nonneg
      hkprob_mass p hp
    have hpos' : (∫ x : UnitAddCircle, rconv x ^ p ∂μ) ≤
        ∫ x : UnitAddCircle, ‖u x‖ ^ p ∂μ := by
      simpa [μ, rconv, unorm, Real.norm_eq_abs,
        abs_of_nonneg (hrconv_nonneg _), abs_of_nonneg (norm_nonneg _)] using hpos
    calc
      (∫ x : UnitAddCircle, ‖cconv x‖ ^ p ∂μ) ≤
          ∫ x : UnitAddCircle, (a * rconv x) ^ p ∂μ := by
            apply integral_mono hLHSint
            · apply Integrable.of_bound
                (((Real.continuous_rpow_const (by linarith : 0 ≤ p)).measurable.comp
                  (continuous_const.measurable.mul hrconvMeas)).aestronglyMeasurable)
                ((a * ‖u‖) ^ p)
              filter_upwards [] with x
              change |(a * rconv x) ^ p| ≤ (a * ‖u‖) ^ p
              rw [abs_of_nonneg (Real.rpow_nonneg (mul_nonneg ha_pos.le (hrconv_nonneg x)) _)]
              exact Real.rpow_le_rpow (mul_nonneg ha_pos.le (hrconv_nonneg x))
                (mul_le_mul_of_nonneg_left (hrconvBound x) ha_pos.le) (by linarith)
            · exact hpoint
      _ = a ^ p * (∫ x : UnitAddCircle, rconv x ^ p ∂μ) := by
          rw [show (fun x : UnitAddCircle => (a * rconv x) ^ p) =
            (fun x => a ^ p * rconv x ^ p) by funext x; rw [Real.mul_rpow ha_pos.le (hrconv_nonneg x)]]
          rw [integral_const_mul]
      _ ≤ a ^ p * (∫ x : UnitAddCircle, ‖u x‖ ^ p ∂μ) :=
          mul_le_mul_of_nonneg_left hpos' (Real.rpow_nonneg ha_pos.le _)

end BrownianSharp

end
