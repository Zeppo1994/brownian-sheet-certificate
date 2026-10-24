import BrownianSharp.YoungLp
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! Complex Young inequality on a compact probability group, with translation
invariance supplied as a hypothesis so the result also applies to product
Haar tori. -/

noncomputable section
open MeasureTheory

namespace BrownianSharp

/-- The usual `L¹`-kernel to `Lᵖ` convolution estimate for continuous
complex functions on a compact additive group with translation-invariant
probability measure. -/
theorem compactGroup_complex_convolution_rpow_le
    {G : Type*} [AddGroup G] [TopologicalSpace G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G] [OpensMeasurableSpace G]
    [SecondCountableTopology G] [IsTopologicalAddGroup G]
    (μ : Measure G) [IsProbabilityMeasure μ]
    (htrans : ∀ y : G, MeasurePreserving (fun x : G => x-y) μ μ)
    (K u : C(G, ℂ)) (p : ℝ) (hp : 1 ≤ p) :
    (∫ x : G, ‖∫ y : G, K y * u (x-y) ∂μ‖ ^ p ∂μ) ≤
      (∫ y : G, ‖K y‖ ∂μ) ^ p * (∫ x : G, ‖u x‖ ^ p ∂μ) := by
  classical
  let a : ℝ := ∫ y : G, ‖K y‖ ∂μ
  let knorm : C(G, ℝ) := ⟨fun y => ‖K y‖, K.continuous.norm⟩
  let unorm : C(G, ℝ) := ⟨fun x => ‖u x‖, u.continuous.norm⟩
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact integral_nonneg (fun _ => norm_nonneg _)
  have hKint : Integrable (fun y : G => ‖K y‖) μ :=
    K.continuous.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have huInt : Integrable (fun x : G => ‖u x‖ ^ p) μ := by
    have hc : Continuous (fun x : G => ‖u x‖ ^ p) :=
      (Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp
        (continuous_norm.comp u.continuous)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hjoint : StronglyMeasurable (fun z : G × G => K z.2 * u (z.1-z.2)) :=
    (K.continuous.comp continuous_snd).mul
      (u.continuous.comp (continuous_fst.sub continuous_snd)) |>.stronglyMeasurable
  have hconvSM : StronglyMeasurable (fun x : G => ∫ y, K y * u (x-y) ∂μ) :=
    hjoint.integral_prod_right
  have hconvMeas : Measurable (fun x : G => ∫ y, K y * u (x-y) ∂μ) :=
    hconvSM.measurable
  by_cases ha : a = 0
  · have hKzero : (fun y : G => ‖K y‖) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => norm_nonneg _) hKint).mp
        (by simpa [a] using ha)
    have hconvzero (x : G) : (∫ y : G, K y * u (x-y) ∂μ) = 0 := by
      have hzero : (fun y : G => K y * u (x-y)) =ᵐ[μ] 0 := by
        filter_upwards [hKzero] with y hy
        have hKy : K y = 0 := norm_eq_zero.mp (by simpa using hy)
        simp [hKy]
      rw [integral_congr_ae hzero]
      simp
    have hfun : (fun x : G => ‖∫ y : G, K y * u (x-y) ∂μ‖ ^ p) = fun _ => 0 := by
      funext x
      rw [hconvzero x]
      simp [Real.zero_rpow (by linarith : p ≠ 0)]
    rw [hfun]
    simp [a, ha, Real.zero_rpow (by linarith : p ≠ 0)]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg (Ne.symm ha)
    let kprob : C(G, ℝ) := ⟨fun y => ‖K y‖ / a, K.continuous.norm.div_const a⟩
    have hk_nonneg : ∀ y, 0 ≤ kprob y := fun y => div_nonneg (norm_nonneg _) ha_pos.le
    have hk_mass : (∫ y : G, kprob y ∂μ) = 1 := by
      have heq : (∫ y : G, kprob y ∂μ) = a⁻¹ * a := by
        dsimp [kprob]
        rw [show (fun y : G => ‖K y‖ / a) = fun y => a⁻¹ * ‖K y‖ by
          funext y
          simp [div_eq_mul_inv, mul_comm]]
        rw [integral_const_mul]
      rw [heq]
      exact inv_mul_cancel₀ ha
    let gpow : C(G, ℝ) := ⟨fun x => ‖u x‖ ^ p,
      (Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp
        (continuous_norm.comp u.continuous)⟩
    have hboundU : ∀ x, ‖u x‖ ≤ ‖u‖ := (u.norm_le (norm_nonneg _)).mp le_rfl
    have hconvBound (x : G) :
        ‖∫ y : G, K y * u (x-y) ∂μ‖ ≤ a * ‖u‖ := by
      have hnormeq (y : G) : ‖K y‖ = a * kprob y := by
        dsimp [kprob]
        field_simp
      calc
        _ ≤ ∫ y : G, ‖K y * u (x-y)‖ ∂μ := norm_integral_le_integral_norm _
        _ = ∫ y : G, a * (kprob y * ‖u (x-y)‖) ∂μ := by
          congr 1
          funext y
          rw [norm_mul, hnormeq y]
          ring
        _ ≤ ∫ y : G, a * (kprob y * ‖u‖) ∂μ := by
          apply integral_mono
          · exact (continuous_const.mul (kprob.continuous.mul
              (continuous_norm.comp (u.continuous.comp (continuous_const.sub continuous_id))))).integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _)
          · exact (continuous_const.mul (kprob.continuous.mul continuous_const)).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)
          · intro y
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hboundU (x-y)) (hk_nonneg y)) ha_pos.le
        _ = a * ‖u‖ := by
          rw [integral_const_mul, integral_mul_const, hk_mass]
          ring
    have hconvPowBound (x : G) :
        ‖∫ y : G, K y * u (x-y) ∂μ‖ ^ p ≤ (a * ‖u‖) ^ p :=
      Real.rpow_le_rpow (norm_nonneg _) (hconvBound x) (by linarith)
    have hLHSint : Integrable (fun x : G =>
        ‖∫ y : G, K y * u (x-y) ∂μ‖ ^ p) μ := by
      apply Integrable.of_bound
        ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).measurable.comp
          (continuous_norm.measurable.comp hconvMeas)).aestronglyMeasurable
        ((a * ‖u‖) ^ p)
      filter_upwards [] with x
      change |‖∫ y : G, K y * u (x-y) ∂μ‖ ^ p| ≤ _
      rw [abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      exact hconvPowBound x
    let rpowConv : G → ℝ := fun x => ∫ y : G, kprob y * ‖u (x-y)‖ ^ p ∂μ
    have hrpowBound (x : G) :
        ‖∫ y : G, K y * u (x-y) ∂μ‖ ^ p ≤ a ^ p * rpowConv x := by
      have hsub : Continuous (fun y : G => x-y) := continuous_const.sub continuous_id
      let f : G → ℝ := fun y => ‖u (x-y)‖
      have hfcont : Continuous f := continuous_norm.comp (u.continuous.comp hsub)
      have hνmass : (μ.withDensity (fun y => ENNReal.ofReal (kprob y))) Set.univ = 1 := by
        rw [withDensity_apply _ MeasurableSet.univ]
        simp only [setLIntegral_univ]
        rw [← ofReal_integral_eq_lintegral_ofReal
          (kprob.continuous.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)) (ae_of_all _ hk_nonneg), hk_mass]
        norm_num
      letI : IsProbabilityMeasure (μ.withDensity (fun y => ENNReal.ofReal (kprob y))) := ⟨hνmass⟩
      have hfInt : Integrable f (μ.withDensity (fun y => ENNReal.ofReal (kprob y))) := by
        apply Integrable.of_bound hfcont.aestronglyMeasurable ‖u‖
        filter_upwards [] with y
        simpa [f] using hboundU (x-y)
      have hfabs : Integrable (fun y => |f y|)
          (μ.withDensity (fun y => ENNReal.ofReal (kprob y))) := by
        simpa [Real.norm_eq_abs, f] using hfInt.norm
      have hfpow : Integrable (fun y => |f y| ^ p)
          (μ.withDensity (fun y => ENNReal.ofReal (kprob y))) := by
        apply Integrable.of_bound
          ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp
            (continuous_abs.comp hfcont)).aestronglyMeasurable (‖u‖ ^ p)
        filter_upwards [] with y
        change |(|f y| ^ p)| ≤ _
        rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact Real.rpow_le_rpow (abs_nonneg _) (by simpa [f] using hboundU (x-y))
          (by linarith)
      have hjensen := weighted_integral_rpow_le μ kprob kprob.continuous.measurable
        hk_nonneg (kprob.continuous.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)) hk_mass f p hp hfInt hfabs hfpow
      have hkernelNorm (y : G) : ‖K y‖ = a * kprob y := by
        dsimp [kprob]
        field_simp
      have hnorm : ‖∫ y : G, K y * u (x-y) ∂μ‖ ≤
          a * (∫ y : G, kprob y * f y ∂μ) := by
        calc
          _ ≤ ∫ y : G, ‖K y * u (x-y)‖ ∂μ := norm_integral_le_integral_norm _
          _ = ∫ y : G, a * (kprob y * f y) ∂μ := by
            congr 1
            funext y
            rw [norm_mul, hkernelNorm y]
            ring
          _ = a * (∫ y : G, kprob y * f y ∂μ) := integral_const_mul _ _
      have hrpowNonneg : 0 ≤ rpowConv x := integral_nonneg fun y =>
        mul_nonneg (hk_nonneg y) (Real.rpow_nonneg (norm_nonneg _) _)
      calc
        _ ≤ (a * ∫ y : G, kprob y * f y ∂μ) ^ p :=
          Real.rpow_le_rpow (norm_nonneg _) hnorm (by linarith)
        _ = a ^ p * (∫ y : G, kprob y * f y ∂μ) ^ p := by
          rw [Real.mul_rpow ha_pos.le (integral_nonneg fun y =>
            mul_nonneg (hk_nonneg y) (norm_nonneg _))]
        _ ≤ a ^ p * rpowConv x := by
          have hjensen' : (∫ y : G, kprob y * f y ∂μ) ^ p ≤ rpowConv x := by
            have hmean : 0 ≤ ∫ y : G, kprob y * f y ∂μ :=
              integral_nonneg fun y => mul_nonneg (hk_nonneg y) (norm_nonneg _)
            simpa [rpowConv, f, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hmean] using hjensen
          exact mul_le_mul_of_nonneg_left hjensen' (Real.rpow_nonneg ha_pos.le _)
    have hrpowMeas : Measurable rpowConv := by
      have hj : StronglyMeasurable (fun z : G × G =>
          kprob z.2 * ‖u (z.1-z.2)‖ ^ p) := by
        exact ((kprob.continuous.comp continuous_snd).mul
          ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp
            (continuous_norm.comp (u.continuous.comp (continuous_fst.sub continuous_snd))))).stronglyMeasurable
      exact hj.integral_prod_right.measurable
    have hFubini : Integrable (fun z : G × G =>
        kprob z.2 * ‖u (z.1-z.2)‖ ^ p) (μ.prod μ) := by
      have hcont : Continuous (fun z : G × G =>
          kprob z.2 * ‖u (z.1-z.2)‖ ^ p) :=
        (kprob.continuous.comp continuous_snd).mul
          ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp
            (continuous_norm.comp (u.continuous.comp (continuous_fst.sub continuous_snd))))
      apply Integrable.of_bound
        hcont.aestronglyMeasurable
        (‖kprob‖ * ‖u‖ ^ p)
      filter_upwards [] with z
      change ‖kprob z.2 * ‖u (z.1-z.2)‖ ^ p‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hk_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
      calc
        kprob z.2 * ‖u (z.1-z.2)‖ ^ p ≤ ‖kprob‖ * ‖u (z.1-z.2)‖ ^ p := by
          exact mul_le_mul_of_nonneg_right
            (calc
              kprob z.2 ≤ |kprob z.2| := le_abs_self _
              _ = ‖kprob z.2‖ := by rw [Real.norm_eq_abs]
              _ ≤ ‖kprob‖ := (kprob.norm_le (norm_nonneg _)).mp le_rfl _)
            (Real.rpow_nonneg (norm_nonneg _) _)
        _ ≤ ‖kprob‖ * ‖u‖ ^ p := by gcongr; exact hboundU _
    have htransPow (y : G) :
        (∫ x : G, ‖u (x-y)‖ ^ p ∂μ) = ∫ x : G, ‖u x‖ ^ p ∂μ := by
      exact (htrans y).integral_comp (Homeomorph.subRight y).measurableEmbedding
        (fun x => ‖u x‖ ^ p)
    have hRHSint : Integrable (fun x : G => a ^ p * rpowConv x) μ := by
      apply Integrable.of_bound (continuous_const.measurable.mul hrpowMeas).aestronglyMeasurable
        ((a * ‖u‖) ^ p)
      filter_upwards [] with x
      have hrpowU (x : G) : rpowConv x ≤ ‖u‖ ^ p := by
        have hint : Integrable (fun y : G => kprob y * ‖u (x-y)‖ ^ p) μ :=
          (kprob.continuous.mul
            ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp
              (continuous_norm.comp (u.continuous.comp (continuous_const.sub continuous_id))))).integrable_of_hasCompactSupport
                (HasCompactSupport.of_compactSpace _)
        have hupper : Integrable (fun y : G => kprob y * ‖u‖ ^ p) μ :=
          (kprob.continuous.mul continuous_const).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        calc
          rpowConv x ≤ ∫ y : G, kprob y * ‖u‖ ^ p ∂μ := by
            apply integral_mono hint hupper
            intro y
            exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow (norm_nonneg _) (hboundU (x-y)) (by linarith))
              (hk_nonneg y)
          _ = ‖u‖ ^ p := by rw [integral_mul_const, hk_mass, one_mul]
      have hnonneg : 0 ≤ a ^ p * rpowConv x :=
        mul_nonneg (Real.rpow_nonneg ha_pos.le _) (integral_nonneg fun y =>
          mul_nonneg (hk_nonneg y) (Real.rpow_nonneg (norm_nonneg _) _))
      change ‖a ^ p * rpowConv x‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      calc
        a ^ p * rpowConv x ≤ a ^ p * ‖u‖ ^ p :=
          mul_le_mul_of_nonneg_left (hrpowU x) (Real.rpow_nonneg ha_pos.le _)
        _ = (a * ‖u‖) ^ p := (Real.mul_rpow ha_pos.le (norm_nonneg u)).symm
    calc
      _ ≤ ∫ x : G, a ^ p * rpowConv x ∂μ := integral_mono hLHSint hRHSint
        (fun x => hrpowBound x)
      _ = a ^ p * (∫ x : G, ‖u x‖ ^ p ∂μ) := by
        calc
          (∫ x : G, a ^ p * rpowConv x ∂μ) =
              a ^ p * ∫ x : G, rpowConv x ∂μ := by rw [integral_const_mul]
          _ = a ^ p * ∫ y : G, ∫ x : G,
              kprob y * ‖u (x-y)‖ ^ p ∂μ ∂μ := by
                congr 1
                exact integral_integral_swap hFubini
          _ = a ^ p * (∫ y : G, kprob y ∂μ) * (∫ x : G, ‖u x‖ ^ p ∂μ) := by
                have hdouble : (∫ y : G, ∫ x : G,
                    kprob y * ‖u (x-y)‖ ^ p ∂μ ∂μ) =
                    (∫ y : G, kprob y ∂μ) * (∫ x : G, ‖u x‖ ^ p ∂μ) := by
                  calc
                    _ = ∫ y : G, kprob y * (∫ x : G, ‖u x‖ ^ p ∂μ) ∂μ := by
                      apply integral_congr_ae
                      filter_upwards [] with y
                      rw [integral_const_mul, htransPow y]
                    _ = _ := integral_mul_const _ _
                rw [hdouble]
                ring
          _ = a ^ p * (∫ x : G, ‖u x‖ ^ p ∂μ) := by rw [hk_mass]; ring

end BrownianSharp

end
