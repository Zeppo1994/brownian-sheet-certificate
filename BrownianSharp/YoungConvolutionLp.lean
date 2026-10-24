import BrownianSharp.YoungLp
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic

/-! The positive-kernel part of Young's inequality on the unit circle. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp

/-- Convolution by a nonnegative, unit-mass continuous kernel contracts every
finite real `Lᵖ` moment with `p ≥ 1`. -/
theorem addCircle_positive_convolution_rpow_le
    (K u : C(UnitAddCircle, ℝ)) (hK : ∀ x, 0 ≤ K x)
    (hKmass : (∫ x, K x ∂AddCircle.haarAddCircle) = 1)
    (p : ℝ) (hp : 1 ≤ p) :
    (∫ x, |∫ y, K y * u (x - y) ∂AddCircle.haarAddCircle| ^ p
        ∂AddCircle.haarAddCircle) ≤
      ∫ x, |u x| ^ p ∂AddCircle.haarAddCircle := by
  classical
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  let ν : Measure UnitAddCircle := μ.withDensity (fun y => ENNReal.ofReal (K y))
  have hKmeas : Measurable K := K.continuous.measurable
  have hKsup : ∀ y, ‖K y‖ ≤ ‖K‖ := (K.norm_le (norm_nonneg _)).mp le_rfl
  have hKint : Integrable K μ := by
    apply Integrable.of_bound K.continuous.aestronglyMeasurable ‖K‖
    filter_upwards [] with y
    exact hKsup y
  have hνprob : ν Set.univ = 1 := by
    change (μ.withDensity (fun y => ENNReal.ofReal (K y))) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ]
    simp only [setLIntegral_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hKint (ae_of_all _ hK), hKmass]
    norm_num
  letI : IsProbabilityMeasure ν := ⟨hνprob⟩
  let B : ℝ := ‖u‖
  have hBnonneg : 0 ≤ B := norm_nonneg _
  have hBu : ∀ x, ‖u x‖ ≤ B := (u.norm_le hBnonneg).mp le_rfl
  have hpowcont : Continuous fun x : UnitAddCircle => |u x| ^ p := by
    exact (Real.continuous_rpow_const (le_trans (by norm_num) hp)).comp
      (continuous_abs.comp u.continuous)
  have hpowbound : ∀ x, |u x| ^ p ≤ B ^ p := by
    intro x
    have hb : |u x| ≤ B := by simpa [Real.norm_eq_abs] using hBu x
    exact Real.rpow_le_rpow (abs_nonneg _) hb (le_trans (by norm_num) hp)
  have hνint_u (f : UnitAddCircle → ℝ) (hfcont : Continuous f)
      (hfbound : ∀ x, ‖f x‖ ≤ B) : Integrable f ν := by
    apply Integrable.of_bound hfcont.aestronglyMeasurable B
    filter_upwards [] with x
    exact hfbound x
  have hνint_abs (f : UnitAddCircle → ℝ) (hfcont : Continuous f)
      (hfbound : ∀ x, |f x| ≤ B) : Integrable (fun x => |f x|) ν := by
    apply Integrable.of_bound (continuous_abs.comp hfcont).aestronglyMeasurable B
    filter_upwards [] with x
    simpa [Real.norm_eq_abs] using hfbound x
  have hνint_pow (f : UnitAddCircle → ℝ) (hfcont : Continuous f)
      (hfbound : ∀ x, |f x| ^ p ≤ B ^ p) :
      Integrable (fun x => |f x| ^ p) ν := by
    apply Integrable.of_bound
      ((Real.continuous_rpow_const (le_trans (by norm_num) hp)).comp
        (continuous_abs.comp hfcont)).aestronglyMeasurable (B ^ p)
    filter_upwards [] with x
    change |(|f x| ^ p)| ≤ B ^ p
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hfbound x
  have hsubx (x : UnitAddCircle) : Continuous (fun y : UnitAddCircle => x-y) :=
    continuous_const.sub continuous_id
  have hsection (x : UnitAddCircle) :
      |∫ y, K y * u (x - y) ∂μ| ^ p ≤ ∫ y, K y * |u (x - y)| ^ p ∂μ := by
    apply weighted_integral_rpow_le μ K hKmeas hK hKint hKmass
      (fun y => u (x - y)) p hp
    · exact hνint_u _ (u.continuous.comp (hsubx x)) (fun y => by
        simpa [Real.norm_eq_abs] using (hBu (x-y)))
    · exact hνint_abs _ (u.continuous.comp (hsubx x)) (fun y => by
        simpa using (show |u (x-y)| ≤ B by
          simpa [Real.norm_eq_abs] using hBu (x-y)))
    · exact hνint_pow _ (u.continuous.comp (hsubx x)) (fun y => by
        exact hpowbound (x-y))
  let BK : ℝ := ‖K‖
  have hBKnonneg : 0 ≤ BK := norm_nonneg _
  have hKbound : ∀ y, |K y| ≤ BK := fun y => by
    simpa [Real.norm_eq_abs, BK] using hKsup y
  have hFubini : Integrable (fun z : UnitAddCircle × UnitAddCircle =>
      K z.2 * |u (z.1 - z.2)| ^ p) (μ.prod μ) := by
    apply Integrable.of_bound
      ((K.continuous.comp continuous_snd).mul
        (hpowcont.comp (continuous_fst.sub continuous_snd))).aestronglyMeasurable
      (BK * B ^ p)
    filter_upwards [] with z
    change ‖K z.2 * |u (z.1-z.2)| ^ p‖ ≤ _
    rw [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    calc
      |K z.2| * |u (z.1-z.2)| ^ p ≤ BK * |u (z.1-z.2)| ^ p :=
        mul_le_mul_of_nonneg_right (hKbound z.2) (Real.rpow_nonneg (abs_nonneg _) _)
      _ ≤ BK * B ^ p := mul_le_mul_of_nonneg_left (hpowbound (z.1-z.2)) hBKnonneg
  have hJointSM : StronglyMeasurable (fun z : UnitAddCircle × UnitAddCircle =>
      K z.2 * u (z.1-z.2)) :=
    ((K.continuous.comp continuous_snd).mul
      (u.continuous.comp (continuous_fst.sub continuous_snd))).stronglyMeasurable
  have hconvSM : StronglyMeasurable (fun x : UnitAddCircle =>
      ∫ y, K y * u (x-y) ∂μ) := hJointSM.integral_prod_right
  have hconvMeas : Measurable (fun x : UnitAddCircle =>
      ∫ y, K y * u (x-y) ∂μ) := hconvSM.measurable
  have hLHSint : Integrable (fun x : UnitAddCircle =>
      |∫ y, K y * u (x-y) ∂μ| ^ p) μ := by
    apply Integrable.of_bound
      ((Real.continuous_rpow_const (le_trans (by norm_num) hp)).measurable.comp
        (continuous_abs.measurable.comp hconvMeas)).aestronglyMeasurable (B ^ p)
    filter_upwards [] with x
    -- The bound follows from the probability-weighted Jensen inequality and `hpowbound`.
    have h := hsection x
    have hrhs : ∫ y, K y * |u (x-y)| ^ p ∂μ ≤ B ^ p := by
      calc
        _ ≤ ∫ y, K y * B ^ p ∂μ := by
          have hinnerCont : Continuous (fun y : UnitAddCircle =>
              K y * |u (x-y)| ^ p) := K.continuous.mul
                (hpowcont.comp (hsubx x))
          have hinnerInt : Integrable (fun y : UnitAddCircle =>
              K y * |u (x-y)| ^ p) μ := by
            apply Integrable.of_bound hinnerCont.aestronglyMeasurable (BK * B ^ p)
            filter_upwards [] with y
            rw [Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
            calc
              |K y| * |u (x-y)| ^ p ≤ BK * |u (x-y)| ^ p :=
                mul_le_mul_of_nonneg_right (hKbound y)
                  (Real.rpow_nonneg (abs_nonneg _) _)
              _ ≤ BK * B ^ p := mul_le_mul_of_nonneg_left (hpowbound (x-y)) hBKnonneg
          have hupperInt : Integrable (fun y : UnitAddCircle => K y * B ^ p) μ :=
            Integrable.mul_const hKint (B ^ p)
          apply integral_mono hinnerInt hupperInt
          intro y
          exact mul_le_mul_of_nonneg_left (hpowbound (x-y)) (hK y)
        _ = B ^ p := by rw [integral_mul_const, hKmass, one_mul]
    have : |∫ y, K y * u (x-y) ∂μ| ^ p ≤ B ^ p := h.trans hrhs
    change |(|∫ y, K y * u (x-y) ∂μ| ^ p)| ≤ B ^ p
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact this
  have hRHSint : Integrable (fun x : UnitAddCircle => |u x| ^ p) μ := by
    apply Integrable.of_bound hpowcont.aestronglyMeasurable (B ^ p)
    filter_upwards [] with x
    change |(|u x| ^ p)| ≤ B ^ p
    rw [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hpowbound x
  have htrans (y : UnitAddCircle) :
      (∫ x : UnitAddCircle, |u (x-y)| ^ p ∂μ) = ∫ x, |u x| ^ p ∂μ := by
    letI : Measure.IsAddLeftInvariant μ := inferInstance
    have hmp := measurePreserving_add_left μ (-y)
    calc
      (∫ x, |u (x-y)| ^ p ∂μ) = ∫ x, |u ((-y)+x)| ^ p ∂μ := by
        congr 1
        funext x
        congr 2
        abel
      _ = ∫ x, |u x| ^ p ∂μ :=
        hmp.integral_comp (Homeomorph.addLeft (-y)).measurableEmbedding
          (fun x => |u x| ^ p)
  calc
    (∫ x, |∫ y, K y * u (x-y) ∂μ| ^ p ∂μ)
        ≤ ∫ x, (∫ y, K y * |u (x-y)| ^ p ∂μ) ∂μ := by
          exact integral_mono hLHSint hFubini.integral_prod_left hsection
    _ = ∫ y, (∫ x, K y * |u (x-y)| ^ p ∂μ) ∂μ :=
          integral_integral_swap hFubini
    _ = ∫ y, K y * (∫ x, |u (x-y)| ^ p ∂μ) ∂μ := by
          congr 1; funext y; rw [integral_const_mul]
    _ = ∫ y, K y * (∫ x, |u x| ^ p ∂μ) ∂μ := by
          congr 1; funext y; rw [htrans y]
    _ = ∫ x, |u x| ^ p ∂μ := by
          calc
            _ = (∫ y, K y ∂μ) * (∫ x, |u x| ^ p ∂μ) :=
              integral_mul_const (∫ x, |u x| ^ p ∂μ) K
            _ = ∫ x, |u x| ^ p ∂μ := by rw [hKmass, one_mul]

end BrownianSharp
