import BrownianSharp.AlignmentPaperKernelTranslation
import BrownianSharp.AlignmentPaperDyadicThresholdSums
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace BrownianSharp.AlignmentPaperKernelHörmander

open BrownianSharp.AlignmentPaperKernelTranslation
open BrownianSharp.AlignmentPaperFejerPointwise
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open HaarQuarter.TrigonometricHaarExtraction

lemma characterChord_eq_two_abs_sin (x : ℝ) :
    characterChord x = 2*|Real.sin (Real.pi*x)| := by
  unfold characterChord character
  have harg : (2:ℂ)*(Real.pi:ℂ)*(((1:ℤ):ℝ):ℂ)*(x:ℂ)*Complex.I =
      Complex.I*((2*Real.pi*x:ℝ):ℂ) := by push_cast; ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2*Real.pi*x/2=Real.pi*x by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]

lemma characterChord_lower_four_abs {x : ℝ} (hx : |x| ≤ 1/2) :
    4*|x| ≤ characterChord x := by
  rw [characterChord_eq_two_abs_sin]
  have harg : |Real.pi*x| ≤ Real.pi := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos]
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi harg]
  rw [abs_mul, abs_of_pos Real.pi_pos]
  have ht : 0 ≤ Real.pi*|x| := by positivity
  have ht' : Real.pi*|x| ≤ Real.pi/2 := by nlinarith [Real.pi_pos, hx]
  have hj := Real.mul_le_sin ht ht'
  calc
    4*|x| = 2*(2/Real.pi*(Real.pi*|x|)) := by field_simp; ring
    _ ≤ 2*Real.sin (Real.pi*|x|) :=
      mul_le_mul_of_nonneg_left hj (by norm_num)

private def farKernelDifference (s : ℕ) (h x : ℝ) : ℝ :=
  if 8*Real.pi*|h| ≤ characterChord x then
    ‖smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x‖
  else 0

private theorem continuous_characterChord : Continuous characterChord := by
  unfold characterChord character
  fun_prop

private theorem circleChord_coe (x : ℝ) :
    circleCharacterChord (x:UnitAddCircle) = characterChord x := by
  unfold circleCharacterChord characterChord
  rw [show fourier (T := (1:ℝ)) 1 (x:UnitAddCircle) =
      HaarQuarter.TrigonometricHaarExtraction.character 1 x by
    simpa [HaarQuarter.TrigonometricHaarExtraction.addCircleCharacter] using
      HaarQuarter.TrigonometricHaarExtraction.addCircleCharacter_coe (1:ℤ) x]

theorem circleCharacterChord_coe (x : ℝ) :
    circleCharacterChord (x:UnitAddCircle) = characterChord x :=
  circleChord_coe x

private theorem integrableOn_farKernelDifference
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hsize : ∀ s (x : UnitAddCircle),
      ‖scalarBlockKernel smoothResolutionCutoff s x‖ ≤
        C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*circleCharacterChord x)^2))
    (s : ℕ) (h : ℝ) :
    IntegrableOn (farKernelDifference s h) (Set.Ioc (-1/2) (1/2)) volume := by
  have hq : 0 ≤ (2:ℝ)^s := by positivity
  have hcurve := smoothResolutionKernelCurve_differentiable s
  have hcont : Continuous (fun x : ℝ =>
      ‖smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x‖) := by
    exact continuous_norm.comp (Continuous.sub
      (hcurve.continuous.comp (continuous_id.add continuous_const)) hcurve.continuous)
  have hmeas : Measurable (farKernelDifference s h) := by
    apply Measurable.ite
      (measurableSet_le measurable_const continuous_characterChord.measurable)
    · exact hcont.measurable
    · exact measurable_const
  have hfinite : volume (Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    simp
  apply Measure.integrableOn_of_bounded (μ:=volume)
    (s:=Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2)) hfinite hmeas.aestronglyMeasurable
    (M:=2*C₀*(2:ℝ)^s)
  filter_upwards with x
  by_cases hfar : 8*Real.pi*|h| ≤ characterChord x
  · simp only [farKernelDifference, if_pos hfar, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    have hK : ∀ y, ‖smoothResolutionKernelCurve s y‖ ≤ C₀*(2:ℝ)^s := by
      intro y
      have hraw := hsize s (y:UnitAddCircle)
      have hcircle := circleChord_coe y
      have hden : 1 ≤ 1+(((2:ℝ)^s)*characterChord y)^2 := by
        nlinarith [sq_nonneg (((2:ℝ)^s)*characterChord y)]
      have hdenPos : 0 < 1+(((2:ℝ)^s)*characterChord y)^2 := by positivity
      have hnum : 0 ≤ C₀*(2:ℝ)^s := mul_nonneg hC₀ hq
      have hscaled : C₀*(2:ℝ)^s/
          (1+(((2:ℝ)^s)*characterChord y)^2) ≤ C₀*(2:ℝ)^s := by
        rw [div_le_iff₀ hdenPos]
        nlinarith [mul_nonneg hnum
          (sub_nonneg.mpr hden)]
      calc
        ‖smoothResolutionKernelCurve s y‖ ≤
            C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*characterChord y)^2) := by
              simpa [smoothResolutionKernelCurve, hcircle] using hraw
        _ ≤ C₀*(2:ℝ)^s := hscaled
    have hKx := hK x
    have hKY := hK (x+h)
    calc
      ‖smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x‖ ≤
          ‖smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x‖ := le_rfl
      _ ≤ ‖smoothResolutionKernelCurve s (x+h)‖+
          ‖smoothResolutionKernelCurve s x‖ := norm_sub_le _ _
      _ ≤ 2*C₀*(2:ℝ)^s := by linarith
  · simp [farKernelDifference, hfar]
    positivity

private theorem integral_inv_chord_fundamental
    (q : ℝ) (hq : 0 < q) :
    ∫ x in Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2),
      (1+(q*characterChord x)^2)⁻¹ ≤ Real.pi/(4*q) := by
  let I : Set ℝ := Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2)
  let f : ℝ → ℝ := fun x => (1+(q*characterChord x)^2)⁻¹
  let g : ℝ → ℝ := fun x => (1+(4*q*x)^2)⁻¹
  have hI : I = Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2) := rfl
  have hIfinite : volume I ≠ ⊤ := by
    rw [hI, Real.volume_Ioc]
    simp
  have hfmeas : Measurable f := by
    have hbase : Measurable (fun x : ℝ => 1+(q*characterChord x)^2) := by
      exact (continuous_const.add
        ((continuous_const.mul continuous_characterChord).pow 2)).measurable
    change Measurable (fun x : ℝ => (1+(q*characterChord x)^2)⁻¹)
    exact Measurable.inv hbase
  have hgfull : Integrable g volume := by
    dsimp [g]
    exact integrable_inv_one_add_mul_sq (by positivity : 4*q ≠ 0)
  have hfint : IntegrableOn f I volume := by
    apply Measure.integrableOn_of_bounded (μ:=volume) (s:=I) hIfinite
      hfmeas.aestronglyMeasurable (M:=1)
    filter_upwards with x
    have hden : 0 < 1+(q*characterChord x)^2 := by positivity
    have hden1 : 1 ≤ 1+(q*characterChord x)^2 := by
      nlinarith [sq_nonneg (q*characterChord x)]
    have hval : 0 ≤ (1+(q*characterChord x)^2)⁻¹ := by positivity
    have hval' : (1+(q*characterChord x)^2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hden]
      exact hden1
    have hfval : 0 ≤ f x := by simpa [f] using hval
    rw [Real.norm_eq_abs, abs_of_nonneg hfval]
    exact hval'
  have hgint : IntegrableOn g I volume := hgfull.integrableOn
  have hpoint : ∀ x ∈ I, f x ≤ g x := by
    intro x hx
    have hx' : |x| ≤ 1/2 := by
      have := hx.2
      have := hx.1
      rw [Set.mem_Ioc] at hx
      rw [abs_le]
      constructor <;> linarith
    have hch := characterChord_lower_four_abs hx'
    have hden : 1+(4*q*x)^2 ≤ 1+(q*characterChord x)^2 := by
      have hmul := mul_le_mul_of_nonneg_left hch (le_of_lt hq)
      have habs : |4*q*x| ≤ q*characterChord x := by
        have habsEq : |4*q*x| = 4*q*|x| := by
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<4),
            abs_of_pos hq]
        rw [habsEq]
        nlinarith
      have hsq : (4*q*x)^2 ≤ (q*characterChord x)^2 := by
        rw [← sq_abs (4*q*x)]
        exact (sq_le_sq₀ (abs_nonneg _)
          (mul_nonneg (le_of_lt hq) (by unfold characterChord; positivity))).2 habs
      nlinarith [hsq]
    have hpos₁ : 0 < 1+(q*characterChord x)^2 := by positivity
    have hpos₂ : 0 < 1+(4*q*x)^2 := by positivity
    dsimp [f, g]
    exact (inv_le_inv₀ hpos₁ hpos₂).2 hden
  have hmono : ∫ x in I, f x ∂volume ≤ ∫ x in I, g x ∂volume :=
    MeasureTheory.setIntegral_mono_on hfint hgint (by measurability) hpoint
  have hnonneg : 0 ≤ᵐ[volume] g := by
    filter_upwards with x
    dsimp [g]
    positivity
  have hset : ∫ x in I, g x ∂volume ≤ ∫ x, g x ∂volume :=
    MeasureTheory.setIntegral_le_integral hgfull hnonneg
  have hwhole : ∫ x, g x ∂volume = Real.pi/|4*q| := by
    dsimp [g]
    exact integral_univ_inv_one_add_mul_sq (4*q)
  calc
    ∫ x in Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2),
        (1+(q*characterChord x)^2)⁻¹
        = ∫ x in I, f x ∂volume := by simp [I, f]
    _ ≤ ∫ x in I, g x ∂volume := hmono
    _ ≤ ∫ x, g x ∂volume := hset
    _ = Real.pi/(4*q) := by rw [hwhole, abs_of_pos (by positivity : 0 < 4*q)]

private theorem integrableOn_inv_chord_fundamental
    (q : ℝ) :
    IntegrableOn (fun x : ℝ => (1+(q*characterChord x)^2)⁻¹)
      (Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2)) volume := by
  let I : Set ℝ := Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2)
  have hIfinite : volume I ≠ ⊤ := by
    dsimp [I]
    rw [Real.volume_Ioc]
    simp
  have hfmeas : Measurable (fun x : ℝ => (1+(q*characterChord x)^2)⁻¹) := by
    have hbase : Measurable (fun x : ℝ => 1+(q*characterChord x)^2) := by
      exact (continuous_const.add
        ((continuous_const.mul continuous_characterChord).pow 2)).measurable
    exact hbase.inv
  apply Measure.integrableOn_of_bounded (μ:=volume) (s:=I) hIfinite
    hfmeas.aestronglyMeasurable (M:=1)
  filter_upwards with x
  have hden : 0 < 1+(q*characterChord x)^2 := by positivity
  have hval : 0 ≤ (1+(q*characterChord x)^2)⁻¹ := by positivity
  have hval' : (1+(q*characterChord x)^2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hden]
    nlinarith [sq_nonneg (q*characterChord x)]
  rw [Real.norm_eq_abs, abs_of_nonneg hval]
  exact hval'

private theorem integral_farKernelDifference_small
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsize : ∀ s (x : UnitAddCircle),
      ‖scalarBlockKernel smoothResolutionCutoff s x‖ ≤
        C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*circleCharacterChord x)^2))
    (hderiv : ∀ s (x : ℝ),
      ‖deriv (smoothResolutionKernelCurve s) x‖ ≤
        C₁*(2:ℝ)^(2*s)/
          (1+(((2:ℝ)^s)*circleCharacterChord (x:UnitAddCircle))^2))
    (s : ℕ) (h : ℝ) :
    ∫ x in Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2), farKernelDifference s h x ∂volume ≤
      2*Real.pi*C₁*(|h|)*(2:ℝ)^s := by
  let I : Set ℝ := Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2)
  let q := (2:ℝ)^s
  have hq : 0 < q := by positivity
  have hfi : IntegrableOn (farKernelDifference s h) I volume := by
    simpa [I] using integrableOn_farKernelDifference C₀ hC₀ hsize s h
  have hgi : IntegrableOn
      (fun x : ℝ => 8*C₁*(|h|)*q^2*(1+(q*characterChord x)^2)⁻¹) I volume := by
    have hb : Integrable (fun x : ℝ => (1+(q*characterChord x)^2)⁻¹)
        (volume.restrict I) := integrableOn_inv_chord_fundamental q
    have hi : Integrable (fun x : ℝ =>
        8*C₁*(|h|)*q^2*(1+(q*characterChord x)^2)⁻¹) (volume.restrict I) := by
      convert hb.const_mul (8*C₁*(|h|)*q^2) using 1
    exact hi
  have hmono : ∫ x in I, farKernelDifference s h x ∂volume ≤
      ∫ x in I, 8*C₁*(|h|)*q^2*(1+(q*characterChord x)^2)⁻¹ ∂volume := by
    apply MeasureTheory.setIntegral_mono_on hfi hgi (by measurability)
    intro x hx
    by_cases hh : h = 0
    · simp [farKernelDifference, hh]
    · by_cases hfar : 8*Real.pi*|h| ≤ characterChord x
      · have hD : 0 < characterChord x := by
          have : 0 < 8*Real.pi*|h| := by positivity
          linarith
        have hsmall : |h| ≤ characterChord x/(8*Real.pi) := by
          apply (le_div_iff₀ (by positivity : 0 < 8*Real.pi)).2
          nlinarith [hfar]
        have hmin := smoothResolutionKernelCurve_difference_min
          C₀ C₁ hC₀ hC₁ hsize hderiv s x h hD hsmall
        have hpart := (le_min_iff.mp hmin).2
        have hfar' : Real.pi*((|h|)*8) ≤ characterChord x := by
          calc
            Real.pi*((|h|)*8) = 8*Real.pi*|h| := by ring
            _ ≤ characterChord x := hfar
        have hpart' := hpart
        have hpow : (2:ℝ)^(2*s)=((2:ℝ)^s)^2 := by
          rw [show 2*s=s*2 by omega, pow_mul]
        rw [hpow] at hpart'
        simpa [farKernelDifference, hfar, hfar', q, div_eq_mul_inv,
          mul_comm, mul_left_comm, mul_assoc] using hpart'
      · simp [farKernelDifference, hfar]
        positivity
  have hscale : ∫ x in I,
      8*C₁*(|h|)*q^2*(1+(q*characterChord x)^2)⁻¹ ∂volume =
        8*C₁*(|h|)*q^2*
          (∫ x in I, (1+(q*characterChord x)^2)⁻¹ ∂volume) := by
    rw [integral_const_mul]
  have hchint := integral_inv_chord_fundamental q hq
  have hIeq : I = Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2) := rfl
  have hbound : ∫ x in I, (1+(q*characterChord x)^2)⁻¹ ∂volume ≤ Real.pi/(4*q) := by
    simpa [I] using hchint
  calc
    ∫ x in Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2), farKernelDifference s h x ∂volume
        = ∫ x in I, farKernelDifference s h x ∂volume := by rfl
    _ ≤ ∫ x in I, 8*C₁*(|h|)*q^2*(1+(q*characterChord x)^2)⁻¹ ∂volume := hmono
    _ = 8*C₁*(|h|)*q^2*
        (∫ x in I, (1+(q*characterChord x)^2)⁻¹ ∂volume) := hscale
    _ ≤ 8*C₁*(|h|)*q^2*(Real.pi/(4*q)) := by
      gcongr
    _ = 2*Real.pi*C₁*(|h|)*q := by field_simp; ring

private theorem integrableOn_inv_sq_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (x^2)⁻¹) (Set.Ioi a) volume := by
  have h := integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) ha
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hx0 : 0 ≤ x := le_of_lt (lt_trans ha hx)
  change x^(-2:ℝ) = (x^2)⁻¹
  rw [Real.rpow_neg hx0]
  change (x^(2:ℝ))⁻¹ = (x^(2:ℕ))⁻¹
  exact congrArg Inv.inv (Real.rpow_natCast x 2)

private theorem integral_inv_sq_Ioi {a : ℝ} (ha : 0 < a) :
    ∫ x in Set.Ioi a, (x^2)⁻¹ = 1/a := by
  have h := integral_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) (c:=a) ha
  have heq : ∫ x in Set.Ioi a, (x^2)⁻¹ =
      ∫ x in Set.Ioi a, x^(-2:ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt (lt_trans ha hx)
    change (x^2)⁻¹ = x^(-2:ℝ)
    rw [Real.rpow_neg hx0]
    change (x^(2:ℕ))⁻¹ = (x^(2:ℝ))⁻¹
    exact congrArg Inv.inv (Real.rpow_natCast x 2).symm
  calc
    ∫ x in Set.Ioi a, (x^2)⁻¹
        = ∫ x in Set.Ioi a, x^(-2:ℝ) := heq
    _ = -a^((-2:ℝ)+1)/((-2:ℝ)+1) := h
    _ = 1/a := by
      rw [show (-2:ℝ)+1 = -1 by norm_num, Real.rpow_neg_one]
      field_simp

private def inverseSquareTail (a x : ℝ) : ℝ :=
  Set.indicator (Set.Ioi a) (fun y : ℝ => (y^2)⁻¹) x +
    Set.indicator (Set.Iic (-a)) (fun y : ℝ => (y^2)⁻¹) x

private theorem inverseSquareTail_nonneg (a x : ℝ) : 0 ≤ inverseSquareTail a x := by
  unfold inverseSquareTail
  exact add_nonneg
    (Set.indicator_nonneg (fun y hy => inv_nonneg.mpr (sq_nonneg y)) x)
    (Set.indicator_nonneg (fun y hy => inv_nonneg.mpr (sq_nonneg y)) x)

private theorem integrable_inverseSquareTail {a : ℝ} (ha : 0 < a) :
    Integrable (inverseSquareTail a) volume := by
  have hpos : IntegrableOn (fun x : ℝ => (x^2)⁻¹) (Set.Ioi a) volume :=
    integrableOn_inv_sq_Ioi ha
  have hneg : IntegrableOn (fun x : ℝ => (x^2)⁻¹) (Set.Iic (-a)) volume := by
    have hci : IntegrableOn (fun x : ℝ => (x^2)⁻¹) (Set.Ici a) volume :=
      integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.2 hpos
    rw [← Measure.map_neg_eq_self (volume:Measure ℝ)]
    let e : MeasurableEmbedding fun x : ℝ => -x :=
      (Homeomorph.neg ℝ).measurableEmbedding
    rw [e.integrableOn_map_iff]
    convert hci using 1 <;> ext x <;> simp [Function.comp_def, neg_sq]
  have hpos' : Integrable
      (Set.indicator (Set.Ioi a) (fun x : ℝ => (x^2)⁻¹)) volume :=
    hpos.integrable_indicator measurableSet_Ioi
  have hneg' : Integrable
      (Set.indicator (Set.Iic (-a)) (fun x : ℝ => (x^2)⁻¹)) volume :=
    hneg.integrable_indicator measurableSet_Iic
  change Integrable
    ((Set.indicator (Set.Ioi a) (fun x : ℝ => (x^2)⁻¹)) +
      Set.indicator (Set.Iic (-a)) (fun x : ℝ => (x^2)⁻¹)) volume
  exact hpos'.add hneg'

private theorem integral_inverseSquareTail {a : ℝ} (ha : 0 < a) :
    ∫ x, inverseSquareTail a x ∂volume = 2/a := by
  have hpos := integral_inv_sq_Ioi ha
  have hneg : ∫ x in Set.Iic (-a), (x^2)⁻¹ = 1/a := by
    have h := integral_comp_neg_Ioi a (fun x : ℝ => (x^2)⁻¹)
    have h' : ∫ x in Set.Ioi a, ((-x)^2)⁻¹ =
        ∫ x in Set.Ioi a, (x^2)⁻¹ := by
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro x hx
      simp [neg_sq]
    rw [h'] at h
    rw [hpos] at h
    exact h.symm
  have hposI : Integrable (Set.indicator (Set.Ioi a)
      (fun x : ℝ => (x^2)⁻¹)) volume :=
    (integrableOn_inv_sq_Ioi ha).integrable_indicator measurableSet_Ioi
  have hnegI : Integrable (Set.indicator (Set.Iic (-a))
      (fun x : ℝ => (x^2)⁻¹)) volume := by
    have hn : IntegrableOn (fun x : ℝ => (x^2)⁻¹) (Set.Iic (-a)) volume := by
      have hc : IntegrableOn (fun x : ℝ => (x^2)⁻¹) (Set.Ici a) volume :=
        integrableOn_Ici_iff_integrableOn_Ioi (by finiteness) |>.2
          (integrableOn_inv_sq_Ioi ha)
      rw [← Measure.map_neg_eq_self (volume:Measure ℝ)]
      let e : MeasurableEmbedding fun x : ℝ => -x :=
        (Homeomorph.neg ℝ).measurableEmbedding
      rw [e.integrableOn_map_iff]
      convert hc using 1 <;> ext x <;> simp
    exact hn.integrable_indicator measurableSet_Iic
  unfold inverseSquareTail
  rw [integral_add,
    integral_indicator measurableSet_Ioi,
    integral_indicator measurableSet_Iic]
  · rw [hpos, hneg]
    ring
  · exact hposI
  · exact hnegI

private theorem integral_farKernelDifference_large
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsize : ∀ s (x : UnitAddCircle),
      ‖scalarBlockKernel smoothResolutionCutoff s x‖ ≤
        C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*circleCharacterChord x)^2))
    (hderiv : ∀ s (x : ℝ),
      ‖deriv (smoothResolutionKernelCurve s) x‖ ≤
        C₁*(2:ℝ)^(2*s)/
          (1+(((2:ℝ)^s)*circleCharacterChord (x:UnitAddCircle))^2))
    (s : ℕ) (h : ℝ) (hh : h ≠ 0)
    (hlarge : 1 < (2:ℝ)^s*|h|) :
    ∫ x in Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2), farKernelDifference s h x ∂volume ≤
      3*C₀/(16*(2:ℝ)^s*|h|) := by
  let I : Set ℝ := Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2)
  let q := (2:ℝ)^s
  let a := 2*|h|
  have hq : 0 < q := by positivity
  have habs : 0 < |h| := abs_pos.mpr hh
  have ha : 0 < a := by dsimp [a]; positivity
  have hfi : IntegrableOn (farKernelDifference s h) I volume := by
    simpa [I] using integrableOn_farKernelDifference C₀ hC₀ hsize s h
  have hgi : IntegrableOn
      (fun x : ℝ => (3*C₀/(16*q))*inverseSquareTail a x) I volume := by
    have hi : Integrable (fun x : ℝ =>
        (3*C₀/(16*q))*inverseSquareTail a x) volume :=
      (integrable_inverseSquareTail ha).const_mul (3*C₀/(16*q))
    have hi' : Integrable (fun x : ℝ =>
        (3*C₀/(16*q))*inverseSquareTail a x) (volume.restrict I) :=
      hi.mono_measure (Measure.restrict_le_self)
    exact hi'
  have hmono : ∫ x in I, farKernelDifference s h x ∂volume ≤
      ∫ x in I, (3*C₀/(16*q))*inverseSquareTail a x ∂volume := by
    apply MeasureTheory.setIntegral_mono_on hfi hgi (by measurability)
    intro x hx
    by_cases hhfar : 8*Real.pi*|h| ≤ characterChord x
    · have hDpos : 0 < characterChord x := by
        have : 0 < 8*Real.pi*|h| := by positivity
        linarith
      have hsmall : |h| ≤ characterChord x/(8*Real.pi) := by
        apply (le_div_iff₀ (by positivity : 0 < 8*Real.pi)).2
        nlinarith [hhfar]
      have hmin := smoothResolutionKernelCurve_difference_min
        C₀ C₁ hC₀ hC₁ hsize hderiv s x h hDpos hsmall
      have hsizepart := (le_min_iff.mp hmin).1
      have hfund : |x| ≤ 1/2 := by
        rw [Set.mem_Ioc] at hx
        rw [abs_le]
        constructor <;> linarith
      have hchlow := characterChord_lower_four_abs hfund
      have hchhigh := characterChord_le_two_pi_abs x
      have hxlarge : a < |x| := by
        have hcmp : 8*Real.pi*|h| ≤ 2*Real.pi*|x| := by
          exact hhfar.trans hchhigh
        dsimp [a]
        nlinarith [Real.pi_pos, hcmp]
      have hxne : x ≠ 0 := by
        intro heq
        rw [heq, abs_zero] at hxlarge
        linarith
      have hdenD : (q*characterChord x)^2 ≤
          1+(q*characterChord x)^2 := by nlinarith
      have hbound₁ :
          C₀*q/(1+(q*characterChord x)^2) ≤
            C₀/(q*(characterChord x)^2) := by
        have hCq : 0 ≤ C₀*q := mul_nonneg hC₀ (le_of_lt hq)
        have hdenpos : 0 < 1+(q*characterChord x)^2 := by positivity
        have hdencomp : 0 < q*(characterChord x)^2 := by positivity
        rw [div_le_div_iff₀ hdenpos hdencomp]
        nlinarith [mul_nonneg hCq (sq_nonneg (q*characterChord x))]
      have hbound₂ :
          C₀/(q*(characterChord x)^2) ≤ C₀/(16*q*x^2) := by
        have hDsq : 16*x^2 ≤ characterChord x^2 := by
          have hs := (sq_le_sq₀ (by positivity : 0 ≤ 4*|x|)
            (by positivity : 0 ≤ characterChord x)).2 hchlow
          nlinarith [hs, sq_abs x]
        have hden : 16*q*x^2 ≤ q*characterChord x^2 :=
          calc
            16*q*x^2 = q*(16*x^2) := by ring
            _ ≤ q*characterChord x^2 := mul_le_mul_of_nonneg_left hDsq (le_of_lt hq)
        have hdenpos : 0 < 16*q*x^2 := by positivity
        have hdenpos' : 0 < q*characterChord x^2 := by positivity
        exact (div_le_div_iff₀ hdenpos' hdenpos).2 (by nlinarith [hC₀])
      have hmem : x ∈ Set.Ioi a ∨ x ∈ Set.Iic (-a) := by
        by_cases hxnonneg : 0 ≤ x
        · left
          rw [abs_of_nonneg hxnonneg] at hxlarge
          exact Set.mem_Ioi.mpr hxlarge
        · right
          have hxneg : x < 0 := lt_of_not_ge hxnonneg
          rw [abs_of_neg hxneg] at hxlarge
          exact Set.mem_Iic.mpr (by linarith)
      have htail : (x^2)⁻¹ ≤ inverseSquareTail a x := by
        rcases hmem with hp | hn
        · have hpx : a < x := hp
          have hnot : x ∉ Set.Iic (-a) := by
            rw [Set.mem_Iic]
            linarith
          simp [inverseSquareTail, hp, hnot]
        · have hnx : x ≤ -a := hn
          have hnot : x ∉ Set.Ioi a := by
            rw [Set.mem_Ioi]
            linarith
          simp [inverseSquareTail, hnot, hn]
      have hcoef : 0 ≤ 3*C₀/(16*q) := by positivity
      have hfinal :
          3*C₀*q/(1+(q*characterChord x)^2) ≤
            (3*C₀/(16*q))*inverseSquareTail a x := by
        have hscale := mul_le_mul_of_nonneg_left
          (le_trans hbound₁ hbound₂) (by positivity : (0:ℝ) ≤ 3)
        have htail' := mul_le_mul_of_nonneg_left htail hcoef
        have hx2pos : 0 < x^2 := sq_pos_of_ne_zero hxne
        have halgebra :
            (3*C₀/(16*q))*(x^2)⁻¹ = 3*C₀/(16*q*x^2) := by
          field_simp
        calc
          3*C₀*q/(1+(q*characterChord x)^2) ≤
              3*C₀/(16*q*x^2) := by
            have hb := le_trans hbound₁ hbound₂
            have hb3 := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ) ≤ 3)
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hb3
          _ = (3*C₀/(16*q))*(x^2)⁻¹ := halgebra.symm
          _ ≤ (3*C₀/(16*q))*inverseSquareTail a x := htail'
      simp only [farKernelDifference, if_pos hhfar]
      calc
        ‖smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x‖ ≤
            3*C₀*q/(1+(q*characterChord x)^2) := by simpa [q] using hsizepart
        _ ≤ (3*C₀/(16*q))*inverseSquareTail a x := hfinal
    · simp [farKernelDifference, hhfar]
      exact mul_nonneg (by positivity) (inverseSquareTail_nonneg a x)
  have hset : ∫ x in I, inverseSquareTail a x ∂volume ≤
      ∫ x, inverseSquareTail a x ∂volume :=
    MeasureTheory.setIntegral_le_integral (integrable_inverseSquareTail ha) (by
      filter_upwards with x
      unfold inverseSquareTail
      exact add_nonneg
        (Set.indicator_nonneg (fun y hy => inv_nonneg.mpr (sq_nonneg y)) x)
        (Set.indicator_nonneg (fun y hy => inv_nonneg.mpr (sq_nonneg y)) x))
  have htail := integral_inverseSquareTail ha
  have hIeq : I = Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2) := rfl
  calc
    ∫ x in Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2), farKernelDifference s h x ∂volume
        = ∫ x in I, farKernelDifference s h x ∂volume := by rfl
    _ ≤ ∫ x in I, (3*C₀/(16*q))*inverseSquareTail a x ∂volume := hmono
    _ = (3*C₀/(16*q))*∫ x in I, inverseSquareTail a x ∂volume := by
      rw [integral_const_mul]
    _ ≤ (3*C₀/(16*q))*∫ x, inverseSquareTail a x ∂volume := by gcongr
    _ = 3*C₀/(16*q)* (2/a) := by rw [htail]
    _ = 3*C₀/(16*q*|h|) := by dsimp [a]; field_simp

def farSignedKernelDifference (S : Finset ℕ) (c : ℕ → ℝ)
    (h x : ℝ) : ℝ :=
  if 8*Real.pi*|h| ≤ characterChord x then
    ‖∑ s ∈ S, c s *
      (smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x)‖
  else 0

def circleFarSignedKernelDifference (S : Finset ℕ) (c : ℕ → ℝ)
    (h : ℝ) (x : UnitAddCircle) : ℝ :=
  if 8*Real.pi*|h| ≤ circleCharacterChord x then
    ‖∑ s ∈ S, c s *
      (scalarBlockKernel smoothResolutionCutoff s (x + (h:UnitAddCircle)) -
        scalarBlockKernel smoothResolutionCutoff s x)‖
  else 0

def circleSignedKernelDifference (S : Finset ℕ) (c : ℕ → ℝ)
    (h : ℝ) (x : UnitAddCircle) : ℂ :=
  ∑ s ∈ S, c s *
    (scalarBlockKernel smoothResolutionCutoff s (x+(h:UnitAddCircle))-
      scalarBlockKernel smoothResolutionCutoff s x)

theorem circleSignedKernelDifference_continuous (S : Finset ℕ)
    (c : ℕ → ℝ) (h : ℝ) :
    Continuous (circleSignedKernelDifference S c h) := by
  classical
  unfold circleSignedKernelDifference
  fun_prop

theorem circleSignedKernelDifference_integrable
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hsize : ∀ s (x : UnitAddCircle),
      ‖scalarBlockKernel smoothResolutionCutoff s x‖ ≤
        C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*circleCharacterChord x)^2))
    (S : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ s ∈ S, |c s| ≤ 1) (h : ℝ) :
    Integrable (circleSignedKernelDifference S c h) volume := by
  classical
  let G : UnitAddCircle → ℂ := circleSignedKernelDifference S c h
  have hcont : Continuous G := circleSignedKernelDifference_continuous S c h
  have hmeas : Measurable G := hcont.measurable
  have hbound : ∀ x, ‖G x‖ ≤ ∑ s ∈ S, 2*C₀*(2:ℝ)^s := by
    intro x
    dsimp [G, circleSignedKernelDifference]
    calc
      ‖∑ s ∈ S, c s *
          (scalarBlockKernel smoothResolutionCutoff s (x+(h:UnitAddCircle))-
            scalarBlockKernel smoothResolutionCutoff s x)‖ ≤
          ∑ s ∈ S, ‖c s *
            (scalarBlockKernel smoothResolutionCutoff s (x+(h:UnitAddCircle))-
              scalarBlockKernel smoothResolutionCutoff s x)‖ := norm_sum_le _ _
      _ ≤ ∑ s ∈ S, 2*C₀*(2:ℝ)^s := by
        apply Finset.sum_le_sum
        intro s hs
        have hq : 0 ≤ (2:ℝ)^s := by positivity
        have hcoeff : |c s| ≤ 1 := hc s hs
        have hpoint : ∀ y, ‖scalarBlockKernel smoothResolutionCutoff s y‖ ≤
            C₀*(2:ℝ)^s := by
          intro y
          have hnum : 0 ≤ C₀*(2:ℝ)^s := mul_nonneg hC₀ hq
          have hden : 1 ≤ 1+(((2:ℝ)^s)*circleCharacterChord y)^2 := by nlinarith
          have hdenpos : 0 < 1+(((2:ℝ)^s)*circleCharacterChord y)^2 := by positivity
          have hscaled : C₀*(2:ℝ)^s /
              (1+(((2:ℝ)^s)*circleCharacterChord y)^2) ≤ C₀*(2:ℝ)^s := by
            rw [div_le_iff₀ hdenpos]
            nlinarith [mul_nonneg hnum (sub_nonneg.mpr hden)]
          exact (hsize s y).trans hscaled
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc
          (|c s|)*‖scalarBlockKernel smoothResolutionCutoff s
              (x+(h:UnitAddCircle))-scalarBlockKernel smoothResolutionCutoff s x‖ ≤
              ‖scalarBlockKernel smoothResolutionCutoff s
                (x+(h:UnitAddCircle))-scalarBlockKernel smoothResolutionCutoff s x‖ := by
                  simpa [one_mul] using
                    mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
          _ ≤ ‖scalarBlockKernel smoothResolutionCutoff s
              (x+(h:UnitAddCircle))‖+‖scalarBlockKernel smoothResolutionCutoff s x‖ :=
                norm_sub_le _ _
          _ ≤ 2*C₀*(2:ℝ)^s := by linarith [hpoint (x+(h:UnitAddCircle)), hpoint x]
  have hfinite : volume (Set.univ : Set UnitAddCircle) ≠ ⊤ := by finiteness
  have hI : IntegrableOn G Set.univ volume := by
    apply Measure.integrableOn_of_bounded (μ:=volume) (s:=Set.univ) hfinite
      hmeas.aestronglyMeasurable (M:=∑ s ∈ S, 2*C₀*(2:ℝ)^s)
    filter_upwards with x
    exact hbound x
  change Integrable G (volume.restrict (Set.univ : Set UnitAddCircle)) at hI
  rw [Measure.restrict_univ] at hI
  simpa [G] using hI

theorem circleFarSignedKernelDifference_nonneg (S : Finset ℕ)
    (c : ℕ → ℝ) (h : ℝ) (x : UnitAddCircle) :
    0 ≤ circleFarSignedKernelDifference S c h x := by
  unfold circleFarSignedKernelDifference
  split_ifs <;> positivity

theorem circleFarSignedKernelDifference_integrable
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hsize : ∀ s (x : UnitAddCircle),
      ‖scalarBlockKernel smoothResolutionCutoff s x‖ ≤
        C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*circleCharacterChord x)^2))
    (S : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ s ∈ S, |c s| ≤ 1) (h : ℝ) :
    Integrable (circleFarSignedKernelDifference S c h) volume := by
  classical
  let G : UnitAddCircle → ℝ := circleFarSignedKernelDifference S c h
  have hKcont : ∀ s, Continuous (scalarBlockKernel smoothResolutionCutoff s) := by
    intro s
    exact (scalarBlockKernel smoothResolutionCutoff s).continuous
  have hnorm : Continuous (fun x : UnitAddCircle => ‖∑ s ∈ S, c s *
      (scalarBlockKernel smoothResolutionCutoff s (x+(h:UnitAddCircle))-
        scalarBlockKernel smoothResolutionCutoff s x)‖) := by
    apply continuous_norm.comp
    fun_prop
  have hchord : Continuous circleCharacterChord := by
    unfold circleCharacterChord
    fun_prop
  have hcond : MeasurableSet {x : UnitAddCircle |
      8*Real.pi*|h| ≤ circleCharacterChord x} :=
    measurableSet_le measurable_const hchord.measurable
  have hGmeas : Measurable G := by
    dsimp [G, circleFarSignedKernelDifference]
    exact hnorm.measurable.ite hcond measurable_const
  have hbound : ∀ x, ‖G x‖ ≤ ∑ s ∈ S, 2*C₀*(2:ℝ)^s := by
    intro x
    by_cases hfar : 8*Real.pi*|h| ≤ circleCharacterChord x
    · simp [G, circleFarSignedKernelDifference, hfar]
      calc
        ‖∑ s ∈ S, c s *
            (scalarBlockKernel smoothResolutionCutoff s (x+(h:UnitAddCircle))-
              scalarBlockKernel smoothResolutionCutoff s x)‖ ≤
            ∑ s ∈ S, ‖c s *
              (scalarBlockKernel smoothResolutionCutoff s (x+(h:UnitAddCircle))-
                scalarBlockKernel smoothResolutionCutoff s x)‖ := norm_sum_le _ _
        _ ≤ ∑ s ∈ S, 2*C₀*(2:ℝ)^s := by
          apply Finset.sum_le_sum
          intro s hs
          have hq : 0 ≤ (2:ℝ)^s := by positivity
          have hcoeff : |c s| ≤ 1 := hc s hs
          have hpoint : ∀ y, ‖scalarBlockKernel smoothResolutionCutoff s y‖ ≤
              C₀*(2:ℝ)^s := by
            intro y
            have hnum : 0 ≤ C₀*(2:ℝ)^s := mul_nonneg hC₀ hq
            have hden : 1 ≤ 1+(((2:ℝ)^s)*circleCharacterChord y)^2 := by nlinarith
            have hdenpos : 0 < 1+(((2:ℝ)^s)*circleCharacterChord y)^2 := by positivity
            have hscaled : C₀*(2:ℝ)^s /
                (1+(((2:ℝ)^s)*circleCharacterChord y)^2) ≤ C₀*(2:ℝ)^s := by
              rw [div_le_iff₀ hdenpos]
              nlinarith [mul_nonneg hnum (sub_nonneg.mpr hden)]
            exact (hsize s y).trans hscaled
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc
            (|c s|)*‖scalarBlockKernel smoothResolutionCutoff s
                (x+(h:UnitAddCircle))-scalarBlockKernel smoothResolutionCutoff s x‖ ≤
                ‖scalarBlockKernel smoothResolutionCutoff s
                  (x+(h:UnitAddCircle))-scalarBlockKernel smoothResolutionCutoff s x‖ :=
              (by simpa [one_mul] using
                mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))
            _ ≤ ‖scalarBlockKernel smoothResolutionCutoff s
                (x+(h:UnitAddCircle))‖+‖scalarBlockKernel smoothResolutionCutoff s x‖ :=
              norm_sub_le _ _
            _ ≤ 2*C₀*(2:ℝ)^s := by linarith [hpoint (x+(h:UnitAddCircle)),hpoint x]
    · simp [G, circleFarSignedKernelDifference, hfar]
      exact Finset.sum_nonneg fun s hs =>
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC₀)
          (by positivity : 0 ≤ (2:ℝ)^s)
  have hfinite : volume (Set.univ : Set UnitAddCircle) ≠ ⊤ := by finiteness
  have hI : IntegrableOn G Set.univ volume := by
    apply Measure.integrableOn_of_bounded (μ:=volume) (s:=Set.univ) hfinite
      hGmeas.aestronglyMeasurable (M:=∑ s ∈ S, 2*C₀*(2:ℝ)^s)
    filter_upwards with x
    exact hbound x
  change Integrable G (volume.restrict (Set.univ : Set UnitAddCircle)) at hI
  rw [Measure.restrict_univ] at hI
  simpa [G] using hI

theorem circleFarSignedKernelDifference_coe (S : Finset ℕ) (c : ℕ → ℝ)
    (h x : ℝ) :
    circleFarSignedKernelDifference S c h (x:UnitAddCircle) =
      farSignedKernelDifference S c h x := by
  simp [circleFarSignedKernelDifference, farSignedKernelDifference,
    circleChord_coe, smoothResolutionKernelCurve]

theorem finite_signedKernel_integrated_hormander
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsize : ∀ s (x : UnitAddCircle),
      ‖scalarBlockKernel smoothResolutionCutoff s x‖ ≤
        C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*circleCharacterChord x)^2))
    (hderiv : ∀ s (x : ℝ),
      ‖deriv (smoothResolutionKernelCurve s) x‖ ≤
        C₁*(2:ℝ)^(2*s)/
          (1+(((2:ℝ)^s)*circleCharacterChord (x:UnitAddCircle))^2))
    (S : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ s ∈ S, |c s| ≤ 1) (h : ℝ) :
    ∫ x in Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2),
      farSignedKernelDifference S c h x ∂volume ≤ 4*Real.pi*C₁+3*C₀/8 := by
  classical
  let I : Set ℝ := Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2)
  let G : ℝ → ℝ := farSignedKernelDifference S c h
  let H : ℝ → ℝ := fun x => ∑ s ∈ S, farKernelDifference s h x
  let a : ℝ := |h|
  have hfinite : volume I ≠ ⊤ := by
    rw [show I=Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2) by rfl, Real.volume_Ioc]
    simp
  have hGmeas : Measurable G := by
    have hcurve : ∀ s, Continuous (smoothResolutionKernelCurve s) := fun s =>
      (smoothResolutionKernelCurve_differentiable s).continuous
    have hnorm : Continuous (fun x : ℝ => ‖∑ s ∈ S, c s *
        (smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x)‖) := by
      apply continuous_norm.comp
      fun_prop
    have hcond : MeasurableSet {x : ℝ | 8*Real.pi*|h| ≤ characterChord x} := by
      exact measurableSet_le measurable_const continuous_characterChord.measurable
    dsimp [G, farSignedKernelDifference]
    exact hnorm.measurable.ite hcond measurable_const
  have hboundG : ∀ x, ‖G x‖ ≤ ∑ s ∈ S, 2*C₀*(2:ℝ)^s := by
    intro x
    by_cases hfar : 8*Real.pi*|h| ≤ characterChord x
    · simp [G, farSignedKernelDifference, hfar, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
      calc
        ‖∑ s ∈ S, c s *
            (smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x)‖ ≤
            ∑ s ∈ S, ‖c s *
              (smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x)‖ :=
                norm_sum_le _ _
        _ ≤ ∑ s ∈ S, 2*C₀*(2:ℝ)^s := by
          apply Finset.sum_le_sum
          intro s hs
          have hcoeff : |c s| ≤ 1 := hc s hs
          have hq : 0 ≤ (2:ℝ)^s := by positivity
          have hK : ∀ y, ‖smoothResolutionKernelCurve s y‖ ≤ C₀*(2:ℝ)^s := by
            intro y
            have hr := hsize s (y:UnitAddCircle)
            have hcirc := circleChord_coe y
            have hden : 1 ≤ 1+(((2:ℝ)^s)*characterChord y)^2 := by nlinarith
            have hnum : 0 ≤ C₀*(2:ℝ)^s := mul_nonneg hC₀ hq
            have hscaled : C₀*(2:ℝ)^s /
                (1+(((2:ℝ)^s)*characterChord y)^2) ≤ C₀*(2:ℝ)^s := by
              rw [div_le_iff₀ (by positivity)]
              nlinarith [mul_nonneg hnum (sub_nonneg.mpr hden)]
            calc
              ‖smoothResolutionKernelCurve s y‖ ≤
                  C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*characterChord y)^2) := by
                    simpa [smoothResolutionKernelCurve, hcirc] using hr
              _ ≤ C₀*(2:ℝ)^s := hscaled
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          calc
            (|c s|)*‖smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x‖ ≤
                ‖smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x‖ :=
                  (by simpa [one_mul] using
                    mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _))
            _ ≤ ‖smoothResolutionKernelCurve s (x+h)‖+
                ‖smoothResolutionKernelCurve s x‖ := norm_sub_le _ _
            _ ≤ 2*C₀*(2:ℝ)^s := by linarith [hK (x+h), hK x]
    · simp [G, farSignedKernelDifference, hfar]
      exact Finset.sum_nonneg fun s hs =>
        mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC₀) (by positivity)
  have hGint : IntegrableOn G I volume := by
    apply Measure.integrableOn_of_bounded (μ:=volume) (s:=I) hfinite
      hGmeas.aestronglyMeasurable
      (M:=∑ s ∈ S, 2*C₀*(2:ℝ)^s)
    filter_upwards with x
    exact hboundG x
  have hHint : IntegrableOn H I volume := by
    apply integrable_finset_sum
    intro s hs
    exact integrableOn_farKernelDifference C₀ hC₀ hsize s h
  have hpoint : ∀ x ∈ I, G x ≤ H x := by
    intro x hx
    by_cases hfar : 8*Real.pi*|h| ≤ characterChord x
    · simp [G, H, farSignedKernelDifference, farKernelDifference, hfar]
      calc
        ‖∑ s ∈ S, c s *
            (smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x)‖ ≤
            ∑ s ∈ S, ‖c s *
              (smoothResolutionKernelCurve s (x+h)-smoothResolutionKernelCurve s x)‖ :=
                norm_sum_le _ _
        _ ≤ ∑ s ∈ S, ‖smoothResolutionKernelCurve s (x+h)-
              smoothResolutionKernelCurve s x‖ := by
          apply Finset.sum_le_sum
          intro s hs
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_of_le_one_left (norm_nonneg _) (hc s hs)
    · simp [G, H, farSignedKernelDifference, farKernelDifference, hfar]
  have hmono : ∫ x in I, G x ∂volume ≤ ∫ x in I, H x ∂volume :=
    MeasureTheory.setIntegral_mono_on hGint hHint (by measurability) hpoint
  have hsum : ∫ x in I, H x ∂volume =
      ∑ s ∈ S, ∫ x in I, farKernelDifference s h x ∂volume := by
    change ∫ x, (∑ s ∈ S, farKernelDifference s h x) ∂(volume.restrict I) = _
    rw [integral_finset_sum]
    · intro s hs
      exact integrableOn_farKernelDifference C₀ hC₀ hsize s h
  have hterm : ∀ s ∈ S,
      ∫ x in I, farKernelDifference s h x ∂volume ≤
        if (a*(2:ℝ)^s ≤ 1) then 2*Real.pi*C₁*a*(2:ℝ)^s
        else 3*C₀/(16*(2:ℝ)^s*a) := by
    intro s hs
    by_cases hlow : a*(2:ℝ)^s ≤ 1
    · simpa [I, hlow, a, mul_comm] using integral_farKernelDifference_small C₀ C₁ hC₀ hC₁
        hsize hderiv s h
    · have hh : h ≠ 0 := by
        intro heq
        subst h
        simp [a] at hlow
      have hlarge' : 1 < a*(2:ℝ)^s := lt_of_not_ge hlow
      have hlarge : 1 < (2:ℝ)^s*|h| := by simpa [a, mul_comm] using hlarge'
      simpa [I, hlow, a, mul_comm] using integral_farKernelDifference_large C₀ C₁
        hC₀ hC₁ hsize hderiv s h hh hlarge
  have hsumBound : (∑ s ∈ S,
      if (a*(2:ℝ)^s ≤ 1) then 2*Real.pi*C₁*a*(2:ℝ)^s
      else 3*C₀/(16*(2:ℝ)^s*a)) ≤ 4*Real.pi*C₁+3*C₀/8 := by
    by_cases hh : h = 0
    · subst h
      simp [a]
      positivity
    · have ha : 0 < |h| := abs_pos.mpr hh
      let L := S.filter (fun s => a*(2:ℝ)^s ≤ 1)
      let U := S.filter (fun s => 1 < a*(2:ℝ)^s)
      have hpartition : S = L ∪ U := by
        ext s
        simp only [Finset.mem_union, Finset.mem_filter, L, U]
        constructor
        · intro hs
          by_cases hle : a*(2:ℝ)^s ≤ 1
          · exact Or.inl ⟨hs, hle⟩
          · exact Or.inr ⟨hs, lt_of_not_ge hle⟩
        · rintro (⟨hs, hle⟩ | ⟨hs, hgt⟩) <;> exact hs
      have hdisj : Disjoint L U := by
        rw [Finset.disjoint_left]
        intro s hsL hsU
        have hle := (Finset.mem_filter.mp hsL).2
        have hgt := (Finset.mem_filter.mp hsU).2
        linarith
      have hsumParts : (∑ s ∈ S,
          if (a*(2:ℝ)^s ≤ 1) then 2*Real.pi*C₁*a*(2:ℝ)^s
          else 3*C₀/(16*(2:ℝ)^s*a)) =
          (∑ s ∈ L, 2*Real.pi*C₁*a*(2:ℝ)^s)+
          (∑ s ∈ U, 3*C₀/(16*(2:ℝ)^s*a)) := by
        rw [hpartition, Finset.sum_union hdisj]
        congr 1
        · apply Finset.sum_congr rfl
          intro s hs
          simp [L, (Finset.mem_filter.mp hs).2]
        · apply Finset.sum_congr rfl
          intro s hs
          have hgt : 1 < a*(2:ℝ)^s := (Finset.mem_filter.mp hs).2
          simp [U, hgt, not_le_of_gt hgt]
      have hlowSum : (∑ s ∈ L, 2*Real.pi*C₁*a*(2:ℝ)^s) ≤ 4*Real.pi*C₁ := by
        rw [show (∑ s ∈ L, 2*Real.pi*C₁*a*(2:ℝ)^s) =
            (2*Real.pi*C₁)*∑ s ∈ L, a*(2:ℝ)^s by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s hs; ring]
        have ht := BrownianSharp.AlignmentPaperDyadicThresholdSums.low_dyadic_threshold_sum_le_two S ha
        have ht' : (∑ s ∈ L, a*(2:ℝ)^s) ≤ 2 := by simpa [L] using ht
        nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2)
          (mul_nonneg Real.pi_pos.le hC₁)) (le_of_lt ha)]
      have hhighSum : (∑ s ∈ U, 3*C₀/(16*(2:ℝ)^s*a)) ≤ 3*C₀/8 := by
        rw [show (∑ s ∈ U, 3*C₀/(16*(2:ℝ)^s*a)) =
            (3*C₀/16)*∑ s ∈ U, (a*(2:ℝ)^s)⁻¹ by
              rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s hs; field_simp]
        have ht := BrownianSharp.AlignmentPaperDyadicThresholdSums.high_dyadic_threshold_sum_le_two S ha
        have ht' : (∑ s ∈ U, (a*(2:ℝ)^s)⁻¹) ≤ 2 := by simpa [U] using ht
        have hc : 0 ≤ 3*C₀/16 := by positivity
        calc
          (3*C₀/16)*∑ s ∈ U, (a*(2:ℝ)^s)⁻¹ ≤ (3*C₀/16)*2 :=
            mul_le_mul_of_nonneg_left ht' hc
          _ = 3*C₀/8 := by ring
      rw [hsumParts]
      linarith
  calc
    ∫ x in Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2),
        farSignedKernelDifference S c h x ∂volume = ∫ x in I, G x ∂volume := by rfl
    _ ≤ ∫ x in I, H x ∂volume := hmono
    _ = ∑ s ∈ S, ∫ x in I, farKernelDifference s h x ∂volume := hsum
    _ ≤ ∑ s ∈ S, (if (a*(2:ℝ)^s ≤ 1) then
          2*Real.pi*C₁*a*(2:ℝ)^s else
          3*C₀/(16*(2:ℝ)^s*a)) := by
      apply Finset.sum_le_sum
      intro s hs
      simpa [a] using hterm s hs
    _ ≤ 4*Real.pi*C₁+3*C₀/8 := hsumBound

theorem finite_signedKernel_circle_integrated_hormander
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsize : ∀ s (x : UnitAddCircle),
      ‖scalarBlockKernel smoothResolutionCutoff s x‖ ≤
        C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*circleCharacterChord x)^2))
    (hderiv : ∀ s (x : ℝ),
      ‖deriv (smoothResolutionKernelCurve s) x‖ ≤
        C₁*(2:ℝ)^(2*s)/
          (1+(((2:ℝ)^s)*circleCharacterChord (x:UnitAddCircle))^2))
    (S : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ s ∈ S, |c s| ≤ 1) (h : ℝ) :
    ∫ x : UnitAddCircle, circleFarSignedKernelDifference S c h x ∂volume ≤
      4*Real.pi*C₁+3*C₀/8 := by
  rw [← UnitAddCircle.integral_preimage (-(1:ℝ)/2)
    (circleFarSignedKernelDifference S c h)]
  norm_num
  have hIoc := finite_signedKernel_integrated_hormander
    C₀ C₁ hC₀ hC₁ hsize hderiv S c hc h
  have heq : (∫ x in Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2),
      circleFarSignedKernelDifference S c h (x:UnitAddCircle) ∂volume) =
      ∫ x in Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2),
        farSignedKernelDifference S c h x ∂volume := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    exact circleFarSignedKernelDifference_coe S c h x
  calc
    ∫ a in Set.Ioc (-(1/2:ℝ)) (1/2:ℝ),
        circleFarSignedKernelDifference S c h (a:UnitAddCircle) ∂volume =
      ∫ x in Set.Ioc (-(1:ℝ)/2) ((1:ℝ)/2),
        farSignedKernelDifference S c h x ∂volume := by
          convert heq using 1 <;> norm_num
    _ ≤ 4*Real.pi*C₁+3*C₀/8 := hIoc

theorem finite_signedKernel_circle_norm_integral_le
    (C₀ C₁ : ℝ) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hsize : ∀ s (x : UnitAddCircle),
      ‖scalarBlockKernel smoothResolutionCutoff s x‖ ≤
        C₀*(2:ℝ)^s/(1+(((2:ℝ)^s)*circleCharacterChord x)^2))
    (hderiv : ∀ s (x : ℝ),
      ‖deriv (smoothResolutionKernelCurve s) x‖ ≤
        C₁*(2:ℝ)^(2*s)/
          (1+(((2:ℝ)^s)*circleCharacterChord (x:UnitAddCircle))^2))
    (S : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ s ∈ S, |c s| ≤ 1) (h : ℝ) :
    Integrable (circleFarSignedKernelDifference S c h) volume ∧
      ∫ x : UnitAddCircle, ‖circleFarSignedKernelDifference S c h x‖ ∂volume ≤
        4*Real.pi*C₁+3*C₀/8 := by
  refine ⟨circleFarSignedKernelDifference_integrable C₀ hC₀ hsize S c hc h, ?_⟩
  have hnorm : ∀ x : UnitAddCircle,
      ‖circleFarSignedKernelDifference S c h x‖ =
        circleFarSignedKernelDifference S c h x := by
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg
      (circleFarSignedKernelDifference_nonneg S c h x)]
  calc
    ∫ x : UnitAddCircle, ‖circleFarSignedKernelDifference S c h x‖ ∂volume =
        ∫ x, circleFarSignedKernelDifference S c h x ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      exact hnorm x
    _ ≤ 4*Real.pi*C₁+3*C₀/8 :=
      finite_signedKernel_circle_integrated_hormander C₀ C₁ hC₀ hC₁
        hsize hderiv S c hc h

theorem exists_smoothResolution_signedKernel_circle_norm_integral_and_integrable :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (S : Finset ℕ) (c : ℕ → ℝ),
      (∀ s ∈ S, |c s| ≤ 1) → ∀ h : ℝ,
      Integrable (circleFarSignedKernelDifference S c h) volume ∧
      ∫ x : UnitAddCircle, ‖circleFarSignedKernelDifference S c h x‖ ∂volume ≤ C := by
  obtain ⟨C₀, hC₀, hsize⟩ :=
    BrownianSharp.AlignmentPaperSmoothKernelDecay.exists_smoothResolution_scalarKernel_chord_decay
  obtain ⟨C₁, hC₁, hderiv⟩ :=
    BrownianSharp.AlignmentPaperSmoothKernelDerivative.exists_smoothResolution_scalarKernel_deriv_chord_decay
  have hderiv' : ∀ s (x : ℝ),
      ‖deriv (smoothResolutionKernelCurve s) x‖ ≤
        C₁*(2:ℝ)^(2*s)/
          (1+(((2:ℝ)^s)*circleCharacterChord (x:UnitAddCircle))^2) := by
    intro s x
    change ‖deriv (fun y : ℝ =>
      scalarBlockKernel smoothResolutionCutoff s (y:UnitAddCircle)) x‖ ≤ _
    exact hderiv s x
  refine ⟨4*Real.pi*C₁+3*C₀/8, by positivity, ?_⟩
  intro S c hc h
  exact finite_signedKernel_circle_norm_integral_le C₀ C₁ hC₀ hC₁
    hsize hderiv' S c hc h

end BrownianSharp.AlignmentPaperKernelHörmander
