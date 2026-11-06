import BrownianSharp.AlignmentPaperAnchoredLpSourceFourier
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section
open MeasureTheory
open intervalIntegral

namespace BrownianSharp.AlignmentPaperAnchoredLpScalarKernelFormula

open BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
open BrownianSharp.AlignmentPaperAnchoredLpSourceFourier
open BrownianSharp.AlignmentPaperAnchoredLpReflection
open BrownianSharp.AlignmentPaperAnchoredLpReflectionTensor
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLp
open HaarQuarter

/-- The exact nonzero scalar frequency factor, expressed through the endpoint
values of the exponential primitive. -/
theorem anchoredScalarFourierKernel_nonzero_formula (n : ℤ) (v : ℝ)
    (hn : n ≠ 0) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    anchoredScalarFourierKernel n v =
      (Complex.exp ((-2 * Real.pi * Complex.I * n) * (1-v/2)) -
        Complex.exp ((-2 * Real.pi * Complex.I * n) * (v/2))) /
          (-2 * Real.pi * Complex.I * n) := by
  let a : ℝ := v/2
  let b : ℝ := 1-v/2
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hfold (t : ℝ) (ht : t ∈ Set.Ioc (0:ℝ) 1) :
      triangleWave ((t:ℝ):UnitAddCircle) = foldUnitInterval (2*t) := by
    by_cases ht1 : t = 1
    · subst t
      simp [triangleWave_eq_fold_representative, circleIcoRepresentative,
        foldUnitInterval]
    · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
      have hrep : t ∈ Set.Ico (0:ℝ) (0+1) := by
        constructor
        · exact le_of_lt ht.1
        · simpa using htlt
      rw [triangleWave, AddCircle.liftIco_coe_apply hrep]
  have hcond (t : ℝ) :
      v < foldUnitInterval (2*t) ↔ a < t ∧ t < b := by
    rw [foldUnitInterval, lt_min_iff]
    constructor
    · intro h
      constructor <;> dsimp [a, b] <;> nlinarith
    · rintro ⟨h₁, h₂⟩
      constructor <;> dsimp [a, b] at * <;> nlinarith
  have hchar : -2 * Real.pi * Complex.I * n ≠ 0 := by
    apply mul_ne_zero
    · apply mul_ne_zero
      · apply mul_ne_zero <;> norm_num
      · exact Complex.I_ne_zero
    · exact_mod_cast hn
  calc
    anchoredScalarFourierKernel n v =
        ∫ t in Set.Ioc (0:ℝ) 1,
          fourier (-n) ((t:ℝ):UnitAddCircle) *
            (if v < triangleWave ((t:ℝ):UnitAddCircle) then (1:ℂ) else 0)
          ∂volume := by
            unfold anchoredScalarFourierKernel
            simpa only [zero_add] using
              (UnitAddCircle.integral_preimage 0
                (fun x : UnitAddCircle => fourier (-n) x *
                  (if v < triangleWave x then (1:ℂ) else 0))).symm
    _ = ∫ t in Set.Ioc (0:ℝ) 1,
          if a < t ∧ t < b then
            Complex.exp ((-2 * Real.pi * Complex.I * n) * t) else 0 ∂volume := by
          apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
          filter_upwards [] with t
          intro ht
          rw [hfold t ht]
          simp only [hcond t]
          rw [fourier_coe_apply]
          by_cases h : a < t ∧ t < b
          · simp [h]
          · simp [h]
    _ = ∫ t in Set.Ioc (0:ℝ) 1,
          Set.indicator (Set.Ioo a b)
            (fun t => Complex.exp ((-2 * Real.pi * Complex.I * n) * t)) t ∂volume := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          rw [Set.indicator_apply]
          simp only [Set.mem_Ioo]
    _ = ∫ t in Set.Ioo a b,
          Complex.exp ((-2 * Real.pi * Complex.I * n) * t) ∂volume := by
          rw [MeasureTheory.setIntegral_indicator measurableSet_Ioo]
          have hset : Set.Ioc (0:ℝ) 1 ∩ Set.Ioo a b = Set.Ioo a b := by
            ext t
            simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ioo]
            constructor
            · rintro ⟨_, ht⟩
              exact ht
            · intro ht
              refine ⟨?_, ht⟩
              change v/2 < t ∧ t < 1-v/2 at ht
              constructor <;> linarith [hv0, ht.1, ht.2]
          rw [hset]
    _ = ∫ t in a..b,
          Complex.exp ((-2 * Real.pi * Complex.I * n) * t) := by
          rw [intervalIntegral.integral_of_le hab]
          exact (integral_Ioc_eq_integral_Ioo).symm
    _ = (Complex.exp ((-2 * Real.pi * Complex.I * n) * b) -
          Complex.exp ((-2 * Real.pi * Complex.I * n) * a)) /
          (-2 * Real.pi * Complex.I * n) := by
          rw [integral_exp_mul_complex hchar]
    _ = _ := by simp [a, b]

/-- Reflection sign in one torus coordinate, read from the two halves of its
unit representative. -/
def anchoredFaceSignCoordinate (x : UnitAddTorus (Fin d)) (i : Fin d) : ℝ :=
  if circleIocRepresentative (x i) ≤ 1/2 then 1 else -1

def anchoredFaceSource {d : ℕ} (J : Finset (Fin d))
    (g : (Fin d → ℝ) → ℝ) (x : UnitAddTorus (Fin d)) : ℝ :=
  (2:ℝ)^J.card * (∏ i ∈ J, anchoredFaceSignCoordinate x i) *
    (g (fun i => triangleWave (x i)) *
      ∏ i ∈ Finset.univ \ J, (1 - triangleWave (x i)))

theorem measurable_anchoredFaceSignCoordinate {d : ℕ} (i : Fin d) :
    Measurable (fun x : UnitAddTorus (Fin d) => anchoredFaceSignCoordinate x i) := by
  unfold anchoredFaceSignCoordinate
  apply Measurable.ite
  · exact measurableSet_le
      (measurable_circleIocRepresentative.comp (measurable_pi_apply i)) measurable_const
  · exact measurable_const
  · exact measurable_const

theorem measurable_anchoredFaceWeight {d : ℕ} (J : Finset (Fin d)) :
    Measurable (fun x : UnitAddTorus (Fin d) =>
      ∏ i ∈ Finset.univ \ J, (1 - triangleWave (x i))) := by
  classical
  apply Finset.measurable_prod
  intro i hi
  exact measurable_const.sub
    (continuous_triangleWave.measurable.comp (measurable_pi_apply i))

theorem anchoredFaceSignCoordinate_norm {d : ℕ}
    (x : UnitAddTorus (Fin d)) (i : Fin d) :
    ‖anchoredFaceSignCoordinate x i‖ = 1 := by
  unfold anchoredFaceSignCoordinate
  split_ifs <;> norm_num

theorem anchoredFaceWeight_bounds {d : ℕ} (J : Finset (Fin d))
    (x : UnitAddTorus (Fin d)) :
    0 ≤ (∏ i ∈ Finset.univ \ J, (1 - triangleWave (x i))) ∧
      (∏ i ∈ Finset.univ \ J, (1 - triangleWave (x i))) ≤ 1 := by
  constructor
  · apply Finset.prod_nonneg
    intro i hi
    exact sub_nonneg.mpr (triangleWave_mem_Icc (x i)).2
  · apply Finset.prod_le_one₀
    · intro i hi
      exact sub_nonneg.mpr (triangleWave_mem_Icc (x i)).2
    · intro i hi
      exact sub_le_self 1 (triangleWave_mem_Icc (x i)).1

/-- The parity-twisted periodic source for a frequency face. Its Lp cost is
only the active-coordinate factor `2^|J|`; zero coordinates are controlled
by the bounded lower-face weight. -/
theorem anchoredFaceSource_eLpNorm_le {d : ℕ} {p : ℝ}
    (J : Finset (Fin d))
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    eLpNorm (anchoredFaceSource J (g : (Fin d → ℝ) → ℝ))
        (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) ≤
      ENNReal.ofReal ((2:ℝ)^J.card) *
        eLpNorm (g : (Fin d → ℝ) → ℝ) (ENNReal.ofReal p) (cubeMeasure d) := by
  let fold : UnitAddTorus (Fin d) → (Fin d → ℝ) :=
    fun x i => triangleWave (x i)
  let sign : UnitAddTorus (Fin d) → ℝ := fun x =>
    ∏ i ∈ J, anchoredFaceSignCoordinate x i
  let wt : UnitAddTorus (Fin d) → ℝ := fun x =>
    ∏ i ∈ Finset.univ \ J, (1 - triangleWave (x i))
  let c : ℝ := (2:ℝ)^J.card
  have hfold : MeasurePreserving fold (volume : Measure (UnitAddTorus (Fin d)))
      (cubeMeasure d) := by
    simpa [fold, cubeMeasure, AlignmentFractionalTensor.unitCube_measure_eq_pi,
      unitIntervalMeasure] using measurePreserving_foldCoordinates d
  have hsignMeas : Measurable sign := by
    classical
    dsimp [sign]
    apply Finset.measurable_prod
    intro i hi
    exact measurable_anchoredFaceSignCoordinate i
  have hwtMeas : Measurable wt := by
    simpa [wt] using measurable_anchoredFaceWeight J
  have hgComp : AEStronglyMeasurable
      ((g : (Fin d → ℝ) → ℝ) ∘ fold) (volume : Measure (UnitAddTorus (Fin d))) :=
    (Lp.stronglyMeasurable g).aestronglyMeasurable.comp_measurePreserving hfold
  have hsm : AEStronglyMeasurable
      (anchoredFaceSource J (g : (Fin d → ℝ) → ℝ))
      (volume : Measure (UnitAddTorus (Fin d))) := by
    have hs : AEStronglyMeasurable sign (volume : Measure (UnitAddTorus (Fin d))) :=
      hsignMeas.aestronglyMeasurable
    have hw : AEStronglyMeasurable wt (volume : Measure (UnitAddTorus (Fin d))) :=
      hwtMeas.aestronglyMeasurable
    have hrepr : anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) =
        fun x => c * sign x * (((g : (Fin d → ℝ) → ℝ) ∘ fold) x * wt x) := by
      funext x
      simp [anchoredFaceSource, sign, wt, c, fold, Function.comp_apply]
    rw [hrepr]
    have hmul := (measurable_const : Measurable
      (fun _ : UnitAddTorus (Fin d) => c)).aestronglyMeasurable.mul
        (hs.mul (hgComp.mul hw))
    convert hmul using 1
    ext x
    simp only [Pi.mul_apply, Function.comp_apply]
    ring
  have hbound : ∀ᵐ x ∂(volume : Measure (UnitAddTorus (Fin d))),
      ‖anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x‖ ≤
        ‖c * ((g : (Fin d → ℝ) → ℝ) ∘ fold) x‖ := by
    filter_upwards [] with x
    rw [show anchoredFaceSource J (g : (Fin d → ℝ) → ℝ) x =
      c * sign x * (((g : (Fin d → ℝ) → ℝ) ∘ fold) x * wt x) by
        simp [anchoredFaceSource, sign, wt, c, fold]]
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hsignnorm : ‖sign x‖ = 1 := by
      dsimp [sign]
      rw [Finset.abs_prod]
      apply Finset.prod_eq_one
      intro i hi
      simpa only [Real.norm_eq_abs] using anchoredFaceSignCoordinate_norm x i
    have hwtnorm : ‖wt x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (anchoredFaceWeight_bounds J x).1]
      exact (anchoredFaceWeight_bounds J x).2
    have hineq : c * (‖(g : (Fin d → ℝ) → ℝ) (fold x)‖ * ‖wt x‖) ≤
        c * ‖(g : (Fin d → ℝ) → ℝ) (fold x)‖ := by
      calc
        c * (‖(g : (Fin d → ℝ) → ℝ) (fold x)‖ * ‖wt x‖) ≤
            c * (‖(g : (Fin d → ℝ) → ℝ) (fold x)‖ * 1) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hwtnorm (norm_nonneg _)) hc
        _ = c * ‖(g : (Fin d → ℝ) → ℝ) (fold x)‖ := by ring
    simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg hc, hsignnorm] using hineq
  have hmono := eLpNorm_mono_ae (p := ENNReal.ofReal p) hsm hbound
  have hconst : eLpNorm (fun x => c * ((g : (Fin d → ℝ) → ℝ) ∘ fold) x)
      (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) =
      ENNReal.ofReal c * eLpNorm (((g : (Fin d → ℝ) → ℝ) ∘ fold))
        (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) := by
    rw [show (fun x => c * ((g : (Fin d → ℝ) → ℝ) ∘ fold) x) =
      c • ((g : (Fin d → ℝ) → ℝ) ∘ fold) by funext x; simp]
    rw [eLpNorm_const_smul]
    have htwo : ‖(2:ℝ)‖ₑ = (2:ENNReal) := by
      rw [Real.enorm_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]
      norm_num
    simp [c, ENNReal.ofReal_pow, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ (2:ℝ)^J.card), htwo]
  calc
    eLpNorm (anchoredFaceSource J (g : (Fin d → ℝ) → ℝ))
        (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) ≤
      eLpNorm (fun x => c * ((g : (Fin d → ℝ) → ℝ) ∘ fold) x)
        (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) := hmono
    _ = ENNReal.ofReal c * eLpNorm (((g : (Fin d → ℝ) → ℝ) ∘ fold))
        (ENNReal.ofReal p) (volume : Measure (UnitAddTorus (Fin d))) := hconst
    _ = ENNReal.ofReal c * eLpNorm (g : (Fin d → ℝ) → ℝ)
        (ENNReal.ofReal p) (cubeMeasure d) := by
          rw [eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable g) hfold]
    _ = ENNReal.ofReal ((2:ℝ)^J.card) * eLpNorm (g : (Fin d → ℝ) → ℝ)
        (ENNReal.ofReal p) (cubeMeasure d) := by rfl

end BrownianSharp.AlignmentPaperAnchoredLpScalarKernelFormula
