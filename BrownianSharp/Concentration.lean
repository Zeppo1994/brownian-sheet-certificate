import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Order.Filter.Defs
import Mathlib.Probability.CDF
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import BrownianSharp.Statistics
import BrownianSharp.GaussianSupport
import BrownianSharp.GaussianRows

/-!
# Elementary concentration utilities for the Brownian sharp candidate

This file formalizes consequences of the Paouris–Valettas inequality. It does not
formalize or assume that external convex-Gaussian inequality.
-/

open MeasureTheory Filter
open scoped ENNReal Topology ProbabilityTheory

namespace BrownianSharp.Concentration

/-- Chernoff's lower-tail estimate for a standard real Gaussian, proved directly
from mathlib's Gaussian moment-generating function and Markov inequality. This
is a Gaussian-model ingredient; it does not establish concentration for a
nonlinear convex observable. -/
theorem gaussianReal_lower_tail_exp {t : ℝ} (ht : 0 ≤ t) :
    (ProbabilityTheory.gaussianReal 0 1).real {x | x < -t} ≤
      Real.exp (-t ^ 2 / 2) := by
  let μ := ProbabilityTheory.gaussianReal 0 1
  let f : ℝ → ℝ := fun x => Real.exp (-t * x)
  have hint : Integrable f μ := by
    simpa [f, μ] using ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (-t)
  have hnonneg : 0 ≤ᵐ[μ] f := ae_of_all _ (fun x => (Real.exp_pos _).le)
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hint (Real.exp (t ^ 2))
  have hmgf := congrFun (ProbabilityTheory.mgf_id_gaussianReal (μ := 0) (v := 1)) (-t)
  have hint_eq : ∫ x, f x ∂μ = Real.exp (t ^ 2 / 2) := by
    simpa [f, μ, ProbabilityTheory.mgf, mul_comm] using hmgf
  have hsubset : {x : ℝ | x < -t} ⊆ {x | Real.exp (t ^ 2) ≤ f x} := by
    intro x hx
    change x < -t at hx
    change Real.exp (t ^ 2) ≤ Real.exp (-t * x)
    apply Real.exp_le_exp.mpr
    have hprod : t ^ 2 ≤ -t * x := by
      have hmul := mul_le_mul_of_nonneg_left hx.le ht
      nlinarith [hmul]
    exact hprod
  have htail : μ.real {x : ℝ | x < -t} ≤ μ.real {x | Real.exp (t ^ 2) ≤ f x} :=
    MeasureTheory.measureReal_mono hsubset
  have hexp : 0 < Real.exp (t ^ 2) := Real.exp_pos _
  have hratio : μ.real {x | Real.exp (t ^ 2) ≤ f x} ≤
      Real.exp (t ^ 2 / 2) / Real.exp (t ^ 2) := by
    apply (le_div_iff₀ hexp).2
    simpa [hint_eq, mul_comm] using hmarkov
  calc
    μ.real {x : ℝ | x < -t} ≤ μ.real {x | Real.exp (t ^ 2) ≤ f x} := htail
    _ ≤ Real.exp (t ^ 2 / 2) / Real.exp (t ^ 2) := hratio
    _ = Real.exp (-t ^ 2 / 2) := by rw [← Real.exp_sub]; congr 1; ring

/-- The strict standard Gaussian distribution function, defined directly from
mathlib's Gaussian measure. -/
noncomputable def standardGaussianCDF (x : ℝ) : ℝ :=
  (ProbabilityTheory.gaussianReal 0 1).real {z | z < x}

/-- The standard Gaussian CDF is strictly increasing. We use the positive density
on every open interval; thus the strictness premise in the quantile bridge is
proved from mathlib's Gaussian absolute-continuity result. -/
theorem standardGaussianCDF_strictMono : StrictMono standardGaussianCDF := by
  intro a b hab
  let μ := ProbabilityTheory.gaussianReal 0 1
  let A : Set ℝ := Set.Iio a
  let C : Set ℝ := Set.Ioo a b
  let B : Set ℝ := Set.Iio b
  have hvol : (volume : Measure ℝ) ≪ μ := by
    simpa [μ] using (ProbabilityTheory.gaussianReal_absolutelyContinuous'
      (0 : ℝ) (v := (1 : NNReal)) (by norm_num))
  letI : MeasureTheory.Measure.IsOpenPosMeasure (volume : Measure ℝ) := inferInstance
  haveI : MeasureTheory.Measure.IsOpenPosMeasure μ := hvol.isOpenPosMeasure
  have hCopen : IsOpen C := by dsimp [C]; exact isOpen_Ioo
  have hCne : C.Nonempty := by
    refine ⟨(a + b) / 2, Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩⟩
  have hCpos : 0 < μ C := hCopen.measure_pos μ hCne
  have hCposR : 0 < μ.real C := by
    exact ENNReal.toReal_pos hCpos.ne' (measure_ne_top μ C)
  have hA : MeasurableSet A := by dsimp [A]; exact measurableSet_Iio
  have hC : MeasurableSet C := by dsimp [C]; exact measurableSet_Ioo
  have hdisj : Disjoint A C := by
    rw [Set.disjoint_left]
    intro z hzA hzC
    exact (not_lt_of_ge (Set.mem_Ioo.mp hzC).1.le) (Set.mem_Iio.mp hzA)
  have hsum := MeasureTheory.measureReal_union hdisj hC
    (measure_ne_top μ A) (measure_ne_top μ C)
  have hsub : A ∪ C ⊆ B := by
    intro z hz
    simp only [A, C, B, Set.mem_union] at hz
    rcases hz with hz | hz
    · exact lt_trans (Set.mem_Iio.mp hz) hab
    · exact (Set.mem_Ioo.mp hz).2
  have hmass : μ.real A + μ.real C ≤ μ.real B := by
    calc
      μ.real A + μ.real C = μ.real (A ∪ C) := hsum.symm
      _ ≤ μ.real B := MeasureTheory.measureReal_mono hsub
  have ha : μ.real A = standardGaussianCDF a := by rfl
  have hb : μ.real B = standardGaussianCDF b := by rfl
  rw [ha, hb] at hmass
  dsimp [μ] at hCposR
  dsimp [C] at hCposR
  linarith

/-- Symmetry of the standard Gaussian gives CDF value one half at zero. -/
theorem standardGaussianCDF_zero : standardGaussianCDF 0 = 1 / 2 := by
  let μ := ProbabilityTheory.gaussianReal 0 1
  let A : Set ℝ := Set.Iio 0
  let B : Set ℝ := Set.Ioi 0
  let Z : Set ℝ := {0}
  have hsym : μ A = μ B := by
    have hmap := congrArg (fun ν : Measure ℝ => ν A)
      (ProbabilityTheory.gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
    rw [Measure.map_apply measurable_neg measurableSet_Iio] at hmap
    simpa [μ, A, B] using hmap.symm
  have hZ : μ Z = 0 := by
    haveI : MeasureTheory.NullSingletonClass μ := by
      simpa [μ] using (ProbabilityTheory.nullSingletonClass_gaussianReal
        (μ := (0 : ℝ)) (v := (1 : NNReal)) (by norm_num))
    simp [Z]
  have hAZdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro x hxA hxB
    exact (not_lt_of_ge (Set.mem_Ioi.mp hxB).le) (Set.mem_Iio.mp hxA)
  have hAB := MeasureTheory.measureReal_union hAZdisj
    (by dsimp [A, B]; exact measurableSet_Ioi)
    (measure_ne_top μ A) (measure_ne_top μ B)
  have hABZdisj : Disjoint (A ∪ B) Z := by
    rw [Set.disjoint_left]
    intro x hxAB hxZ
    have hx : x = 0 := by simpa [Z] using hxZ
    subst x
    simp [A, B] at hxAB
  have hABZ := MeasureTheory.measureReal_union hABZdisj
    (by simp [Z]) (measure_ne_top μ (A ∪ B)) (measure_ne_top μ Z)
  have htotal : μ.real (A ∪ B ∪ Z) = 1 := by
    have huniv : A ∪ B ∪ Z = Set.univ := by
      ext x
      simp only [A, B, Z, Set.mem_union, Set.mem_Iio, Set.mem_Ioi,
        Set.mem_singleton_iff, Set.mem_univ]
      constructor
      · intro _
        trivial
      · intro _
        by_cases hx : x = 0
        · exact Or.inr hx
        · rcases lt_or_gt_of_ne hx with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inl (Or.inr h)
    rw [huniv]
    simp [μ]
  have hsum : μ.real A + μ.real B + μ.real Z = 1 := by
    calc
      μ.real A + μ.real B + μ.real Z = μ.real (A ∪ B) + μ.real Z := by rw [hAB.symm]
      _ = μ.real (A ∪ B ∪ Z) := hABZ.symm
      _ = 1 := htotal
  have hhalf : μ.real A = 1 / 2 := by
    have hs : μ.real A = μ.real B := by
      change (μ A).toReal = (μ B).toReal
      exact congrArg ENNReal.toReal hsym
    have hZR : μ.real Z = 0 := by simpa [measureReal_def] using congrArg ENNReal.toReal hZ
    rw [hZR] at hsum
    have hs' : μ.real A + μ.real A = 1 := by linarith [hs]
    linarith
  change (ProbabilityTheory.gaussianReal 0 1).real (Set.Iio 0) = 1 / 2
  exact hhalf

/-- A probability CDF is continuous when its underlying measure has no atoms.
The proof identifies the jump at `x` with the Stieltjes measure of `{x}` and
uses the monotonicity/one-sided-limit characterization of continuity. -/
theorem cdf_continuous_of_null_singletons (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hnull : ∀ x, μ {x} = 0) :
    Continuous (ProbabilityTheory.cdf μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hsingle : (ProbabilityTheory.cdf μ).measure {x} = 0 := by
    rw [ProbabilityTheory.measure_cdf, hnull]
  rw [StieltjesFunction.measure_singleton] at hsingle
  have hdiff_le : ProbabilityTheory.cdf μ x -
      Function.leftLim (ProbabilityTheory.cdf μ) x ≤ 0 :=
    ENNReal.ofReal_eq_zero.mp hsingle
  have hdiff_nonneg : 0 ≤ ProbabilityTheory.cdf μ x -
      Function.leftLim (ProbabilityTheory.cdf μ) x := by
    exact sub_nonneg.mpr ((ProbabilityTheory.cdf μ).mono.leftLim_le le_rfl)
  have hdiff : ProbabilityTheory.cdf μ x -
      Function.leftLim (ProbabilityTheory.cdf μ) x = 0 := by linarith
  have hleft : Function.leftLim (ProbabilityTheory.cdf μ) x =
      ProbabilityTheory.cdf μ x := by linarith
  have hright : Function.rightLim (ProbabilityTheory.cdf μ) x =
      ProbabilityTheory.cdf μ x := StieltjesFunction.rightLim_eq _ _
  rw [(ProbabilityTheory.cdf μ).mono.continuousAt_iff_leftLim_eq_rightLim]
  rw [hleft, hright]

/-- The strict CDF agrees with mathlib's right-continuous CDF because the
standard Gaussian has no singleton atoms. -/
theorem standardGaussianCDF_eq_cdf :
    standardGaussianCDF = ProbabilityTheory.cdf
      (ProbabilityTheory.gaussianReal 0 1) := by
  funext x
  let μ := ProbabilityTheory.gaussianReal 0 1
  haveI : MeasureTheory.NullSingletonClass μ := by
    simpa [μ] using (ProbabilityTheory.nullSingletonClass_gaussianReal
      (μ := (0 : ℝ)) (v := (1 : NNReal)) (by norm_num))
  have hdecomp : Set.Iic x = Set.Iio x ∪ {x} := by
    ext y
    simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio,
      Set.mem_singleton_iff]
    constructor
    · intro hy
      by_cases hyx : y = x
      · exact Or.inr hyx
      · exact Or.inl (lt_of_le_of_ne hy hyx)
    · rintro (hy | hy)
      · exact le_of_lt hy
      · rw [hy]
  have hdisj : Disjoint (Set.Iio x) ({x} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro y hyI hyS
    simp only [Set.mem_singleton_iff] at hyS
    change y < x at hyI
    subst y
    exact (lt_irrefl _ hyI)
  have hsum := MeasureTheory.measureReal_union hdisj (measurableSet_singleton x)
    (measure_ne_top μ _) (measure_ne_top μ _)
  have hsingleton : μ.real {x} = 0 := by simp [measureReal_def]
  have hIio : μ.real (Set.Iio x) = μ.real (Set.Iic x) := by
    calc
      μ.real (Set.Iio x) = μ.real (Set.Iio x) + μ.real {x} := by
        rw [hsingleton, add_zero]
      _ = μ.real (Set.Iio x ∪ {x}) := hsum.symm
      _ = μ.real (Set.Iic x) := by rw [hdecomp]
  change μ.real (Set.Iio x) = ProbabilityTheory.cdf μ x
  rw [ProbabilityTheory.cdf_eq_real]
  exact hIio

/-- The standard Gaussian strict CDF is continuous and has the usual endpoint
limits. -/
theorem standardGaussianCDF_continuous : Continuous standardGaussianCDF := by
  rw [standardGaussianCDF_eq_cdf]
  exact cdf_continuous_of_null_singletons _ (by
    intro x
    haveI : MeasureTheory.NullSingletonClass
        (ProbabilityTheory.gaussianReal 0 1) := by
      exact ProbabilityTheory.nullSingletonClass_gaussianReal
        (μ := (0 : ℝ)) (v := (1 : NNReal)) (by norm_num)
    exact measure_singleton x)

theorem tendsto_standardGaussianCDF_atBot :
    Tendsto standardGaussianCDF atBot (𝓝 0) := by
  rw [standardGaussianCDF_eq_cdf]
  exact ProbabilityTheory.tendsto_cdf_atBot _

theorem tendsto_standardGaussianCDF_atTop :
    Tendsto standardGaussianCDF atTop (𝓝 1) := by
  rw [standardGaussianCDF_eq_cdf]
  exact ProbabilityTheory.tendsto_cdf_atTop _

/-- Every probability strictly between zero and one has a standard-Gaussian
quantile. -/
theorem exists_standardGaussianCDF_eq {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    ∃ x, standardGaussianCDF x = u := by
  have hsmall : ∀ᶠ x : ℝ in atBot, standardGaussianCDF x < u :=
    tendsto_standardGaussianCDF_atBot.eventually
      (Iio_mem_nhds (by linarith))
  have hlarge : ∀ᶠ x : ℝ in atTop, u < standardGaussianCDF x :=
    tendsto_standardGaussianCDF_atTop.eventually
      (Ioi_mem_nhds (by linarith))
  obtain ⟨a, ha⟩ := eventually_atBot.mp hsmall
  obtain ⟨b, hb⟩ := eventually_atTop.mp hlarge
  have hab : a ≤ b := by
    by_contra h
    have hba : b ≤ a := le_of_not_ge h
    have hmono := standardGaussianCDF_strictMono.monotone hba
    have ha' := ha a le_rfl
    have hb' := hb b le_rfl
    linarith
  have hu : u ∈ Set.Icc (standardGaussianCDF a) (standardGaussianCDF b) :=
    ⟨le_of_lt (ha a le_rfl), le_of_lt (hb b le_rfl)⟩
  obtain ⟨x, _, hfx⟩ :=
    intermediate_value_Icc hab standardGaussianCDF_continuous.continuousOn hu
  exact ⟨x, hfx⟩

/-- A totalized standard Gaussian quantile, used only for arguments in `(0,1)`. -/
noncomputable def standardGaussianQuantile (u : ℝ) : ℝ :=
  if h : 0 < u ∧ u < 1 then
    Classical.choose (exists_standardGaussianCDF_eq h.1 h.2)
  else 0

theorem standardGaussianCDF_standardGaussianQuantile {u : ℝ}
    (hu0 : 0 < u) (hu1 : u < 1) :
    standardGaussianCDF (standardGaussianQuantile u) = u := by
  unfold standardGaussianQuantile
  rw [dif_pos ⟨hu0, hu1⟩]
  exact Classical.choose_spec (exists_standardGaussianCDF_eq hu0 hu1)

/-- Quantile transformation of a sublevel CDF, with its representation proved
at every threshold whose mass lies strictly between zero and one. -/
noncomputable def cdfGaussianQuantile (F : ℝ → ℝ) (s : ℝ) : ℝ :=
  standardGaussianQuantile (F s)

theorem cdfGaussianQuantile_representation (F : ℝ → ℝ) {s : ℝ}
    (hF0 : 0 < F s) (hF1 : F s < 1) :
    F s = standardGaussianCDF (cdfGaussianQuantile F s) := by
  symm
  exact standardGaussianCDF_standardGaussianQuantile hF0 hF1

/-- A direct density estimate gives the Gaussian quantile cutoff used by the
Paouris--Valettas argument: `Φ(√π/4) < 3/4`. The proof only uses `π ≥ 2`,
`π < 4`, and `exp(-x²/2) ≤ 1`. -/
theorem standardGaussianCDF_sqrt_pi_div_four_lt_three_quarters :
    standardGaussianCDF (Real.sqrt Real.pi / 4) < 3 / 4 := by
  let μ := ProbabilityTheory.gaussianReal 0 1
  let c := Real.sqrt Real.pi / 4
  let C : Set ℝ := Set.Ioo 0 c
  have hpdfReal (x : ℝ) : ProbabilityTheory.gaussianPDFReal 0 1 x ≤ 1 / 2 := by
    rw [ProbabilityTheory.gaussianPDFReal_def]
    have hden : (2 : ℝ) ≤ Real.sqrt (2 * Real.pi) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [Real.two_le_pi]
    have hcoef : (Real.sqrt (2 * Real.pi))⁻¹ ≤ (1 / 2 : ℝ) := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      exact (inv_le_inv₀ (by positivity) (by norm_num)).2 hden
    have hexp : Real.exp (-(x - 0) ^ 2 / (2 * 1)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [sq_nonneg x]
    calc
      (Real.sqrt (2 * Real.pi * (1 : ℝ)))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * (1 : ℝ))) ≤
          (Real.sqrt (2 * Real.pi))⁻¹ * 1 := by
        have hmul := mul_le_mul_of_nonneg_left hexp
          (inv_nonneg.mpr (Real.sqrt_nonneg (2 * Real.pi)))
        simpa using hmul
      _ ≤ 1 / 2 := by simpa using hcoef
  have hpdfENN : ProbabilityTheory.gaussianPDF 0 1 ≤ᵐ[volume]
      fun _ : ℝ => (1 / 2 : ℝ≥0∞) := ae_of_all _ fun x => by
    rw [ProbabilityTheory.gaussianPDF_def]
    simpa using ENNReal.ofReal_le_ofReal (hpdfReal x)
  have hdom : μ ≤ (1 / 2 : ℝ≥0∞) • (volume : Measure ℝ) := by
    dsimp [μ]
    rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0)]
    rw [← MeasureTheory.withDensity_const]
    exact MeasureTheory.withDensity_mono hpdfENN
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hCbound : μ.real C ≤ c / 2 := by
    have hC := hdom C
    have hreal := ENNReal.toReal_mono
      (by
        rw [Measure.smul_apply, Real.volume_Ioo]
        exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
      hC
    calc
      μ.real C ≤ (1 / 2 : ℝ) * c := by
        simpa [Measure.real_def, μ, C, c,
          ENNReal.toReal_ofReal (le_of_lt hcpos)] using hreal
      _ = c / 2 := by ring
  let A : Set ℝ := Set.Iio 0
  let Z : Set ℝ := {0}
  have hA : MeasurableSet A := by dsimp [A]; exact measurableSet_Iio
  have hC : MeasurableSet C := by dsimp [C]; exact measurableSet_Ioo
  have hZ : μ Z = 0 := by
    haveI : MeasureTheory.NullSingletonClass μ := by
      simpa [μ] using (ProbabilityTheory.nullSingletonClass_gaussianReal
        (μ := (0 : ℝ)) (v := (1 : NNReal)) (by norm_num))
    simp [Z]
  have hZreal : μ.real Z = 0 := by simpa [Measure.real_def] using congrArg ENNReal.toReal hZ
  have hdisj : Disjoint A C := by
    rw [Set.disjoint_left]
    intro x hxA hxC
    exact (not_lt_of_ge (Set.mem_Ioo.mp hxC).1.le) (Set.mem_Iio.mp hxA)
  have hsum := MeasureTheory.measureReal_union hdisj hC
    (measure_ne_top μ A) (measure_ne_top μ C)
  have hAZdisj : Disjoint (A ∪ C) Z := by
    rw [Set.disjoint_left]
    intro x hxAC hxZ
    have hx : x = 0 := by simpa [Z] using hxZ
    subst x
    simp only [Set.mem_union] at hxAC
    rcases hxAC with hxA | hxC
    · simp [A] at hxA
    · simp [C] at hxC
  have hsumZ := MeasureTheory.measureReal_union hAZdisj
    (by simp [Z]) (measure_ne_top μ (A ∪ C)) (measure_ne_top μ Z)
  have hunion : A ∪ C ∪ Z = Set.Iio c := by
    ext x
    simp only [Set.mem_union, A, C, Z, Set.mem_Iio, Set.mem_Ioo,
      Set.mem_singleton_iff]
    constructor
    · rintro ((hxA | hxC) | hxZ)
      · exact lt_trans hxA hcpos
      · exact hxC.2
      · rw [hxZ]
        exact hcpos
    · intro hx
      by_cases hxA : x < 0
      · exact Or.inl (Or.inl hxA)
      · by_cases hxZ : x = 0
        · exact Or.inr hxZ
        · have hxpos : 0 < x := by
            rcases lt_or_gt_of_ne (Ne.symm hxZ) with h | h
            · exact h
            · exact (hxA h).elim
          exact Or.inl (Or.inr ⟨hxpos, hx⟩)
  have hmassEq : μ.real (Set.Iio c) = μ.real (Set.Iio 0) + μ.real C := by
    calc
      μ.real (Set.Iio c) = μ.real (A ∪ C ∪ Z) := by rw [hunion]
      _ = μ.real (A ∪ C) + μ.real Z := hsumZ
      _ = μ.real A + μ.real C := by rw [hZreal, hsum]; simp
  have hsqrtLt : Real.sqrt Real.pi < 2 := by
    have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by norm_num
    rw [← hsqrt4]
    exact Real.sqrt_lt_sqrt (le_of_lt Real.pi_pos) Real.pi_lt_four
  have hcHalf : c / 2 < 1 / 4 := by dsimp [c]; nlinarith
  calc
    standardGaussianCDF c = μ.real (Set.Iio c) := rfl
    _ = μ.real (Set.Iio 0) + μ.real C := hmassEq
    _ = 1 / 2 + μ.real C := by rw [← standardGaussianCDF_zero]; rfl
    _ ≤ 1 / 2 + c / 2 := by linarith [hCbound]
    _ < 3 / 4 := by linarith

/-- Convert the scalar Ehrhard interpolation inequality for a sublevel-set CDF
into concavity of its Gaussian-quantile transform. The premise
`hEhrhardMass` is precisely the Gaussian set-interpolation step: for the
homothetic sublevel sets of a nonnegative homogeneous convex observable, it
states that the interpolated set has Gaussian mass at least the standard
Gaussian mass at the interpolated quantile. Thus the remaining geometric
obligation is Ehrhard's inequality itself, not a concavity restatement. -/
theorem transformed_cdf_concave_of_ehrhard_mass
    (F G : ℝ → ℝ)
    (hrepresentation : ∀ s, 0 < s → F s = standardGaussianCDF (G s))
    (hEhrhardMass : ∀ s ∈ Set.Ioi (0 : ℝ), ∀ t ∈ Set.Ioi (0 : ℝ),
      ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
        standardGaussianCDF (a • G s + b • G t) ≤ F (a • s + b • t)) :
    ConcaveOn ℝ (Set.Ioi 0) G := by
  rw [concaveOn_iff_forall_pos]
  constructor
  · exact convex_Ioi (𝕜 := ℝ) (β := ℝ) (0 : ℝ)
  · intro s hs t ht a b ha hb hab
    have hintpos : 0 < a • s + b • t := by
      have hs' : 0 < s := hs
      have ht' : 0 < t := ht
      simp only [smul_eq_mul]
      positivity
    have hrep := hrepresentation (a • s + b • t) hintpos
    have hmass := hEhrhardMass s hs t ht a b ha hb hab
    rw [hrep] at hmass
    by_contra hnot
    have hlt : G (a • s + b • t) < a • G s + b • G t := lt_of_not_ge hnot
    have hstrict := standardGaussianCDF_strictMono hlt
    linarith

/-- A quarter of interval mass moves the transformed-CDF value past the
three-quarter Gaussian quantile. The strict monotonicity of the Gaussian CDF
and the numerical cutoff `Φ(c) < 3/4` remain explicit inputs. -/
theorem transformed_cdf_right_quantile_of_interval_mass
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXmeas : Measurable X) (F G : ℝ → ℝ)
    (median y c : ℝ)
    (hmy : median < y)
    (hF : ∀ s, F s = μ.real {ω | X ω < s})
    (hrepresentation : F y = standardGaussianCDF (G y))
    (hmedian : μ.real {ω | X ω < median} = 1 / 2)
    (hinterval : (1 / 4 : ℝ) ≤ μ.real
      {ω | median < X ω ∧ X ω < y})
    (hCDFstrict : StrictMono standardGaussianCDF)
    (hcutoff : standardGaussianCDF c < 3 / 4) :
    c ≤ G y := by
  let A : Set Ω := {ω | X ω < median}
  let B : Set Ω := {ω | median < X ω ∧ X ω < y}
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lt hXmeas measurable_const
  have hB : MeasurableSet B := by
    dsimp [B]
    exact (measurableSet_lt measurable_const hXmeas).inter
      (measurableSet_lt hXmeas measurable_const)
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro ω hωA hωB
    exact (not_lt_of_ge hωB.1.le) hωA
  have hsub : A ∪ B ⊆ {ω | X ω < y} := by
    intro ω hω
    simp only [A, B, Set.mem_union, Set.mem_setOf_eq] at hω
    rcases hω with hω | hω
    · exact lt_trans hω hmy
    · exact hω.2
  have hsum := MeasureTheory.measureReal_union hdisj hB
    (measure_ne_top μ A) (measure_ne_top μ B)
  have hmass : (3 / 4 : ℝ) ≤ μ.real {ω | X ω < y} := by
    calc
      (3 / 4 : ℝ) ≤ μ.real A + μ.real B := by
        dsimp [A, B]
        linarith [hmedian, hinterval]
      _ = μ.real (A ∪ B) := hsum.symm
      _ ≤ μ.real {ω | X ω < y} := MeasureTheory.measureReal_mono hsub
  have hFy : 3 / 4 ≤ standardGaussianCDF (G y) := by
    calc
      (3 / 4 : ℝ) ≤ μ.real {ω | X ω < y} := hmass
      _ = F y := (hF y).symm
      _ = standardGaussianCDF (G y) := hrepresentation
  by_contra hnot
  have hgy : G y < c := lt_of_not_ge hnot
  have hstrict := hCDFstrict hgy
  linarith

/-- The deterministic Ehrhard-concavity step behind a median lower-tail bound.
If the Gaussian-quantile transform of a CDF is concave, is zero at the median,
and rises by at least `c` over a right interval of length `y - median`, then
its values to the left of the median fall at least linearly with the secant
slope. The concavity hypothesis is explicit: this lemma does not prove the
Ehrhard theorem for convex Gaussian observables. -/
theorem concave_median_left_bound (G : ℝ → ℝ) (x median y c : ℝ)
    (hG : ConcaveOn ℝ (Set.Ioi 0) G)
    (hxpos : 0 < x) (hxm : x < median) (hmy : median < y)
    (hmedian : G median = 0) (hright : c ≤ G y) :
    G x ≤ -c * (median - x) / (y - median) := by
  have hslopes := hG.slope_anti_adjacent (Set.mem_Ioi.mpr hxpos)
    (Set.mem_Ioi.mpr (lt_trans hxpos (lt_trans hxm hmy))) hxm hmy
  rw [hmedian] at hslopes
  have hden₁ : 0 < y - median := by linarith
  have hden₂ : 0 < median - x := by linarith
  have hcdiv : c / (y - median) ≤ G y / (y - median) :=
    div_le_div_of_nonneg_right hright hden₁.le
  have hratio : c / (y - median) ≤ (0 - G x) / (median - x) :=
    hcdiv.trans (by simpa using hslopes)
  have hmult := mul_le_mul_of_nonneg_right hratio hden₂.le
  have hcancel : ((0 - G x) / (median - x)) * (median - x) = -G x := by
    rw [div_mul_cancel₀ _ hden₂.ne']
    ring
  have hbound : -c * (median - x) / (y - median) =
      -((c / (y - median)) * (median - x)) := by ring
  rw [hbound]
  nlinarith

/-- Conditional median concentration from transformed-CDF concavity. The CDF
identity and the right quantile bound are explicit inputs; the latter is the
place where the interval-mass estimate and Gaussian quantile calculation enter.
Together with Ehrhard's theorem, these are the analytic core of the
Paouris--Valettas argument. -/
theorem measure_median_lower_tail_le_of_transformed_cdf_concave
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (F G : ℝ → ℝ) (median δ c t : ℝ)
    (hF : F (median - t * δ) = μ.real {ω | X ω < median - t * δ})
    (hrepresentation : F (median - t * δ) =
      (ProbabilityTheory.gaussianReal 0 1).real {z | z < G (median - t * δ)})
    (hG : ConcaveOn ℝ (Set.Ioi 0) G)
    (hmedian : G median = 0) (hright : c ≤ G (median + δ))
    (hleft : 0 < median - t * δ) (hδ : 0 < δ) (hc : 0 ≤ c) (ht : 0 < t) :
    μ.real {ω | X ω < median - t * δ} ≤ Real.exp (-(c * t) ^ 2 / 2) := by
  let x := median - t * δ
  have hxm : x < median := by dsimp [x]; nlinarith
  have hmy : median < median + δ := by linarith
  have hGx := concave_median_left_bound G x median (median + δ) c
    hG (by simpa [x] using hleft) hxm hmy hmedian hright
  have hGx' : G x ≤ -(c * t) := by
    dsimp [x] at hGx
    have hδne : δ ≠ 0 := ne_of_gt hδ
    apply le_trans hGx
    rw [show median - (median - t * δ) = t * δ by ring,
      show median + δ - median = δ by ring]
    have hratio : -c * (t * δ) / δ = -(c * t) := by
      field_simp
    exact hratio.le
  have hthreshold : 0 ≤ c * t := mul_nonneg hc ht.le
  have hsubset : {z : ℝ | z < G x} ⊆ {z | z < -(c * t)} := by
    intro z hz
    exact lt_of_lt_of_le hz hGx'
  have htail := MeasureTheory.measureReal_mono hsubset
    (measure_ne_top (ProbabilityTheory.gaussianReal 0 1) _)
  calc
    μ.real {ω | X ω < median - t * δ} = F x := by
      simpa [x] using hF.symm
    _ = (ProbabilityTheory.gaussianReal 0 1).real {z | z < G x} := by
      simpa [x] using hrepresentation
    _ ≤ (ProbabilityTheory.gaussianReal 0 1).real {z | z < -(c * t)} := htail
    _ ≤ Real.exp (-(c * t) ^ 2 / 2) := gaussianReal_lower_tail_exp hthreshold

/-- Cantelli's one-sided Chebyshev inequality for the lower tail. The proof uses
Markov on a shifted square, optimizing the shift to `variance / δ`. -/
theorem measure_lower_tail_le_cantelli {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) (δ : ℝ) (hδ : 0 < δ) :
    μ.real {ω | δ ≤ μ[X] - X ω} ≤
      ProbabilityTheory.variance X μ /
        (ProbabilityTheory.variance X μ + δ ^ 2) := by
  let m : ℝ := μ[X]
  let v : ℝ := ProbabilityTheory.variance X μ
  let shift : ℝ := v / δ
  let g : Ω → ℝ := fun ω => m - X ω + shift
  have hv : 0 ≤ v := by
    dsimp [v, ProbabilityTheory.variance]
    exact ENNReal.toReal_nonneg
  have hshift_nonneg : 0 ≤ shift := div_nonneg hv hδ.le
  have hG : MemLp g 2 μ := by
    have hneg : MemLp (-X) 2 μ := hX.neg
    have hsum : MemLp (fun ω => -X ω + (m + shift)) 2 μ := hneg.add (memLp_const (m + shift))
    convert hsum using 1
    funext ω
    dsimp [g]
    ring
  have hGint : Integrable (fun ω => g ω ^ 2) μ := hG.integrable_sq
  have hGmean : μ[g] = shift := by
    calc
      μ[g] = ∫ ω, -X ω + (m + shift) ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        dsimp [g]
        ring
      _ = (∫ ω, -X ω ∂μ) + ∫ _, (m + shift) ∂μ :=
        integral_add (hX.neg.integrable one_le_two) (integrable_const _)
      _ = shift := by
        rw [integral_neg]
        simp [m]
  have hGfun : g = fun ω => -X ω + (m + shift) := by
    funext ω
    dsimp [g]
    ring
  have hGvar : ProbabilityTheory.variance g μ = v := by
    calc
      ProbabilityTheory.variance g μ =
          ProbabilityTheory.variance (fun ω => -X ω + (m + shift)) μ := by rw [hGfun]
      _ = ProbabilityTheory.variance (fun ω => -X ω) μ :=
        ProbabilityTheory.variance_add_const (X := fun ω => -X ω)
          hX.neg.aestronglyMeasurable (m + shift)
      _ = ProbabilityTheory.variance X μ := by rw [ProbabilityTheory.variance_fun_neg]
      _ = v := rfl
  have hmoment : ∫ ω, g ω ^ 2 ∂μ = v + shift ^ 2 := by
    have hv_eq := ProbabilityTheory.variance_eq_sub hG
    dsimp [v] at hv_eq
    rw [hGmean] at hv_eq
    rw [hGvar] at hv_eq
    linarith
  have hnonneg : 0 ≤ᵐ[μ] fun ω => g ω ^ 2 := ae_of_all _ fun _ => sq_nonneg _
  have hthreshold : 0 < (δ + shift) ^ 2 := by positivity
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hGint ((δ + shift) ^ 2)
  have hsubset : {ω | δ ≤ m - X ω} ⊆ {ω | (δ + shift) ^ 2 ≤ g ω ^ 2} := by
    intro ω hω
    change δ ≤ m - X ω at hω
    have hg : δ + shift ≤ g ω := by
      dsimp [g]
      linarith
    exact (sq_le_sq₀ (by linarith [hδ, hshift_nonneg]) (by linarith [hg])).2 hg
  have hprob : μ.real {ω | δ ≤ m - X ω} ≤ (v + shift ^ 2) / (δ + shift) ^ 2 := by
    have hmono := MeasureTheory.measureReal_mono hsubset (measure_ne_top μ _)
    apply (le_div_iff₀ hthreshold).2
    calc
      μ.real {ω | δ ≤ m - X ω} * (δ + shift) ^ 2 =
          (δ + shift) ^ 2 * μ.real {ω | δ ≤ m - X ω} := by ring
      _ ≤ (δ + shift) ^ 2 * μ.real {ω | (δ + shift) ^ 2 ≤ g ω ^ 2} :=
          mul_le_mul_of_nonneg_left hmono (sq_nonneg _)
      _ ≤ ∫ ω, g ω ^ 2 ∂μ := hmarkov
      _ = v + shift ^ 2 := hmoment
  have hratio : (v + shift ^ 2) / (δ + shift) ^ 2 = v / (v + δ ^ 2) := by
    dsimp [shift]
    field_simp
    ring
  calc
    μ.real {ω | δ ≤ μ[X] - X ω} = μ.real {ω | δ ≤ m - X ω} := by simp [m]
    _ ≤ (v + shift ^ 2) / (δ + shift) ^ 2 := hprob
    _ = v / (v + δ ^ 2) := hratio
    _ = ProbabilityTheory.variance X μ / (ProbabilityTheory.variance X μ + δ ^ 2) := by rfl

/-- A median is within one standard deviation above the mean. This is the
mean/median displacement bound needed to normalize the Paouris–Valettas tail.
The proof uses the lower-tail Cantelli bound and the median's half-mass property. -/
theorem mean_sub_median_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) (median : ℝ)
    (hmedian : (1 / 2 : ℝ) ≤ μ.real {ω | X ω ≤ median}) :
    μ[X] - median ≤ Real.sqrt (ProbabilityTheory.variance X μ) := by
  let σ := Real.sqrt (ProbabilityTheory.variance X μ)
  have hσ : 0 ≤ σ := Real.sqrt_nonneg _
  by_contra! hbad
  have hΔ : 0 < μ[X] - median := by linarith
  have hc := measure_lower_tail_le_cantelli μ X hX (μ[X] - median) hΔ
  have hsubset : {ω | X ω ≤ median} ⊆ {ω | μ[X] - median ≤ μ[X] - X ω} := by
    intro ω hω
    change X ω ≤ median at hω
    change μ[X] - median ≤ μ[X] - X ω
    linarith
  have htail := (MeasureTheory.measureReal_mono hsubset).trans hc
  have hv : 0 ≤ ProbabilityTheory.variance X μ := by
    dsimp [ProbabilityTheory.variance]
    exact ENNReal.toReal_nonneg
  have hsquares : (Real.sqrt (ProbabilityTheory.variance X μ)) ^ 2 =
      ProbabilityTheory.variance X μ := Real.sq_sqrt hv
  have hden : 0 < ProbabilityTheory.variance X μ + (μ[X] - median) ^ 2 := by positivity
  have hratio : ProbabilityTheory.variance X μ /
      (ProbabilityTheory.variance X μ + (μ[X] - median) ^ 2) < 1 / 2 := by
    have hσlt : Real.sqrt (ProbabilityTheory.variance X μ) < μ[X] - median := by linarith
    rw [div_lt_iff₀ hden]
    nlinarith [sq_nonneg (μ[X] - median)]
  linarith

/-- The opposite displacement estimate follows by applying the lower-tail
Cantelli argument to `-X`. Together with `mean_sub_median_le_sqrt_variance`,
this gives a two-sided mean/median bound whenever both median half-mass
conditions hold. -/
theorem median_sub_mean_le_sqrt_variance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) (median : ℝ)
    (hmedian : (1 / 2 : ℝ) ≤ μ.real {ω | median ≤ X ω}) :
    median - μ[X] ≤ Real.sqrt (ProbabilityTheory.variance X μ) := by
  have hs : {ω | -X ω ≤ -median} = {ω | median ≤ X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  have hmedian' : (1 / 2 : ℝ) ≤ μ.real {ω | -X ω ≤ -median} := by
    rw [hs]
    exact hmedian
  have h := mean_sub_median_le_sqrt_variance μ (fun ω => -X ω) hX.neg
    (-median) hmedian'
  have h' : median ≤ μ[X] + Real.sqrt (ProbabilityTheory.variance X μ) := by
    simpa [integral_neg, ProbabilityTheory.variance_fun_neg] using h
  linarith

/-- For a two-sided median, the mean-centered second moment around the median
is at most twice the variance. The proof expands the square and uses that the
centered observable has integral zero. -/
theorem integral_sq_deviation_le_two_variance_of_median
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (median : ℝ)
    (hmedianLower : (1 / 2 : ℝ) ≤ μ.real {ω | X ω ≤ median})
    (hmedianUpper : (1 / 2 : ℝ) ≤ μ.real {ω | median ≤ X ω}) :
    ∫ ω, (X ω - median) ^ 2 ∂μ ≤ 2 * ProbabilityTheory.variance X μ := by
  let Z : Ω → ℝ := fun ω => X ω - μ[X]
  let d : ℝ := μ[X] - median
  have hZ : MemLp Z 2 μ := by
    exact hX.sub (memLp_const _)
  have hZint : Integrable Z μ := hZ.integrable one_le_two
  have hZmean : ∫ ω, Z ω ∂μ = 0 := by
    dsimp [Z]
    rw [integral_sub (hX.integrable one_le_two) (integrable_const _)]
    simp [integral_const]
  have hconstSqInt : Integrable (fun _ : Ω => (d ^ 2 : ℝ)) μ := integrable_const _
  have hcrossInt : Integrable (fun ω => 2 * Z ω * d) μ := by
    convert hZint.const_mul (2 * d) using 1 <;> ext ω <;> ring
  have hsqInt : Integrable (fun ω => Z ω ^ 2) μ := hZ.integrable_sq
  have hdevInt : Integrable (fun ω => (X ω - median) ^ 2) μ := by
    have hdev : MemLp (fun ω => X ω - median) 2 μ := hX.sub (memLp_const _)
    exact hdev.integrable_sq
  have hexpand : ∀ ω, (X ω - median) ^ 2 = Z ω ^ 2 + 2 * Z ω * d + d ^ 2 := by
    intro ω
    dsimp [Z, d]
    ring
  have hsecond : ∫ ω, (X ω - median) ^ 2 ∂μ =
      ProbabilityTheory.variance X μ + d ^ 2 := by
    calc
      ∫ ω, (X ω - median) ^ 2 ∂μ =
          ∫ ω, (Z ω ^ 2 + 2 * Z ω * d + d ^ 2) ∂μ := by
            apply integral_congr_ae
            filter_upwards with ω
            exact hexpand ω
      _ = (∫ ω, Z ω ^ 2 ∂μ) + (∫ ω, 2 * Z ω * d ∂μ) +
          ∫ _, d ^ 2 ∂μ := by
            calc
              ∫ ω, (Z ω ^ 2 + 2 * Z ω * d + d ^ 2) ∂μ =
                  ∫ ω, Z ω ^ 2 ∂μ + ∫ ω, (2 * Z ω * d + d ^ 2) ∂μ := by
                    simpa only [Pi.add_apply, add_assoc] using
                      integral_add hsqInt (hcrossInt.add hconstSqInt)
              _ = (∫ ω, Z ω ^ 2 ∂μ) + (∫ ω, 2 * Z ω * d ∂μ) +
                  ∫ _, d ^ 2 ∂μ := by
                    rw [integral_add hcrossInt hconstSqInt]
                    ring
      _ = ProbabilityTheory.variance X μ + d ^ 2 := by
            have hvar := ProbabilityTheory.variance_eq_integral hX.aemeasurable
            have hcross : ∫ ω, 2 * Z ω * d ∂μ = 0 := by
              rw [show (fun ω => 2 * Z ω * d) = fun ω => (2 * d) * Z ω by
                funext ω; ring, integral_const_mul, hZmean]
              ring
            have hvarZ : ∫ ω, Z ω ^ 2 ∂μ = ProbabilityTheory.variance X μ := by
              simpa [Z] using hvar.symm
            rw [hvarZ, hcross, integral_const]
            simp [d]
  have hvarnonneg : 0 ≤ ProbabilityTheory.variance X μ := by
    dsimp [ProbabilityTheory.variance]
    exact ENNReal.toReal_nonneg
  have hdist₁ := mean_sub_median_le_sqrt_variance μ X hX median hmedianLower
  have hdist₂ := median_sub_mean_le_sqrt_variance μ X hX median hmedianUpper
  have hdist : |d| ≤ Real.sqrt (ProbabilityTheory.variance X μ) := by
    rw [abs_le]
    constructor <;> dsimp [d] <;> linarith
  have hdistSq : d ^ 2 ≤ ProbabilityTheory.variance X μ := by
    have hsqrtSq : (Real.sqrt (ProbabilityTheory.variance X μ)) ^ 2 =
        ProbabilityTheory.variance X μ := Real.sq_sqrt hvarnonneg
    calc
      d ^ 2 = |d| ^ 2 := by simp
      _ ≤ (Real.sqrt (ProbabilityTheory.variance X μ)) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg d) (Real.sqrt_nonneg _)).2 hdist
      _ = ProbabilityTheory.variance X μ := hsqrtSq
  rw [hsecond]
  linarith

/-- The positive-part scale selected by Paouris--Valettas is at most
`√2` times the standard deviation of a two-sided median. This is the
variance-sensitive input that turns their interval choice
`δ = 4 E[(X−median)⁺]` into `δ ≤ 4√2 σ`. -/
theorem median_pospart_expectation_le_sqrt_two_mul_sqrt_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (median : ℝ)
    (hmedianLower : (1 / 2 : ℝ) ≤ μ.real {ω | X ω ≤ median})
    (hmedianUpper : (1 / 2 : ℝ) ≤ μ.real {ω | median ≤ X ω}) :
    ∫ ω, max (X ω - median) 0 ∂μ ≤
      Real.sqrt 2 * Real.sqrt (ProbabilityTheory.variance X μ) := by
  let W : Ω → ℝ := fun ω => X ω - median
  let Y : Ω → ℝ := fun ω => max (W ω) 0
  have hW : MemLp W 2 μ := hX.sub (memLp_const _)
  have hY : MemLp Y 2 μ := hW.pos_part
  have hYint : Integrable Y μ := hY.integrable one_le_two
  have hWsq : Integrable (fun ω => W ω ^ 2) μ := hW.integrable_sq
  have hYsq : ∫ ω, Y ω ^ 2 ∂μ ≤ ∫ ω, W ω ^ 2 ∂μ := by
    apply integral_mono_ae (hY.integrable_sq) hWsq
    filter_upwards with ω
    dsimp [Y]
    by_cases hw : 0 ≤ W ω
    · rw [max_eq_left hw]
    · have hnw : W ω < 0 := lt_of_not_ge hw
      rw [max_eq_right hnw.le]
      nlinarith
  have hsecond := integral_sq_deviation_le_two_variance_of_median
    μ X hX median hmedianLower hmedianUpper
  have hYsq' : ∫ ω, Y ω ^ 2 ∂μ ≤ 2 * ProbabilityTheory.variance X μ := by
    exact hYsq.trans (by simpa [W] using hsecond)
  have h1 : MemLp (fun _ : Ω => (1 : ℝ)) 2 μ := memLp_const _
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩)
    (ae_of_all _ (fun _ => le_max_right _ _))
    (ae_of_all _ (fun _ => (show 0 ≤ (1 : ℝ) by norm_num)))
    (by simpa [Y] using hY) (by simpa using h1)
  have hmass : ∫ ω, (1 : ℝ) ^ (2 : ℝ) ∂μ = 1 := by simp
  have hproduct : ∫ ω, Y ω ∂μ ≤
      (∫ ω, Y ω ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
    calc
      (∫ ω, Y ω ∂μ) = ∫ ω, Y ω * (1 : ℝ) ∂μ := by simp
      _ ≤ (∫ ω, Y ω ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
          (∫ ω, (1 : ℝ) ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by
            simpa [Y] using hh
      _ = (∫ ω, Y ω ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := by simp [hmass]
  have hYsq'' : ∫ ω, Y ω ^ (2 : ℝ) ∂μ ≤
      2 * ProbabilityTheory.variance X μ := by
    calc
      ∫ ω, Y ω ^ (2 : ℝ) ∂μ = ∫ ω, Y ω ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with ω
        norm_num [Real.rpow_natCast]
      _ ≤ 2 * ProbabilityTheory.variance X μ := hYsq'
  have hvarnonneg : 0 ≤ ProbabilityTheory.variance X μ := by
    dsimp [ProbabilityTheory.variance]
    exact ENNReal.toReal_nonneg
  have hroot : (∫ ω, Y ω ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤
      Real.sqrt 2 * Real.sqrt (ProbabilityTheory.variance X μ) := by
    calc
      (∫ ω, Y ω ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) ≤
          (2 * ProbabilityTheory.variance X μ) ^ (1 / 2 : ℝ) := by
            apply Real.rpow_le_rpow (by positivity) hYsq''
            norm_num
      _ = Real.sqrt (2 * ProbabilityTheory.variance X μ) := by
            rw [Real.sqrt_eq_rpow]
      _ = Real.sqrt 2 * Real.sqrt (ProbabilityTheory.variance X μ) := by
            rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (∫ ω, max (X ω - median) 0 ∂μ) = ∫ ω, Y ω ∂μ := by
      apply integral_congr_ae
      filter_upwards with ω
      rfl
    _ ≤ (∫ ω, Y ω ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hproduct
    _ ≤ Real.sqrt 2 * Real.sqrt (ProbabilityTheory.variance X μ) := hroot

/-- The upper-tail Markov step used in the Paouris--Valettas median argument.
It bounds the mass above `median + δ` by the expectation of the positive part
divided by `δ`, with the positive-part expectation kept explicit. -/
theorem measure_upper_tail_le_pospart_markov {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : MemLp X 2 μ) (median δ : ℝ) (hδ : 0 < δ) :
    μ.real {ω | median + δ < X ω} ≤
      (∫ ω, max (X ω - median) 0 ∂μ) / δ := by
  let Y : Ω → ℝ := fun ω => max (X ω - median) 0
  have hY : MemLp (fun ω => X ω - median) 2 μ := by
    exact hX.sub (memLp_const median)
  have hYint : Integrable Y μ := by
    change Integrable (fun ω => max (X ω - median) 0) μ
    exact (hY.pos_part).integrable one_le_two
  have hnonneg : 0 ≤ᵐ[μ] Y := ae_of_all _ (fun ω => le_max_right _ _)
  have hmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnonneg hYint δ
  have hsubset : {ω | median + δ < X ω} ⊆ {ω | δ ≤ Y ω} := by
    intro ω hω
    change median + δ < X ω at hω
    change δ ≤ max (X ω - median) 0
    exact le_trans (by linarith) (le_max_left _ _)
  have hmono : μ.real {ω | median + δ < X ω} ≤ μ.real {ω | δ ≤ Y ω} :=
    MeasureTheory.measureReal_mono hsubset
  apply (le_div_iff₀ hδ).2
  calc
    μ.real {ω | median + δ < X ω} * δ =
        δ * μ.real {ω | median + δ < X ω} := by ring
    _ ≤ δ * μ.real {ω | δ ≤ Y ω} := mul_le_mul_of_nonneg_left hmono hδ.le
    _ ≤ ∫ ω, Y ω ∂μ := hmarkov
    _ = ∫ ω, max (X ω - median) 0 ∂μ := by rfl

/-- A right half-mass median and a Markov upper-tail bound force at least a
quarter of the measure into the adjacent interval. This is the measure step
used to lower-bound the right secant of the CDF. -/
theorem measure_median_interval_mass_ge_quarter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hXmeas : Measurable X) (median δ : ℝ) (hδ : 0 < δ)
    (hright : μ.real {ω | median < X ω} = 1 / 2)
    (hupper : μ.real {ω | median + δ < X ω} ≤ 1 / 4) :
    (1 / 4 : ℝ) ≤ μ.real {ω | median < X ω ∧ X ω ≤ median + δ} := by
  let I : Set Ω := {ω | median < X ω ∧ X ω ≤ median + δ}
  let B : Set Ω := {ω | median + δ < X ω}
  let A : Set Ω := {ω | median < X ω}
  have hI : MeasurableSet I := by
    dsimp [I]
    exact (measurableSet_lt measurable_const hXmeas).inter
      (measurableSet_le hXmeas measurable_const)
  have hB : MeasurableSet B := by
    dsimp [B]
    exact measurableSet_lt measurable_const hXmeas
  have hdisj : Disjoint I B := by
    rw [Set.disjoint_left]
    intro ω hωI hωB
    exact (not_lt_of_ge hωI.2) hωB
  have hunion : I ∪ B = A := by
    ext ω
    simp only [I, B, A, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · rintro (hωI | hωB)
      · exact hωI.1
      · linarith
    · intro hωA
      by_cases hcut : X ω ≤ median + δ
      · exact Or.inl ⟨hωA, hcut⟩
      · exact Or.inr (lt_of_not_ge hcut)
  have hsum := MeasureTheory.measureReal_union hdisj hB
    (measure_ne_top μ I) (measure_ne_top μ B)
  rw [hunion] at hsum
  rw [hright] at hsum
  have hB' : μ.real B ≤ 1 / 4 := by simpa [B] using hupper
  have hI' : μ.real I = 1 / 2 - μ.real B := by linarith [hsum]
  have hbound : (1 / 4 : ℝ) ≤ μ.real I := by rw [hI']; linarith
  simpa [I] using hbound

/-- The Paouris--Valettas Markov interval estimate with its interval length
chosen as four times the positive-part expectation. The right half-mass premise
is stated explicitly, as is positivity of that expectation. -/
theorem measure_median_interval_mass_ge_quarter_of_pospart {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hX : MemLp X 2 μ) (hXmeas : Measurable X) (median : ℝ)
    (hright : μ.real {ω | median < X ω} = 1 / 2)
    (hpos : 0 < ∫ ω, max (X ω - median) 0 ∂μ) :
    (1 / 4 : ℝ) ≤ μ.real {ω | median < X ω ∧
      X ω ≤ median + 4 * (∫ ω, max (X ω - median) 0 ∂μ)} := by
  let e : ℝ := ∫ ω, max (X ω - median) 0 ∂μ
  have he : 0 < e := by simpa [e] using hpos
  have hδ : 0 < 4 * e := by positivity
  have hupper := measure_upper_tail_le_pospart_markov μ X hX median (4 * e) hδ
  have hupper' : μ.real {ω | median + 4 * e < X ω} ≤ 1 / 4 := by
    calc
      μ.real {ω | median + 4 * e < X ω} ≤ e / (4 * e) := by
        simpa [e] using hupper
      _ = 1 / 4 := by field_simp
  have hinterval := measure_median_interval_mass_ge_quarter
    μ X hXmeas median (4 * e) hδ hright hupper'
  simpa [e] using hinterval

/-- The open interval retains the quarter-mass bound when the observable has
no atom at its right endpoint. This is the exact form used by the strict CDF. -/
theorem measure_median_open_interval_mass_ge_quarter {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → ℝ) (hXmeas : Measurable X) (median y : ℝ)
    (hmy : median < y)
    (hweak : (1 / 4 : ℝ) ≤ μ.real
      {ω | median < X ω ∧ X ω ≤ y})
    (hatom : μ.real {ω | X ω = y} = 0) :
    (1 / 4 : ℝ) ≤ μ.real {ω | median < X ω ∧ X ω < y} := by
  let I : Set Ω := {ω | median < X ω ∧ X ω ≤ y}
  let J : Set Ω := {ω | median < X ω ∧ X ω < y}
  let E : Set Ω := {ω | X ω = y}
  have hJ : MeasurableSet J := by
    dsimp [J]
    exact (measurableSet_lt measurable_const hXmeas).inter
      (measurableSet_lt hXmeas measurable_const)
  have hE : MeasurableSet E := by
    dsimp [E]
    exact measurableSet_eq_fun hXmeas measurable_const
  have hdisj : Disjoint J E := by
    rw [Set.disjoint_left]
    intro ω hωJ hωE
    exact (ne_of_lt hωJ.2) hωE
  have hunion : J ∪ E = I := by
    ext ω
    simp only [I, J, E, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro (hω | hω)
      · exact ⟨hω.1, hω.2.le⟩
      · rw [hω]
        exact ⟨by linarith, le_of_eq rfl⟩
    · rintro ⟨hω₁, hω₂⟩
      by_cases hlt : X ω < y
      · exact Or.inl ⟨hω₁, hlt⟩
      · exact Or.inr (le_antisymm hω₂ (le_of_not_gt hlt))
  have hsum := MeasureTheory.measureReal_union hdisj hE
    (measure_ne_top μ J) (measure_ne_top μ E)
  have hE' : μ.real E = 0 := by simpa [E] using hatom
  have hJ' : μ.real J = μ.real I := by
    rw [← hunion, hsum, hE', add_zero]
  have hweak' : (1 / 4 : ℝ) ≤ μ.real I := by simpa [I] using hweak
  rw [hJ']
  exact hweak'

/-- An atomless real random variable has a two-sided median. We obtain it by
applying the intermediate value theorem to the continuous CDF of its pushforward
law; the atomlessness hypothesis then identifies strict and weak half-mass
versions. -/
theorem exists_two_sided_median_of_null_levels
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hnull : ∀ x, μ {ω | X ω = x} = 0) :
    ∃ m : ℝ,
      μ.real {ω | X ω < m} = 1 / 2 ∧
      μ.real {ω | m < X ω} = 1 / 2 := by
  let ν : Measure ℝ := μ.map X
  have hnullν : ∀ x, ν {x} = 0 := by
    intro x
    rw [show ν = μ.map X by rfl, Measure.map_apply hX (measurableSet_singleton x)]
    simpa [Set.preimage, Set.mem_singleton_iff] using hnull x
  have hcont : Continuous (ProbabilityTheory.cdf ν) :=
    cdf_continuous_of_null_singletons ν hnullν
  have hatBot := ProbabilityTheory.tendsto_cdf_atBot ν
  have hatTop := ProbabilityTheory.tendsto_cdf_atTop ν
  have hsmall : ∀ᶠ x : ℝ in atBot, ProbabilityTheory.cdf ν x < 1 / 2 :=
    hatBot.eventually (Iio_mem_nhds (by norm_num))
  have hlarge : ∀ᶠ x : ℝ in atTop, 1 / 2 < ProbabilityTheory.cdf ν x :=
    hatTop.eventually (Ioi_mem_nhds (by norm_num))
  obtain ⟨a, ha⟩ := (eventually_atBot.mp hsmall)
  obtain ⟨b, hb⟩ := (eventually_atTop.mp hlarge)
  have hab : a ≤ b := by
    by_contra h
    have hba : b ≤ a := le_of_not_ge h
    have hmono := (ProbabilityTheory.monotone_cdf ν) hba
    have ha' := ha a le_rfl
    have hb' := hb b le_rfl
    linarith
  have hvalue : (1 / 2 : ℝ) ∈ Set.Icc
      (ProbabilityTheory.cdf ν a) (ProbabilityTheory.cdf ν b) := by
    constructor
    · exact le_of_lt (ha a le_rfl)
    · exact le_of_lt (hb b le_rfl)
  obtain ⟨m, hmab, hmedianCdf⟩ :=
    intermediate_value_Icc hab hcont.continuousOn hvalue
  have hmedianIic : ν.real (Set.Iic m) = 1 / 2 := by
    rw [← ProbabilityTheory.cdf_eq_real ν m, hmedianCdf]
  have hmedianIio : ν.real (Set.Iio m) = 1 / 2 := by
    have hdecomp : Set.Iic m = Set.Iio m ∪ {m} := by
      ext x
      simp only [Set.mem_Iic, Set.mem_union, Set.mem_Iio,
        Set.mem_singleton_iff]
      constructor
      · intro hx
        by_cases hxm : x = m
        · exact Or.inr hxm
        · exact Or.inl (lt_of_le_of_ne hx hxm)
      · rintro (hx | hx)
        · exact le_of_lt hx
        · rw [hx]
    have hdisj : Disjoint (Set.Iio m) ({m} : Set ℝ) := by
      rw [Set.disjoint_left]
      intro x hxI hxM
      simp only [Set.mem_singleton_iff] at hxM
      change x < m at hxI
      subst x
      exact (lt_irrefl _ hxI)
    have hsum := MeasureTheory.measureReal_union hdisj (measurableSet_singleton m)
      (measure_ne_top ν _) (measure_ne_top ν _)
    have hnullReal : ν.real {m} = 0 := by
      rw [Measure.real_def, hnullν m, ENNReal.toReal_zero]
    rw [hdecomp, hsum, hnullReal, add_zero] at hmedianIic
    exact hmedianIic
  have hstrict : ν.real (Set.Ioi m) = 1 / 2 := by
    have hpartition : Set.Iic m ∪ Set.Ioi m = Set.univ := by
      ext x
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ioi, Set.mem_univ]
      constructor
      · intro _; trivial
      · intro _
        by_cases hxm : x ≤ m
        · exact Or.inl hxm
        · exact Or.inr (lt_of_not_ge hxm)
    have hdisj : Disjoint (Set.Iic m) (Set.Ioi m) := by
      rw [Set.disjoint_left]
      intro x h₁ h₂
      change x ≤ m at h₁
      change m < x at h₂
      exact (not_lt_of_ge h₁) h₂
    have hsum := MeasureTheory.measureReal_union hdisj measurableSet_Ioi
      (measure_ne_top ν _) (measure_ne_top ν _)
    have htotal : ν.real Set.univ = 1 := by simp [ν]
    rw [hpartition, htotal] at hsum
    rw [hmedianIic] at hsum
    linarith
  have hmapIio : ν.real (Set.Iio m) = μ.real {ω | X ω < m} := by
    change (μ.map X).real (Set.Iio m) = μ.real {ω | X ω < m}
    rw [Measure.real_def, Measure.real_def,
      Measure.map_apply hX measurableSet_Iio]
    rfl
  have hmapIoi : ν.real (Set.Ioi m) = μ.real {ω | m < X ω} := by
    change (μ.map X).real (Set.Ioi m) = μ.real {ω | m < X ω}
    rw [Measure.real_def, Measure.real_def,
      Measure.map_apply hX measurableSet_Ioi]
    rfl
  exact ⟨m, hmapIio ▸ hmedianIio, hmapIoi ▸ hstrict⟩

/-- Positive upper-median mass forces the positive-part scale to be strictly
positive. This rules out division by a vanishing interval length in the PV
secant argument. -/
theorem pospart_integral_pos_of_positive_upper_median
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : MemLp X 2 μ)
    (median : ℝ) (hupper : 0 < μ.real {ω | median < X ω}) :
    0 < ∫ ω, max (X ω - median) 0 ∂μ := by
  let Y : Ω → ℝ := fun ω => max (X ω - median) 0
  let B : Set Ω := {ω | median < X ω}
  have hshift : MemLp (fun ω => X ω - median) 2 μ := hX.sub (memLp_const median)
  have hY : MemLp Y 2 μ := by
    change MemLp (fun ω => max (X ω - median) 0) 2 μ
    exact hshift.pos_part
  have hYint : Integrable Y μ := hY.integrable one_le_two
  have hBpos : 0 < μ B := by
    by_contra hnot
    have hzero : μ B = 0 := le_antisymm (le_of_not_gt hnot) bot_le
    have hreal : μ.real B = 0 := by
      simp [Measure.real_def, hzero]
    rw [hreal] at hupper
    norm_num at hupper
  have hsub : B ⊆ Function.support Y := by
    intro ω hω
    change median < X ω at hω
    have hYpos : 0 < Y ω := by
      dsimp [Y]
      have hp : 0 < X ω - median := by linarith
      rw [max_eq_left hp.le]
      exact hp
    exact (Function.mem_support.mpr (ne_of_gt hYpos))
  have hsupp : 0 < μ (Function.support Y) :=
    lt_of_lt_of_le hBpos (measure_mono hsub)
  have hYnonneg : 0 ≤ᵐ[μ] Y := ae_of_all _ fun _ => le_max_right _ _
  exact (integral_pos_iff_support_of_nonneg_ae hYnonneg hYint).2 hsupp

end BrownianSharp.Concentration
