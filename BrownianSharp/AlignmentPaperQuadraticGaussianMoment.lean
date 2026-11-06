import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic
import BrownianSharp.GaussianCDFCalculus
import BrownianSharp.Ehrhard
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import BrownianSharp.AlignmentPaperGaussianDilation

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Pointwise Topology

namespace BrownianSharp.AlignmentPaperQuadraticGaussianMoment

/-- The exact scalar quadratic exponential moment of a standard normal. -/
theorem integral_exp_mul_sq_standardGaussian {c : ℝ} (_hc0 : 0 ≤ c) (hc1 : c < 1 / 2) :
    Integrable (fun x : ℝ => Real.exp (c * x ^ 2)) (gaussianReal 0 1) ∧
      (∫ x, Real.exp (c * x ^ 2) ∂gaussianReal 0 1) = Real.sqrt ((1 - 2 * c)⁻¹) := by
  have hbase : 0 < 1 - 2 * c := by linarith
  let v : ℝ≥0 := ⟨(1 - 2 * c)⁻¹, (inv_pos.mpr hbase).le⟩
  have hv : (v : ℝ) = (1 - 2 * c)⁻¹ := rfl
  have hvne : v ≠ 0 := by
    apply ne_of_gt
    change 0 < (1 - 2 * c)⁻¹
    positivity
  have hpdf (x : ℝ) : gaussianPDFReal 0 1 x * Real.exp (c * x ^ 2) =
      Real.sqrt ((1 - 2 * c)⁻¹) * gaussianPDFReal 0 v x := by
    simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    have hexp_prod : Real.exp (-x ^ 2 / 2) * Real.exp (c * x ^ 2) =
        Real.exp (-x ^ 2 / 2 + c * x ^ 2) := by rw [← Real.exp_add]
    rw [mul_assoc, hexp_prod]
    have hexp : -x ^ 2 / 2 + c * x ^ 2 =
        -x ^ 2 / (2 * ((1 - 2 * c)⁻¹)) := by
      field_simp
      ring
    rw [hexp, hv, Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi)]
    field_simp
  have hvol : Integrable (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp (c * x ^ 2)) := by
    rw [show (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp (c * x ^ 2)) =
      fun x => Real.sqrt ((1 - 2 * c)⁻¹) * gaussianPDFReal 0 v x from by
        funext x; exact hpdf x]
    exact (integrable_gaussianPDFReal 0 v).const_mul _
  have hInt : Integrable (fun x : ℝ => Real.exp (c * x ^ 2)) (gaussianReal 0 1) := by
    rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
    rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun x => by simp [gaussianPDF, ENNReal.ofReal_lt_top])]
    simpa [toReal_gaussianPDF, NNReal.smul_def] using hvol
  refine ⟨hInt, ?_⟩
  rw [integral_gaussianReal_eq_integral_smul (μ := 0) (v := 1) (by norm_num)]
  have hfun : (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp (c * x ^ 2)) =
      fun x => Real.sqrt ((1 - 2 * c)⁻¹) * gaussianPDFReal 0 v x := by
    funext x; exact hpdf x
  simp only [smul_eq_mul]
  rw [hfun, integral_const_mul, integral_gaussianPDFReal_eq_one 0 hvne]
  simp

/-- Finite-product quadratic exponential moment, obtained by the actual finite-product
integral theorem from the scalar identity. -/
theorem integral_exp_mul_sum_sq_productGaussian {ι : Type*} [Fintype ι]
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1 / 2) :
    Integrable (fun x : ι → ℝ => Real.exp (c * ∑ i, x i ^ 2))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) ∧
      (∫ x, Real.exp (c * ∑ i, x i ^ 2) ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
        (Real.sqrt ((1 - 2 * c)⁻¹)) ^ Fintype.card ι := by
  let g : ℝ → ℝ := fun x => Real.exp (c * x ^ 2)
  have hs := integral_exp_mul_sq_standardGaussian hc0 hc1
  have hprod : Integrable (fun x : ι → ℝ => ∏ i, g (x i))
      (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    exact MeasureTheory.Integrable.fintype_prod (fun _ => hs.1)
  have hrewrite : (fun x : ι → ℝ => Real.exp (c * ∑ i, x i ^ 2)) =
      fun x => ∏ i, g (x i) := by
    funext x
    simp [g, Real.exp_sum, Finset.mul_sum]
  refine ⟨?_, ?_⟩
  · rw [hrewrite]
    exact hprod
  · rw [hrewrite, MeasureTheory.integral_fintype_prod_eq_pow]
    simp [g, hs.2]

/-- Chernoff bound for the squared Euclidean radius of a finite standard Gaussian
vector. This is the concrete finite-dimensional tail estimate used in the
balanced-ball enlargement argument. -/
theorem productGaussian_sq_radius_tail {ι : Type*} [Fintype ι]
    {c R : ℝ} (hc0 : 0 < c) (hc1 : c < 1 / 2) :
    (Measure.pi (fun _ : ι => gaussianReal 0 1))
        {x : ι → ℝ | R ^ 2 ≤ ∑ i, x i ^ 2} ≤
      ENNReal.ofReal (Real.exp (-c * R ^ 2) *
        (Real.sqrt ((1 - 2 * c)⁻¹)) ^ Fintype.card ι) := by
  have hm := integral_exp_mul_sum_sq_productGaussian (ι := ι) hc0.le hc1
  let g : (ι → ℝ) → ℝ := fun x => Real.exp (c * (∑ i, x i ^ 2 - R ^ 2))
  have hfun : g = fun x => Real.exp (-c * R ^ 2) *
      Real.exp (c * ∑ i, x i ^ 2) := by
    funext x
    dsimp [g]
    rw [← Real.exp_add]
    congr 1
    ring
  have hgi : Integrable g (Measure.pi (fun _ : ι => gaussianReal 0 1)) := by
    rw [hfun]
    exact hm.1.const_mul _
  have hnonneg : 0 ≤ᵐ[Measure.pi (fun _ : ι => gaussianReal 0 1)] g :=
    ae_of_all _ (fun x => (Real.exp_pos _).le)
  have hMarkov := hgi.measure_le_integral hnonneg (s := {x | R ^ 2 ≤ ∑ i, x i ^ 2})
    (by
      intro x hx
      change R ^ 2 ≤ ∑ i, x i ^ 2 at hx
      dsimp [g]
      have harg : 0 ≤ c * (∑ i, x i ^ 2 - R ^ 2) := by
        apply mul_nonneg hc0.le
        linarith
      simpa using (Real.exp_le_exp.mpr harg))
  have hEval : (∫ x, g x ∂Measure.pi (fun _ : ι => gaussianReal 0 1)) =
      Real.exp (-c * R ^ 2) * (Real.sqrt ((1 - 2 * c)⁻¹)) ^ Fintype.card ι := by
    rw [hfun, integral_const_mul, hm.2]
  rw [hEval] at hMarkov
  exact hMarkov

/-- A unit interval in the positive half-line carries at least its minimum
standard Gaussian density there. -/
theorem standardGaussian_unit_interval_lower {u : ℝ} (hu : 0 ≤ u) :
    gaussianReal 0 1 (Set.Icc u (u + 1)) ≥
      ENNReal.ofReal (Real.exp (-(u + 1) ^ 2 / 2) / Real.sqrt (2 * Real.pi)) := by
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have hpdf : ∀ x ∈ Set.Icc u (u + 1),
      Real.exp (-(u + 1) ^ 2 / 2) / Real.sqrt (2 * Real.pi) ≤ gaussianPDFReal 0 1 x := by
    intro x hx
    simp only [gaussianPDFReal_def, NNReal.coe_one, mul_one, sub_zero]
    have hx0 : 0 ≤ x := le_trans hu hx.1
    have hxupper : x ^ 2 ≤ (u + 1) ^ 2 := by
      nlinarith [hx.2]
    have hexp : Real.exp (-(u + 1) ^ 2 / 2) ≤ Real.exp (-(x - 0) ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    have hroot : 0 < Real.sqrt (2 * Real.pi) := by positivity
    have hmul : Real.sqrt (2 * Real.pi)⁻¹ * Real.exp (-(u + 1) ^ 2 / 2) ≤
        Real.sqrt (2 * Real.pi)⁻¹ * Real.exp (-(x - 0) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    simpa [div_eq_mul_inv, mul_comm] using hmul
  have hfinite : volume (Set.Icc u (u + 1)) ≠ ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hmono := setIntegral_mono_on
    (integrableOn_const hfinite)
    ((integrable_gaussianPDFReal 0 1).integrableOn)
    measurableSet_Icc hpdf
  have hconst : (∫ x in Set.Icc u (u + 1),
      Real.exp (-(u + 1) ^ 2 / 2) / Real.sqrt (2 * Real.pi) ∂volume) =
      Real.exp (-(u + 1) ^ 2 / 2) / Real.sqrt (2 * Real.pi) := by
    rw [setIntegral_const]
    simp [Real.volume_Icc]
  have hresult : (∫ x in Set.Icc u (u + 1), gaussianPDFReal 0 1 x ∂volume) ≥
      Real.exp (-(u + 1) ^ 2 / 2) / Real.sqrt (2 * Real.pi) := by
    rw [← hconst]
    exact hmono
  exact ENNReal.ofReal_le_ofReal hresult

/-- Quadratic decay with the stronger exponent eventually dominates a Gaussian
unit-interval lower bound. The threshold is explicit in the fixed parameters. -/
theorem exp_quadratic_eventually_le {a c A B : ℝ} (ha : 0 ≤ a)
    (hc : a ^ 2 / 2 < c) (hA : 0 < A) (hB : 0 < B) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀,
      A * Real.exp (-c * R ^ 2) ≤ B * Real.exp (-(a * R + 1) ^ 2 / 2) := by
  let δ := c - a ^ 2 / 2
  let C := Real.log (A / B) + 1 / 2
  let R₀ := max 1 (max (2 * a / δ) (2 * |C| / δ))
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hR0 : 0 ≤ R₀ := by dsimp [R₀]; positivity
  refine ⟨R₀, ?_⟩
  intro R hR
  have hR1 : 1 ≤ R := le_trans (le_max_left _ _) hR
  have hR2 : 2 * a / δ ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have hR3 : 2 * |C| / δ ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans hR)
  have hδa : 2 * a ≤ R * δ := (div_le_iff₀ hδ).mp hR2
  have hδC : 2 * |C| ≤ R * δ := (div_le_iff₀ hδ).mp hR3
  have hRnonneg : 0 ≤ R := le_trans (by norm_num) hR1
  have hdelta : C ≤ δ * R ^ 2 - a * R := by
    have hmul := mul_le_mul_of_nonneg_right hδa hRnonneg
    have hmulC := mul_le_mul_of_nonneg_right hδC hRnonneg
    have habs : C ≤ |C| := le_abs_self C
    nlinarith [mul_nonneg hδ.le (sq_nonneg R)]
  have hlogs : Real.log A - c * R ^ 2 ≤
      Real.log B - (a * R + 1) ^ 2 / 2 := by
    dsimp [δ, C] at hdelta
    have hlogratio : Real.log (A / B) = Real.log A - Real.log B := by
      rw [Real.log_div hA.ne' hB.ne']
    rw [hlogratio] at hdelta
    nlinarith [sq_nonneg (a * R)]
  rw [← Real.exp_log hA, ← Real.exp_log hB]
  rw [← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by nlinarith [hlogs])

/-- For any fixed `0<a<1`, the finite-dimensional standard Gaussian mass of the
Euclidean radius-`R` ball eventually dominates the one-dimensional Gaussian
CDF at `aR`. This is the balanced-ball quantile lower bound. -/
theorem productGaussian_ball_mass_ge_cdf_eventually {ι : Type*} [Fintype ι] [Nonempty ι]
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀,
      (Measure.pi (fun _ : ι => gaussianReal 0 1)).real
        {x : ι → ℝ | ∑ i, x i ^ 2 ≤ R ^ 2} ≥ BrownianSharp.Concentration.standardGaussianCDF (a * R) := by
  classical
  let d := Fintype.card ι
  let c := (1 + a ^ 2) / 4
  let A := (Real.sqrt ((1 - 2 * c)⁻¹)) ^ d
  let B := 1 / Real.sqrt (2 * Real.pi)
  have hgap : a ^ 2 / 2 < c := by dsimp [c]; nlinarith
  have hc : c < 1 / 2 := by dsimp [c]; nlinarith [ha1]
  have hbase : 0 < 1 - 2 * c := by linarith [hc]
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨R₀, hR₀⟩ := exp_quadratic_eventually_le ha0.le hgap hA hB
  refine ⟨max R₀ 1, ?_⟩
  intro R hR
  have hRbase : R₀ ≤ R := (le_max_left _ _).trans hR
  have hRpos : 0 ≤ R := le_trans (by norm_num : (0 : ℝ) ≤ 1) ((le_max_right _ _).trans hR)
  let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
  have hprob : IsProbabilityMeasure μ := by infer_instance
  let ball : Set (ι → ℝ) := {x | ∑ i, x i ^ 2 ≤ R ^ 2}
  let comp : Set (ι → ℝ) := ballᶜ
  let q := a * R
  have hq : 0 ≤ q := mul_nonneg ha0.le hRpos
  have hstrength : μ {x : ι → ℝ | R ^ 2 ≤ ∑ i, x i ^ 2} ≤
      ENNReal.ofReal (B * Real.exp (-(q + 1) ^ 2 / 2)) := by
    have htail := productGaussian_sq_radius_tail (ι := ι) (c := c) (R := R)
      (by dsimp [c]; positivity) hc
    have hcompare := hR₀ R hRbase
    have hcompareENN := ENNReal.ofReal_le_ofReal hcompare
    have htailEq : Real.exp (-c * R ^ 2) *
        (Real.sqrt ((1 - 2 * c)⁻¹)) ^ Fintype.card ι =
        A * Real.exp (-c * R ^ 2) := by dsimp [A, d]; ring
    calc
      μ {x : ι → ℝ | R ^ 2 ≤ ∑ i, x i ^ 2} ≤
          ENNReal.ofReal (Real.exp (-c * R ^ 2) *
            (Real.sqrt ((1 - 2 * c)⁻¹)) ^ Fintype.card ι) := htail
      _ = ENNReal.ofReal (A * Real.exp (-c * R ^ 2)) := by rw [htailEq]
      _ ≤ ENNReal.ofReal (B * Real.exp (-(a * R + 1) ^ 2 / 2)) := hcompareENN
  have hcompENN : μ comp ≤ ENNReal.ofReal (B * Real.exp (-(q + 1) ^ 2 / 2)) := by
    apply le_trans (measure_mono ?_) hstrength
    intro x hx
    simp only [comp, ball, Set.mem_compl_iff, Set.mem_setOf_eq] at hx ⊢
    linarith
  have hcompFinite : μ comp ≠ ⊤ := ne_top_of_le_ne_top (by simp)
    (measure_mono (Set.subset_univ comp))
  have hcompReal : μ.real comp ≤ B * Real.exp (-(q + 1) ^ 2 / 2) := by
    calc
      μ.real comp = (μ comp).toReal := rfl
      _ ≤ (ENNReal.ofReal (B * Real.exp (-(q + 1) ^ 2 / 2))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hcompENN
      _ = B * Real.exp (-(q + 1) ^ 2 / 2) := ENNReal.toReal_ofReal (by positivity)
  have hinterval := standardGaussian_unit_interval_lower hq
  have hintervalFinite : gaussianReal 0 1 (Set.Icc q (q + 1)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ _))
  have hintervalReal : (gaussianReal 0 1).real (Set.Icc q (q + 1)) ≥
      B * Real.exp (-(q + 1) ^ 2 / 2) := by
    change B * Real.exp (-(q + 1) ^ 2 / 2) ≤
      ((gaussianReal 0 1) (Set.Icc q (q + 1))).toReal
    have h := ENNReal.toReal_mono hintervalFinite hinterval
    rw [ENNReal.toReal_ofReal (by positivity)] at h
    have hconst : Real.exp (-(q + 1) ^ 2 / 2) / Real.sqrt (2 * Real.pi) =
        B * Real.exp (-(q + 1) ^ 2 / 2) := by dsimp [B]; ring
    rw [← hconst]
    exact h
  have hsubset : Set.Icc q (q + 1) ⊆ (Set.Iio q)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Iio]
    exact not_lt.mpr hx.1
  have hIioComp : (gaussianReal 0 1).real (Set.Iio q)ᶜ =
      1 - BrownianSharp.Concentration.standardGaussianCDF q := by
    have hsum := measureReal_add_measureReal_compl
      (μ := gaussianReal 0 1) (s := Set.Iio q) measurableSet_Iio
    have hcdf : BrownianSharp.Concentration.standardGaussianCDF q =
        (gaussianReal 0 1).real (Set.Iio q) := rfl
    have huniv : (gaussianReal 0 1).real Set.univ = 1 := by simp
    have hsum' : BrownianSharp.Concentration.standardGaussianCDF q +
        (gaussianReal 0 1).real (Set.Iio q)ᶜ = 1 := by
      rw [hcdf]
      rw [huniv] at hsum
      exact hsum
    linarith
  have hIioLower : B * Real.exp (-(q + 1) ^ 2 / 2) ≤
      1 - BrownianSharp.Concentration.standardGaussianCDF q := by
    calc
      _ ≤ (gaussianReal 0 1).real (Set.Icc q (q + 1)) := hintervalReal
      _ ≤ (gaussianReal 0 1).real (Set.Iio q)ᶜ :=
        MeasureTheory.measureReal_mono hsubset (measure_ne_top _ _)
      _ = _ := hIioComp
  have hBallMeas : MeasurableSet ball := by
    dsimp [ball]
    apply measurableSet_le
    · exact Finset.measurable_sum _ (fun i hi => (measurable_pi_apply i).pow_const 2)
    · exact measurable_const
  have hballAdd : μ.real ball + μ.real comp = 1 := by
    have hsum := measureReal_add_measureReal_compl (μ := μ) (s := ball) hBallMeas
    have huniv : μ.real Set.univ = 1 := by simp [μ]
    simpa [comp, huniv] using hsum
  have hCDF : μ.real ball ≥ BrownianSharp.Concentration.standardGaussianCDF q := by
    have hballEq : μ.real ball = 1 - μ.real comp := by linarith [hballAdd]
    rw [hballEq]
    linarith
  simpa [q] using hCDF

/-- The preceding mass comparison implies the matching Gaussian quantile lower
bound whenever the ball masses are interior probabilities. -/
theorem productGaussian_ball_quantile_lower_eventually {ι : Type*} [Fintype ι] [Nonempty ι]
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hinterior : ∀ R : ℝ, 0 < R → 0 < (Measure.pi (fun _ : ι => gaussianReal 0 1)).real
        {x : ι → ℝ | ∑ i, x i ^ 2 ≤ R ^ 2} ∧
      (Measure.pi (fun _ : ι => gaussianReal 0 1)).real
        {x : ι → ℝ | ∑ i, x i ^ 2 ≤ R ^ 2} < 1) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀,
      BrownianSharp.Concentration.standardGaussianQuantile
        ((Measure.pi (fun _ : ι => gaussianReal 0 1)).real
          {x : ι → ℝ | ∑ i, x i ^ 2 ≤ R ^ 2}) ≥ a * R := by
  obtain ⟨R₀, hmass⟩ := productGaussian_ball_mass_ge_cdf_eventually (ι := ι) ha0 ha1
  refine ⟨max R₀ 1, ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le (by
    have : (0 : ℝ) < 1 := by norm_num
    exact lt_of_lt_of_le this (le_max_right R₀ 1)) hR
  have hprob := hinterior R hRpos
  have hquant := BrownianSharp.Concentration.standardGaussianCDF_standardGaussianQuantile
    hprob.1 hprob.2
  apply (BrownianSharp.Concentration.standardGaussianCDF_strictMono.le_iff_le).mp
  rw [hquant]
  exact hmass R (le_trans (le_max_left R₀ 1) hR)

/-- Large-radius ball quantile growth for a standard Gaussian on any
finite-dimensional Hilbert space. The basis expansion identifies each ball
with the chi-square event in product Gaussian coordinates. -/
theorem finiteHilbertStdGaussian_isOpenPosMeasure
    {E ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (b : OrthonormalBasis ι ℝ E) :
    MeasureTheory.Measure.IsOpenPosMeasure (ProbabilityTheory.stdGaussian E) := by
  classical
  let μ := Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)
  let e : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] E :=
    (EuclideanSpace.basisFun ι ℝ).equiv b (Equiv.refl ι)
  let f : (ι → ℝ) → E := fun x => ∑ i, x i • b i
  have hf : f = fun x => e (WithLp.toLp 2 x) := by
    funext x
    dsimp [f, e]
    rw [← b.equiv_apply_euclideanSpace]
  have hgaussOpen : MeasureTheory.Measure.IsOpenPosMeasure
      (ProbabilityTheory.gaussianReal 0 1) := by
    have hvol : (volume : Measure ℝ) ≪ ProbabilityTheory.gaussianReal 0 1 :=
      ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)
    exact hvol.isOpenPosMeasure
  letI : MeasureTheory.Measure.IsOpenPosMeasure
      (ProbabilityTheory.gaussianReal 0 1) := hgaussOpen
  have hpiOpen : MeasureTheory.Measure.IsOpenPosMeasure μ := inferInstance
  have hmapOpen : MeasureTheory.Measure.IsOpenPosMeasure (μ.map f) := by
    have hfcont : Continuous f := by
      rw [hf]
      exact e.continuous.comp (PiLp.continuous_toLp 2 (fun _ : ι => ℝ))
    apply hfcont.isOpenPosMeasure_map
    intro y
    refine ⟨(e.symm y).ofLp, ?_⟩
    rw [hf]
    change e (WithLp.toLp 2 ((e.symm y).ofLp)) = y
    simp
  rw [ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis b]
  exact hmapOpen

theorem finiteHilbertStdGaussian_ball_quantile_lower_eventually
    {E ι : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (b : OrthonormalBasis ι ℝ E) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ R₀ : ℝ, ∀ R ≥ R₀,
      0 < (ProbabilityTheory.stdGaussian E).real (Metric.closedBall 0 R) ∧
      (ProbabilityTheory.stdGaussian E).real (Metric.closedBall 0 R) < 1 ∧
      a * R ≤ BrownianSharp.Concentration.standardGaussianQuantile
        ((ProbabilityTheory.stdGaussian E).real (Metric.closedBall 0 R)) := by
  classical
  let μ := Measure.pi (fun _ : ι => ProbabilityTheory.gaussianReal 0 1)
  let B := fun R : ℝ => {x : ι → ℝ | ∑ i, x i ^ 2 ≤ R ^ 2}
  let e : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] E :=
    (EuclideanSpace.basisFun ι ℝ).equiv b (Equiv.refl ι)
  let f : (ι → ℝ) → E := fun x => ∑ i, x i • b i
  have hf : f = fun x => e (WithLp.toLp 2 x) := by
    funext x
    dsimp [f, e]
    rw [← b.equiv_apply_euclideanSpace]
  have hnorm (x : ι → ℝ) : ‖f x‖ ^ 2 = ∑ i, x i ^ 2 := by
    rw [hf, e.norm_map, EuclideanSpace.real_norm_sq_eq]
  have hgaussOpen : MeasureTheory.Measure.IsOpenPosMeasure
      (ProbabilityTheory.gaussianReal 0 1) := by
    have hvol : (volume : Measure ℝ) ≪ ProbabilityTheory.gaussianReal 0 1 :=
      ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 (by norm_num)
    exact hvol.isOpenPosMeasure
  letI : MeasureTheory.Measure.IsOpenPosMeasure
      (ProbabilityTheory.gaussianReal 0 1) := hgaussOpen
  have hpiOpen : MeasureTheory.Measure.IsOpenPosMeasure μ := inferInstance
  have hmapOpen : MeasureTheory.Measure.IsOpenPosMeasure (μ.map f) := by
    have hfcont : Continuous f := by
      rw [hf]
      exact e.continuous.comp (PiLp.continuous_toLp 2 (fun _ : ι => ℝ))
    apply hfcont.isOpenPosMeasure_map
    intro y
    refine ⟨(e.symm y).ofLp, ?_⟩
    rw [hf]
    change e (WithLp.toLp 2 ((e.symm y).ofLp)) = y
    simpa using e.apply_symm_apply y
  have hstdOpen : MeasureTheory.Measure.IsOpenPosMeasure
      (ProbabilityTheory.stdGaussian E) := by
    rw [ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis b]
    exact hmapOpen
  letI : MeasureTheory.Measure.IsOpenPosMeasure (ProbabilityTheory.stdGaussian E) := hstdOpen
  have hinterior : ∀ R : ℝ, 0 < R →
      0 < (ProbabilityTheory.stdGaussian E).real (Metric.closedBall 0 R) ∧
      (ProbabilityTheory.stdGaussian E).real (Metric.closedBall 0 R) < 1 := by
    intro R hR
    have hballpos : 0 < (ProbabilityTheory.stdGaussian E) (Metric.closedBall 0 R) := by
      apply lt_of_lt_of_le
        ((Metric.isOpen_ball (x := (0 : E)) (ε := R)).measure_pos
          (μ := ProbabilityTheory.stdGaussian E) ⟨0, Metric.mem_ball_self hR⟩)
      exact measure_mono Metric.ball_subset_closedBall
    let i₀ : ι := Classical.choice ‹Nonempty ι›
    have hbi : ‖b i₀‖ = 1 := b.orthonormal.1 i₀
    let y : E := (R + 1) • b i₀
    have hy : R < ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < R + 1), hbi]
      linarith
    have hcomplpos : 0 < (ProbabilityTheory.stdGaussian E) (Metric.closedBall (0 : E) R)ᶜ :=
      Metric.isClosed_closedBall.isOpen_compl.measure_pos (μ := ProbabilityTheory.stdGaussian E)
        ⟨y, by simp [Metric.mem_closedBall, dist_zero_right, not_le_of_gt hy]⟩
    have hsum := MeasureTheory.measureReal_add_measureReal_compl
      (μ := ProbabilityTheory.stdGaussian E) (s := Metric.closedBall (0 : E) R)
      Metric.isClosed_closedBall.measurableSet
    have htotal : (ProbabilityTheory.stdGaussian E).real Set.univ = 1 := by simp
    rw [htotal] at hsum
    constructor
    · exact ENNReal.toReal_pos hballpos.ne' (measure_ne_top _ _)
    · have hc : 0 < (ProbabilityTheory.stdGaussian E).real (Metric.closedBall (0 : E) R)ᶜ :=
        ENNReal.toReal_pos hcomplpos.ne' (measure_ne_top _ _)
      linarith
  have hmass (R : ℝ) (hR : 0 < R) :
      (ProbabilityTheory.stdGaussian E).real (Metric.closedBall (0 : E) R) = μ.real (B R) := by
    rw [ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis b]
    change ((μ.map f) (Metric.closedBall (0 : E) R)).toReal = _
    have hpre : f ⁻¹' Metric.closedBall (0 : E) R = B R := by
      ext x
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
      have hsquare := hnorm x
      constructor
      · intro hx
        change ‖f x‖ ≤ R at hx
        change ∑ i, x i ^ 2 ≤ R ^ 2
        nlinarith [norm_nonneg (f x), sq_nonneg (‖f x‖ - R)]
      · intro hx
        change ∑ i, x i ^ 2 ≤ R ^ 2 at hx
        change ‖f x‖ ≤ R
        nlinarith [norm_nonneg (f x), sq_nonneg R]
    rw [MeasureTheory.Measure.map_apply (by fun_prop : Measurable f)
      Metric.isClosed_closedBall.measurableSet, hpre]
    rfl
  obtain ⟨R₀, hquant⟩ := productGaussian_ball_quantile_lower_eventually
    (ι := ι) ha0 ha1 (fun R hR => by
      have hp := hinterior R hR
      rw [hmass R hR] at hp
      exact hp)
  refine ⟨max R₀ 1, ?_⟩
  intro R hR
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (le_trans (le_max_right R₀ 1) hR)
  have hi := hinterior R hRpos
  have hi' : 0 < μ.real (B R) ∧ μ.real (B R) < 1 := by
    rw [← hmass R hRpos]
    exact hi
  have hq := hquant R (le_trans (le_max_left R₀ 1) hR)
  rw [hmass R hRpos]
  exact ⟨hi'.1, hi'.2, hq⟩

/-- Finite-radius balanced Ehrhard step. It lifts the quantile of the actual
Gaussian `R•K` ball to a lower bound for the mass of `A+t•K`, when `A` is a
convex set containing the origin. The exact enlargement limit is obtained by
letting `R` tend to infinity and the ball quantile ratio tend to one. -/
theorem gaussianEhrhard_finiteRadius_dilation
    {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) [IsFiniteMeasure μ]
    (hEhrhard : BrownianSharp.Concentration.GaussianEhrhard E μ)
    (A K : Set E) (hAconv : Convex ℝ A) (hKconv : Convex ℝ K)
    (hA0 : (0 : E) ∈ A) (hK0 : (0 : E) ∈ K)
    {t R a : ℝ} (ht : 0 < t) (hR : 0 < R) (ha : 0 < a) (ha1 : a < 1)
    (hAm : μ.real A ∈ Set.Ioo (0 : ℝ) 1)
    (hRm : μ.real (R • K) ∈ Set.Ioo (0 : ℝ) 1)
    (hRq : a * R ≤ BrownianSharp.Concentration.standardGaussianQuantile (μ.real (R • K))) :
    BrownianSharp.Concentration.standardGaussianCDF
        ((R / (R + t)) * BrownianSharp.Concentration.standardGaussianQuantile (μ.real A) +
          (t / (R + t)) * (a * R)) ≤ μ.real (A + t • K) := by
  classical
  let lam : ℝ := R / (R + t)
  let beta : ℝ := t / (R + t)
  have hden : 0 < R + t := by positivity
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hbeta : 0 < beta := by dsimp [beta]; positivity
  have hsum : lam + beta = 1 := by dsimp [lam, beta]; field_simp
  have hlamle : lam ≤ 1 := by dsimp [lam]; rw [div_le_one hden]; linarith
  have hCconv : Convex ℝ (A + t • K) := hAconv.add (hKconv.smul t)
  have hC0 : (0 : E) ∈ A + t • K := by
    have hk0 : t • (0 : E) ∈ t • K := Set.smul_mem_smul_set hK0
    simpa using Set.add_mem_add hA0 hk0
  have hsubset :
      BrownianSharp.Concentration.weightedMinkowski lam A beta (R • K) ⊆ A + t • K := by
    intro z hz
    rcases hz with ⟨x, hx, y, hy, hxy⟩
    rcases Set.mem_smul_set.mp hy with ⟨k, hk, rfl⟩
    have hcoeff : beta * R = lam * t := by dsimp [lam, beta]; field_simp
    have hrewrite : lam • x + beta • (R • k) = lam • (x + t • k) := by
      calc
        lam • x + beta • (R • k) = lam • x + (beta * R) • k := by rw [smul_smul]
        _ = lam • x + (lam * t) • k := by rw [hcoeff]
        _ = lam • (x + t • k) := by rw [smul_add, smul_smul]
    have hz' : z = lam • (x + t • k) := hxy.trans hrewrite
    have hsumMem : x + t • k ∈ A + t • K := by
      exact Set.add_mem_add hx (Set.smul_mem_smul_set hk)
    have hlammem : lam ∈ Set.Icc (0 : ℝ) 1 := ⟨hlam.le, hlamle⟩
    have hscaled := hCconv.smul_mem_of_zero_mem hC0 hsumMem hlammem
    exact hz' ▸ hscaled
  have hEhrhardMass := hEhrhard A (R • K) hAconv (hKconv.smul R)
    lam beta hlam hbeta hsum hAm.1 hAm.2 hRm.1 hRm.2
  have hquantMono :
      BrownianSharp.Concentration.standardGaussianCDF
        (lam * BrownianSharp.Concentration.standardGaussianQuantile (μ.real A) + beta * (a * R)) ≤
      BrownianSharp.Concentration.standardGaussianCDF
        (lam * BrownianSharp.Concentration.standardGaussianQuantile (μ.real A) +
          beta * BrownianSharp.Concentration.standardGaussianQuantile (μ.real (R • K))) := by
    apply BrownianSharp.Concentration.standardGaussianCDF_strictMono.monotone
    have hqbeta := mul_le_mul_of_nonneg_left hRq hbeta.le
    nlinarith
  have hmass := hquantMono.trans hEhrhardMass
  exact le_trans hmass (MeasureTheory.measureReal_mono hsubset (measure_ne_top _ _))

/-- Full finite-dimensional Gaussian enlargement from Ehrhard and a verified
ball-quantile growth input. The ball input is kept explicit so that actual
finite Gaussian feature spaces can instantiate it with
`productGaussian_ball_quantile_lower_eventually`. -/
theorem gaussianEhrhard_dilation_of_ball_quantile_growth
    {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) [IsFiniteMeasure μ]
    (hEhrhard : BrownianSharp.Concentration.GaussianEhrhard E μ)
    (A K : Set E) (hAconv : Convex ℝ A) (hKconv : Convex ℝ K)
    (hA0 : (0 : E) ∈ A) (hK0 : (0 : E) ∈ K)
    (hAm : μ.real A ∈ Set.Ioo (0 : ℝ) 1)
    (hball : ∀ a : ℝ, 0 < a → a < 1 →
      ∃ R₀ : ℝ, ∀ R ≥ R₀,
        μ.real (R • K) ∈ Set.Ioo (0 : ℝ) 1 ∧
        a * R ≤ BrownianSharp.Concentration.standardGaussianQuantile (μ.real (R • K)))
    {t : ℝ} (ht : 0 < t) :
    BrownianSharp.Concentration.standardGaussianCDF
        (BrownianSharp.Concentration.standardGaussianQuantile (μ.real A) + t) ≤
      μ.real (A + t • K) := by
  classical
  let qA := BrownianSharp.Concentration.standardGaussianQuantile (μ.real A)
  have hfixed : ∀ a : ℝ, 0 < a → a < 1 →
      BrownianSharp.Concentration.standardGaussianCDF (qA + a * t) ≤ μ.real (A + t • K) := by
    intro a ha ha1
    obtain ⟨R₀, hR₀⟩ := hball a ha ha1
    let ρ : ℝ → ℝ := fun R => R / (R + t)
    let arg : ℝ → ℝ := fun R => ρ R * qA + (t / (R + t)) * (a * R)
    have hdenTendsto : Tendsto (fun R : ℝ => R + t) atTop atTop := by
      apply Filter.tendsto_atTop.2
      intro b
      filter_upwards [eventually_atTop.2 ⟨b - t, fun R hR => hR⟩] with R hR
      change b ≤ R + t
      linarith
    have hinv : Tendsto (fun R : ℝ => (R + t)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hdenTendsto
    have hfrac : Tendsto (fun R : ℝ => t / (R + t)) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using tendsto_const_nhds.mul hinv
    have hρ : Tendsto ρ atTop (𝓝 1) := by
      have heq : (fun R : ℝ => ρ R) =ᶠ[atTop] fun R => 1 - t / (R + t) := by
        filter_upwards [eventually_atTop.2 ⟨0, fun R hR => hR⟩] with R hR
        dsimp [ρ]
        have hden : R + t ≠ 0 := by linarith
        field_simp
        ring
      have hconst : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      have h := hconst.sub hfrac
      simpa using Tendsto.congr' heq.symm h
    have hargEq : ∀ᶠ R : ℝ in atTop, arg R = (qA + a * t) * ρ R := by
      filter_upwards [eventually_atTop.2 ⟨0, fun R hR => hR⟩] with R hR
      dsimp [arg, ρ]
      have hden : R + t ≠ 0 := by linarith
      field_simp
    have hargTendsto : Tendsto arg atTop (𝓝 (qA + a * t)) := by
      have hmul : Tendsto (fun R : ℝ => (qA + a * t) * ρ R) atTop
          (𝓝 ((qA + a * t) * 1)) := tendsto_const_nhds.mul hρ
      simpa using Tendsto.congr' (hargEq.mono fun _ h => h.symm) hmul
    have hcdfTendsto : Tendsto
        (fun R : ℝ => BrownianSharp.Concentration.standardGaussianCDF (arg R))
        atTop (𝓝 (BrownianSharp.Concentration.standardGaussianCDF (qA + a * t))) :=
      BrownianSharp.Concentration.standardGaussianCDF_continuous.continuousAt.tendsto.comp hargTendsto
    have hEventually : ∀ᶠ R : ℝ in atTop,
        BrownianSharp.Concentration.standardGaussianCDF (arg R) ≤ μ.real (A + t • K) := by
      filter_upwards [eventually_atTop.2 ⟨max R₀ (1 : ℝ), fun R hR => hR⟩] with R hR
      have hR0 : R₀ ≤ R := (le_max_left _ _).trans hR
      have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ((le_max_right _ _).trans hR)
      have hq := hR₀ R hR0
      have hfinite := gaussianEhrhard_finiteRadius_dilation μ hEhrhard A K
        hAconv hKconv hA0 hK0 ht hRpos ha ha1 hAm hq.1 hq.2
      have hargEq' : arg R = (R / (R + t)) * qA + (t / (R + t)) * (a * R) := by
        rfl
      simpa [arg, ρ, qA] using hfinite
    exact le_of_tendsto_of_tendsto hcdfTendsto tendsto_const_nhds hEventually
  let aSeq : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
  have hrecip : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have hbase := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hshift := hbase.comp (tendsto_add_atTop_nat 1)
    convert hshift using 1 <;> ext n <;> simp [Nat.cast_add] <;> ring
  have haSeq : Tendsto aSeq atTop (𝓝 1) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa [aSeq] using hconst.sub hrecip
  have hseq : ∀ n : ℕ, BrownianSharp.Concentration.standardGaussianCDF
      (qA + aSeq n * t) ≤ μ.real (A + t • K) := by
    intro n
    have hapos : 0 < aSeq n := by
      dsimp [aSeq]
      have hn : 0 < (n : ℝ) + 2 := by positivity
      have hrec : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := by
        apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).2
        nlinarith
      linarith
    have haone : aSeq n < 1 := by
      dsimp [aSeq]
      have hn : 0 < (n : ℝ) + 2 := by positivity
      have : 0 < 1 / ((n : ℝ) + 2) := by positivity
      linarith
    exact hfixed (aSeq n) hapos haone
  have harglim : Tendsto (fun n : ℕ => qA + aSeq n * t) atTop (𝓝 (qA + t)) := by
    have hmul : Tendsto (fun n : ℕ => aSeq n * t) atTop (𝓝 t) := by
      simpa [mul_comm] using haSeq.const_mul t
    have hconst : Tendsto (fun _ : ℕ => qA) atTop (𝓝 qA) := tendsto_const_nhds
    simpa using hconst.add hmul
  have hlast : Tendsto (fun n : ℕ => BrownianSharp.Concentration.standardGaussianCDF
      (qA + aSeq n * t)) atTop
      (𝓝 (BrownianSharp.Concentration.standardGaussianCDF (qA + t))) :=
    BrownianSharp.Concentration.standardGaussianCDF_continuous.continuousAt.tendsto.comp harglim
  exact le_of_tendsto_of_tendsto hlast tendsto_const_nhds (Filter.Eventually.of_forall hseq)

/-- Exact Ehrhard enlargement in a finite-dimensional Hilbert space. This
version is specialized to its actual standard Gaussian and norm ball; the
quantile-growth input is discharged by the product chi-square proof above. -/
theorem finiteHilbertStdGaussian_exact_dilation
    {E ι : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (b : OrthonormalBasis ι ℝ E)
    (hEhrhard : BrownianSharp.Concentration.GaussianEhrhard E
      (ProbabilityTheory.stdGaussian E))
    (A : Set E) (hAconv : Convex ℝ A) (hA0 : 0 ∈ A)
    (hAprob : (ProbabilityTheory.stdGaussian E).real A ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (ht : 0 < t) :
    BrownianSharp.Concentration.standardGaussianCDF
        (BrownianSharp.Concentration.standardGaussianQuantile
          ((ProbabilityTheory.stdGaussian E).real A) + t) ≤
      (ProbabilityTheory.stdGaussian E).real (A + t • Metric.closedBall (0 : E) 1) := by
  let K : Set E := Metric.closedBall 0 1
  have hKconv : Convex ℝ K := convex_closedBall _ _
  have hK0 : (0 : E) ∈ K := by simp [K]
  have hball : ∀ a : ℝ, 0 < a → a < 1 →
      ∃ R₀ : ℝ, ∀ R ≥ R₀,
        (ProbabilityTheory.stdGaussian E).real (R • K) ∈ Set.Ioo (0 : ℝ) 1 ∧
        a * R ≤ BrownianSharp.Concentration.standardGaussianQuantile
          ((ProbabilityTheory.stdGaussian E).real (R • K)) := by
    intro a ha0 ha1
    obtain ⟨R₀, hquant⟩ := finiteHilbertStdGaussian_ball_quantile_lower_eventually b ha0 ha1
    refine ⟨max R₀ 1, ?_⟩
    intro R hR
    have hRpos : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (le_trans (le_max_right R₀ 1) hR)
    have hp := hquant R (le_trans (le_max_left R₀ 1) hR)
    have hEq : R • K = Metric.closedBall (0 : E) R := by
      dsimp [K]
      rw [smul_unitClosedBall_of_nonneg hRpos.le]
    rw [hEq]
    exact ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩
  exact gaussianEhrhard_dilation_of_ball_quantile_growth
    (ProbabilityTheory.stdGaussian E) hEhrhard A K hAconv hKconv hA0 hK0
    hAprob hball ht

/-- Certified finite-dimensional version of the exact enlargement theorem.
Measurable-embedding change of variables transports set masses without
imposing false measurability assumptions on arbitrary convex sets. -/
theorem finiteHilbertStdGaussian_exact_dilation_certified
    {E ι : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (b : OrthonormalBasis ι ℝ E)
    (A : Set E) (hAconv : Convex ℝ A) (hA0 : 0 ∈ A)
    (hAprob : (ProbabilityTheory.stdGaussian E).real A ∈ Set.Ioo (0 : ℝ) 1)
    (t : ℝ) (ht : 0 < t) :
    BrownianSharp.Concentration.standardGaussianCDF
        (BrownianSharp.Concentration.standardGaussianQuantile
          ((ProbabilityTheory.stdGaussian E).real A) + t) ≤
      (ProbabilityTheory.stdGaussian E).real (A + t • Metric.closedBall (0 : E) 1) := by
  apply finiteHilbertStdGaussian_exact_dilation b
    (BrownianSharp.AlignmentPaperGaussianDilation.stdGaussian_gaussianEhrhard
      b) A hAconv hA0 hAprob t ht

/-- Finite feature evaluation: a Hilbert vector is represented by its inner
products against finitely many feature vectors. -/
def finiteFeatureEval {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {N : ℕ}
    (v : Fin N → H) : H → (Fin N → ℝ) :=
  fun h i => inner ℝ h (v i)

/-- Restricting the unit-ball feature parameter to the finite span of the
observed features changes none of its evaluations and cannot increase its
norm. This is the exact finite-grid Cameron--Martin projection identity. -/
theorem finiteFeatureEvaluation_unitBall_image_eq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {N : ℕ} (v : Fin N → H) :
    finiteFeatureEval v '' Metric.closedBall (0 : H) 1 =
      (fun g : ↥(Submodule.span ℝ (Set.range v)) => finiteFeatureEval v (g : H)) ''
        Metric.closedBall (0 : ↥(Submodule.span ℝ (Set.range v))) 1 := by
  classical
  let S : Submodule ℝ H := Submodule.span ℝ (Set.range v)
  have hfg : S.FG := Submodule.fg_span (Set.finite_range v)
  letI : FiniteDimensional ℝ S := (Submodule.fg_iff_finiteDimensional S).mp hfg
  ext y
  constructor
  · rintro ⟨h, hh, rfl⟩
    have hh' : ‖h‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hh
    let g : S := S.orthogonalProjectionOnto h
    have hg : ‖g‖ ≤ 1 := by
      calc
        ‖g‖ ≤ ‖h‖ := (S.norm_orthogonalProjectionOnto_apply_le h)
        _ ≤ 1 := hh'
    have heval : finiteFeatureEval v (g : H) = finiteFeatureEval v h := by
      funext i
      dsimp [finiteFeatureEval]
      have hi : (v i : H) ∈ S := Submodule.subset_span ⟨i, rfl⟩
      have hproj : inner ℝ (v i) (g : H) = inner ℝ (v i) h := by
        change inner ℝ (v i) (S.orthogonalProjectionOnto h : H) = inner ℝ (v i) h
        exact S.inner_orthogonalProjectionOnto_eq_of_mem_left ⟨v i, hi⟩ h
      change inner ℝ (g : H) (v i) = inner ℝ h (v i)
      calc
        inner ℝ (g : H) (v i) = inner ℝ (v i) (g : H) := real_inner_comm _ _
        _ = inner ℝ (v i) h := hproj
        _ = inner ℝ h (v i) := (real_inner_comm _ _).symm
    refine ⟨g, ?_, heval⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hg
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(g : H), ?_, rfl⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hg

/-- The finite-dimensional standard-Gaussian enlargement for an actual
finite feature family. Its base set is the preimage of the coordinate cube;
the enlarged event is the set of outputs within `ε` in every coordinate of a
scaled image of the feature unit ball. The feature span is exact, by the
projection identity immediately above. -/
theorem finiteFeatureSpan_stdGaussian_cube_enlargement
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {N : ℕ} (v : Fin N → E) (hv : ∃ i, v i ≠ 0)
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    let μ := ProbabilityTheory.stdGaussian E
    let A : Set E := {g | ∀ i, |finiteFeatureEval v g i| ≤ ε}
    let D : Set E := {g | ∃ z ∈ Metric.closedBall (0 : E) 1,
      ∀ i, |finiteFeatureEval v g i - t * finiteFeatureEval v z i| ≤ ε}
    BrownianSharp.Concentration.standardGaussianCDF
        (BrownianSharp.Concentration.standardGaussianQuantile (μ.real A) + t) ≤ μ.real D := by
  classical
  have hdim : 0 < Module.finrank ℝ E := by
    obtain ⟨i, hi⟩ := hv
    apply (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := E)).2
    exact ⟨v i, hi⟩
  letI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hdim
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  let μ : Measure E := ProbabilityTheory.stdGaussian E
  let A : Set E := {g | ∀ i, |finiteFeatureEval v g i| ≤ ε}
  let D : Set E := {g | ∃ z ∈ Metric.closedBall (0 : E) 1,
    ∀ i, |finiteFeatureEval v g i - t * finiteFeatureEval v z i| ≤ ε}
  have hstdOpen := finiteHilbertStdGaussian_isOpenPosMeasure b
  have hevalCont : Continuous (fun g : E => finiteFeatureEval v g) := by
    refine continuous_pi fun i => ?_
    exact continuous_inner.comp (continuous_id.prodMk continuous_const)
  have hWopen : IsOpen (Set.univ.pi (fun _ : Fin N => Set.Ioo (-ε) ε)) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have hzeroA : (0 : E) ∈ A := by
    intro i
    change |inner ℝ (0 : E) (v i)| ≤ ε
    simp only [inner_zero_left, abs_zero]
    exact hε.le
  have hAmeas : MeasurableSet A := by
    have hclosed : IsClosed A := by
      rw [show A = ⋂ i : Fin N, {g : E |
        |finiteFeatureEval v g i| ≤ ε} by
        ext g
        simp [A]]
      exact isClosed_iInter fun i =>
        isClosed_Iic.preimage (continuous_abs.comp
          ((continuous_apply i).comp hevalCont))
    exact hclosed.measurableSet
  have hApos : 0 < μ A := by
    let W : Set (Fin N → ℝ) := Set.univ.pi (fun _ => Set.Ioo (-ε) ε)
    have hW : IsOpen W := by simpa [W] using hWopen
    let U : Set E := (fun g : E => finiteFeatureEval v g) ⁻¹' W
    have hUopen : IsOpen U := hW.preimage hevalCont
    have hU0 : (0 : E) ∈ U := by
      change finiteFeatureEval v (0 : E) ∈ W
      simp only [W, Set.mem_pi, Set.mem_univ]
      intro i _
      change finiteFeatureEval v (0 : E) i ∈ Set.Ioo (-ε) ε
      simp only [finiteFeatureEval, inner_zero_left]
      exact ⟨by linarith [hε], hε⟩
    have hUA : U ⊆ A := by
      intro g hg i
      have hgi : finiteFeatureEval v g i ∈ Set.Ioo (-ε) ε :=
        (Set.mem_pi.mp hg) i (Set.mem_univ i)
      rw [Set.mem_Ioo] at hgi
      exact abs_le.mpr ⟨by linarith [hgi.1], by linarith [hgi.2]⟩
    exact lt_of_lt_of_le (hUopen.measure_pos μ ⟨0, hU0⟩) (measure_mono hUA)
  obtain ⟨i₀, hi₀⟩ := hv
  have hvnorm : 0 < ‖v i₀‖ := norm_pos_iff.mpr hi₀
  let z₀ : E := v i₀
  let c : ℝ := (ε + 1) / ‖v i₀‖ ^ 2
  let g₀ : E := c • z₀
  have hlarge : ε < finiteFeatureEval v g₀ i₀ := by
    dsimp [finiteFeatureEval, g₀, c, z₀]
    rw [inner_smul_left]
    simp only [real_inner_self_eq_norm_sq]
    have hsq : ‖v i₀‖ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hvnorm)
    have hc : ‖v i₀‖ ^ 2 * ((ε + 1) / ‖v i₀‖ ^ 2) = ε + 1 := by
      field_simp
    simp only [starRingEnd_apply, star_trivial]
    change ε < ((ε + 1) / ‖v i₀‖ ^ 2) * ‖v i₀‖ ^ 2
    nlinarith [hc]
  let O : Set E := {g | ε < finiteFeatureEval v g i₀}
  have hOopen : IsOpen O := by
    exact isOpen_Ioi.preimage ((continuous_apply i₀).comp hevalCont)
  have hOsub : O ⊆ Aᶜ := by
    intro g hg hAg
    change ε < finiteFeatureEval v g i₀ at hg
    have := hAg i₀
    have := abs_le.mp this
    linarith
  have hOpos : 0 < μ O := hOopen.measure_pos μ ⟨g₀, hlarge⟩
  have hAcpos : 0 < μ Aᶜ := lt_of_lt_of_le hOpos (measure_mono hOsub)
  have hsum := MeasureTheory.measureReal_add_measureReal_compl
    (μ := μ) (s := A) hAmeas
  have htotal : μ.real Set.univ = 1 := by simp [μ]
  rw [htotal] at hsum
  have hArealpos : 0 < μ.real A := ENNReal.toReal_pos hApos.ne' (measure_ne_top _ _)
  have hAcompRealpos : 0 < μ.real Aᶜ :=
    ENNReal.toReal_pos hAcpos.ne' (measure_ne_top _ _)
  have hAprob : μ.real A ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact hArealpos
    · linarith
  have hAconv : Convex ℝ A := by
    intro x hx y hy a b ha hb hab i
    have hlin : finiteFeatureEval v (a • x + b • y) i =
        a * finiteFeatureEval v x i + b * finiteFeatureEval v y i := by
      simp [finiteFeatureEval, inner_add_left, inner_smul_left]
    rw [hlin]
    calc
      |a * finiteFeatureEval v x i + b * finiteFeatureEval v y i|
          ≤ |a * finiteFeatureEval v x i| + |b * finiteFeatureEval v y i| := by
            have := norm_add_le (a * finiteFeatureEval v x i) (b * finiteFeatureEval v y i)
            simpa [Real.norm_eq_abs] using this
      _ = a * |finiteFeatureEval v x i| + b * |finiteFeatureEval v y i| := by
        rw [abs_mul, abs_of_nonneg ha, abs_mul, abs_of_nonneg hb]
      _ ≤ a * ε + b * ε := add_le_add
        (mul_le_mul_of_nonneg_left (hx i) ha) (mul_le_mul_of_nonneg_left (hy i) hb)
      _ = ε := by rw [← add_mul, hab, one_mul]
  have hA0 : (0 : E) ∈ A := hzeroA
  have hset : A + t • Metric.closedBall (0 : E) 1 = D := by
    ext g
    simp only [Set.mem_add, Set.mem_smul_set, Set.mem_setOf_eq, A, D]
    constructor
    · rintro ⟨x, hx, z, hz, rfl⟩
      rcases hz with ⟨y, hy, rfl⟩
      refine ⟨y, hy, ?_⟩
      intro i
      have hlin : finiteFeatureEval v (x + t • y) i =
          finiteFeatureEval v x i + t * finiteFeatureEval v y i := by
        simp [finiteFeatureEval, inner_add_left, inner_smul_left]
      rw [hlin]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hx i
    · rintro ⟨z, hz, hgz⟩
      refine ⟨g - t • z, ?_, t • z, ?_, ?_⟩
      · intro i
        have hlin : finiteFeatureEval v (g - t • z) i =
            finiteFeatureEval v g i - t * finiteFeatureEval v z i := by
          simp [finiteFeatureEval, inner_sub_left, inner_smul_left]
        rw [hlin]
        exact hgz i
      · exact ⟨z, hz, rfl⟩
      · simp [sub_add_cancel]
  have hmain := finiteHilbertStdGaussian_exact_dilation_certified b A hAconv hA0 hAprob t ht
  rw [hset] at hmain
  exact hmain

end BrownianSharp.AlignmentPaperQuadraticGaussianMoment
