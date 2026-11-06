import BrownianSharp.GaussianEhrhardCertified
import BrownianSharp.Concentration
import BrownianSharp.GaussianDensity
import BrownianSharp.GaussianSupport
import BrownianSharp.ActualConcentration
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Continuous

/-! Literal finite-dimensional convex-observable route for Proposition 2.6.

The proof is assembled from variance-based Chebyshev anchors and the actual
set-level Ehrhard inequality for closed convex sublevel sets. In particular,
the scale `σ` is an external upper bound on the standard deviation and need
not equal it, so the zero-variance case remains included.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open BrownianSharp.Concentration
open BrownianSharp

namespace BrownianSharp.AlignmentPaperConvexTail

/-- Chebyshev controls both closed distribution anchors of a nonnegative
random variable with mean one. The bounds are stated with `σ` as an external
variance scale (`Var ≤ σ²`). -/
theorem chebyshev_exp_anchors
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (hY : MemLp Y 2 μ) (hYmeas : Measurable Y)
    (hmean : μ[Y] = 1) {σ : ℝ} (hσ : 0 < σ)
    (hvar : ProbabilityTheory.variance Y μ ≤ σ ^ 2) :
    μ.real {ω | Y ω ≤ 1 - 2 * σ} ≤ 1 / 4 ∧
      3 / 4 ≤ μ.real {ω | Y ω ≤ 1 + 2 * σ} := by
  have hδ : 0 < 2 * σ := by positivity
  have hlow := BrownianSharp.Concentration.measure_lower_tail_le_cantelli μ Y hY
    (2 * σ) hδ
  have hvnonneg : 0 ≤ ProbabilityTheory.variance Y μ := by
    dsimp [ProbabilityTheory.variance]
    exact ENNReal.toReal_nonneg
  have hden : 0 < ProbabilityTheory.variance Y μ + (2 * σ) ^ 2 := by positivity
  have hratio : ProbabilityTheory.variance Y μ /
      (ProbabilityTheory.variance Y μ + (2 * σ) ^ 2) ≤ 1 / 5 := by
    apply (div_le_iff₀ hden).2
    nlinarith [hvar]
  have hlow' : μ.real {ω | 2 * σ ≤ μ[Y] - Y ω} ≤ 1 / 5 :=
    hlow.trans hratio
  have hsetLow : {ω | Y ω ≤ 1 - 2 * σ} =
      {ω | 2 * σ ≤ μ[Y] - Y ω} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [hmean]
    constructor <;> intro h <;> linarith
  have hlower : μ.real {ω | Y ω ≤ 1 - 2 * σ} ≤ 1 / 4 := by
    rw [hsetLow]
    linarith
  have hneg : MemLp (-Y) 2 μ := hY.neg
  have hupperCantelli := BrownianSharp.Concentration.measure_lower_tail_le_cantelli μ
    (-Y) hneg (2 * σ) hδ
  have hvarneg : ProbabilityTheory.variance (-Y) μ =
      ProbabilityTheory.variance Y μ := ProbabilityTheory.variance_neg
  rw [hvarneg] at hupperCantelli
  have hupper : μ.real {ω | 2 * σ ≤ Y ω - 1} ≤ 1 / 5 := by
    have htmp : μ.real {ω | 2 * σ ≤ μ[-Y] - (-Y ω)} ≤ 1 / 5 :=
      hupperCantelli.trans hratio
    have hmeanNeg : μ[-Y] = -1 := by
      change (∫ ω, -Y ω ∂μ) = -1
      rw [integral_neg, hmean]
    have hset : {ω | 2 * σ ≤ μ[-Y] - (-Y ω)} =
        {ω | 2 * σ ≤ Y ω - 1} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      rw [hmeanNeg]
      constructor <;> intro h <;> linarith
    rw [hset] at htmp
    exact htmp
  have hbadMeas : MeasurableSet {ω | 1 + 2 * σ < Y ω} :=
    measurableSet_lt measurable_const hYmeas
  have hbadSubset : {ω | 1 + 2 * σ < Y ω} ⊆
      {ω | 2 * σ ≤ Y ω - 1} := by
    intro ω hω
    change 1 + 2 * σ < Y ω at hω
    change 2 * σ ≤ Y ω - 1
    linarith
  have hbad : μ.real {ω | 1 + 2 * σ < Y ω} ≤ 1 / 5 :=
    (MeasureTheory.measureReal_mono hbadSubset).trans hupper
  have hcompl := MeasureTheory.measureReal_add_measureReal_compl
    (μ := μ) hbadMeas
  have huniv : μ.real Set.univ = 1 := by simp
  rw [huniv] at hcompl
  have hcompeq : {ω | Y ω ≤ 1 + 2 * σ} =
      ({ω | 1 + 2 * σ < Y ω})ᶜ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    constructor <;> intro h <;> linarith
  have hgood : μ.real {ω | Y ω ≤ 1 + 2 * σ} =
      1 - μ.real {ω | 1 + 2 * σ < Y ω} := by
    rw [hcompeq]
    linarith [hcompl]
  rw [hgood]
  constructor <;> linarith

/-- Elementary logarithmic geometry of the two Chebyshev anchors. -/
theorem exp_anchor_log_geometry {σ t : ℝ} (hσ : 0 < σ) (hσ₄ : σ ≤ 1 / 4)
    (ht : 1 ≤ t) :
    Real.log (1 - 2 * σ) ≥ -4 * σ ∧
      Real.log (1 + 2 * σ) - Real.log (1 - 2 * σ) ≤ 6 * σ ∧
      t + Real.log (1 - 2 * σ) ≥ t - 1 := by
  have hminus : 0 < 1 - 2 * σ := by linarith
  have hplus : 0 < 1 + 2 * σ := by linarith
  have hrec : 0 < 1 / (1 - 2 * σ) := by positivity
  have hnegLog : -Real.log (1 - 2 * σ) ≤ 4 * σ := by
    have hlog := Real.log_le_sub_one_of_pos hrec
    rw [show (1 / (1 - 2 * σ) : ℝ) = (1 - 2 * σ)⁻¹ by ring] at hlog
    rw [Real.log_inv] at hlog
    have hfrac : (1 / (1 - 2 * σ) : ℝ) - 1 ≤ 4 * σ := by
      field_simp [ne_of_gt hminus]
      nlinarith [hσ₄]
    have hlog' : -Real.log (1 - 2 * σ) ≤
        (1 / (1 - 2 * σ) : ℝ) - 1 := by simpa [one_div] using hlog
    exact hlog'.trans hfrac
  have hplusLog : Real.log (1 + 2 * σ) ≤ 2 * σ := by
    have h := Real.log_le_sub_one_of_pos hplus
    linarith
  refine ⟨by linarith, ?_, ?_⟩
  · have : -Real.log (1 - 2 * σ) ≤ 4 * σ := hnegLog
    linarith
  · have hts : 4 * σ ≤ 1 := by linarith
    linarith

/-- Ehrhard's set inequality gives concavity of the quantile of the *closed*
sublevel CDF on any half-line where that CDF stays strictly between zero and
one. Using closed levels avoids an atomlessness assumption on a general convex
observable (which can have flat regions). -/
theorem closedSublevel_quantile_concave
    {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (X : E → ℝ) (hXconvex : ConvexOn ℝ Set.univ X)
    (hEhrhard : Concentration.GaussianEhrhard E μ)
    (x₀ : ℝ) (hRange : ∀ s ∈ Set.Ici x₀,
      0 < μ.real {x | X x ≤ s} ∧ μ.real {x | X x ≤ s} < 1) :
    ConcaveOn ℝ (Set.Ici x₀)
      (cdfGaussianQuantile (fun s => μ.real {x | X x ≤ s})) := by
  let F : ℝ → ℝ := fun s => μ.real {x | X x ≤ s}
  let G : ℝ → ℝ := cdfGaussianQuantile F
  refine ⟨convex_Ici x₀, ?_⟩
  intro s hs u hu a b ha hb hab
  by_cases ha0 : a = 0
  · subst a
    have hb1 : b = 1 := by linarith
    subst b
    simp
  by_cases hb0 : b = 0
  · subst b
    have ha1 : a = 1 := by linarith
    subst a
    simp
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hsx : 0 ≤ s - x₀ := by simpa [Set.mem_Ici] using hs
  have hux : 0 ≤ u - x₀ := by simpa [Set.mem_Ici] using hu
  have hsle : x₀ ≤ s := by simpa [Set.mem_Ici] using hs
  have hule : x₀ ≤ u := by simpa [Set.mem_Ici] using hu
  have hzmem : a * s + b * u ∈ Set.Ici x₀ := by
    change x₀ ≤ a * s + b * u
    calc
      x₀ = (a + b) * x₀ := by rw [hab]; ring
      _ = a * x₀ + b * x₀ := by ring
      _ ≤ a * s + b * u := add_le_add
        (mul_le_mul_of_nonneg_left hsle ha)
        (mul_le_mul_of_nonneg_left hule hb)
  have hFs := hRange s hs
  have hFu := hRange u hu
  have hFz := hRange (a * s + b * u) hzmem
  let A : Set E := {x | X x ≤ s}
  let B : Set E := {x | X x ≤ u}
  have hAconv : Convex ℝ A := by
    simpa [A] using hXconvex.convex_le s
  have hBconv : Convex ℝ B := by
    simpa [B] using hXconvex.convex_le u
  have hset := hEhrhard A B hAconv hBconv a b hapos hbpos hab
    (by simpa [F, A] using hFs.1) (by simpa [F, A] using hFs.2)
    (by simpa [F, B] using hFu.1) (by simpa [F, B] using hFu.2)
  have hsubset : Concentration.weightedMinkowski a A b B ⊆
      {z | X z ≤ a * s + b * u} := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    change X x ≤ s at hx
    change X y ≤ u at hy
    have hconv := hXconvex.2 (Set.mem_univ x) (Set.mem_univ y)
      ha hb hab
    have hle : X (a • x + b • y) ≤ a * X x + b * X y := by
      simpa [smul_eq_mul] using hconv
    calc
      X (a • x + b • y) ≤ a * X x + b * X y := hle
      _ ≤ a * s + b * u := add_le_add
        (mul_le_mul_of_nonneg_left hx ha)
        (mul_le_mul_of_nonneg_left hy hb)
  have hmass : μ.real (Concentration.weightedMinkowski a A b B) ≤ F (a * s + b * u) := by
    calc
      μ.real (Concentration.weightedMinkowski a A b B) ≤
          μ.real {z | X z ≤ a * s + b * u} := MeasureTheory.measureReal_mono hsubset
      _ = F (a * s + b * u) := rfl
  have hrepZ : F (a * s + b * u) =
      standardGaussianCDF (G (a * s + b * u)) := by
    simpa [F, G] using cdfGaussianQuantile_representation F hFz.1 hFz.2
  have hqS : standardGaussianQuantile (μ.real A) = G s := by
    simpa [A, F, G] using (show standardGaussianQuantile (F s) = G s from rfl)
  have hqU : standardGaussianQuantile (μ.real B) = G u := by
    simpa [B, F, G] using (show standardGaussianQuantile (F u) = G u from rfl)
  rw [hqS, hqU] at hset
  have hleft : standardGaussianCDF (a * G s + b * G u) ≤
      standardGaussianCDF (G (a * s + b * u)) := by
    exact hset.trans (hmass.trans hrepZ.le)
  have hright : a * G s + b * G u ≤ G (a * s + b * u) := by
    by_contra hn
    have hgt : G (a * s + b * u) < a * G s + b * G u := lt_of_not_ge hn
    exact (not_le_of_gt (standardGaussianCDF_strictMono hgt)) hleft
  simpa [smul_eq_mul, G] using hright

/-- Symmetry of the standard Gaussian identifies the lower quartile with the
negative of the upper quartile. -/
theorem standardGaussianQuantile_quarter_eq_neg_threeQuarter :
    standardGaussianQuantile (1 / 4) =
      -standardGaussianQuantile (3 / 4) := by
  let μ := ProbabilityTheory.gaussianReal 0 1
  let q := standardGaussianQuantile (3 / 4)
  have hq : standardGaussianCDF q = 3 / 4 := by
    exact standardGaussianCDF_standardGaussianQuantile (by norm_num) (by norm_num)
  have hmap : μ.map (fun z : ℝ => -z) = μ := by
    dsimp [μ]
    rw [ProbabilityTheory.gaussianReal_map_neg]
    congr 1 <;> norm_num
  have htailMeasure : μ.real (Set.Iio (-q)) = μ.real (Set.Ioi q) := by
    have hmeasure : μ (Set.Iio (-q)) = μ (Set.Ioi q) := by
      calc
        μ (Set.Iio (-q)) = (μ.map (fun z : ℝ => -z)) (Set.Iio (-q)) := by rw [hmap]
        _ = μ ((fun z : ℝ => -z) ⁻¹' Set.Iio (-q)) := by
          rw [Measure.map_apply measurable_neg measurableSet_Iio]
        _ = μ (Set.Ioi q) := by congr 1 <;> ext z <;> simp
    simp [Measure.real_def, hmeasure]
  have hAtom : ∀ r, μ {z : ℝ | z = r} = 0 := by
    intro r
    have hac : μ ≪ (volume : Measure ℝ) := by
      have hv : (1 : NNReal) ≠ 0 := by norm_num
      have hac0 := ProbabilityTheory.gaussianReal_absolutelyContinuous
        (0 : ℝ) (v := (1 : NNReal)) hv
      simpa [μ] using hac0
    apply hac
    rw [show {z : ℝ | z = r} = ({r} : Set ℝ) by ext z; simp]
    simp
  have hweak : μ.real (Set.Iic q) = μ.real (Set.Iio q) := by
    exact (measureReal_strictLevel_eq_weakLevel_of_null μ (fun z : ℝ => z)
      measurable_id hAtom q).symm
  have hcompl := MeasureTheory.measureReal_add_measureReal_compl
    (μ := μ) (s := Set.Iic q) measurableSet_Iic
  have huniv : μ.real Set.univ = 1 := by simp [μ]
  change μ.real (Set.Iio q) = 3 / 4 at hq
  rw [huniv, hweak, hq] at hcompl
  have htail : μ.real (Set.Ioi q) = 1 / 4 := by
    have hcompSet : (Set.Iic q : Set ℝ)ᶜ = Set.Ioi q := by ext z; simp
    rw [hcompSet] at hcompl
    linarith
  have hquarter : standardGaussianCDF (-q) = 1 / 4 := by
    change μ.real (Set.Iio (-q)) = 1 / 4
    exact htailMeasure.trans (by rw [htail])
  have hqleft : standardGaussianCDF (standardGaussianQuantile (1 / 4)) = 1 / 4 :=
    standardGaussianCDF_standardGaussianQuantile (by norm_num) (by norm_num)
  have hqright : standardGaussianCDF (-standardGaussianQuantile (3 / 4)) = 1 / 4 := by
    simpa [q] using hquarter
  exact standardGaussianCDF_strictMono.injective (by rw [hqleft, hqright])

/-- The finite-dimensional Proposition 2.6 secant argument, with the exact
closed-sublevel range condition displayed. In the paper application this range
condition follows from full support of the standard Gaussian and unboundedness
above of a nonconstant finite convex function. Keeping it explicit here makes
the measure-theoretic Ehrhard/secant step reusable without silently assuming
atomlessness. -/
theorem convex_exp_lower_tail_of_closed_sublevel_range
    {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E → ℝ) (hfconv : ConvexOn ℝ Set.univ f)
    (hEhrhard : Concentration.GaussianEhrhard E μ)
    {t : ℝ} (ht : 1 ≤ t)
    (hRange : ∀ s ∈ Set.Ici (-t),
      0 < μ.real {x | f x ≤ s} ∧ μ.real {x | f x ≤ s} < 1)
    (hY : MemLp (fun x => Real.exp (f x)) 2 μ)
    (hYmeas : Measurable (fun x => Real.exp (f x)))
    (hmean : μ[fun x => Real.exp (f x)] = 1)
    {σ : ℝ} (hσ : 0 < σ) (hσ₄ : σ ≤ 1 / 4)
    (hvar : ProbabilityTheory.variance (fun x => Real.exp (f x)) μ ≤ σ ^ 2) :
    μ.real {x | f x ≤ -t} ≤
      standardGaussianCDF (-standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ)) := by
  let F : ℝ → ℝ := fun s => μ.real {x | f x ≤ s}
  let G : ℝ → ℝ := cdfGaussianQuantile F
  have hanchors := chebyshev_exp_anchors μ (fun x => Real.exp (f x)) hY hYmeas
    hmean hσ hvar
  have hgeom := exp_anchor_log_geometry hσ hσ₄ ht
  let s₁ := Real.log (1 - 2 * σ)
  let s₂ := Real.log (1 + 2 * σ)
  have hs₁ : -1 ≤ s₁ := by dsimp [s₁]; linarith [hgeom.1]
  have hs₁mem : s₁ ∈ Set.Ici (-t) := by
    change -t ≤ s₁
    linarith
  have hs₂mem : s₂ ∈ Set.Ici (-t) := by
    dsimp [s₂]
    have hpos : 1 ≤ 1 + 2 * σ := by linarith
    have hlog : 0 ≤ Real.log (1 + 2 * σ) := Real.log_nonneg hpos
    change -t ≤ Real.log (1 + 2 * σ)
    linarith
  have hF₁ := hRange s₁ hs₁mem
  have hF₂ := hRange s₂ hs₂mem
  have hF₁rep : F s₁ = standardGaussianCDF (G s₁) :=
    cdfGaussianQuantile_representation F hF₁.1 hF₁.2
  have hF₂rep : F s₂ = standardGaussianCDF (G s₂) :=
    cdfGaussianQuantile_representation F hF₂.1 hF₂.2
  have hF₁eq : F s₁ = μ.real {x | Real.exp (f x) ≤ 1 - 2 * σ} := by
    dsimp [F, s₁]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    have hp : 0 < 1 - 2 * σ := by linarith
    exact Real.le_log_iff_exp_le hp
  have hF₂eq : F s₂ = μ.real {x | Real.exp (f x) ≤ 1 + 2 * σ} := by
    dsimp [F, s₂]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq]
    have hp : 0 < 1 + 2 * σ := by linarith
    exact Real.le_log_iff_exp_le hp
  have hqquarter : standardGaussianCDF (standardGaussianQuantile (1 / 4)) = 1 / 4 :=
    standardGaussianCDF_standardGaussianQuantile (by norm_num) (by norm_num)
  have hqthree : standardGaussianCDF (standardGaussianQuantile (3 / 4)) = 3 / 4 :=
    standardGaussianCDF_standardGaussianQuantile (by norm_num) (by norm_num)
  have hG₁ : G s₁ ≤ -standardGaussianQuantile (3 / 4) := by
    apply standardGaussianCDF_strictMono.le_iff_le.mp
    rw [← hF₁rep, ← standardGaussianQuantile_quarter_eq_neg_threeQuarter,
      hqquarter, hF₁eq]
    exact hanchors.1
  have hG₂ : standardGaussianQuantile (3 / 4) ≤ G s₂ := by
    apply standardGaussianCDF_strictMono.le_iff_le.mp
    rw [hqthree, ← hF₂rep, hF₂eq]
    exact hanchors.2
  have hqpos : 0 < standardGaussianQuantile (3 / 4) := by
    by_contra hn
    have hle : standardGaussianQuantile (3 / 4) ≤ 0 := le_of_not_gt hn
    have : (3 / 4 : ℝ) ≤ standardGaussianCDF 0 := by
      rw [← hqthree]
      exact standardGaussianCDF_strictMono.monotone hle
    rw [standardGaussianCDF_zero] at this
    norm_num at this
  have hFconc : ConcaveOn ℝ (Set.Ici (-t)) G := by
    simpa [F, G] using closedSublevel_quantile_concave μ f hfconv hEhrhard
      (-t) hRange
  have htargetRange := hRange (-t) (by simp)
  have htailRep : F (-t) = standardGaussianCDF (G (-t)) :=
    cdfGaussianQuantile_representation F htargetRange.1 htargetRange.2
  by_cases htone : t = 1
  · subst t
    have hFmono : F (-1) ≤ F s₁ := by
      apply MeasureTheory.measureReal_mono
      · intro x hx
        change f x ≤ -1 at hx
        change f x ≤ s₁
        linarith [hs₁]
      · simp
    have hmass : F (-1) ≤ 1 / 4 := by
      exact hFmono.trans (by rw [hF₁eq]; exact hanchors.1)
    change F (-1) ≤ _
    have harg : -standardGaussianQuantile (3 / 4) * (1 - 1) / (3 * σ) = 0 := by ring
    rw [harg, standardGaussianCDF_zero]
    linarith
  · have htgt : -t < s₁ := by
      have ht1 : 1 < t := lt_of_le_of_ne ht (Ne.symm htone)
      have : -t < -1 := by linarith
      exact this.trans_le hs₁
    have hs₁s₂ : s₁ < s₂ := by
      dsimp [s₁, s₂]
      apply Real.log_lt_log
      · linarith
      · linarith
    have hslopes := hFconc.slope_anti_adjacent
      (show -t ∈ Set.Ici (-t) by simp)
      (show s₂ ∈ Set.Ici (-t) by exact hs₂mem)
      htgt hs₁s₂
    have hsecant : standardGaussianQuantile (3 / 4) / (3 * σ) ≤
        (G s₁ - G (-t)) / (s₁ + t) := by
      have hden : 0 < s₂ - s₁ := by linarith
      have hden' : 0 < s₁ + t := by linarith
      have hnum : 2 * standardGaussianQuantile (3 / 4) ≤ G s₂ - G s₁ := by
        rw [sub_eq_add_neg]
        nlinarith [hG₁, hG₂]
      have hupper : s₂ - s₁ ≤ 6 * σ := hgeom.2.1
      have hleft : standardGaussianQuantile (3 / 4) / (3 * σ) ≤
          (G s₂ - G s₁) / (s₂ - s₁) := by
        have hσden : 0 < 3 * σ := by positivity
        have hA : (2 * standardGaussianQuantile (3 / 4)) / (6 * σ) ≤
            (G s₂ - G s₁) / (s₂ - s₁) :=
          div_le_div₀ (by linarith [hqpos]) hnum hden hupper
        convert hA using 1 <;> field_simp <;> ring
      exact hleft.trans (by simpa [sub_eq_add_neg] using hslopes)
    have hnum : standardGaussianQuantile (3 / 4) * (s₁ + t) / (3 * σ) ≤
        G s₁ - G (-t) := by
      have hcross := (div_le_div_iff₀ (by positivity)
        (show 0 < s₁ + t by linarith)).mp hsecant
      apply (div_le_iff₀ (by positivity)).2
      nlinarith [hcross]
    have hGbound : G (-t) ≤
        -standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ) := by
      have hgap : t - 1 ≤ s₁ + t + 3 * σ := by linarith [hs₁, hσ₄]
      have hden : 0 < 3 * σ := by positivity
      have hcross := (div_le_iff₀ hden).mp hnum
      have hgap' := mul_le_mul_of_nonneg_left hgap hqpos.le
      apply (le_div_iff₀ hden).2
      nlinarith [hG₁, hgap']
    have hPhi := standardGaussianCDF_strictMono.monotone hGbound
    change F (-t) ≤ _
    rw [htailRep]
    exact hPhi

/-- Exponential relaxation in Proposition 2.6, retaining the explicit CDF
range premise of the closed-sublevel version. -/
theorem convex_exp_lower_tail_exp_of_closed_sublevel_range
    {E : Type*} [MeasurableSpace E] [AddCommGroup E] [Module ℝ E]
    (μ : Measure E) [IsProbabilityMeasure μ]
    (f : E → ℝ) (hfconv : ConvexOn ℝ Set.univ f)
    (hEhrhard : Concentration.GaussianEhrhard E μ)
    {t : ℝ} (ht : 1 ≤ t)
    (hRange : ∀ s ∈ Set.Ici (-t),
      0 < μ.real {x | f x ≤ s} ∧ μ.real {x | f x ≤ s} < 1)
    (hY : MemLp (fun x => Real.exp (f x)) 2 μ)
    (hYmeas : Measurable (fun x => Real.exp (f x)))
    (hmean : μ[fun x => Real.exp (f x)] = 1)
    {σ : ℝ} (hσ : 0 < σ) (hσ₄ : σ ≤ 1 / 4)
    (hvar : ProbabilityTheory.variance (fun x => Real.exp (f x)) μ ≤ σ ^ 2) :
    μ.real {x | f x ≤ -t} ≤
      Real.exp (-(standardGaussianQuantile (3 / 4) * (t - 1)) ^ 2 /
        (18 * σ ^ 2)) := by
  have hΦ := convex_exp_lower_tail_of_closed_sublevel_range μ f hfconv hEhrhard
    ht hRange hY hYmeas hmean hσ hσ₄ hvar
  have hq : 0 < standardGaussianQuantile (3 / 4) := by
    have hqcdf := standardGaussianCDF_standardGaussianQuantile (u := (3 / 4 : ℝ))
      (by norm_num) (by norm_num)
    by_contra hn
    have hle : standardGaussianQuantile (3 / 4) ≤ 0 := le_of_not_gt hn
    have h := standardGaussianCDF_strictMono.monotone hle
    rw [hqcdf, standardGaussianCDF_zero] at h
    norm_num at h
  have ha : 0 ≤ standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ) :=
    div_nonneg (mul_nonneg hq.le (by linarith)) (by positivity)
  have htail := Concentration.gaussianReal_lower_tail_exp ha
  have harg : -standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ) =
      -(standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ)) := by ring
  have harg' : -(standardGaussianQuantile (3 / 4) * (t - 1)) / (3 * σ) =
      -(standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ)) := by ring
  have hset : {x : ℝ | x < -standardGaussianQuantile (3 / 4) * (t - 1) /
      (3 * σ)} = {x | x < -(standardGaussianQuantile (3 / 4) * (t - 1) /
      (3 * σ))} := by ext x; simp [harg, harg']
  have hrelax : Real.exp (-((standardGaussianQuantile (3 / 4) * (t - 1) /
      (3 * σ)) ^ 2) / 2) = Real.exp (-(standardGaussianQuantile (3 / 4) *
      (t - 1)) ^ 2 / (18 * σ ^ 2)) := by
    congr 1
    field_simp
    ring
  calc
    μ.real {x | f x ≤ -t} ≤ standardGaussianCDF
        (-standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ)) := hΦ
    _ = (ProbabilityTheory.gaussianReal 0 1).real
        {x | x < -standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ)} := rfl
    _ = (ProbabilityTheory.gaussianReal 0 1).real
        {x | x < -(standardGaussianQuantile (3 / 4) * (t - 1) / (3 * σ))} := by rw [hset]
    _ ≤ Real.exp (-(standardGaussianQuantile (3 / 4) * (t - 1) /
        (3 * σ)) ^ 2 / 2) := htail
    _ = Real.exp (-(standardGaussianQuantile (3 / 4) * (t - 1)) ^ 2 /
        (18 * σ ^ 2)) := hrelax

/-- A nonconstant finite convex function on a finite-dimensional vector space
is unbounded above. The proof extends a strict secant ray using convexity. -/
theorem finiteConvex_unboundedAbove
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ)
    (hf : ConvexOn ℝ Set.univ f)
    (hneq : ∃ x y, f x < f y) : ∀ M : ℝ, ∃ z, M < f z := by
  rcases hneq with ⟨x, y, hxy⟩
  intro M
  let δ := f y - f x
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let u := max 0 ((M - f y) / δ) + 1
  have hu : 0 < u := by dsimp [u]; linarith [le_max_left 0 ((M - f y) / δ)]
  let a := 1 / (u + 1)
  let b := u / (u + 1)
  let z := (u + 1) • y - u • x
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : a + b = 1 := by dsimp [a, b]; field_simp <;> ring
  have hcomb : a • z + b • x = y := by
    change (1 / (u + 1)) • ((u + 1) • y - u • x) +
      (u / (u + 1)) • x = y
    have hden : u + 1 ≠ 0 := ne_of_gt (by linarith)
    have hycoef : (1 / (u + 1)) * (u + 1) = 1 := by field_simp [hden]
    have hxcoef : -(1 / (u + 1) * u) + u / (u + 1) = 0 := by
      field_simp [hden]
      <;> ring
    rw [smul_sub, smul_smul, smul_smul, hycoef]
    rw [one_smul, sub_eq_add_neg, ← neg_smul, add_assoc, ← add_smul,
      hxcoef, zero_smul, add_zero]
  have hconv := hf.2 (Set.mem_univ z) (Set.mem_univ x) ha.le hb hab
  have hineq : f y ≤ a * f z + b * f x := by simpa [hcomb, smul_eq_mul] using hconv
  have hrhs : a * f z + b * f x = (f z + u * f x) / (u + 1) := by
    dsimp [a, b]
    field_simp
    <;> ring
  rw [hrhs] at hineq
  have hlower : f y + u * δ ≤ f z := by
    dsimp [δ]
    have hden : 0 < u + 1 := by linarith
    have hc := (le_div_iff₀ hden).mp hineq
    nlinarith [hc]
  have huM : M < f y + u * δ := by
    dsimp [u]
    have hmax : (M - f y) / δ ≤ max 0 ((M - f y) / δ) := le_max_right _ _
    have hmul : M - f y ≤ δ * max 0 ((M - f y) / δ) := by
      rw [div_le_iff₀ hδ] at hmax
      nlinarith
    dsimp [δ]
    nlinarith
  exact ⟨z, huM.trans_le hlower⟩

/-- Full support turns a continuous finite-dimensional observable's strict
sublevel and superlevel witnesses into the closed-sublevel CDF range needed by
the secant proof. -/
theorem finiteProductGaussian_closedSublevel_range
    {κ : Type*} [Fintype κ]
    (f : (κ → ℝ) → ℝ) (hfcont : Continuous f) {t : ℝ}
    (hlow : 0 < (productStandardGaussian κ).real {x | f x ≤ -t})
    (hhigh : ∀ s : ℝ, ∃ x, s < f x) :
    ∀ s ∈ Set.Ici (-t),
      0 < (productStandardGaussian κ).real {x | f x ≤ s} ∧
        (productStandardGaussian κ).real {x | f x ≤ s} < 1 := by
  intro s hs
  change -t ≤ s at hs
  let μ := productStandardGaussian κ
  let C : Set (κ → ℝ) := {x | f x ≤ s}
  have hCclosed : IsClosed C := by
    simpa [C] using isClosed_le hfcont continuous_const
  have hCmeas : MeasurableSet C := hCclosed.measurableSet
  have hCfinite : μ C ≠ ⊤ := by simp [μ]
  have hCpos : 0 < μ.real C := by
    by_cases heq : s = -t
    · subst s
      simpa [C, μ] using hlow
    · have hts : -t < s := lt_of_le_of_ne hs (Ne.symm heq)
      have hlowSet : ({x | f x ≤ -t} : Set (κ → ℝ)).Nonempty := by
        by_contra hn
        have he : {x | f x ≤ -t} = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
        rw [he] at hlow
        simp at hlow
      obtain ⟨x₀, hx₀⟩ := hlowSet
      have hLnonempty : {x | f x < s}.Nonempty := by
        refine ⟨x₀, ?_⟩
        change f x₀ < s
        exact lt_of_le_of_lt hx₀ hts
      have hLopen : IsOpen {x | f x < s} := by
        simpa using isOpen_lt hfcont continuous_const
      have hLmass : 0 < μ {x | f x < s} :=
        GaussianDensity.standardGaussian_open_pos hLopen hLnonempty
      have hLreal : 0 < μ.real {x | f x < s} :=
        ENNReal.toReal_pos (ne_of_gt hLmass) (measure_ne_top μ _)
      have hLsub : {x | f x < s} ⊆ C := by
        intro x hx
        change f x ≤ s
        exact hx.le
      exact lt_of_lt_of_le hLreal (MeasureTheory.measureReal_mono hLsub hCfinite)
  obtain ⟨y, hy⟩ := hhigh s
  have hUopen : IsOpen {x | s < f x} := by
    simpa using isOpen_lt continuous_const hfcont
  have hUmass : 0 < μ {x | s < f x} :=
    GaussianDensity.standardGaussian_open_pos hUopen ⟨y, hy⟩
  have hUreal : 0 < μ.real {x | s < f x} :=
    ENNReal.toReal_pos (ne_of_gt hUmass) (measure_ne_top μ _)
  have hUsub : {x | s < f x} ⊆ Cᶜ := by
    intro x hx
    change ¬ f x ≤ s
    exact not_le_of_gt hx
  have hCcomp : 0 < μ.real Cᶜ :=
    lt_of_lt_of_le hUreal (MeasureTheory.measureReal_mono hUsub (by simp [μ]))
  have hsum := MeasureTheory.measureReal_add_measureReal_compl (μ := μ) hCmeas
  have huniv : μ.real Set.univ = 1 := by simp [μ]
  rw [huniv] at hsum
  dsimp [C] at hCpos hCcomp ⊢
  constructor
  · exact hCpos
  · have : μ.real C + μ.real Cᶜ = 1 := hsum
    linarith

/-- Finite-product Gaussian form of Proposition 2.6 with the CDF range
condition discharged. If the target tail has zero mass the estimate is
immediate. Otherwise `E exp(f)=1` excludes constant `f`; finite-dimensional
convexity then supplies arbitrarily high values, and full support supplies the
strict upper CDF bound at every level. -/
theorem finiteProductGaussian_convex_exp_lower_tail
    {κ : Type*} [Fintype κ]
    (f : (κ → ℝ) → ℝ) (hfconv : ConvexOn ℝ Set.univ f)
    {t : ℝ} (ht : 1 ≤ t)
    (hY : MemLp (fun x => Real.exp (f x)) 2 (productStandardGaussian κ))
    (hYmeas : Measurable (fun x => Real.exp (f x)))
    (hmean : (productStandardGaussian κ)[fun x => Real.exp (f x)] = 1)
    {σ : ℝ} (hσ : 0 < σ) (hσ₄ : σ ≤ 1 / 4)
    (hvar : ProbabilityTheory.variance (fun x => Real.exp (f x))
      (productStandardGaussian κ) ≤ σ ^ 2) :
    (productStandardGaussian κ).real {x | f x ≤ -t} ≤
      Real.exp (-(standardGaussianQuantile (3 / 4) * (t - 1)) ^ 2 /
        (18 * σ ^ 2)) := by
  let μ := productStandardGaussian κ
  by_cases htail : 0 < μ.real {x | f x ≤ -t}
  · have hnonconstant : ∃ x y, f x < f y := by
      by_contra hnot
      have hconst : ∀ x : κ → ℝ, f x = f 0 := by
        intro x
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact hnot ⟨x, 0, hlt⟩
        · exact hnot ⟨0, x, hgt⟩
      have hexp : Real.exp (f 0) = 1 := by
        have hfun : (fun x : κ → ℝ => Real.exp (f x)) = fun _ => Real.exp (f 0) :=
          funext (fun x => by rw [hconst x])
        rw [hfun] at hmean
        simpa using hmean
      have hzero : f 0 = 0 := by
        exact Real.exp_injective (by simpa using hexp)
      have hempty : {x : κ → ℝ | f x ≤ -t} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro hx
        rw [hconst x, hzero] at hx
        linarith
      rw [hempty] at htail
      simp at htail
    have hfcont : Continuous f := by
      exact continuousOn_univ.mp (hfconv.continuousOn isOpen_univ)
    have hhigh : ∀ s : ℝ, ∃ x, s < f x :=
      finiteConvex_unboundedAbove f hfconv hnonconstant
    have hrange := finiteProductGaussian_closedSublevel_range f hfcont htail hhigh
    have hEhrhard := finiteProductGaussianEhrhard_certified (κ := κ)
    simpa [μ] using convex_exp_lower_tail_exp_of_closed_sublevel_range μ f hfconv
      hEhrhard ht hrange hY hYmeas hmean hσ hσ₄ hvar
  · have htailzero : μ.real {x | f x ≤ -t} = 0 := by
      apply le_antisymm (le_of_not_gt htail)
      exact MeasureTheory.measureReal_nonneg
    rw [htailzero]
    positivity

end BrownianSharp.AlignmentPaperConvexTail
