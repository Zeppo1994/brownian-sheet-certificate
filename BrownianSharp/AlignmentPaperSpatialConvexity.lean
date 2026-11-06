import BrownianSharp.AlignmentPaperSpatialExponential
import BrownianSharp.AlignmentPaperConvexTail
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! Convexity for a spatial integral of exponentials. This proves the actual
integral step in the paper, independently of the finite-grid alternative. -/
noncomputable section
open MeasureTheory BrownianSharp.Concentration
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperSpatialConvexity

variable {α E : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Positive spatial exponential partition function. -/
def integralExponential (μ : Measure α) (L : α → E →ₗ[ℝ] ℝ) (z : E) : ℝ :=
  ∫ x, Real.exp (L x z) ∂μ

theorem integralExponential_pos (μ : Measure α) [NeZero μ]
    (L : α → E →ₗ[ℝ] ℝ) (z : E)
    (hi : Integrable (fun x => Real.exp (L x z)) μ) :
    0 < integralExponential μ L z := by
  apply (integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hi).2
  simpa [Function.support, Real.exp_ne_zero] using (show 0 < μ Set.univ from pos_iff_ne_zero.mpr (fun hz => NeZero.ne μ (Measure.measure_univ_eq_zero.mp hz)))

/-- The integral form of the normalized weighted-AM--GM argument. Every
integral is the actual spatial integral; no quadrature grid is substituted. -/
theorem integralExponential_holder (μ : Measure α) [NeZero μ]
    (L : α → E →ₗ[ℝ] ℝ)
    (hI : ∀ z, Integrable (fun x => Real.exp (L x z)) μ)
    (x y : E) (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u+v=1) :
    integralExponential μ L (u • x+v • y) ≤
      (integralExponential μ L x)^u * (integralExponential μ L y)^v := by
  let sx := integralExponential μ L x
  let sy := integralExponential μ L y
  have hsx : 0 < sx := integralExponential_pos μ L x (hI x)
  have hsy : 0 < sy := integralExponential_pos μ L y (hI y)
  let A := sx^u * sy^v
  have hA : 0 < A := by dsimp [A]; positivity
  have hterm (i : α) :
      Real.exp (L i (u • x+v • y)) = A *
        ((Real.exp (L i x)/sx)^u * (Real.exp (L i y)/sy)^v) := by
    dsimp [A]
    rw [show L i (u • x+v • y) = u*L i x+v*L i y by simp, Real.exp_add]
    rw [Real.rpow_def_of_pos hsx, Real.rpow_def_of_pos hsy,
      Real.rpow_def_of_pos (div_pos (Real.exp_pos _) hsx),
      Real.rpow_def_of_pos (div_pos (Real.exp_pos _) hsy)]
    rw [Real.log_div (Real.exp_pos _).ne' hsx.ne',
      Real.log_div (Real.exp_pos _).ne' hsy.ne', Real.log_exp, Real.log_exp]
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hpoint (i : α) :
      Real.exp (L i (u • x+v • y))/A ≤
        u*(Real.exp (L i x)/sx)+v*(Real.exp (L i y)/sy) := by
    rw [hterm]
    rw [mul_div_cancel_left₀ _ hA.ne']
    exact Real.geom_mean_le_arith_mean2_weighted hu hv (by positivity) (by positivity) huv
  have hbound := integral_mono ((hI (u • x+v • y)).div_const A)
    (((hI x).div_const sx).const_mul u |>.add (((hI y).div_const sy).const_mul v)) hpoint
  change (∫ i, Real.exp (L i (u • x+v • y))/A ∂μ) ≤
    ∫ i, u*(Real.exp (L i x)/sx)+v*(Real.exp (L i y)/sy) ∂μ at hbound
  rw [integral_div, integral_add (((hI x).div_const sx).const_mul u)
    (((hI y).div_const sy).const_mul v), integral_const_mul, integral_const_mul,
    integral_div, integral_div] at hbound
  change integralExponential μ L (u • x+v • y)/A ≤ u*(sx/sx)+v*(sy/sy) at hbound
  rw [div_self hsx.ne', div_self hsy.ne', mul_one, mul_one, huv] at hbound
  exact (div_le_one hA).mp hbound

/-- The literal spatial log-partition function is convex on the coefficient
space, with integrability the only analytic premise. -/
theorem log_integralExponential_convexOn (μ : Measure α) [NeZero μ]
    (L : α → E →ₗ[ℝ] ℝ)
    (hI : ∀ z, Integrable (fun x => Real.exp (L x z)) μ) :
    ConvexOn ℝ Set.univ (fun z => Real.log (integralExponential μ L z)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy u v hu hv huv
  have hsx := integralExponential_pos μ L x (hI x)
  have hsy := integralExponential_pos μ L y (hI y)
  have hsz := integralExponential_pos μ L (u • x+v • y) (hI _)
  calc
    Real.log (integralExponential μ L (u • x+v • y)) ≤
      Real.log ((integralExponential μ L x)^u * (integralExponential μ L y)^v) :=
      Real.log_le_log hsz (integralExponential_holder μ L hI x y u v hu hv huv)
    _ = u • Real.log (integralExponential μ L x)+v • Real.log (integralExponential μ L y) := by
      rw [Real.log_mul (Real.rpow_pos_of_pos hsx _).ne' (Real.rpow_pos_of_pos hsy _).ne',
        Real.log_rpow hsx, Real.log_rpow hsy]
      rfl

/-- The added sign coordinate turns the actual cosh integral into an
exponential integral. The coefficient action remains the same linear row. -/
def signedRowLinear {κ : Type*} [Fintype κ] (τ : ℝ) (a : α → κ → ℝ)
    (p : α × Bool) : (κ → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun z => (if p.2 then 1 else -1) * Real.sqrt τ * ∑ i, a p.1 i*z i
  map_add' := by intro x y; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c z
    simp only [Pi.smul_apply, smul_eq_mul]
    simp_rw [show ∀ i, a p.1 i*(c*z i) = c*(a p.1 i*z i) by intro i; ring]
    rw [← Finset.mul_sum]
    simp only [RingHom.id_apply]
    ring

theorem signedRowLinear_abs_le {κ : Type*} [Fintype κ] (τ : ℝ)
    (a : α → κ → ℝ) (ha : ∀ x, ∑ i, a x i^2=1)
    (p : α × Bool) (z : κ → ℝ) :
    |signedRowLinear τ a p z| ≤ Real.sqrt τ * ∑ i, |z i| := by
  have hc (i : κ) : |a p.1 i| ≤ 1 := by
    have hs : a p.1 i^2 ≤ 1 := by
      calc
        _ ≤ ∑ j, a p.1 j^2 := Finset.single_le_sum
          (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        _ = 1 := ha p.1
    nlinarith [sq_abs (a p.1 i)]
  have hs : |∑ i, a p.1 i*z i| ≤ ∑ i, |z i| := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i hi
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (hc i)
  change |(if p.2 then 1 else -1) * Real.sqrt τ * ∑ i, a p.1 i*z i| ≤ _
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg τ)]
  have hsign : |(if p.2 then (1:ℝ) else -1)| = 1 := by cases p.2 <;> norm_num
  rw [hsign, one_mul]
  exact mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg τ)

theorem signedRowLinear_exp_integrable {κ : Type*} [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (τ : ℝ)
    (a : α → κ → ℝ) (ha : ∀ x, ∑ i, a x i^2=1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) (z : κ → ℝ) :
    Integrable (fun p : α × Bool => Real.exp (signedRowLinear τ a p z))
      (μ.prod (Measure.count : Measure Bool)) := by
  have hsign : Measurable (fun b : Bool => if b then (1:ℝ) else -1) :=
    measurable_of_countable _
  have hm : Measurable (fun p : α × Bool => Real.exp (signedRowLinear τ a p z)) := by
    dsimp [signedRowLinear]
    exact (hsign.comp measurable_snd |>.mul measurable_const |>.mul
      (Finset.measurable_sum Finset.univ (fun i _ =>
        (haMeas i |>.comp measurable_fst).mul_const (z i)))).exp
  apply Integrable.of_bound hm.aestronglyMeasurable
    (Real.exp (Real.sqrt τ * ∑ i, |z i|))
  filter_upwards [] with p
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_exp.mpr
    ((le_abs_self _).trans (signedRowLinear_abs_le τ a ha p z))

theorem signedRow_integral_eq_two_cosh {κ : Type*} [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (τ : ℝ)
    (a : α → κ → ℝ) (ha : ∀ x, ∑ i, a x i^2=1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) (z : κ → ℝ) :
    integralExponential (μ.prod (Measure.count : Measure Bool))
      (signedRowLinear τ a) z =
      2 * ∫ x, Real.cosh (Real.sqrt τ * ∑ i, a x i*z i) ∂μ := by
  unfold integralExponential
  rw [integral_prod _ (signedRowLinear_exp_integrable μ τ a ha haMeas z)]
  have heq (x : α) :
      (∫ b : Bool, Real.exp (signedRowLinear τ a (x,b) z) ∂Measure.count) =
        2*Real.cosh (Real.sqrt τ * ∑ i, a x i*z i) := by
    rw [integral_count]
    simp [signedRowLinear, Real.cosh_eq] <;> ring
  simp_rw [heq]
  exact integral_const_mul _ _

/-- Actual spatial log-cosh convexity, including the paper's exponential
normalization. All spatial integrability is discharged from unit rows. -/
theorem spatialCoshAverage_log_convexOn {κ : Type*} [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (τ : ℝ)
    (a : α → κ → ℝ) (ha : ∀ x, ∑ i, a x i^2=1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) :
    ConvexOn ℝ Set.univ (fun z => Real.log
      (AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a z)) := by
  let ν := μ.prod (Measure.count : Measure Bool)
  haveI : NeZero ν := by
    refine ⟨?_⟩
    intro hz
    have hv : ν Set.univ = 2 := by
      change (μ.prod (Measure.count : Measure Bool)) Set.univ = 2
      rw [← Set.univ_prod_univ, Measure.prod_prod]
      simp [Measure.count_apply_finite]
    rw [hz] at hv
    norm_num at hv
  have hI := signedRowLinear_exp_integrable μ τ a ha haMeas
  have hconv := log_integralExponential_convexOn ν (signedRowLinear τ a) hI
  have heq : (fun z => Real.log
      (AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a z)) =
      (fun z => Real.log (integralExponential ν (signedRowLinear τ a) z) +
        (-τ/2-Real.log 2)) := by
    funext z
    have hp := integralExponential_pos ν (signedRowLinear τ a) z (hI z)
    have hid := signedRow_integral_eq_two_cosh μ τ a ha haMeas z
    have hcosh : 0 < ∫ x, Real.cosh (Real.sqrt τ * ∑ i, a x i*z i) ∂μ := by
      change 0 < integralExponential ν (signedRowLinear τ a) z at hp
      change integralExponential ν (signedRowLinear τ a) z = _ at hid
      linarith
    change Real.log (Real.exp (-τ/2) * _) = _
    rw [Real.log_mul (Real.exp_pos _).ne' hcosh.ne', Real.log_exp]
    rw [hid, Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hcosh.ne']
    ring
  rw [heq]
  exact hconv.add_const _

theorem unitRow_evaluation_abs_le_sqrt {κ : Type*} [Fintype κ]
    (a z : κ → ℝ) (ha : ∑ i, a i^2=1) :
    |∑ i, a i*z i| ≤ Real.sqrt (∑ i, z i^2) := by
  have hsq := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a z
  simp only [ha, one_mul] at hsq
  have hnon : 0 ≤ ∑ i, z i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hsqrt := Real.sq_sqrt hnon
  nlinarith [sq_abs (∑ i, a i*z i), abs_nonneg (∑ i, a i*z i),
    Real.sqrt_nonneg (∑ i, z i^2)]

private theorem cosh_le_exp_abs (t : ℝ) : Real.cosh t ≤ Real.exp |t| := by
  rw [Real.cosh_eq]
  have hp := Real.exp_le_exp.mpr (le_abs_self t)
  have hn := Real.exp_le_exp.mpr (neg_le_abs t)
  linarith

theorem spatialCosh_integrand_integrable {κ : Type*} [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (τ : ℝ)
    (a : α → κ → ℝ) (ha : ∀ x, ∑ i, a x i^2=1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) (z : κ → ℝ) :
    Integrable (fun x => Real.cosh (Real.sqrt τ * ∑ i, a x i*z i)) μ := by
  apply Integrable.of_bound
    (by fun_prop (disch := exact haMeas _))
    (Real.exp (Real.sqrt τ * Real.sqrt (∑ i, z i^2)))
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Real.cosh_pos _).le]
  apply (cosh_le_exp_abs _).trans
  apply Real.exp_le_exp.mpr
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg τ)]
  exact mul_le_mul_of_nonneg_left (unitRow_evaluation_abs_le_sqrt (a x) z (ha x))
    (Real.sqrt_nonneg τ)

/-- The manuscript's exact coefficient-size bounds, expressed as the square
root of the finite sum of coordinate squares (the Euclidean norm). -/
theorem spatialCoshAverage_bounds {κ : Type*} [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (τ : ℝ)
    (a : α → κ → ℝ) (ha : ∀ x, ∑ i, a x i^2=1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) (z : κ → ℝ) :
    Real.exp (-τ/2) ≤ AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a z ∧
    AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a z ≤
      Real.exp (-τ/2+Real.sqrt τ * Real.sqrt (∑ i, z i^2)) := by
  have hi := spatialCosh_integrand_integrable μ τ a ha haMeas z
  have hlo : (1:ℝ) ≤ ∫ x, Real.cosh (Real.sqrt τ * ∑ i, a x i*z i) ∂μ := by
    calc
      1 = ∫ _ : α, (1:ℝ) ∂μ := by simp
      _ ≤ _ := integral_mono (integrable_const _) hi (fun x => Real.one_le_cosh _)
  have hhi : (∫ x, Real.cosh (Real.sqrt τ * ∑ i, a x i*z i) ∂μ) ≤
      Real.exp (Real.sqrt τ * Real.sqrt (∑ i, z i^2)) := by
    calc
      _ ≤ ∫ _ : α, Real.exp (Real.sqrt τ * Real.sqrt (∑ i, z i^2)) ∂μ := by
        apply integral_mono hi (integrable_const _)
        intro x
        apply (cosh_le_exp_abs _).trans
        apply Real.exp_le_exp.mpr
        rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg τ)]
        exact mul_le_mul_of_nonneg_left (unitRow_evaluation_abs_le_sqrt (a x) z (ha x))
          (Real.sqrt_nonneg τ)
      _ = _ := by simp
  constructor
  · change Real.exp (-τ/2) ≤ Real.exp (-τ/2)*_
    nlinarith [Real.exp_pos (-τ/2)]
  · change Real.exp (-τ/2)*_ ≤ _
    rw [Real.exp_add]
    exact mul_le_mul_of_nonneg_left hhi (Real.exp_pos _).le

theorem spatialCoshAverage_measurable {κ : Type*} [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (τ : ℝ)
    (a : α → κ → ℝ) (haMeas : ∀ i, Measurable (fun x => a x i)) :
    Measurable (AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a) := by
  have hm : Measurable (fun p : (κ → ℝ) × α =>
      Real.cosh (Real.sqrt τ * ∑ i, a p.2 i*p.1 i)) := by
    fun_prop (disch := exact haMeas _)
  exact (hm.stronglyMeasurable.integral_prod_right'.measurable).const_mul _

/-- Every positive moment in the manuscript's spatial observable is finite.
The finite Gaussian envelope is proved, not postulated as a Fernique input. -/
theorem spatialCoshAverage_rpow_integrable {κ : Type*} [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (τ : ℝ) (hτ : 0 ≤ τ)
    (a : α → κ → ℝ) (ha : ∀ x, ∑ i, a x i^2=1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) (p : ℝ) (hp : 0 < p) :
    Integrable (fun z => (AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a z)^p)
      (productStandardGaussian κ) := by
  let U := AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a
  have hmajor := AlignmentPaperSpatialExponential.productGaussian_exp_abs_sum_integrable
    (κ := κ) (p*Real.sqrt τ) (mul_nonneg hp.le (Real.sqrt_nonneg _))
  apply (hmajor.const_mul ((Real.exp (-τ/2))^p)).mono'
    (((spatialCoshAverage_measurable μ τ a haMeas).pow_const p).aestronglyMeasurable)
  filter_upwards [] with z
  obtain ⟨hlo,hhi⟩ := spatialCoshAverage_bounds μ τ a ha haMeas z
  have hU : 0 < U z := (Real.exp_pos (-τ/2)).trans_le hlo
  have hs : Real.sqrt (∑ i, z i^2) ≤ ∑ i, |z i| := by
    have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
      (s := (Finset.univ : Finset κ)) (f := fun i => |z i|)
      (fun i _ => abs_nonneg _)
    simp only [sq_abs] at hsq
    have hsum : 0 ≤ ∑ i, z i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have habs : 0 ≤ ∑ i, |z i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    nlinarith [Real.sq_sqrt hsum, Real.sqrt_nonneg (∑ i, z i^2)]
  have hbound : U z ≤ Real.exp (-τ/2)*Real.exp (Real.sqrt τ * ∑ i, |z i|) := by
    apply hhi.trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    gcongr
  change ‖(U z)^p‖ ≤ _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hU.le _)]
  calc
    (U z)^p ≤ (Real.exp (-τ/2)*Real.exp (Real.sqrt τ * ∑ i, |z i|))^p :=
      Real.rpow_le_rpow hU.le hbound hp.le
    _ = Real.exp (-τ/2)^p * Real.exp (p*Real.sqrt τ * ∑ i, |z i|) := by
      rw [Real.mul_rpow (Real.exp_pos _).le (Real.exp_pos _).le,
        Real.rpow_def_of_pos (Real.exp_pos (Real.sqrt τ * ∑ i, |z i|)), Real.log_exp]
      congr 2
      ring

/-- The spatial observable has genuine finite variance, with no reliance on
Lean's default value for variance outside L2. -/
theorem spatialCoshAverage_memLp_two {κ : Type*} [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (τ : ℝ) (hτ : 0 ≤ τ)
    (a : α → κ → ℝ) (ha : ∀ x, ∑ i, a x i^2=1)
    (haMeas : ∀ i, Measurable (fun x => a x i)) :
    MemLp (AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a) 2
      (productStandardGaussian κ) := by
  apply (memLp_two_iff_integrable_sq
    (spatialCoshAverage_measurable μ τ a haMeas).aestronglyMeasurable).2
  simpa only [Real.rpow_two] using spatialCoshAverage_rpow_integrable
    μ τ hτ a ha haMeas 2 (by norm_num)

/-- Exact variance-scale tail transfer for the actual spatial statistic.
The mean, convexity and finite-variance prerequisites are proved above. The
remaining model-specific input is its spatial correlation variance estimate. -/
theorem spatialCoshAverage_lower_tail {κ : Type*} [Fintype κ]
    (μ : Measure α) [IsProbabilityMeasure μ] (τ : ℝ) (hτ : 0 ≤ τ)
    (a : α → κ → ℝ) (ha : ∀ x, ∑ i, a x i^2=1)
    (haMeas : ∀ i, Measurable (fun x => a x i))
    {t σ : ℝ} (ht : 1 ≤ t) (hσ : 0 < σ) (hσ₄ : σ ≤ 1/4)
    (hvar : ProbabilityTheory.variance
      (AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a)
        (productStandardGaussian κ) ≤ σ^2) :
    (productStandardGaussian κ).real {z |
      Real.log (AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a z) ≤ -t} ≤
      Real.exp (-(standardGaussianQuantile (3/4)*(t-1))^2/(18*σ^2)) := by
  let U := AlignmentPaperSpatialExponential.spatialCoshAverage μ τ a
  have heq : (fun z => Real.exp (Real.log (U z))) = U := by
    funext z
    have hp : 0 < U z := (Real.exp_pos (-τ/2)).trans_le
      (spatialCoshAverage_bounds μ τ a ha haMeas z).1
    exact Real.exp_log hp
  apply AlignmentPaperConvexTail.finiteProductGaussian_convex_exp_lower_tail
    (fun z => Real.log (U z)) (spatialCoshAverage_log_convexOn μ τ a ha haMeas) ht
  · rw [heq]
    exact spatialCoshAverage_memLp_two μ τ hτ a ha haMeas
  · rw [heq]
    exact spatialCoshAverage_measurable μ τ a haMeas
  · rw [heq]
    exact AlignmentPaperSpatialExponential.productGaussian_spatialCoshAverage_mean_actual
      μ a τ hτ ha haMeas
  · exact hσ
  · exact hσ₄
  · rw [heq]
    exact hvar

end BrownianSharp.AlignmentPaperSpatialConvexity
