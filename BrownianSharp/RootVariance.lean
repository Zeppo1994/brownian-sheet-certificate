import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# Root-variance repair for the Brownian sharp candidate

This module records the deterministic last step of the p-th-root variance
repair.  It does not formalize the Paouris--Valettas concentration theorem,
the Gaussian moment calculation, or the analytic estimate controlling the
rare event near zero.  In particular, it makes no Brownian small-ball claim.
Those inputs must be supplied and audited before this lemma can be used in a
certificate of the candidate theorem.
-/

namespace BrownianSharp

open scoped BigOperators
open MeasureTheory

/-- If the root statistic is close to its positive reference level in
mean-square, then its variance is small relative to the square of its mean.
This is the deterministic normalization used after the p-th-root repair.
The estimate is stated directly in terms of the variance and mean so it does
not conceal any probability or concentration hypothesis. -/
theorem root_variance_to_relative
    (reference mean variance error : ℝ)
    (href : 0 < reference)
    (hmean : reference / 2 ≤ mean)
    (herror_nonneg : 0 ≤ error)
    (herror : variance ≤ reference ^ 2 * error) :
    variance / mean ^ 2 ≤ 4 * error := by
  have hmean_pos : 0 < mean := lt_of_lt_of_le (by positivity) hmean
  have hden : 0 < mean ^ 2 := by positivity
  have hreference_sq : reference ^ 2 ≤ 4 * mean ^ 2 := by nlinarith [sq_nonneg (reference - 2 * mean)]
  rw [div_le_iff₀ hden]
  calc
    variance ≤ reference ^ 2 * error := herror
    _ ≤ (4 * mean ^ 2) * error := mul_le_mul_of_nonneg_right hreference_sq herror_nonneg
    _ = (4 * error) * mean ^ 2 := by ring

/-- The explicit root-error budget obtained in the candidate after splitting
at U = 1/2.  `rare` is the probability contribution of U ≤ 1/2, and `v`
is Var(U); supplying the rare-event estimate is an explicit obligation. -/
theorem root_error_budget
    (v rare p D C : ℝ)
    (hrare : rare ≤ 1 / D)
    (hgood : 4 * v / p ^ 2 ≤ 4 * C / D) :
    4 * v / p ^ 2 + rare ≤ (4 * C + 1) / D := by
  calc
    4 * v / p ^ 2 + rare ≤ 4 * C / D + 1 / D := add_le_add hgood hrare
    _ = (4 * C + 1) / D := by ring

/-- A finite-measure version of the rare-event split in (28.9).  The inputs
`hgood` and `hbad` are the pointwise calculus bounds for the p-th root on
`u ≥ 1/2` and `u < 1/2`, respectively.  The theorem proves the expectation
bookkeeping without hiding either pointwise bound or the mass of the bad
event.  `variance` and `rareMass` are unnormalized weighted sums; the caller
may supply a probability measure by requiring its weights to sum to one. -/
theorem finite_root_error_split
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (weight u : ι → ℝ) (bad : ι → Prop) [DecidablePred bad]
    (p : ℝ)
    (hp : 0 < p)
    (hw : ∀ i ∈ s, 0 ≤ weight i)
    (hgood : ∀ i ∈ s, ¬ bad i →
      (u i ^ (1 / p) - 1) ^ 2 ≤ 4 * (u i - 1) ^ 2 / p ^ 2)
    (hbad : ∀ i ∈ s, bad i → (u i ^ (1 / p) - 1) ^ 2 ≤ 1) :
    (∑ i ∈ s, weight i * (u i ^ (1 / p) - 1) ^ 2) ≤
      4 / p ^ 2 * (∑ i ∈ s, weight i * (u i - 1) ^ 2) +
        ∑ i ∈ s, weight i * (if bad i then 1 else 0) := by
  let variance : ℝ := ∑ i ∈ s, weight i * (u i - 1) ^ 2
  let rareMass : ℝ := ∑ i ∈ s, weight i * (if bad i then 1 else 0)
  have hpoint : ∀ i ∈ s,
      weight i * (u i ^ (1 / p) - 1) ^ 2 ≤
        weight i * (4 * (u i - 1) ^ 2 / p ^ 2 + (if bad i then 1 else 0)) := by
    intro i hi
    by_cases hb : bad i
    · have h := hbad i hi hb
      have hw' := hw i hi
      simp [hb]
      have hnonneg : 0 ≤ 4 * (u i - 1) ^ 2 / p ^ 2 := by positivity
      have hbound : (u i ^ (1 / p) - 1) ^ 2 ≤
          4 * (u i - 1) ^ 2 / p ^ 2 + 1 := by linarith
      simpa only [one_div] using mul_le_mul_of_nonneg_left hbound hw'
    · have h := hgood i hi hb
      have hw' := hw i hi
      simp [hb]
      simpa only [one_div] using mul_le_mul_of_nonneg_left h hw'
  calc
    (∑ i ∈ s, weight i * (u i ^ (1 / p) - 1) ^ 2) ≤
        ∑ i ∈ s, weight i *
          (4 * (u i - 1) ^ 2 / p ^ 2 + (if bad i then 1 else 0)) := by
            apply Finset.sum_le_sum
            intro i hi
            exact hpoint i hi
    _ = 4 / p ^ 2 * variance + rareMass := by
      dsimp [variance, rareMass]
      simp_rw [mul_add, Finset.sum_add_distrib]
      congr 1
      · simp_rw [div_eq_mul_inv]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring

/-- Deterministic comparison used in Step 6: the selected confinement
threshold is below half the root statistic's mean lower bound.  The
dimension-dependent scale factor has been separated into `kappa`; all
probabilistic estimates are explicit caller obligations. -/
theorem root_threshold_below_mean_half
    (n p kappa : ℝ)
    (hn : 0 ≤ n)
    (hkappa : 0 < kappa)
    (hp : kappa * (n + 1) / 2 ≤ p) :
    Real.sqrt kappa * Real.sqrt n / (32 * Real.sqrt 2) ≤
      Real.sqrt p / 16 := by
  have hp0 : 0 ≤ p := by nlinarith
  have hκ0 : 0 ≤ kappa := le_of_lt hkappa
  have hn0 : 0 ≤ n := hn
  have hA : 0 ≤ Real.sqrt kappa * Real.sqrt n := by positivity
  have hB : 0 ≤ 2 * Real.sqrt 2 * Real.sqrt p := by positivity
  have hprod : kappa * n ≤ 2 * p := by nlinarith
  have hsq : (Real.sqrt kappa * Real.sqrt n) ^ 2 ≤
      (2 * Real.sqrt 2 * Real.sqrt p) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hκ0, Real.sq_sqrt hn0]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
      Real.sq_sqrt hp0]
  have hAB : Real.sqrt kappa * Real.sqrt n ≤
      2 * Real.sqrt 2 * Real.sqrt p := by nlinarith
  have hden : 0 < 32 * Real.sqrt 2 := by positivity
  apply (div_le_iff₀ hden).2
  nlinarith [hAB]

end BrownianSharp

namespace BrownianSharp

open MeasureTheory

/-- The pointwise derivative bound behind the good half of the p-th-root
split. The exponent is in `(0, 1/2]`, and for every `x ≥ 1/2` the derivative
of `x^(1/p)` is at most `2/p` in absolute value. -/
theorem root_derivative_bound (p x : ℝ) (hp : 2 ≤ p) (hx : 1 / 2 ≤ x) :
    ‖deriv (fun t : ℝ => t ^ (1 / p)) x‖ ≤ 2 / p := by
  have hp0 : 0 < p := by linarith
  have hx0 : 0 < x := by linarith
  have hexp_nonpos : 1 / p - 1 ≤ 0 := by
    have hfrac : 1 / p ≤ 1 := (div_le_iff₀ hp0).2 (by linarith)
    linarith
  have hbase : x ^ (1 / p - 1) ≤ 2 := by
    by_cases hx1 : x ≤ 1
    · calc
        x ^ (1 / p - 1) ≤ (1 / 2 : ℝ) ^ (1 / p - 1) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hx hexp_nonpos
        _ ≤ (1 / 2 : ℝ) ^ (-1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num)
          have : 0 ≤ 1 / p := by positivity
          linarith
        _ = 2 := by norm_num
    · have hx1' : 1 ≤ x := le_of_not_ge hx1
      calc
        x ^ (1 / p - 1) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos hx1' hexp_nonpos
        _ ≤ 2 := by norm_num
  have hderiv : deriv (fun t : ℝ => t ^ (1 / p)) x =
      (1 / p) * x ^ (1 / p - 1) := by
    rw [Real.deriv_rpow_const x (1 / p)]
  rw [hderiv, Real.norm_eq_abs, abs_of_nonneg (by positivity :
    0 ≤ (1 / p) * x ^ (1 / p - 1))]
  calc
    (1 / p) * x ^ (1 / p - 1) ≤ (1 / p) * 2 :=
      mul_le_mul_of_nonneg_left hbase (by positivity)
    _ = 2 / p := by ring

/-- Pointwise p-th-root deviation on the good event `u ≥ 1/2`, proved by the
mean value theorem from `root_derivative_bound`. -/
theorem root_deviation_good (p u : ℝ) (hp : 2 ≤ p) (hu : 1 / 2 ≤ u) :
    |u ^ (1 / p) - 1| ≤ 2 / p * |u - 1| := by
  have hdiff : ∀ x ∈ Set.Ici (1 / 2 : ℝ),
      DifferentiableAt ℝ (fun t : ℝ => t ^ (1 / p)) x := by
    intro x hx
    change 1 / 2 ≤ x at hx
    exact Real.differentiableAt_rpow_const_of_ne (1 / p) (ne_of_gt (by linarith))
  have hbound : ∀ x ∈ Set.Ici (1 / 2 : ℝ),
      ‖deriv (fun t : ℝ => t ^ (1 / p)) x‖ ≤ 2 / p := by
    intro x hx
    exact root_derivative_bound p x hp hx
  have h := (convex_Ici (1 / 2 : ℝ)).norm_image_sub_le_of_norm_deriv_le
    (f := fun t : ℝ => t ^ (1 / p)) hdiff hbound
    (show u ∈ Set.Ici (1 / 2 : ℝ) from hu)
    (show (1 : ℝ) ∈ Set.Ici (1 / 2 : ℝ) by norm_num)
  simpa [Real.one_rpow, abs_sub_comm] using h

/-- Pointwise p-th-root deviation on the rare event `0 ≤ u < 1/2`. -/
theorem root_deviation_bad (p u : ℝ) (hp : 2 ≤ p) (hu0 : 0 ≤ u)
    (hu : u < 1 / 2) : |u ^ (1 / p) - 1| ≤ 1 := by
  have hroot0 : 0 ≤ u ^ (1 / p) := Real.rpow_nonneg hu0 _
  have hexp0 : 0 ≤ 1 / p := by positivity
  have hroot1 : u ^ (1 / p) ≤ 1 :=
    Real.rpow_le_one hu0 (by linarith) hexp0
  rw [abs_of_nonpos (by linarith : u ^ (1 / p) - 1 ≤ 0)]
  linarith

/-- Integrating the pointwise split preserves its exact variance and rare-mass
terms. Integrability and the pointwise estimate are explicit; no concentration
or Gaussian input is introduced here. -/
theorem integral_root_error_split
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f g badMass : α → ℝ) (coefficient : ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ) (hb : Integrable badMass μ)
    (hpoint : ∀ᵐ x ∂μ, f x ≤ coefficient * g x + badMass x) :
    (∫ x, f x ∂μ) ≤ coefficient * (∫ x, g x ∂μ) + ∫ x, badMass x ∂μ := by
  have hrhs : Integrable (fun x => coefficient * g x + badMass x) μ :=
    (hg.const_mul coefficient).add hb
  calc
    (∫ x, f x ∂μ) ≤ ∫ x, (coefficient * g x + badMass x) ∂μ :=
      integral_mono_ae hf hrhs hpoint
    _ = coefficient * (∫ x, g x ∂μ) + ∫ x, badMass x ∂μ := by
      rw [integral_add (hg.const_mul coefficient) hb]
      rw [integral_const_mul coefficient g]


/-- The actual measure-theoretic p-th-root variance split.  It applies the
proved good and bad pointwise bounds to a nonnegative random variable `U`.
The variance proxy and rare-event probability are the displayed integrals;
Gaussian concentration is still needed separately to bound the latter. -/
theorem integral_pth_root_variance_split
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (U : α → ℝ) (p : ℝ) (hp : 2 ≤ p)
    (hU : ∀ x, 0 ≤ U x)
    (hroot : Integrable (fun x => (U x ^ (1 / p) - 1) ^ 2) μ)
    (hvariance : Integrable (fun x => (U x - 1) ^ 2) μ)
    (hrare : Integrable (fun x => if U x < 1 / 2 then (1 : ℝ) else 0) μ) :
    (∫ x, (U x ^ (1 / p) - 1) ^ 2 ∂μ) ≤
      4 / p ^ 2 * (∫ x, (U x - 1) ^ 2 ∂μ) +
        ∫ x, (if U x < 1 / 2 then (1 : ℝ) else 0) ∂μ := by
  apply integral_root_error_split μ
    (fun x => (U x ^ (1 / p) - 1) ^ 2)
    (fun x => (U x - 1) ^ 2)
    (fun x => if U x < 1 / 2 then (1 : ℝ) else 0)
    (4 / p ^ 2) hroot hvariance hrare
  filter_upwards [] with x
  by_cases hbad : U x < 1 / 2
  · have hdev := root_deviation_bad p (U x) hp (hU x) hbad
    have hsq' : |U x ^ (1 / p) - 1| ^ 2 ≤ 1 ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).2 hdev
    have hsq : |U x ^ (1 / p) - 1| ^ 2 ≤ 1 := by simpa using hsq'
    have hnonneg : 0 ≤ 4 / p ^ 2 * (U x - 1) ^ 2 := by positivity
    have hsum : 1 ≤ 4 / p ^ 2 * (U x - 1) ^ 2 + 1 := by linarith
    have hif : (if U x < (1 / 2 : ℝ) then (1 : ℝ) else 0) = 1 := if_pos hbad
    rw [hif]
    simpa [sq_abs] using hsq.trans hsum
  · have hgood : 1 / 2 ≤ U x := le_of_not_gt hbad
    have hdev := root_deviation_good p (U x) hp hgood
    have hsq : |U x ^ (1 / p) - 1| ^ 2 ≤
        (2 / p * |U x - 1|) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (by positivity) (abs_nonneg _))).2 hdev
    have hformula : (2 / p * |U x - 1|) ^ 2 =
        4 / p ^ 2 * (U x - 1) ^ 2 := by rw [mul_pow, sq_abs]; ring
    have hsq' : (U x ^ (1 / p) - 1) ^ 2 ≤
        4 / p ^ 2 * (U x - 1) ^ 2 := by
      simpa [sq_abs, hformula] using hsq
    simpa [hbad] using hsq'.trans (le_add_of_nonneg_right (by positivity))

end BrownianSharp

namespace BrownianSharp

open MeasureTheory ProbabilityTheory

/-- An L2 error at most `δ ≤ 1/4` forces the mean root statistic to be at
least `1/2`. The proof uses Young's inequality pointwise and the probability
normalization, so no variance or mean estimate is assumed. -/
theorem l2_error_lower_bounds_mean
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (Y : α → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 4)
    (hY : Integrable Y μ)
    (hZsq : Integrable (fun x => (Y x - 1) ^ 2) μ)
    (hL2 : (∫ x, (Y x - 1) ^ 2 ∂μ) ≤ δ) :
    1 / 2 ≤ ∫ x, Y x ∂μ := by
  let Z : α → ℝ := fun x => Y x - 1
  let c : ℝ := (2 * Real.sqrt δ)⁻¹
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hpoint : ∀ x, |Z x| ≤ c * (Z x ^ 2 + δ) := by
    intro x
    have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
    have hsquare : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt (le_of_lt hδ)
    have hYoung : 2 * Real.sqrt δ * |Z x| ≤ Z x ^ 2 + δ := by
      nlinarith [sq_nonneg (|Z x| - Real.sqrt δ), sq_abs (Z x)]
    have hden : 0 < 2 * Real.sqrt δ := by positivity
    have hdiv : |Z x| ≤ (Z x ^ 2 + δ) / (2 * Real.sqrt δ) := by
      calc
        |Z x| = (2 * Real.sqrt δ * |Z x|) / (2 * Real.sqrt δ) := by field_simp
        _ ≤ (Z x ^ 2 + δ) / (2 * Real.sqrt δ) := by
          have h := div_le_div_of_nonneg_right hYoung hden.le
          simpa [mul_div_cancel_left₀, hden.ne'] using h
    simpa [c, div_eq_mul_inv, mul_comm] using hdiv
  have hZ : Integrable Z μ := hY.sub (integrable_const 1)
  have hrhs : Integrable (fun x => c * (Z x ^ 2 + δ)) μ :=
    (hZsq.add (integrable_const δ)).const_mul c
  have hAbs : (∫ x, |Z x| ∂μ) ≤ Real.sqrt δ := by
    calc
      (∫ x, |Z x| ∂μ) ≤ ∫ x, c * (Z x ^ 2 + δ) ∂μ :=
        integral_mono_ae hZ.norm hrhs (ae_of_all _ hpoint)
      _ = c * (∫ x, Z x ^ 2 ∂μ + δ) := by
        rw [integral_const_mul c, integral_add hZsq (integrable_const δ)]
        simp [Z]
      _ ≤ c * (δ + δ) := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hcpos)
        linarith
      _ = Real.sqrt δ := by
        dsimp [c]
        have hsquare : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt (le_of_lt hδ)
        field_simp
        nlinarith
  have hnorm := norm_integral_le_integral_norm (μ := μ) Z
  have hnorm' : |∫ x, Z x ∂μ| ≤ Real.sqrt δ := by
    simpa [Real.norm_eq_abs] using hnorm.trans hAbs
  have hZlower : -Real.sqrt δ ≤ ∫ x, Z x ∂μ := (abs_le.mp hnorm').1
  have hYeq : (∫ x, Y x ∂μ) = (∫ x, Z x ∂μ) + 1 := by
    calc
      (∫ x, Y x ∂μ) = ∫ x, (Z x + 1) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp [Z]
      _ = (∫ x, Z x ∂μ) + ∫ x, (1 : ℝ) ∂μ := integral_add hZ (integrable_const 1)
      _ = (∫ x, Z x ∂μ) + 1 := by simp
  have hsqrtδ : Real.sqrt δ ≤ 1 / 2 := by
    calc
      Real.sqrt δ ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hδsmall
      _ = 1 / 2 := by norm_num
  calc
    (1 / 2 : ℝ) ≤ 1 - Real.sqrt δ := by linarith
    _ ≤ 1 + ∫ x, Z x ∂μ := by linarith
    _ = ∫ x, Y x ∂μ := by rw [hYeq]; ring

/-- The probability variance is bounded by the mean-square error from one.
Together with `l2_error_lower_bounds_mean`, this gives the relative variance
needed for the second convex-concentration application. -/
theorem l2_error_bounds_variance
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (Y : α → ℝ)
    (hY : AEStronglyMeasurable Y μ) :
    variance Y μ ≤ ∫ x, (Y x - 1) ^ 2 ∂μ := by
  have hZ : AEStronglyMeasurable (fun x => Y x - 1) μ :=
    hY.sub aestronglyMeasurable_const
  have hshift := variance_le_expectation_sq (X := fun x => Y x - 1) hZ
  rw [variance_sub_const hY 1] at hshift
  exact hshift

/-- Convert the L2 root-error estimate in probability directly into the
mean and relative-variance inputs for Step 5. -/
theorem l2_error_to_relative_variance
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (Y : α → ℝ) (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 4)
    (hY : Integrable Y μ)
    (hZsq : Integrable (fun x => (Y x - 1) ^ 2) μ)
    (hL2 : (∫ x, (Y x - 1) ^ 2 ∂μ) ≤ δ) :
    1 / 2 ≤ ∫ x, Y x ∂μ ∧
      variance Y μ / (∫ x, Y x ∂μ) ^ 2 ≤ 4 * δ := by
  have hmean := l2_error_lower_bounds_mean μ Y δ hδ hδsmall hY hZsq hL2
  have hvariance := l2_error_bounds_variance μ Y hY.aestronglyMeasurable
  have hvariance' : variance Y μ ≤ δ := hvariance.trans hL2
  have hmeanpos : 0 < ∫ x, Y x ∂μ := lt_of_lt_of_le (by norm_num) hmean
  constructor
  · exact hmean
  · rw [div_le_iff₀ (sq_pos_of_pos hmeanpos)]
    have hmeansq : (1 / 2 : ℝ) ^ 2 ≤ (∫ x, Y x ∂μ) ^ 2 := by nlinarith
    have hδbound : δ ≤ 4 * δ * (∫ x, Y x ∂μ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hmeansq (le_of_lt hδ)]
    exact le_trans hvariance' hδbound

end BrownianSharp
