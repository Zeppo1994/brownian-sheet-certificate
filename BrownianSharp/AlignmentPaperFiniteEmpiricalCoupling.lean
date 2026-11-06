import BrownianSharp.AlignmentPaperQuantization
import Mathlib.Tactic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Moments.Variance

/-!
# Finite-support empirical coupling estimates

This file isolates the finite transport calculation used in multiscale
empirical Wasserstein bounds. Weights and coupling matrices are represented by
nonnegative real numbers; no Gaussian profile or desired rate is assumed.
-/

noncomputable section
open scoped BigOperators
open scoped ENNReal
open MeasureTheory

namespace BrownianSharp.AlignmentPaperFiniteEmpiricalCoupling

/-- Couple common mass diagonally and couple residual masses independently. -/
def commonResidualMatrix {N : ℕ} (c a b : Fin N → ℝ) (r : ℝ)
    (i j : Fin N) : ℝ :=
  (if i = j then c i else 0) + a i * b j / r

/-- Row sums of the common-mass plus residual-product coupling. -/
theorem commonResidualMatrix_row_sum {N : ℕ} (c a b : Fin N → ℝ)
    (r : ℝ) (i : Fin N) :
    (∑ j : Fin N, commonResidualMatrix c a b r i j) =
      c i + a i * (∑ j : Fin N, b j) / r := by
  simp only [commonResidualMatrix, Finset.sum_add_distrib]
  simp
  rw [← Finset.sum_div, Finset.mul_sum]

/-- Column sums of the common-mass plus residual-product coupling. -/
theorem commonResidualMatrix_col_sum {N : ℕ} (c a b : Fin N → ℝ)
    (r : ℝ) (j : Fin N) :
    (∑ i : Fin N, commonResidualMatrix c a b r i j) =
      c j + b j * (∑ i : Fin N, a i) / r := by
  simp only [commonResidualMatrix, Finset.sum_add_distrib]
  simp
  rw [← Finset.sum_div, ← Finset.sum_mul]
  ring

/-- If the two residual vectors both have total mass `r > 0`, this matrix has
the prescribed row and column marginals `c+a` and `c+b`. -/
theorem commonResidualMatrix_marginals {N : ℕ} (c a b : Fin N → ℝ)
    (r : ℝ) (hr : 0 < r)
    (ha : ∑ i : Fin N, a i = r) (hb : ∑ i : Fin N, b i = r) :
    (∀ i, (∑ j : Fin N, commonResidualMatrix c a b r i j) = c i + a i) ∧
    (∀ j, (∑ i : Fin N, commonResidualMatrix c a b r i j) = c j + b j) := by
  have hrne : r ≠ 0 := ne_of_gt hr
  constructor
  · intro i
    rw [commonResidualMatrix_row_sum c a b r i, hb]
    field_simp [hrne]
  · intro j
    rw [commonResidualMatrix_col_sum c a b r j, ha]
    field_simp [hrne]

/-- When the residual mass is zero, nonnegative residual vectors vanish, so
the diagonal common-mass matrix still has exactly the requested marginals. -/
theorem commonResidualMatrix_zero_marginals {N : ℕ} (c a b : Fin N → ℝ)
    (ha : ∑ i : Fin N, a i = 0) (hb : ∑ i : Fin N, b i = 0)
    (ha_nonneg : ∀ i, 0 ≤ a i) (hb_nonneg : ∀ i, 0 ≤ b i) :
    (∀ i, (∑ j : Fin N, commonResidualMatrix c a b 0 i j) = c i + a i) ∧
    (∀ j, (∑ i : Fin N, commonResidualMatrix c a b 0 i j) = c j + b j) := by
  have h_a_zero : ∀ i, a i = 0 := by
    intro i
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j hj => ha_nonneg j)).1 ha i (Finset.mem_univ i)
    exact hz
  have h_b_zero : ∀ j, b j = 0 := by
    intro j
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i hi => hb_nonneg i)).1 hb j (Finset.mem_univ j)
    exact hz
  constructor
  · intro i
    rw [commonResidualMatrix_row_sum c a b 0 i, hb, h_a_zero i]
    simp
  · intro j
    rw [commonResidualMatrix_col_sum c a b 0 j, ha, h_b_zero j]
    simp

/-- The common-residual coupling matrix has nonnegative entries when all
component masses are nonnegative and the residual mass is positive. -/
theorem commonResidualMatrix_nonneg {N : ℕ} (c a b : Fin N → ℝ)
    (r : ℝ) (hr : 0 < r)
    (hc : ∀ i, 0 ≤ c i) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    ∀ i j, 0 ≤ commonResidualMatrix c a b r i j := by
  intro i j
  unfold commonResidualMatrix
  apply add_nonneg
  · by_cases hij : i = j
    · simp [hij]
      exact hc j
    · simp [hij]
  · exact div_nonneg (mul_nonneg (ha i) (hb j)) (le_of_lt hr)

/-- The normalized residual-product part has total mass `r`. -/
theorem residualProductMatrix_mass {N : ℕ} (a b : Fin N → ℝ)
    (r : ℝ) (hr : 0 < r)
    (ha : ∑ i : Fin N, a i = r) (hb : ∑ i : Fin N, b i = r) :
    (∑ i : Fin N, ∑ j : Fin N, a i * b j / r) = r := by
  have hdouble :
      (∑ i : Fin N, ∑ j : Fin N, a i * b j) =
        (∑ i : Fin N, a i) * (∑ j : Fin N, b j) := by
    calc
      (∑ i : Fin N, ∑ j : Fin N, a i * b j) =
          ∑ i : Fin N, a i * (∑ j : Fin N, b j) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
      _ = _ := by rw [Finset.sum_mul]
  calc
    (∑ i : Fin N, ∑ j : Fin N, a i * b j / r) =
        (∑ i : Fin N, ∑ j : Fin N, a i * b j) / r := by
      simp_rw [← Finset.sum_div]
    _ = (∑ i : Fin N, a i) * (∑ j : Fin N, b j) / r := by rw [hdouble]
    _ = r := by rw [ha, hb]; field_simp [ne_of_gt hr]

/-- Finite atomic measure with extended nonnegative weights. -/
noncomputable def finiteAtomicMeasure {N : ℕ} {X : Type*}
    [MeasurableSpace X] (p : Fin N → ℝ≥0∞) (z : Fin N → X) : Measure X :=
  Measure.sum fun i : Fin N => p i • Measure.dirac (z i)

/-- Measure on pairs induced by a finite transport matrix. -/
noncomputable def finiteCouplingMeasure {N : ℕ} {X : Type*}
    [MeasurableSpace X] (w : Fin N → Fin N → ℝ≥0∞) (z : Fin N → X) :
    Measure (X × X) :=
  Measure.sum fun i : Fin N =>
    Measure.sum fun j : Fin N => w i j • Measure.dirac (z i, z j)

noncomputable def commonResidualTransportWeight {N : ℕ}
    (c a b : Fin N → ℝ) (r : ℝ) : Fin N → Fin N → ℝ≥0∞ :=
  fun i j => ENNReal.ofReal (commonResidualMatrix c a b r i j)

/-- Exact quadratic cost integral of a finite atomic coupling measure. -/
theorem finiteCouplingMeasure_lintegral_edist_sq {N : ℕ} {X : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] [PseudoEMetricSpace X]
    (w : Fin N → Fin N → ℝ≥0∞) (z : Fin N → X) :
    (∫⁻ y : X × X, edist y.1 y.2 ^ 2 ∂finiteCouplingMeasure w z) =
      ∑ i : Fin N, ∑ j : Fin N, w i j * edist (z i) (z j) ^ 2 := by
  simp [finiteCouplingMeasure, lintegral_sum_measure,
    lintegral_smul_measure, lintegral_dirac]

/-- Total coupling mass away from the diagonal. -/
def offDiagonalMatrixMass {N : ℕ} (w : Fin N → Fin N → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ i : Fin N, ∑ j : Fin N, if i = j then 0 else w i j

/-- If a finite coupling moves at most mass `r` off the diagonal and its
support has squared diameter at most `D^2`, its actual quadratic transport
integral is at most `D^2*r`. -/
theorem finiteCouplingMeasure_cost_le_of_offDiagonalMass {N : ℕ} {X : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] [PseudoEMetricSpace X]
    (w : Fin N → Fin N → ℝ≥0∞) (z : Fin N → X) (D r : ℝ≥0∞)
    (hdiam : ∀ i j, edist (z i) (z j) ^ 2 ≤ D ^ 2)
    (hres : offDiagonalMatrixMass w ≤ r) :
    (∫⁻ y : X × X, edist y.1 y.2 ^ 2 ∂finiteCouplingMeasure w z) ≤ D ^ 2 * r := by
  have hpoint : ∀ i j,
      w i j * edist (z i) (z j) ^ 2 ≤
        (if i = j then 0 else w i j) * D ^ 2 := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]
      exact mul_le_mul_of_nonneg_left (hdiam i j) (show 0 ≤ w i j from bot_le)
  rw [finiteCouplingMeasure_lintegral_edist_sq]
  calc
    (∑ i : Fin N, ∑ j : Fin N, w i j * edist (z i) (z j) ^ 2) ≤
        ∑ i : Fin N, ∑ j : Fin N, (if i = j then 0 else w i j) * D ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact hpoint i j
    _ = offDiagonalMatrixMass w * D ^ 2 := by
      simp [offDiagonalMatrixMass, Finset.sum_mul]
    _ ≤ r * D ^ 2 := mul_le_mul_of_nonneg_right hres (sq_nonneg D)
    _ = D ^ 2 * r := mul_comm _ _

/-- Off-diagonal mass of the common-residual matrix is no larger than its
residual mass `r`. -/
theorem commonResidualMatrix_offDiagonalMass_le {N : ℕ}
    (c a b : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    (ha : ∑ i : Fin N, a i = r) (hb : ∑ i : Fin N, b i = r)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (ha_nonneg : ∀ i, 0 ≤ a i) (hb_nonneg : ∀ i, 0 ≤ b i) :
    offDiagonalMatrixMass
      (fun i j => ENNReal.ofReal (commonResidualMatrix c a b r i j)) ≤
      ENNReal.ofReal r := by
  have hres_nonneg : ∀ i j, 0 ≤ a i * b j / r := by
    intro i j
    exact div_nonneg (mul_nonneg (ha_nonneg i) (hb_nonneg j)) (le_of_lt hr)
  have hoff_real :
      (∑ i : Fin N, ∑ j : Fin N,
        if i = j then 0 else commonResidualMatrix c a b r i j) ≤ r := by
    calc
      _ ≤ ∑ i : Fin N, ∑ j : Fin N, a i * b j / r := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i = j
        · subst j
          simp
          exact hres_nonneg i i
        · simp [hij, commonResidualMatrix]
      _ = r := residualProductMatrix_mass a b r hr ha hb
  have hterm_nonneg : ∀ i j,
      0 ≤ if i = j then 0 else commonResidualMatrix c a b r i j := by
    intro i j
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, commonResidualMatrix]
      exact hres_nonneg i j
  have hinner (i : Fin N) :
      (∑ j : Fin N, ENNReal.ofReal
        (if i = j then 0 else commonResidualMatrix c a b r i j)) =
        ENNReal.ofReal (∑ j : Fin N,
          if i = j then 0 else commonResidualMatrix c a b r i j) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun j => if i = j then 0 else commonResidualMatrix c a b r i j)
      (fun j hj => hterm_nonneg i j)]
  have houter :
      (∑ i : Fin N, ENNReal.ofReal
        (∑ j : Fin N, if i = j then 0 else commonResidualMatrix c a b r i j)) =
        ENNReal.ofReal (∑ i : Fin N, ∑ j : Fin N,
          if i = j then 0 else commonResidualMatrix c a b r i j) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun i => ∑ j : Fin N,
        if i = j then 0 else commonResidualMatrix c a b r i j)
      (fun i hi => Finset.sum_nonneg fun j hj => hterm_nonneg i j)]
  calc
    offDiagonalMatrixMass
        (fun i j => ENNReal.ofReal (commonResidualMatrix c a b r i j)) =
      ∑ i : Fin N, ENNReal.ofReal
        (∑ j : Fin N, if i = j then 0 else commonResidualMatrix c a b r i j) := by
        simp only [offDiagonalMatrixMass]
        apply Finset.sum_congr rfl
        intro i hi
        calc
          (∑ j : Fin N,
            if i = j then 0 else ENNReal.ofReal (commonResidualMatrix c a b r i j)) =
              ∑ j : Fin N, ENNReal.ofReal
                (if i = j then 0 else commonResidualMatrix c a b r i j) := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hij : i = j
            · subst j
              simp
            · simp [hij]
          _ = ENNReal.ofReal (∑ j : Fin N,
              if i = j then 0 else commonResidualMatrix c a b r i j) := hinner i
    _ = ENNReal.ofReal (∑ i : Fin N, ∑ j : Fin N,
          if i = j then 0 else commonResidualMatrix c a b r i j) := houter
    _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hoff_real

theorem commonResidualTransportWeight_offDiagonalMass_le {N : ℕ}
    (c a b : Fin N → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (ha : ∑ i : Fin N, a i = r) (hb : ∑ i : Fin N, b i = r)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (ha_nonneg : ∀ i, 0 ≤ a i) (hb_nonneg : ∀ i, 0 ≤ b i) :
    offDiagonalMatrixMass (commonResidualTransportWeight c a b r) ≤ ENNReal.ofReal r := by
  by_cases hr0 : r = 0
  · have hA_zero : ∀ i, a i = 0 := by
      intro i
      have hs : (∑ i : Fin N, a i) = 0 := by rw [ha, hr0]
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => ha_nonneg j)).1 hs i
        (Finset.mem_univ i)
    have hB_zero : ∀ j, b j = 0 := by
      intro j
      have hs : (∑ j : Fin N, b j) = 0 := by rw [hb, hr0]
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => hb_nonneg i)).1 hs j
        (Finset.mem_univ j)
    have hterm (i j : Fin N) :
        (if i = j then 0 else commonResidualTransportWeight c a b r i j) = 0 := by
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, commonResidualTransportWeight, commonResidualMatrix,
          hr0, hA_zero i, hB_zero j]
    rw [show offDiagonalMatrixMass (commonResidualTransportWeight c a b r) = 0 by
      simp only [offDiagonalMatrixMass]
      apply Finset.sum_eq_zero
      intro i hi
      apply Finset.sum_eq_zero
      intro j hj
      exact hterm i j]
    rw [hr0]
    simp
  · have hpositive : 0 < r := lt_of_le_of_ne hr (by intro he; exact hr0 he.symm)
    simpa [commonResidualTransportWeight, offDiagonalMatrixMass] using
      commonResidualMatrix_offDiagonalMass_le c a b r hpositive ha hb
        hc_nonneg ha_nonneg hb_nonneg

/-- Indicator of one category in a finite-valued sample. -/
def categoryIndicator {N : ℕ} (i : Fin N) (y : Fin N) : ℝ :=
  if y = i then 1 else 0

/-- Empirical frequency of category `i` in an `m`-sample. -/
def empiricalCategoryFrequency {N m : ℕ} (hm : 0 < m)
    (x : Fin m → Fin N) (i : Fin N) : ℝ :=
  (m : ℝ)⁻¹ * ∑ k : Fin m, categoryIndicator i (x k)

/-- The product law of `m` independent samples with common finite-valued law. -/
def finiteIidSampleLaw {N m : ℕ} (μ : Measure (Fin N)) : Measure (Fin m → Fin N) :=
  Measure.pi fun _ : Fin m => μ

/-- A finite-category indicator has expectation equal to the mass of that
category. -/
theorem categoryIndicator_integral {N : ℕ} (μ : Measure (Fin N))
    (i : Fin N) :
    ∫ y, categoryIndicator i y ∂μ = μ.real {i} := by
  classical
  have hfun : categoryIndicator i =
      Set.indicator ({i} : Set (Fin N)) (fun _ => (1 : ℝ)) := by
    funext y
    by_cases hy : y = i <;> simp [categoryIndicator, Set.indicator, hy]
  rw [hfun, integral_indicator_const (1 : ℝ) (measurableSet_singleton i)]
  simp

/-- The Bernoulli coordinate for a finite category has variance at most its
probability. -/
theorem categoryIndicator_variance_le {N : ℕ} (μ : Measure (Fin N))
    [IsProbabilityMeasure μ] (i : Fin N) :
    ProbabilityTheory.variance (categoryIndicator i) μ ≤ μ.real {i} := by
  have hbound : ∀ᵐ y ∂μ, categoryIndicator i y ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [] with y
    by_cases h : y = i <;> simp [categoryIndicator, h]
  have hvar := ProbabilityTheory.variance_le_sub_mul_sub
    (μ := μ) (X := categoryIndicator i) hbound (by fun_prop)
  rw [categoryIndicator_integral] at hvar
  have hp0 : 0 ≤ μ.real {i} := measureReal_nonneg
  have hp1 : μ.real {i} ≤ 1 := measureReal_le_one
  nlinarith

/-- The frequency of one category among iid draws has variance at most
`p/m`, where `p` is that category's one-draw probability. -/
theorem empiricalCategoryFrequency_variance_le {N m : ℕ}
    (hm : 0 < m) (μ : Measure (Fin N)) [IsProbabilityMeasure μ]
    (i : Fin N) :
    ProbabilityTheory.variance
      (fun x : Fin m → Fin N => empiricalCategoryFrequency hm x i)
      (finiteIidSampleLaw μ) ≤ μ.real {i} / m := by
  let f : Fin N → ℝ := categoryIndicator i
  have hf : MemLp f 2 μ := by
    have hbound : ∀ᵐ y ∂μ, f y ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [] with y
      by_cases h : y = i <;> simp [f, categoryIndicator, h]
    exact memLp_of_bounded hbound (by fun_prop) 2
  have hsum := ProbabilityTheory.variance_sum_pi
    (μ := fun _ : Fin m => μ) (X := fun _ : Fin m => f)
    (fun _ => hf)
  have hvar : ∀ k : Fin m,
      ProbabilityTheory.variance (f) μ ≤ μ.real {i} := by
    intro k
    simpa [f] using categoryIndicator_variance_le μ i
  have hmcast : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hfreq_eq :
      (fun x : Fin m → Fin N => empiricalCategoryFrequency hm x i) =
        fun x => (m : ℝ)⁻¹ * (∑ k : Fin m, f (x k)) := by
    funext x
    simp [empiricalCategoryFrequency, f]
  calc
    ProbabilityTheory.variance
        (fun x : Fin m → Fin N => empiricalCategoryFrequency hm x i)
        (finiteIidSampleLaw μ) =
      (m : ℝ)⁻¹ ^ 2 *
        ∑ k : Fin m, ProbabilityTheory.variance f μ := by
          rw [hfreq_eq, finiteIidSampleLaw, ProbabilityTheory.variance_const_mul]
          have hsumfun :
              (fun x : Fin m → Fin N => ∑ k : Fin m, f (x k)) =
                ∑ k : Fin m, fun x : Fin m → Fin N => f (x k) := by
            funext x
            simp
          rw [hsumfun]
          rw [hsum]
    _ ≤ (m : ℝ)⁻¹ ^ 2 * (m * μ.real {i}) := by
      gcongr
      calc
        (∑ k : Fin m, ProbabilityTheory.variance f μ) ≤
            ∑ _k : Fin m, μ.real {i} :=
          Finset.sum_le_sum fun k hk => hvar k
        _ = m * μ.real {i} := by simp [mul_comm]
    _ = μ.real {i} / m := by
      field_simp [hmcast]

/-- Empirical frequencies are unbiased under the true product sample law. -/
theorem empiricalCategoryFrequency_integral {N m : ℕ}
    (hm : 0 < m) (μ : Measure (Fin N)) [IsProbabilityMeasure μ]
    (i : Fin N) :
    ∫ x : Fin m → Fin N, empiricalCategoryFrequency hm x i
      ∂finiteIidSampleLaw μ = μ.real {i} := by
  let f : Fin N → ℝ := categoryIndicator i
  have hf : MemLp f 2 μ := by
    have hbound : ∀ᵐ y ∂μ, f y ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [] with y
      by_cases h : y = i <;> simp [f, categoryIndicator, h]
    exact memLp_of_bounded hbound (by fun_prop) 2
  have hcoord : ∀ k : Fin m,
      Integrable (fun x : Fin m → Fin N => f (x k)) (finiteIidSampleLaw μ) := by
    intro k
    exact integrable_comp_eval (μ := fun _ : Fin m => μ) (i := k)
      (hf.integrable one_le_two)
  have hfreq_eq :
      (fun x : Fin m → Fin N => empiricalCategoryFrequency hm x i) =
        fun x => (m : ℝ)⁻¹ * (∑ k : Fin m, f (x k)) := by
    funext x
    simp [empiricalCategoryFrequency, f]
  rw [hfreq_eq, finiteIidSampleLaw, integral_const_mul]
  have hsumInt :
      (∫ x : Fin m → Fin N, ∑ k : Fin m, f (x k) ∂Measure.pi (fun _ : Fin m => μ)) =
        ∑ k : Fin m, ∫ x : Fin m → Fin N, f (x k) ∂Measure.pi (fun _ : Fin m => μ) := by
    simpa [finiteIidSampleLaw] using integral_finsetSum Finset.univ
      (fun k hk => hcoord k)
  rw [hsumInt]
  simp_rw [integral_comp_eval (μ := fun _ : Fin m => μ) (i := _)
    hf.aestronglyMeasurable]
  rw [categoryIndicator_integral]
  simp
  field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hm)]

/-- Every empirical category frequency lies in the unit interval. -/
theorem empiricalCategoryFrequency_mem_Icc {N m : ℕ} (hm : 0 < m)
    (x : Fin m → Fin N) (i : Fin N) :
    empiricalCategoryFrequency hm x i ∈ Set.Icc (0 : ℝ) 1 := by
  have hterm0 : ∀ k : Fin m, 0 ≤ categoryIndicator i (x k) := by
    intro k
    by_cases h : x k = i <;> simp [categoryIndicator, h]
  have hterm1 : ∀ k : Fin m, categoryIndicator i (x k) ≤ 1 := by
    intro k
    by_cases h : x k = i <;> simp [categoryIndicator, h]
  have hsum0 : 0 ≤ ∑ k : Fin m, categoryIndicator i (x k) :=
    Finset.sum_nonneg fun k hk => hterm0 k
  have hsum1 : (∑ k : Fin m, categoryIndicator i (x k)) ≤ (m : ℝ) := by
    calc
      (∑ k : Fin m, categoryIndicator i (x k)) ≤ ∑ _k : Fin m, (1 : ℝ) :=
        Finset.sum_le_sum fun k hk => hterm1 k
      _ = (m : ℝ) := by simp
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  constructor
  · simp only [empiricalCategoryFrequency]
    exact mul_nonneg (inv_nonneg.mpr hmpos.le) hsum0
  · simp only [empiricalCategoryFrequency]
    calc
      (m : ℝ)⁻¹ * (∑ k : Fin m, categoryIndicator i (x k)) ≤
          (m : ℝ)⁻¹ * (m : ℝ) := mul_le_mul_of_nonneg_left hsum1 (inv_nonneg.mpr hmpos.le)
      _ = 1 := by field_simp [ne_of_gt hmpos]

/-- The expected absolute deviation of an iid empirical category frequency is
at most the square root of `p/m`. -/
theorem empiricalCategoryFrequency_abs_deviation_integral_le {N m : ℕ}
    (hm : 0 < m) (μ : Measure (Fin N)) [IsProbabilityMeasure μ]
    (i : Fin N) :
    ∫ x : Fin m → Fin N,
        |empiricalCategoryFrequency hm x i - μ.real {i}|
          ∂finiteIidSampleLaw μ ≤ Real.sqrt (μ.real {i} / m) := by
  let P := finiteIidSampleLaw (m := m) μ
  letI : IsProbabilityMeasure P := by
    dsimp [P, finiteIidSampleLaw]
    infer_instance
  let q : (Fin m → Fin N) → ℝ := fun x => empiricalCategoryFrequency hm x i
  let p : ℝ := μ.real {i}
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have hmean : ∫ x, q x ∂P = p := by
    simpa [P, q, p] using empiricalCategoryFrequency_integral hm μ i
  have hvar := empiricalCategoryFrequency_variance_le hm μ i
  have hqbound : ∀ᵐ x ∂P, q x ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [] with x
    exact empiricalCategoryFrequency_mem_Icc hm x i
  have hdevbound : ∀ᵐ x ∂P, |q x - p| ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hqbound] with x hx
    constructor
    · exact abs_nonneg _
    · rw [abs_le]
      constructor <;> linarith [hp0, hp1, hx.1, hx.2]
  have hq : MemLp q (ENNReal.ofReal 2) P :=
    memLp_of_bounded hqbound (by fun_prop) (ENNReal.ofReal 2)
  have hdev : MemLp (fun x => |q x - p|) (ENNReal.ofReal 2) P :=
    memLp_of_bounded hdevbound (by fun_prop) (ENNReal.ofReal 2)
  have hsecond : (∫ x, |q x - p| ^ 2 ∂P) =
      ProbabilityTheory.variance q P := by
    calc
      (∫ x, |q x - p| ^ 2 ∂P) = ∫ x, (q x - p) ^ 2 ∂P := by
        congr 1
        funext x
        exact sq_abs _
      _ = ProbabilityTheory.variance q P := by
        rw [ProbabilityTheory.variance_eq_integral hq.aemeasurable, hmean]
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := P) Real.HolderConjugate.two_two
    (ae_of_all P fun _ => (show 0 ≤ (1 : ℝ) by norm_num))
    (ae_of_all P fun _ => abs_nonneg (q _ - p))
    (memLp_const (1 : ℝ)) hdev
  have hvar_bound : ProbabilityTheory.variance q P ≤ p / m := by
    simpa [P, q, p] using hvar
  have hnonneg : 0 ≤ p / m := by positivity
  have hsecond_rpow := congrArg
    (fun t : ℝ => t ^ (1 / 2 : ℝ)) hsecond
  calc
    ∫ x, |q x - p| ∂P = ∫ x, (1 : ℝ) * |q x - p| ∂P := by simp
    _ ≤ (∫ x, (1 : ℝ) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) *
        (∫ x, |q x - p| ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := hholder
    _ = Real.sqrt (ProbabilityTheory.variance q P) := by
      calc
        _ = (∫ x, |q x - p| ^ 2 ∂P) ^ (1 / 2 : ℝ) := by simp
        _ = (ProbabilityTheory.variance q P) ^ (1 / 2 : ℝ) := hsecond_rpow
        _ = Real.sqrt (ProbabilityTheory.variance q P) :=
          (Real.sqrt_eq_rpow _).symm
    _ ≤ Real.sqrt (p / m) := Real.sqrt_le_sqrt hvar_bound

/-- The singleton masses of a probability law on a finite type sum to one. -/
theorem sum_singleton_masses_eq_one {N : ℕ} (μ : Measure (Fin N))
    [IsProbabilityMeasure μ] :
    (∑ i : Fin N, μ.real {i}) = 1 := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin N)))
      (fun i => ({i} : Set (Fin N))) := by
    simp only [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun]
    intro i hi j hj hij
    exact Set.disjoint_singleton.mpr hij
  have hunion : (⋃ i ∈ (Finset.univ : Finset (Fin N)), ({i} : Set (Fin N))) =
      Set.univ := by
    ext y
    simp
  calc
    (∑ i : Fin N, μ.real {i}) =
        μ.real (⋃ i ∈ (Finset.univ : Finset (Fin N)), ({i} : Set (Fin N))) := by
      symm
      rw [measureReal_biUnion_finset hdisj (fun i hi => MeasurableSet.singleton i)]
    _ = 1 := by rw [hunion]; simp

/-- The finite multivariate Cauchy--Schwarz bound for square roots of
probability masses. -/
theorem sum_sqrt_mass_over_m_le {N m : ℕ} (hm : 0 < m)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsum : ∑ i : Fin N, p i = 1) :
    (∑ i : Fin N, Real.sqrt (p i / m)) ≤ Real.sqrt ((N : ℝ) / m) := by
  have hsq :
      (∑ i : Fin N, Real.sqrt (p i / m)) ^ 2 ≤
        (∑ _i : Fin N, (1 : ℝ)) * ∑ i : Fin N, p i / m := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    · intro i hi
      norm_num
    · intro i hi
      exact div_nonneg (hp i) (by positivity)
    · intro i hi
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
      have hroot := Real.sq_sqrt (x := p i / (m : ℝ))
        (div_nonneg (hp i) (le_of_lt hmpos))
      nlinarith
  have hsumdiv : (∑ i : Fin N, p i / m) = 1 / m := by
    rw [← Finset.sum_div, hsum]
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have htotal :
      (∑ _i : Fin N, (1 : ℝ)) * ∑ i : Fin N, p i / m = (N : ℝ) / m := by
    rw [hsumdiv]
    simp [div_eq_mul_inv]
  have hleft : 0 ≤ ∑ i : Fin N, Real.sqrt (p i / m) :=
    Finset.sum_nonneg fun i hi => Real.sqrt_nonneg _
  have hright : 0 ≤ Real.sqrt ((N : ℝ) / m) := Real.sqrt_nonneg _
  rw [htotal] at hsq
  nlinarith [Real.sq_sqrt (show 0 ≤ (N : ℝ) / m by positivity)]

/-- Total variation residual between a true finite law and its actual iid
empirical frequencies has expectation at most `1/2 * sqrt(N/m)`. -/
def empiricalFrequencyResidual {N m : ℕ} (hm : 0 < m)
    (μ : Measure (Fin N)) (x : Fin m → Fin N) : ℝ :=
  (1 / 2 : ℝ) * ∑ i : Fin N,
    |empiricalCategoryFrequency hm x i - μ.real {i}|

theorem empiricalFrequencyResidual_integral_le {N m : ℕ}
    (hm : 0 < m) (μ : Measure (Fin N)) [IsProbabilityMeasure μ] :
    ∫ x : Fin m → Fin N, empiricalFrequencyResidual hm μ x
      ∂finiteIidSampleLaw (m := m) μ ≤
        (1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / m) := by
  let P := finiteIidSampleLaw (m := m) μ
  letI : IsProbabilityMeasure P := by
    dsimp [P, finiteIidSampleLaw]
    infer_instance
  have hsumInt : ∀ i : Fin N,
      Integrable (fun x : Fin m → Fin N =>
        |empiricalCategoryFrequency hm x i - μ.real {i}|) P := by
    intro i
    have hbound : ∀ᵐ x ∂P,
        |empiricalCategoryFrequency hm x i - μ.real {i}| ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [] with x
      have hq := empiricalCategoryFrequency_mem_Icc hm x i
      have hp0 : 0 ≤ μ.real {i} := measureReal_nonneg
      have hp1 : μ.real {i} ≤ 1 := measureReal_le_one
      constructor
      · exact abs_nonneg _
      · rw [abs_le]
        constructor <;> linarith [hq.1, hq.2, hp0, hp1]
    exact (memLp_of_bounded hbound (by fun_prop) 2).integrable one_le_two
  have hsumOne := sum_singleton_masses_eq_one μ
  have hmass : ∀ i, 0 ≤ μ.real {i} := fun _ => measureReal_nonneg
  calc
    ∫ x : Fin m → Fin N, empiricalFrequencyResidual hm μ x ∂P =
        (1 / 2 : ℝ) * ∑ i : Fin N,
          ∫ x : Fin m → Fin N,
            |empiricalCategoryFrequency hm x i - μ.real {i}| ∂P := by
        change (∫ x : Fin m → Fin N, (1 / 2 : ℝ) *
          ∑ i : Fin N, |empiricalCategoryFrequency hm x i - μ.real {i}| ∂P) = _
        rw [integral_const_mul]
        rw [integral_finsetSum Finset.univ (fun i hi => hsumInt i)]
    _ ≤ (1 / 2 : ℝ) * ∑ i : Fin N, Real.sqrt (μ.real {i} / m) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro i hi
      exact empiricalCategoryFrequency_abs_deviation_integral_le hm μ i
    _ ≤ (1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / m) := by
      exact mul_le_mul_of_nonneg_left
        (sum_sqrt_mass_over_m_le hm (fun i => μ.real {i}) hmass hsumOne) (by norm_num)

/-- The category indicators sum to one for each finite-valued observation. -/
theorem sum_categoryIndicator_eq_one {N : ℕ} (y : Fin N) :
    (∑ i : Fin N, categoryIndicator i y) = 1 := by
  classical
  simp [categoryIndicator, eq_comm]

/-- Empirical category frequencies form a probability vector for every
nonempty sample. -/
theorem sum_empiricalCategoryFrequency_eq_one {N m : ℕ} (hm : 0 < m)
    (x : Fin m → Fin N) :
    (∑ i : Fin N, empiricalCategoryFrequency hm x i) = 1 := by
  classical
  have hswap :
      (∑ i : Fin N, ∑ k : Fin m, categoryIndicator i (x k)) =
        ∑ k : Fin m, ∑ i : Fin N, categoryIndicator i (x k) := by
    exact Finset.sum_comm
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  calc
    (∑ i : Fin N, empiricalCategoryFrequency hm x i) =
        (m : ℝ)⁻¹ * ∑ i : Fin N, ∑ k : Fin m, categoryIndicator i (x k) := by
          simp [empiricalCategoryFrequency, Finset.mul_sum]
    _ = (m : ℝ)⁻¹ * ∑ k : Fin m, ∑ i : Fin N, categoryIndicator i (x k) := by rw [hswap]
    _ = (m : ℝ)⁻¹ * m := by simp [sum_categoryIndicator_eq_one]
    _ = 1 := by field_simp [ne_of_gt hmpos]

/-- For probability vectors, the mass left over after matching coordinatewise
common mass is exactly half their `ℓ¹` discrepancy. -/
theorem commonMassResidual_eq_half_l1 {N : ℕ} (p q : Fin N → ℝ)
    (hp : ∑ i : Fin N, p i = 1) (hq : ∑ i : Fin N, q i = 1) :
    (∑ i : Fin N, (p i - min (p i) (q i))) =
      (1 / 2 : ℝ) * ∑ i : Fin N, |p i - q i| := by
  have hpoint (i : Fin N) :
      |p i - q i| = p i + q i - 2 * min (p i) (q i) := by
    rcases le_total (p i) (q i) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  have habs :
      (∑ i : Fin N, |p i - q i|) =
        2 * (∑ i : Fin N, (p i - min (p i) (q i))) := by
    calc
      (∑ i : Fin N, |p i - q i|) =
          ∑ i : Fin N, (p i + q i - 2 * min (p i) (q i)) :=
        Finset.sum_congr rfl fun i hi => hpoint i
      _ = (∑ i : Fin N, p i) + (∑ i : Fin N, q i) -
          2 * ∑ i : Fin N, min (p i) (q i) := by
        simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.mul_sum]
      _ = 2 * (∑ i : Fin N, (p i - min (p i) (q i))) := by
        rw [Finset.sum_sub_distrib, hp, hq]
        ring
  rw [habs]
  ring

/-- The empirical law on a finite state space, grouped by category. -/
noncomputable def empiricalCategoryWeight {N m : ℕ} (hm : 0 < m)
    (x : Fin m → Fin N) (i : Fin N) : ℝ≥0∞ :=
  ∑ k : Fin m, if x k = i then ENNReal.ofNNReal (((↑m : NNReal))⁻¹) else 0

/-- Grouping equal atoms in the true equal-weight Dirac empirical measure gives
the category-frequency atomic measure exactly. -/
theorem empiricalMeasure_eq_finiteFrequencyMeasure {N m : ℕ}
    (hm : 0 < m) (x : Fin m → Fin N) :
    empiricalMeasure m hm x =
      finiteAtomicMeasure (empiricalCategoryWeight hm x) id := by
  classical
  ext s hs
  simp only [empiricalMeasure, finiteAtomicMeasure, empiricalCategoryWeight,
    Measure.sum_apply _ hs, Measure.smul_apply, Measure.dirac_apply]
  simp only [tsum_fintype]
  change (∑ k : Fin m, ENNReal.ofNNReal (((↑m : NNReal))⁻¹) •
      s.indicator (fun _ : Fin N => (1 : ℝ≥0∞)) (x k)) = _
  let c : ℝ≥0∞ := ENNReal.ofNNReal (((↑m : NNReal))⁻¹)
  calc
    (∑ k : Fin m, ENNReal.ofNNReal (((↑m : NNReal))⁻¹) •
      s.indicator (fun _ : Fin N => (1 : ℝ≥0∞)) (x k)) =
        ∑ k : Fin m, ∑ i : Fin N,
          (if x k = i then c else 0) • s.indicator (fun _ : Fin N => (1 : ℝ≥0∞)) i := by
      apply Finset.sum_congr rfl
      intro k hk
      have hone : ∑ i : Fin N, (if x k = i then c else 0) • s.indicator 1 i =
          c • s.indicator (fun _ : Fin N => (1 : ℝ≥0∞)) (x k) := by
        rw [Finset.sum_eq_single (x k)]
        · simp [c, Set.indicator]
        · intro i hi hne
          simp [hne.symm]
        · intro hnot
          exact (hnot (Finset.mem_univ (x k))).elim
      simpa [c] using hone.symm
    _ = ∑ i : Fin N, ∑ k : Fin m,
          (if x k = i then c else 0) • s.indicator (fun _ : Fin N => (1 : ℝ≥0∞)) i := by
      rw [Finset.sum_comm]
    _ = ∑ i : Fin N,
          (∑ k : Fin m, if x k = i then c else 0) •
            s.indicator (fun _ : Fin N => (1 : ℝ≥0∞)) i := by
      congr 1
      ext i
      simp only [Finset.sum_smul]
    _ = ∑ i : Fin N,
          empiricalCategoryWeight hm x i •
            s.indicator (fun _ : Fin N => (1 : ℝ≥0∞)) i := by
      simp [empiricalCategoryWeight, c]

/-- The category weights above are exactly `ofReal` of the frequencies used in
the variance estimate. -/
theorem empiricalCategoryWeight_eq_ofReal_frequency {N m : ℕ}
    (hm : 0 < m) (x : Fin m → Fin N) (i : Fin N) :
    empiricalCategoryWeight hm x i =
      ENNReal.ofReal (empiricalCategoryFrequency hm x i) := by
  classical
  let u : ℝ := (m : ℝ)⁻¹
  let t : Fin m → ℝ := fun k => if x k = i then 1 else 0
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hu : ENNReal.ofNNReal (((↑m : NNReal))⁻¹) = ENNReal.ofReal u := by
    rw [← ENNReal.ofReal_coe_nnreal]
    congr 1
  have ht : ∀ k, 0 ≤ t k := by
    intro k
    simp only [t]
    split <;> norm_num
  unfold empiricalCategoryWeight empiricalCategoryFrequency
  simp only [categoryIndicator]
  calc
    (∑ k : Fin m, if x k = i then ENNReal.ofNNReal (((↑m : NNReal))⁻¹) else 0) =
        ∑ k : Fin m, ENNReal.ofReal u * ENNReal.ofReal (t k) := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases h : x k = i <;> simp [h, t, hu]
    _ = ENNReal.ofReal u * ∑ k : Fin m, ENNReal.ofReal (t k) := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal u * ENNReal.ofReal (∑ k : Fin m, t k) := by
      rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := t)
        (fun k hk => ht k)]
    _ = ENNReal.ofReal (u * ∑ k : Fin m, t k) := by
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hmpos.le)]
    _ = ENNReal.ofReal (empiricalCategoryFrequency hm x i) := by
      congr 2

/-- Finite probability law on `Fin N` represented as an atomic measure. -/
noncomputable def finiteCategoryLaw {N : ℕ} (p : Fin N → ℝ) : Measure (Fin N) :=
  finiteAtomicMeasure (fun i => ENNReal.ofReal (p i)) id

theorem finiteCategoryLaw_real_singleton {N : ℕ} (p : Fin N → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i : Fin N, p i = 1) (i : Fin N) :
    (finiteCategoryLaw p).real {i} = p i := by
  have hpi : p i ≤ 1 := by
    calc
      p i ≤ ∑ j : Fin N, p j := Finset.single_le_sum (fun j hj => hp j)
        (Finset.mem_univ i)
      _ = 1 := hsum
  simp [Measure.real, finiteCategoryLaw, finiteAtomicMeasure, Pi.single_apply, hpi]
  exact hp i

/-- Product-mixture coupling: couple each source cell component to each target
cell component with the prescribed finite matrix weight. -/
noncomputable def finiteMixtureCouplingMeasure {N : ℕ} {X : Type*}
    [MeasurableSpace X] (κ η : Fin N → Measure X)
    (w : Fin N → Fin N → ℝ≥0∞) : Measure (X × X) :=
  Measure.sum fun i : Fin N =>
    Measure.sum fun j : Fin N => w i j • (κ i).prod (η j)

theorem sum_smul_measure_eq {N : ℕ} {X : Type*} [MeasurableSpace X]
    (w : Fin N → ℝ≥0∞) (μ : Measure X) :
    Measure.sum (fun i : Fin N => w i • μ) = (∑ i : Fin N, w i) • μ := by
  classical
  ext s hs
  simp [Measure.sum_apply, Measure.smul_apply, Finset.sum_mul]

/-- Lift a finite matrix coupling to a genuine coupling of finite mixtures by
using product measures of the cell components. -/
noncomputable def finiteMixtureTransportCoupling {N : ℕ} {X : Type*}
    [MeasurableSpace X] (μ ν : Measure X)
    (κ η : Fin N → Measure X) (p q : Fin N → ℝ≥0∞)
    (w : Fin N → Fin N → ℝ≥0∞)
    (hκ : ∀ i, IsProbabilityMeasure (κ i))
    (hη : ∀ j, IsProbabilityMeasure (η j))
    (hsource : μ = Measure.sum (fun i : Fin N => p i • κ i))
    (htarget : ν = Measure.sum (fun j : Fin N => q j • η j))
    (hrow : ∀ i, ∑ j : Fin N, w i j = p i)
    (hcol : ∀ j, ∑ i : Fin N, w i j = q j) :
    TransportCoupling μ ν := by
  classical
  refine ⟨finiteMixtureCouplingMeasure κ η w, ?_, ?_⟩
  · rw [finiteMixtureCouplingMeasure, Measure.map_sum measurable_fst.aemeasurable]
    rw [hsource]
    congr 1
    funext i
    rw [Measure.map_sum measurable_fst.aemeasurable]
    have hmap (j : Fin N) :
        Measure.map Prod.fst ((κ i).prod (η j)) = κ i := by
      letI := hη j
      rw [Measure.map_fst_prod, measure_univ, one_smul]
    calc
      Measure.sum (fun j : Fin N =>
          Measure.map Prod.fst (w i j • (κ i).prod (η j))) =
          Measure.sum (fun j : Fin N => w i j • κ i) := by
        congr 1
        funext j
        rw [Measure.map_smul _ measurable_fst.aemeasurable, hmap j]
      _ = (∑ j : Fin N, w i j) • κ i := sum_smul_measure_eq _ _
      _ = p i • κ i := by rw [hrow i]
  · rw [finiteMixtureCouplingMeasure,
      Measure.sum_comm (fun i j => w i j • (κ i).prod (η j)),
      Measure.map_sum measurable_snd.aemeasurable]
    rw [htarget]
    congr 1
    funext j
    rw [Measure.map_sum measurable_snd.aemeasurable]
    have hmap (i : Fin N) :
        Measure.map Prod.snd ((κ i).prod (η j)) = η j := by
      letI := hκ i
      rw [Measure.map_snd_prod, measure_univ, one_smul]
    calc
      Measure.sum (fun i : Fin N =>
          Measure.map Prod.snd (w i j • (κ i).prod (η j))) =
          Measure.sum (fun i : Fin N => w i j • η j) := by
        congr 1
        funext i
        rw [Measure.map_smul _ measurable_snd.aemeasurable, hmap i]
      _ = (∑ i : Fin N, w i j) • η j := sum_smul_measure_eq _ _
      _ = q j • η j := by rw [hcol j]

/-- Cost of the direct mixture coupling is bounded by summing component costs
with the matrix weights. This is the cell-lift estimate used to avoid a
Wasserstein triangle argument. -/
theorem finiteMixtureTransportCoupling_cost_le {N : ℕ} {X : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] [PseudoEMetricSpace X]
    (μ ν : Measure X) (κ η : Fin N → Measure X) (p q : Fin N → ℝ≥0∞)
    (w : Fin N → Fin N → ℝ≥0∞)
    (hκ : ∀ i, IsProbabilityMeasure (κ i))
    (hη : ∀ j, IsProbabilityMeasure (η j))
    (hsource : μ = Measure.sum (fun i : Fin N => p i • κ i))
    (htarget : ν = Measure.sum (fun j : Fin N => q j • η j))
    (hrow : ∀ i, ∑ j : Fin N, w i j = p i)
    (hcol : ∀ j, ∑ i : Fin N, w i j = q j)
    (C : Fin N → Fin N → ℝ≥0∞)
    (hcomponent : ∀ i j,
      (∫⁻ z : X × X, edist z.1 z.2 ^ 2 ∂(κ i).prod (η j)) ≤ C i j) :
    (∫⁻ z : X × X,
      edist z.1 z.2 ^ 2 ∂(finiteMixtureTransportCoupling μ ν κ η p q w
        hκ hη hsource htarget hrow hcol).measure) ≤
      ∑ i : Fin N, ∑ j : Fin N, w i j * C i j := by
  change (∫⁻ z : X × X, edist z.1 z.2 ^ 2 ∂
    finiteMixtureCouplingMeasure κ η w) ≤ _
  rw [finiteMixtureCouplingMeasure]
  simp_rw [lintegral_sum_measure, lintegral_smul_measure]
  simp only [tsum_fintype, ENNReal.smul_def]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left (hcomponent i j) bot_le

end BrownianSharp.AlignmentPaperFiniteEmpiricalCoupling

end
