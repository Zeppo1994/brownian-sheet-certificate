import BrownianSharp.AtomicTensorVariance

/-! Factorization of the actual smooth Fourier block on a rectangular tensor
atom into its one-dimensional scalar block evaluations. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 500000

namespace BrownianSharp.AtomicTensorFactorization

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.PeriodicCover
open BrownianSharp.AtomicTensorVariance
open BrownianSharp.ScalarAtomSpecialization
open UnitAddTorus

abbrev ShapeCell (d : ℕ) (s : Fin d → ℕ) := DyadicShapeCell d s

/-- The scalar evaluation of one smooth block on a one-dimensional cell atom. -/
def scalarBlockEval (t s : ℕ) (j : Fin (2 ^ s)) (x : UnitAddCircle) : ℂ :=
  ∑ n ∈ BrownianSharp.ScalarAtomVariance.scalarFrequencyBox t,
    (scalarBlock t (n : ℝ) : ℂ) *
      fourierCoeff (atomComplex s 0 j) n * fourier n x

/-- The torus Fourier coefficient of a tensor atom is the product of its
one-dimensional Fourier coefficients. -/
theorem shapeAtom_fourierCoeff_eq_prod {d : ℕ} (s : Fin d → ℕ)
    (j : ShapeCell d s) (k : Fin d → ℤ) :
    BrownianSharp.Torus.realPeriodicFourierCoeff (shapePeriodicAtom s j) k =
      ∏ i : Fin d, fourierCoeff (atomComplex (s i) 0 (j i)) (k i) := by
  classical
  unfold BrownianSharp.Torus.realPeriodicFourierCoeff
    BrownianSharp.Torus.complexifyRealPeriodic
    UnitAddTorus.mFourierCoeff
  have hfun :
      (fun x : UnitAddTorus (Fin d) =>
        UnitAddTorus.mFourier (-k) x •
          (shapePeriodicAtom s j x : ℂ)) =
      fun x => ∏ i : Fin d,
        (fourier (-(k i)) (x i) • (atomComplex (s i) 0 (j i) (x i))) := by
    funext x
    simp [UnitAddTorus.mFourier, shapePeriodicAtom, dyadicShapeAtom,
      atomComplex, smul_eq_mul, Finset.prod_mul_distrib]
  rw [hfun]
  change (∫ x : (i : Fin d) → UnitAddCircle,
      ∏ i : Fin d,
        (fourier (-(k i)) (x i) • (atomComplex (s i) 0 (j i) (x i)))
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) = _
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (fun i y => fourier (-(k i)) y • (atomComplex (s i) 0 (j i) y))]
  apply Finset.prod_congr rfl
  intro i hi
  simp [fourierCoeff, fourier, smul_eq_mul]

/-- Pointwise tensor factorization for actual smooth blocks and actual
periodized dyadic atoms. -/
theorem block_shapeAtom_eq_prod_scalar (d : ℕ) (s t : Fin d → ℕ)
    (j : ShapeCell d s) (x : UnitAddTorus (Fin d)) :
    block t (shapePeriodicAtom s j) x =
      ∏ i : Fin d, scalarBlockEval (t i) (s i) (j i) (x i) := by
  classical
  rw [block]
  simp only [torusFourierPolynomial, ContinuousMap.coe_sum, Finset.sum_apply]
  have hterm (k : Fin d → ℤ) :
      ((tensorMultiplier t k : ℂ) *
          BrownianSharp.Torus.realPeriodicFourierCoeff (shapePeriodicAtom s j) k) •
          UnitAddTorus.mFourier k x =
        ∏ i : Fin d,
          ((scalarBlock (t i) (k i : ℝ) : ℂ) *
            fourierCoeff (atomComplex (s i) 0 (j i)) (k i) * fourier (k i) (x i)) := by
    rw [shapeAtom_fourierCoeff_eq_prod]
    simp [tensorMultiplier, UnitAddTorus.mFourier, smul_eq_mul,
      Finset.prod_mul_distrib, mul_assoc]
  have hsum :
      (∑ k ∈ frequencyBox t,
        ((tensorMultiplier t k : ℂ) *
            BrownianSharp.Torus.realPeriodicFourierCoeff (shapePeriodicAtom s j) k) •
            UnitAddTorus.mFourier k x) =
      ∑ k ∈ frequencyBox t, ∏ i : Fin d,
        ((scalarBlock (t i) (k i : ℝ) : ℂ) *
          fourierCoeff (atomComplex (s i) 0 (j i)) (k i) * fourier (k i) (x i)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact hterm k
  have hsum' :
      (∑ k ∈ frequencyBox t,
        (((tensorMultiplier t k : ℂ) *
          BrownianSharp.Torus.realPeriodicFourierCoeff (shapePeriodicAtom s j) k) •
            UnitAddTorus.mFourier k) x) =
      ∑ k ∈ frequencyBox t, ∏ i : Fin d,
        ((scalarBlock (t i) (k i : ℝ) : ℂ) *
          fourierCoeff (atomComplex (s i) 0 (j i)) (k i) * fourier (k i) (x i)) := by
    simpa only [ContinuousMap.smul_apply] using hsum
  rw [hsum']
  change (∑ k ∈ Fintype.piFinset
      (fun i : Fin d => Finset.Icc (-((2 : ℤ) ^ (t i + 1)))
        ((2 : ℤ) ^ (t i + 1))),
      ∏ i : Fin d,
        ((scalarBlock (t i) (k i : ℝ) : ℂ) *
          fourierCoeff (atomComplex (s i) 0 (j i)) (k i) * fourier (k i) (x i))) = _
  rw [(Finset.prod_univ_sum
    (fun i : Fin d => Finset.Icc (-((2 : ℤ) ^ (t i + 1)))
      ((2 : ℤ) ^ (t i + 1)))
    (fun i n => ((scalarBlock (t i) (n : ℝ) : ℂ) *
      fourierCoeff (atomComplex (s i) 0 (j i)) n * fourier n (x i)))).symm]
  simp [scalarBlockEval, BrownianSharp.ScalarAtomVariance.scalarFrequencyBox]

/-- The total pointwise variance over all tensor cells of one rectangular
shape factorizes exactly as the product of its scalar coordinate variances. -/
theorem shape_block_variance_eq_prod (d : ℕ) (s t : Fin d → ℕ)
    (x : UnitAddTorus (Fin d)) :
    (∑ j : ShapeCell d s,
      ‖block t (shapePeriodicAtom s j) x‖ ^ 2) =
      ∏ i : Fin d, ∑ j : Fin (2 ^ (s i)),
        ‖scalarBlockEval (t i) (s i) j (x i)‖ ^ 2 := by
  classical
  let g : (i : Fin d) → Fin (2 ^ (s i)) → ℝ := fun i j =>
    ‖scalarBlockEval (t i) (s i) j (x i)‖ ^ 2
  have hpoint (j : ShapeCell d s) :
      ‖block t (shapePeriodicAtom s j) x‖ ^ 2 = ∏ i : Fin d, g i (j i) := by
    rw [block_shapeAtom_eq_prod_scalar]
    simp [g, norm_prod, Finset.prod_pow]
  calc
    _ = ∑ j : ShapeCell d s, ∏ i : Fin d, g i (j i) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact hpoint j
    _ = ∏ i : Fin d, ∑ j : Fin (2 ^ (s i)), g i j := by
      simpa [ShapeCell, g] using
        (Finset.prod_univ_sum
          (fun i : Fin d => (Finset.univ : Finset (Fin (2 ^ (s i)))))
          (fun i j => g i j)).symm

/-- Coordinatewise scalar variance envelope: low frequencies use disjoint-cell
Bessel, while high frequencies use the inverse-derivative kernel. -/
def scalarVarianceEnvelope (K : ℕ) (C : ℝ) (s t : ℕ) : ℝ :=
  if t ≤ s then 5 * ((2 : ℝ) ^ t / (2 : ℝ) ^ s) else
    (C ^ 2 * (2 : ℝ) ^ ((2 * K - 1) * s)) *
      ((2 : ℝ) ^ (t + 2) + 1) *
        (((2 * Real.pi * (2 : ℝ) ^ (t - 1)) ^ K)⁻¹) ^ 2

private theorem scalarVarianceEnvelope_nonneg (K : ℕ) (C : ℝ) (s t : ℕ) :
    0 ≤ scalarVarianceEnvelope K C s t := by
  unfold scalarVarianceEnvelope
  split_ifs with h
  · positivity
  · positivity

private theorem scalarVarianceEnvelope_bounds_actual (K : ℕ) (hK : 1 ≤ K)
    (C : ℝ) (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (s t : ℕ) (x : UnitAddCircle) :
    (∑ j : Fin (2 ^ s),
      ‖scalarBlockEval t s j x‖ ^ 2) ≤ scalarVarianceEnvelope K C s t := by
  by_cases hts : t ≤ s
  · simpa [scalarBlockEval, scalarVarianceEnvelope, hts] using
      actual_scalar_low_frequency_variance_ratio s t hts smoothAtom_abs_le_one x
  · have ht : 0 < t := by omega
    simpa [scalarBlockEval, scalarVarianceEnvelope, hts] using
      actual_scalar_high_frequency_variance_card s t K ht hK hC x

/-- Full coordinate-product bound for the pointwise variance over every atom
in one rectangular shape. This is the summable high-frequency tail needed
when the depth vector ranges over all of `ℕ^d`. The only scale-dependent
analytic input is the explicit order-`K` bump derivative supremum `C`. -/
theorem actual_shape_block_variance_product_bound (d K : ℕ) (hK : 1 ≤ K)
    (C : ℝ) (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (s t : Fin d → ℕ) (x : UnitAddTorus (Fin d)) :
    (∑ j : ShapeCell d s,
      ‖block t (shapePeriodicAtom s j) x‖ ^ 2) ≤
      ∏ i : Fin d, scalarVarianceEnvelope K C (s i) (t i) := by
  rw [shape_block_variance_eq_prod]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact Finset.sum_nonneg fun j hj => sq_nonneg
      ‖scalarBlockEval (t i) (s i) j (x i)‖
  · intro i hi
    exact scalarVarianceEnvelope_bounds_actual K hK C hC
      (s i) (t i) (x i)

/-- Sum of the tensor variance envelopes over any finite collection of source
depth shapes. This is the deterministic input to the Gaussian second-moment
wrapper; no source-shape tail is hidden in the statement. -/
theorem finite_shape_block_variance_product_bound (d K : ℕ) (hK : 1 ≤ K)
    (C : ℝ) (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (S : Finset (Fin d → ℕ)) (t : Fin d → ℕ)
    (x : UnitAddTorus (Fin d)) :
    (∑ s ∈ S, ∑ j : ShapeCell d s,
      ‖block t (shapePeriodicAtom s j) x‖ ^ 2) ≤
      ∑ s ∈ S, ∏ i : Fin d,
        scalarVarianceEnvelope K C (s i) (t i) := by
  apply Finset.sum_le_sum
  intro s hs
  exact actual_shape_block_variance_product_bound d K hK C hC s t x

/-- The fixed-shape variance envelope is unconditional: compact smoothness of
the chosen bump supplies a finite derivative constant for every order K. -/
theorem exists_actual_shape_block_variance_product_bound (d K : ℕ)
    (hK : 1 ≤ K) (s t : Fin d → ℕ) (x : UnitAddTorus (Fin d)) :
    ∃ C : ℝ, 0 < C ∧
      (∑ j : ShapeCell d s,
        ‖block t (shapePeriodicAtom s j) x‖ ^ 2) ≤
        ∏ i : Fin d, scalarVarianceEnvelope K C (s i) (t i) := by
  obtain ⟨C, hCpos, hC⟩ := exists_smoothAtom_iteratedDeriv_bound K
  exact ⟨C, hCpos,
    actual_shape_block_variance_product_bound d K hK C hC s t x⟩

end BrownianSharp.AtomicTensorFactorization
