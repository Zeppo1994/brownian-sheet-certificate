import BrownianSharp.AlignmentPaperLpDvpBlockCover
import BrownianSharp.ScalarKernelL1
import BrownianSharp.SmoothResolution
import BrownianSharp.LayerIndex

/-! Shape-adapted DVP sampling for an actual smooth hyperbolic grade.

The sample vector is the disjoint union of the four-times midpoint grids of
the rectangular smooth blocks.  Reconstruction is performed blockwise with
the existing exact DVP CLM, so the sample dimension follows the hyperbolic
grade rather than its much larger enclosing rectangle. -/

noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperLpJointDvp

set_option maxHeartbeats 1000000

open BrownianSharp
open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AlignmentPaperLpDvpBlockCover
open BrownianSharp.AlignmentPaperLpDvpReconstruction
open BrownianSharp.AlignmentPaperLpDvpExactReconstruction
open BrownianSharp.AlignmentPaperLpDvpReproduction
open BrownianSharp.AlignmentPaperLpGridOrthogonality
open BrownianSharp.ScalarKernelL1
open HaarQuarter.TheoremD.FejerFourier

private theorem fejerCharacterSum_norm_le (N : ℕ) (x : ℝ) :
    ‖∑ r ∈ Finset.range N,
      HaarQuarter.TrigonometricHaarExtraction.character (r : ℤ) x‖ ≤ N := by
  calc
    _ ≤ ∑ r ∈ Finset.range N,
        ‖HaarQuarter.TrigonometricHaarExtraction.character (r : ℤ) x‖ :=
      norm_sum_le _ _
    _ = N := by
      simp [HaarQuarter.TrigonometricHaarExtraction.character_norm]

private theorem realFejerKernel_le {N : ℕ} (hN : 0 < N) (x : ℝ) :
    HaarQuarter.TheoremD.FejerFourier.realFejerKernel N x ≤ N := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let z := ∑ r ∈ Finset.range N,
      HaarQuarter.TrigonometricHaarExtraction.character (r : ℤ) x
  have hz : ‖z‖ ≤ N := by
    simpa [z] using fejerCharacterSum_norm_le N x
  have hsq : Complex.normSq z ≤ (N : ℝ) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  unfold HaarQuarter.TheoremD.FejerFourier.realFejerKernel
  change Complex.normSq
      (∑ r ∈ Finset.range N,
        HaarQuarter.TrigonometricHaarExtraction.character (r : ℤ) x) /
        (N : ℝ) ≤ N
  rw [show (∑ r ∈ Finset.range N,
      HaarQuarter.TrigonometricHaarExtraction.character (r : ℤ) x) = z by rfl]
  rw [div_le_iff₀ hNreal]
  nlinarith

private theorem realFejerKernel_nonneg (N : ℕ) (x : ℝ) :
    0 ≤ HaarQuarter.TheoremD.FejerFourier.realFejerKernel N x := by
  unfold HaarQuarter.TheoremD.FejerFourier.realFejerKernel
  exact div_nonneg (Complex.normSq_nonneg _) (by positivity)

/-- Pointwise peak bound for the actual DVP scalar kernel. -/
theorem deLaValleePoussinCircleKernel_norm_le {N : ℕ} (hN : 0 < N)
    (x : UnitAddCircle) :
    ‖deLaValleePoussinCircleKernel N x‖ ≤ 5 * N := by
  refine Quotient.inductionOn x ?_
  intro t
  rw [deLaValleePoussinCircleKernel_eval_eq_real]
  unfold HaarQuarter.TheoremD.FejerFourier.realDeLaValleePoussinKernel
  have h1 := realFejerKernel_nonneg (2 * N) t
  have h2 := realFejerKernel_nonneg N t
  have h2N : 0 < 2 * N := by omega
  have h1' := realFejerKernel_le h2N t
  have h2' := realFejerKernel_le hN t
  have h1'' : HaarQuarter.TheoremD.FejerFourier.realFejerKernel (2 * N) t ≤
      2 * (N : ℝ) := by simpa [Nat.cast_mul] using h1'
  have h2'' : HaarQuarter.TheoremD.FejerFourier.realFejerKernel N t ≤
      (N : ℝ) := h2'
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc
    |2 * HaarQuarter.TheoremD.FejerFourier.realFejerKernel (2 * N) t -
        HaarQuarter.TheoremD.FejerFourier.realFejerKernel N t|
      ≤ |2 * HaarQuarter.TheoremD.FejerFourier.realFejerKernel (2 * N) t| +
        |HaarQuarter.TheoremD.FejerFourier.realFejerKernel N t| := abs_sub _ _
    _ = 2 * HaarQuarter.TheoremD.FejerFourier.realFejerKernel (2 * N) t +
          HaarQuarter.TheoremD.FejerFourier.realFejerKernel N t := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) h1), abs_of_nonneg h2]
    _ ≤ 2 * (2 * (N : ℝ)) + (N : ℝ) := by nlinarith
    _ = 5 * N := by ring

/-- Tensor DVP peak bound with the product of the true shape bandwidths. -/
theorem tensorDvpKernel_norm_le {d : ℕ} (N : Fin d → ℕ)
    (hN : ∀ i, 0 < N i) (x : UnitAddTorus (Fin d)) :
    ‖tensorDvpKernel N x‖ ≤ ∏ i, (5 * (N i : ℝ)) := by
  change ‖∏ i, deLaValleePoussinCircleKernel (N i) (x i)‖ ≤ _
  rw [norm_prod]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact norm_nonneg _
  · intro i hi
    exact deLaValleePoussinCircleKernel_norm_le (hN i) (x i)

/-- Normalized absolute reconstruction weights for one shape. -/
def normalizedKernelWeight {d : ℕ} (N : Fin d → ℕ)
    (j : OversampledGrid d N) (x : UnitAddTorus (Fin d)) : ℝ :=
  (oversampledGridSize N)⁻¹ *
    ‖tensorDvpKernel N (oversampledTorusGridPoint N j - x)‖

/-- The squared ℓ² norm of one shape's normalized DVP evaluation row is
bounded independently of its bandwidth.  The proof combines the actual
pointwise peak and translated-grid absolute-mass estimates. -/
theorem normalizedKernelWeight_sq_sum_le {d : ℕ}
    (N : Fin d → ℕ) (hN : ∀ i, 0 < N i)
    (x : UnitAddTorus (Fin d)) :
    (∑ j : OversampledGrid d N, normalizedKernelWeight N j x ^ 2) ≤
      ((25 / 4 : ℝ) ^ d) := by
  classical
  let M : ℝ := oversampledGridSize N
  let P : ℝ := ∏ i, (5 * (N i : ℝ))
  have hM : 0 < M := by
    dsimp [M]
    exact oversampledGridSize_pos N hN
  have hpoint (j : OversampledGrid d N) :
      normalizedKernelWeight N j x ≤ P / M := by
    change (oversampledGridSize N)⁻¹ *
        ‖tensorDvpKernel N (oversampledTorusGridPoint N j - x)‖ ≤ P / M
    have hkernel := tensorDvpKernel_norm_le N hN
      (oversampledTorusGridPoint N j - x)
    have hminv : 0 ≤ (oversampledGridSize N)⁻¹ := by positivity
    calc
      _ ≤ (oversampledGridSize N)⁻¹ * P :=
        mul_le_mul_of_nonneg_left hkernel hminv
      _ = P / M := by simp [M, div_eq_mul_inv, mul_comm]
  have hratio : P / M = (5 / 4 : ℝ) ^ d := by
    dsimp [P, M, oversampledGridSize]
    rw [← Finset.prod_div_distrib]
    calc
      (∏ i, (5 * (N i : ℝ)) / (4 * (N i : ℝ))) =
          ∏ _i : Fin d, (5 / 4 : ℝ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hNi : (N i : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hN i))
        field_simp [hNi]
      _ = (5 / 4 : ℝ) ^ d := by simp [Finset.prod_const, div_pow]
  have hmass : (∑ j : OversampledGrid d N,
      normalizedKernelWeight N j x) ≤ (5 : ℝ) ^ d := by
    have hraw := tensorDvp_oversampled_grid_abs_mass_le N hN x
    have hfactor : ∏ i, (5 * (N i * 4 : ℝ)) = (5 : ℝ) ^ d * M := by
      simp [M, oversampledGridSize, Finset.prod_mul_distrib, mul_comm]
    have hraw' : (∑ j : OversampledGrid d N,
        ‖tensorDvpKernel N (oversampledTorusGridPoint N j - x)‖) ≤
        (5 : ℝ)^d * M := by simpa [hfactor] using hraw
    calc
      _ = M⁻¹ * ∑ j : OversampledGrid d N,
          ‖tensorDvpKernel N (oversampledTorusGridPoint N j - x)‖ := by
        simp [normalizedKernelWeight, M, Finset.mul_sum]
      _ ≤ M⁻¹ * ((5 : ℝ)^d * M) :=
        mul_le_mul_of_nonneg_left hraw' (by positivity)
      _ = (5 : ℝ)^d := by field_simp [ne_of_gt hM]
  have hsquare : ∀ j : OversampledGrid d N,
      normalizedKernelWeight N j x ^ 2 ≤
        (P / M) * normalizedKernelWeight N j x := by
    intro j
    have hnonneg : 0 ≤ normalizedKernelWeight N j x := by
      unfold normalizedKernelWeight
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt
        (oversampledGridSize_pos N hN))) (norm_nonneg _)
    simpa [pow_two] using mul_le_mul_of_nonneg_right (hpoint j) hnonneg
  calc
    _ ≤ ∑ j : OversampledGrid d N,
        (P / M) * normalizedKernelWeight N j x :=
      Finset.sum_le_sum fun j _ => hsquare j
    _ = (P / M) * ∑ j : OversampledGrid d N,
        normalizedKernelWeight N j x := by rw [Finset.mul_sum]
    _ ≤ ((5 / 4 : ℝ) ^ d) * (5 : ℝ)^d := by
      rw [hratio]
      exact mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = ((25 / 4 : ℝ) ^ d) := by
      rw [← mul_pow]
      congr 1
      norm_num

/-- Coordinate bandwidth of the smooth block at one dyadic shape. -/
def shapeBandwidth {d n : ℕ} (r : Shape d n) : Fin d → ℕ :=
  fun i => 2 ^ (r.1 i + 1)

/-- Every coordinate in a grade-`n` shape is at most `n`. -/
theorem shapeCoordinate_le_grade {d n : ℕ} (r : Shape d n) (i : Fin d) :
    r.1 i ≤ n := by
  have htotal : (∑ j : Fin d, r.1 j) = n := by
    have hmem := r.2
    rw [Finset.mem_finsuppAntidiag] at hmem
    simpa using hmem.1
  have hi : r.1 i ≤ ∑ j : Fin d, r.1 j := by
    exact Finset.single_le_sum (fun j hj => Nat.zero_le (r.1 j)) (Finset.mem_univ i)
  omega

/-- The common box bandwidth that contains all grade-`n` smooth blocks. -/
def gradeCommonBandwidth {d n : ℕ} : Fin d → ℕ := fun _ => 2 ^ (n + 1)

theorem shapeBandwidth_le_gradeCommon {d n : ℕ} (r : Shape d n) (i : Fin d) :
    shapeBandwidth r i ≤ gradeCommonBandwidth (d := d) (n := n) i := by
  dsimp [shapeBandwidth, gradeCommonBandwidth]
  exact Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right (shapeCoordinate_le_grade r i) 1)

abbrev ShapeGrid {d n : ℕ} (r : Shape d n) := Grid d (shapeBandwidth r)

/-- A real coordinate of one block's oversampled complex grid. -/
abbrev ShapeSampleIndex (d n : ℕ) :=
  Σ r : Shape d n, (ShapeGrid r × Bool)

/-- The complete, finite real sample vector of all smooth blocks in grade n. -/
abbrev GradeSamples (d n : ℕ) := ShapeSampleIndex d n → ℝ

/-- Decode one shape's real/imaginary sample coordinates to complex grid
values, using the same coordinate convention as the established DVP cover. -/
def decodeShapeSamplesLinearMap {d n : ℕ} (r : Shape d n) :
    (GradeSamples d n) →ₗ[ℝ] (ShapeGrid r → ℂ) where
  toFun a j :=
    (a ⟨r, (j, false)⟩ : ℂ) + Complex.I * (a ⟨r, (j, true)⟩ : ℂ)
  map_add' a b := by
    funext j
    simp
    ring
  map_smul' c a := by
    funext j
    simp
    ring

def decodeShapeSamplesCLM {d n : ℕ} (r : Shape d n) :
    (GradeSamples d n) →L[ℝ] (ShapeGrid r → ℂ) :=
  (decodeShapeSamplesLinearMap r).mkContinuous 2 (by
    intro a
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg (by norm_num) (norm_nonneg a))).2
    intro j
    change ‖(a ⟨r, (j, false)⟩ : ℂ) +
      Complex.I * (a ⟨r, (j, true)⟩ : ℂ)‖ ≤ 2 * ‖a‖
    calc
      _ ≤ |a ⟨r, (j, false)⟩| + |a ⟨r, (j, true)⟩| := by
        calc
          _ ≤ ‖(a ⟨r, (j, false)⟩ : ℂ)‖ +
              ‖Complex.I * (a ⟨r, (j, true)⟩ : ℂ)‖ := norm_add_le _ _
          _ = _ := by simp
      _ ≤ ‖a‖ + ‖a‖ := by
        have h1 := norm_le_pi_norm a ⟨r, (j, false)⟩
        have h2 := norm_le_pi_norm a ⟨r, (j, true)⟩
        simpa [Real.norm_eq_abs] using add_le_add h1 h2
      _ = 2 * ‖a‖ := by ring)

def shapeDvpReconstructionCLM {d n : ℕ} (r : Shape d n) :
    (GradeSamples d n) →L[ℝ] C(UnitAddTorus (Fin d), ℂ) :=
  (oversampledDvpReconstructionCLM (shapeBandwidth r)
    (by intro i; dsimp [shapeBandwidth]; positivity)).restrictScalars ℝ |>.comp
      (decodeShapeSamplesCLM r)

/-- Actual blockwise DVP synthesis of one finite real sample vector. -/
def gradeDvpReconstructionCLM {d n : ℕ} :
    (GradeSamples d n) →L[ℝ] C(UnitAddTorus (Fin d), ℂ) :=
  ∑ r : Shape d n, shapeDvpReconstructionCLM r

/-- The actual smooth periodic Fourier polynomial consisting of all the
shape blocks in grade n. -/
def smoothGradePolynomial {d n : ℕ} (g : RealPeriodic d) :
    C(UnitAddTorus (Fin d), ℂ) :=
  ∑ r : Shape d n, block r.1 g

/-- Real/imaginary coordinates sampled from the actual smooth grade blocks. -/
def encodeSmoothGradeSamples {d n : ℕ} (g : RealPeriodic d) : GradeSamples d n :=
  fun a =>
    let r := a.1
    let j := a.2.1
    let z := block r.1 g (oversampledTorusGridPoint (shapeBandwidth r) j)
    if a.2.2 then z.im else z.re

/-- The complex coefficient of one normalized DVP sample in the synthesis. -/
def normalizedKernelCoefficient {d : ℕ} (N : Fin d → ℕ)
    (j : OversampledGrid d N) (x : UnitAddTorus (Fin d)) : ℂ :=
  (↑((oversampledGridSize N)⁻¹) : ℂ) *
    tensorDvpKernel N (oversampledTorusGridPoint N j - x)

/-- Real part of the actual scalar evaluation row on realified sample data. -/
def gradeEvaluationRealRow {d n : ℕ} (x : UnitAddTorus (Fin d)) :
    ShapeSampleIndex d n → ℝ := fun a =>
  if a.2.2 then
    -(normalizedKernelCoefficient (shapeBandwidth a.1) a.2.1 x).im
  else (normalizedKernelCoefficient (shapeBandwidth a.1) a.2.1 x).re

/-- Imaginary part of the actual scalar evaluation row on realified sample data. -/
def gradeEvaluationImagRow {d n : ℕ} (x : UnitAddTorus (Fin d)) :
    ShapeSampleIndex d n → ℝ := fun a =>
  if a.2.2 then
    (normalizedKernelCoefficient (shapeBandwidth a.1) a.2.1 x).re
  else (normalizedKernelCoefficient (shapeBandwidth a.1) a.2.1 x).im

private theorem normalizedKernelCoefficient_norm {d : ℕ} (N : Fin d → ℕ)
    (hN : ∀ i, 0 < N i) (j : OversampledGrid d N)
    (x : UnitAddTorus (Fin d)) :
    ‖normalizedKernelCoefficient N j x‖ = normalizedKernelWeight N j x := by
  rw [normalizedKernelCoefficient, normalizedKernelWeight, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (le_of_lt (oversampledGridSize_pos N hN)))]

private theorem complex_parts_sq_sum (z : ℂ) :
    z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- The real and imaginary rows have the same joint squared norm, bounded by
the number of shapes times the dimension-only one-shape constant. -/
theorem gradeEvaluationRealRow_sq_sum_le {d n : ℕ}
    (x : UnitAddTorus (Fin d)) :
    (∑ a : ShapeSampleIndex d n, gradeEvaluationRealRow x a ^ 2) ≤
      (((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
        ((25 / 4 : ℝ) ^ d) := by
  classical
  unfold gradeEvaluationRealRow
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool,
    Bool.false_eq_true, ↓reduceIte]
  have hshape (r : Shape d n) :
      (∑ j : ShapeGrid r,
        ((-(normalizedKernelCoefficient (shapeBandwidth r) j x).im) ^ 2 +
          (normalizedKernelCoefficient (shapeBandwidth r) j x).re ^ 2)) ≤
        ((25 / 4 : ℝ) ^ d) := by
    have hNshape : ∀ i : Fin d, 0 < shapeBandwidth r i := by
      intro i
      exact Nat.pow_pos (by norm_num)
    calc
      _ = ∑ j : ShapeGrid r,
          ‖normalizedKernelCoefficient (shapeBandwidth r) j x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        have hc := complex_parts_sq_sum
          (normalizedKernelCoefficient (shapeBandwidth r) j x)
        nlinarith [sq_nonneg
          (normalizedKernelCoefficient (shapeBandwidth r) j x).im]
      _ = ∑ j : ShapeGrid r,
          normalizedKernelWeight (shapeBandwidth r) j x ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        exact normalizedKernelCoefficient_norm (shapeBandwidth r) hNshape j x
      _ ≤ ((25 / 4 : ℝ) ^ d) :=
        normalizedKernelWeight_sq_sum_le (shapeBandwidth r) hNshape x
  calc
    _ ≤ ∑ r : Shape d n, ((25 / 4 : ℝ) ^ d) :=
      Finset.sum_le_sum fun r _ => hshape r
    _ = (((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
        ((25 / 4 : ℝ) ^ d) := by simp [Finset.sum_const, nsmul_eq_mul]

theorem gradeEvaluationImagRow_sq_sum_le {d n : ℕ}
    (x : UnitAddTorus (Fin d)) :
    (∑ a : ShapeSampleIndex d n, gradeEvaluationImagRow x a ^ 2) ≤
      (((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
        ((25 / 4 : ℝ) ^ d) := by
  classical
  unfold gradeEvaluationImagRow
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool,
    Bool.false_eq_true, ↓reduceIte]
  have hshape (r : Shape d n) :
      (∑ j : ShapeGrid r,
        ((normalizedKernelCoefficient (shapeBandwidth r) j x).re ^ 2 +
          (normalizedKernelCoefficient (shapeBandwidth r) j x).im ^ 2)) ≤
        ((25 / 4 : ℝ) ^ d) := by
    have hNshape : ∀ i : Fin d, 0 < shapeBandwidth r i := by
      intro i
      exact Nat.pow_pos (by norm_num)
    calc
      _ = ∑ j : ShapeGrid r,
          ‖normalizedKernelCoefficient (shapeBandwidth r) j x‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        exact complex_parts_sq_sum (normalizedKernelCoefficient (shapeBandwidth r) j x)
      _ = ∑ j : ShapeGrid r,
          normalizedKernelWeight (shapeBandwidth r) j x ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        congr 1
        exact normalizedKernelCoefficient_norm (shapeBandwidth r) hNshape j x
      _ ≤ ((25 / 4 : ℝ) ^ d) :=
        normalizedKernelWeight_sq_sum_le (shapeBandwidth r) hNshape x
  calc
    _ ≤ ∑ r : Shape d n, ((25 / 4 : ℝ) ^ d) :=
      Finset.sum_le_sum fun r _ => hshape r
    _ = (((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
        ((25 / 4 : ℝ) ^ d) := by simp [Finset.sum_const, nsmul_eq_mul]

private theorem sigmaBool_eq_self {d n : ℕ}
    (s : ShapeSampleIndex d n) (b : Bool) :
    (⟨s.1, (s.2.1, b)⟩ : ShapeSampleIndex d n) = s ↔ b = s.2.2 := by
  constructor
  · intro h
    exact congrArg (fun a : ShapeSampleIndex d n => a.2.2) h
  · intro hb
    have hp : (s.2.1, b) = s.2 := Prod.ext rfl hb
    exact (congrArg (Sigma.mk s.1) hp).trans (Sigma.eta s)

theorem decodeShapeSamplesLinearMap_single {d n : ℕ}
    (r : Shape d n) (s : ShapeSampleIndex d n) (j : ShapeGrid r) :
    decodeShapeSamplesLinearMap r (Pi.single s (1 : ℝ)) j =
      (if (⟨r, (j, false)⟩ : ShapeSampleIndex d n) = s then 1 else 0) +
        Complex.I *
          (if (⟨r, (j, true)⟩ : ShapeSampleIndex d n) = s then 1 else 0) := by
  by_cases h0 : (⟨r, (j, false)⟩ : ShapeSampleIndex d n) = s
  · have h1 : (⟨r, (j, true)⟩ : ShapeSampleIndex d n) ≠ s := by
      intro h
      have hfalse := congrArg (fun a : ShapeSampleIndex d n => a.2.2) h0
      have htrue := congrArg (fun a : ShapeSampleIndex d n => a.2.2) h
      rw [← hfalse] at htrue
      cases htrue
    simp [decodeShapeSamplesLinearMap, Pi.single_apply, h0, h1]
  · by_cases h1 : (⟨r, (j, true)⟩ : ShapeSampleIndex d n) = s
    · simp [decodeShapeSamplesLinearMap, Pi.single_apply, h0, h1]
    · simp [decodeShapeSamplesLinearMap, Pi.single_apply, h0, h1]

private theorem dvpReconstruction_singleton {d : ℕ} (N : Fin d → ℕ)
    (j : OversampledGrid d N) (z : ℂ) (x : UnitAddTorus (Fin d)) :
    oversampledDvpReconstruction N (fun k => if k = j then z else 0) x =
      normalizedKernelCoefficient N j x * z := by
  classical
  unfold oversampledDvpReconstruction
  simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply, smul_eq_mul]
  have hsum :
      (∑ k : OversampledGrid d N,
        (if k = j then z else 0) * (translatedTensorDvpKernel N k) x) =
        z * (translatedTensorDvpKernel N j) x := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro k hk hkj
      simp [hkj]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  rw [hsum]
  simp [normalizedKernelCoefficient, translatedTensorDvpKernel, mul_comm]
  ring

private theorem shapeDvpReconstruction_single_sample {d n : ℕ}
    (r : Shape d n) (s : ShapeSampleIndex d n) (x : UnitAddTorus (Fin d)) :
    shapeDvpReconstructionCLM r (Pi.single s (1 : ℝ)) x =
      if r = s.1 then
        normalizedKernelCoefficient (shapeBandwidth s.1) s.2.1 x *
          (if s.2.2 then Complex.I else 1)
      else 0 := by
  classical
  by_cases hr : r = s.1
  · subst r
    have hgrid : decodeShapeSamplesLinearMap s.1 (Pi.single s (1 : ℝ)) =
        fun j => if j = s.2.1 then (if s.2.2 then Complex.I else 1) else 0 := by
      funext j
      rw [decodeShapeSamplesLinearMap_single]
      by_cases hj : j = s.2.1
      · subst j
        cases hb : s.2.2 <;> simp [sigmaBool_eq_self, hb]
      · have h0 : (⟨s.1, (j, false)⟩ : ShapeSampleIndex d n) ≠ s := by
          intro h
          have hp : (j, false) = s.2 := by
            exact eq_of_heq (Sigma.mk.inj h).2
          exact hj (congrArg Prod.fst hp)
        have h1 : (⟨s.1, (j, true)⟩ : ShapeSampleIndex d n) ≠ s := by
          intro h
          have hp : (j, true) = s.2 := by
            exact eq_of_heq (Sigma.mk.inj h).2
          exact hj (congrArg Prod.fst hp)
        simp [hj, h0, h1]
    change oversampledDvpReconstruction (shapeBandwidth s.1)
      (decodeShapeSamplesLinearMap s.1 (Pi.single s (1 : ℝ))) x = _
    rw [hgrid]
    simpa [dvpReconstruction_singleton]
  · have hzero : decodeShapeSamplesLinearMap r (Pi.single s (1 : ℝ)) =
        fun _ => 0 := by
      funext j
      rw [decodeShapeSamplesLinearMap_single]
      have h0 : (⟨r, (j, false)⟩ : ShapeSampleIndex d n) ≠ s := by
        intro h
        exact hr (congrArg (fun a : ShapeSampleIndex d n => a.1) h)
      have h1 : (⟨r, (j, true)⟩ : ShapeSampleIndex d n) ≠ s := by
        intro h
        exact hr (congrArg (fun a : ShapeSampleIndex d n => a.1) h)
      simp [h0, h1]
    change oversampledDvpReconstruction (shapeBandwidth r)
      (decodeShapeSamplesLinearMap r (Pi.single s (1 : ℝ))) x = _
    rw [hzero]
    simp [oversampledDvpReconstruction, hr]

theorem gradeDvpReconstruction_single_sample {d n : ℕ}
    (s : ShapeSampleIndex d n) (x : UnitAddTorus (Fin d)) :
    gradeDvpReconstructionCLM (Pi.single s (1 : ℝ)) x =
      normalizedKernelCoefficient (shapeBandwidth s.1) s.2.1 x *
        (if s.2.2 then Complex.I else 1) := by
  classical
  unfold gradeDvpReconstructionCLM
  simp only [ContinuousLinearMap.sum_apply, ContinuousMap.sum_apply]
  rw [Fintype.sum_eq_single s.1]
  · simpa using shapeDvpReconstruction_single_sample s.1 s x
  · intro r hr
    simp [shapeDvpReconstruction_single_sample, hr]

theorem decodeShapeSamples_encodeSmoothGradeSamples {d n : ℕ}
    (g : RealPeriodic d) (r : Shape d n) :
    decodeShapeSamplesLinearMap r (encodeSmoothGradeSamples g) =
      fun j => block r.1 g (oversampledTorusGridPoint (shapeBandwidth r) j) := by
  funext j
  simp [decodeShapeSamplesLinearMap, encodeSmoothGradeSamples]
  apply Complex.ext <;> simp

theorem smoothBlock_bandlimited {d n : ℕ} (r : Shape d n)
    (g : RealPeriodic d) :
    ∀ k ∈ frequencyBox r.1, ∀ i : Fin d,
      (k i).natAbs ≤ shapeBandwidth r i := by
  intro k hk i
  have hk' := Fintype.mem_piFinset.mp hk i
  rcases Finset.mem_Icc.mp hk' with ⟨hlo, hhi⟩
  have habs : |k i| ≤ (2 : ℤ) ^ (r.1 i + 1) := by
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hnat : ((k i).natAbs : ℤ) ≤ (2 : ℤ) ^ (r.1 i + 1) := by
    simpa only [Int.natCast_natAbs, abs_eq] using habs
  exact_mod_cast hnat

theorem shapeDvpReconstruction_encode_exact {d n : ℕ}
    (g : RealPeriodic d) (r : Shape d n) :
    shapeDvpReconstructionCLM r (encodeSmoothGradeSamples g) = block r.1 g := by
  change oversampledDvpReconstructionCLM (shapeBandwidth r)
      (by intro i; dsimp [shapeBandwidth]; positivity)
      (decodeShapeSamplesLinearMap r (encodeSmoothGradeSamples g)) = _
  rw [decodeShapeSamples_encodeSmoothGradeSamples]
  exact oversampledDvpReconstruction_eq_of_bandlimited_polynomial
    (shapeBandwidth r) (by intro i; dsimp [shapeBandwidth]; positivity)
    (frequencyBox r.1)
    (fun k => (tensorMultiplier r.1 k : ℂ) * realPeriodicFourierCoeff g k)
    (smoothBlock_bandlimited r g)

theorem gradeDvpReconstruction_encode_exact {d n : ℕ}
    (g : RealPeriodic d) :
    gradeDvpReconstructionCLM (d := d) (n := n)
      (encodeSmoothGradeSamples (d := d) (n := n) g) =
      smoothGradePolynomial (d := d) (n := n) g := by
  simp [gradeDvpReconstructionCLM, smoothGradePolynomial,
    shapeDvpReconstruction_encode_exact]

/-- The actual smooth grade is exactly reproduced from the common bounding-box
grid.  Its frequency box is contained in the common DVP pass band. -/
theorem commonDvpReconstruction_smoothGrade_exact {d n : ℕ}
    (g : RealPeriodic d) :
    oversampledDvpRealCoordinateReconstruction
        (gradeCommonBandwidth (d := d) (n := n))
        (by intro i; dsimp [gradeCommonBandwidth]; positivity)
        (encodeComplexSamples (gradeCommonBandwidth (d := d) (n := n))
          (smoothGradePolynomial (d := d) (n := n) g)) =
      smoothGradePolynomial (d := d) (n := n) g := by
  classical
  let N := gradeCommonBandwidth (d := d) (n := n)
  have hN : ∀ i, 0 < N i := by intro i; dsimp [N, gradeCommonBandwidth]; positivity
  have hencode : encodeComplexSamples N (smoothGradePolynomial (d := d) (n := n) g) =
      ∑ r : Shape d n, encodeComplexSamples N (block r.1 g) := by
    funext j
    simp [encodeComplexSamples, smoothGradePolynomial, Complex.re_sum,
      Complex.im_sum]
  rw [hencode]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply oversampledDvpRealCoordinateReconstruction_exact N hN
    (SmoothResolution.frequencyBox r.1)
    (fun k => (tensorMultiplier r.1 k : ℂ) * realPeriodicFourierCoeff g k)
  intro k hk i
  exact (smoothBlock_bandlimited r g k hk i).trans
    (shapeBandwidth_le_gradeCommon r i)

/-- The exact finite Euclidean dimension of the joint shape sample vector. -/
abbrev JointSampleDimension (d n : ℕ) := Fintype.card (ShapeSampleIndex d n)

def jointSampleIndexEquivFin (d n : ℕ) :
    ShapeSampleIndex d n ≃ Fin (JointSampleDimension d n) :=
  Fintype.equivFin (ShapeSampleIndex d n)

/-- Decode a Euclidean vector into the actual joint shape-grid coordinates.
The source is finite dimensional, so the coordinate map is continuous. -/
def decodeJointEuclideanLinearMap {d n : ℕ} :
    EuclideanSpace ℝ (Fin (JointSampleDimension d n)) →ₗ[ℝ] GradeSamples d n where
  toFun z a := z (jointSampleIndexEquivFin d n a)
  map_add' z w := by funext a; simp
  map_smul' c z := by funext a; simp

def decodeJointEuclideanCLM {d n : ℕ} :
    EuclideanSpace ℝ (Fin (JointSampleDimension d n)) →L[ℝ] GradeSamples d n :=
  ⟨decodeJointEuclideanLinearMap,
    decodeJointEuclideanLinearMap.continuous_of_finiteDimensional⟩

/-- The actual blockwise DVP synthesis viewed as a map from Euclidean joint
sample coordinates to continuous functions. -/
def jointGradeSynthesisCLM {d n : ℕ} :
    EuclideanSpace ℝ (Fin (JointSampleDimension d n)) →L[ℝ]
      C(UnitAddTorus (Fin d), ℂ) :=
  (gradeDvpReconstructionCLM (d := d) (n := n)).comp decodeJointEuclideanCLM

@[simp] theorem jointGradeSynthesisCLM_apply_decode {d n : ℕ}
    (a : GradeSamples d n) :
    jointGradeSynthesisCLM (d := d) (n := n)
      (WithLp.toLp 2 (fun i : Fin (JointSampleDimension d n) =>
        a ((jointSampleIndexEquivFin d n).symm i))) =
      gradeDvpReconstructionCLM a := by
  simp [jointGradeSynthesisCLM, decodeJointEuclideanCLM,
    decodeJointEuclideanLinearMap, jointSampleIndexEquivFin]

/-- Real and imaginary scalar evaluations of the actual grade synthesis. -/
def jointGradeRealEvaluationCLM {d n : ℕ} (x : UnitAddTorus (Fin d)) :
    EuclideanSpace ℝ (Fin (JointSampleDimension d n)) →L[ℝ] ℝ :=
  (Complex.reCLM.comp ((ContinuousMap.evalCLM ℂ x).restrictScalars ℝ)).comp
    (jointGradeSynthesisCLM (d := d) (n := n))

def jointGradeImagEvaluationCLM {d n : ℕ} (x : UnitAddTorus (Fin d)) :
    EuclideanSpace ℝ (Fin (JointSampleDimension d n)) →L[ℝ] ℝ :=
  (Complex.imCLM.comp ((ContinuousMap.evalCLM ℂ x).restrictScalars ℝ)).comp
    (jointGradeSynthesisCLM (d := d) (n := n))

/-- The exact global real/imaginary evaluation index for the common DVP grid. -/
abbrev GradeCommonGrid (d n : ℕ) :=
  Grid d (gradeCommonBandwidth (d := d) (n := n))

abbrev GradeCommonOutputIndex (d n : ℕ) := GradeCommonGrid d n × Bool

/-- The finite `ℓ∞` feature map consisting of all real and imaginary values
of the actual joint shape synthesis on the common global grid. -/
def jointGradeCommonGridFeatureLinearMap {d n : ℕ} :
    EuclideanSpace ℝ (Fin (JointSampleDimension d n)) →ₗ[ℝ]
      PiLp ∞ (fun _ : GradeCommonOutputIndex d n => ℝ) where
  toFun z := WithLp.toLp ∞ fun a : GradeCommonOutputIndex d n =>
    if a.2 then
      jointGradeImagEvaluationCLM (oversampledTorusGridPoint
        (gradeCommonBandwidth (d := d) (n := n)) a.1) z
    else jointGradeRealEvaluationCLM (oversampledTorusGridPoint
      (gradeCommonBandwidth (d := d) (n := n)) a.1) z
  map_add' z w := by
    ext a
    by_cases h : a.2 <;> simp [h]
  map_smul' c z := by
    ext a
    by_cases h : a.2 <;> simp [h]

def jointGradeCommonGridFeatureCLM {d n : ℕ} :
    EuclideanSpace ℝ (Fin (JointSampleDimension d n)) →L[ℝ]
      PiLp ∞ (fun _ : GradeCommonOutputIndex d n => ℝ) :=
  ⟨jointGradeCommonGridFeatureLinearMap,
    jointGradeCommonGridFeatureLinearMap.continuous_of_finiteDimensional⟩

@[simp] theorem jointGradeCommonGridFeatureCLM_apply {d n : ℕ}
    (z : EuclideanSpace ℝ (Fin (JointSampleDimension d n)))
    (a : GradeCommonOutputIndex d n) :
    jointGradeCommonGridFeatureCLM (d := d) (n := n) z a =
      if a.2 then
        (jointGradeSynthesisCLM (d := d) (n := n) z
          (oversampledTorusGridPoint (gradeCommonBandwidth (d := d) (n := n)) a.1)).im
      else
        (jointGradeSynthesisCLM (d := d) (n := n) z
          (oversampledTorusGridPoint (gradeCommonBandwidth (d := d) (n := n)) a.1)).re := by
  simp [jointGradeCommonGridFeatureCLM, jointGradeRealEvaluationCLM,
    jointGradeImagEvaluationCLM, jointGradeCommonGridFeatureLinearMap]

/-- The KGG dictionary vector representing one common-grid evaluation row. -/
def jointGradeCommonRowVector {d n : ℕ} (a : GradeCommonOutputIndex d n) :
    EuclideanSpace ℝ (Fin (JointSampleDimension d n)) :=
  WithLp.toLp 2 fun i => jointGradeCommonGridFeatureCLM (d := d) (n := n)
    (EuclideanSpace.basisFun (Fin (JointSampleDimension d n)) ℝ i) a

theorem jointGradeCommonGridFeature_eq_inner_row {d n : ℕ}
    (z : EuclideanSpace ℝ (Fin (JointSampleDimension d n)))
    (a : GradeCommonOutputIndex d n) :
    jointGradeCommonGridFeatureCLM (d := d) (n := n) z a =
      inner ℝ z (jointGradeCommonRowVector (d := d) (n := n) a) := by
  classical
  let b := EuclideanSpace.basisFun (Fin (JointSampleDimension d n)) ℝ
  have hz : z = ∑ i, z i • b i := by
    simpa [b, EuclideanSpace.basisFun_repr] using (b.sum_repr z).symm
  have hrow :
      inner ℝ z (jointGradeCommonRowVector (d := d) (n := n) a) =
        ∑ i, z i * jointGradeCommonGridFeatureCLM (d := d) (n := n) (b i) a := by
    simp [jointGradeCommonRowVector, PiLp.inner_apply,
      EuclideanSpace.basisFun_apply, b, mul_comm]
  calc
    jointGradeCommonGridFeatureCLM (d := d) (n := n) z a =
        ∑ i, z i * jointGradeCommonGridFeatureCLM (d := d) (n := n) (b i) a := by
      conv_lhs => rw [hz]
      simp only [map_sum, map_smul]
      simp [PiLp.toLp_apply, smul_eq_mul]
    _ = inner ℝ z (jointGradeCommonRowVector (d := d) (n := n) a) := hrow.symm

private theorem decodeJointEuclideanCLM_basis_eq_single {d n : ℕ}
    (s : ShapeSampleIndex d n) :
    decodeJointEuclideanCLM (d := d) (n := n)
      (EuclideanSpace.basisFun (Fin (JointSampleDimension d n)) ℝ
        (jointSampleIndexEquivFin d n s)) = Pi.single s (1 : ℝ) := by
  ext a
  simp [decodeJointEuclideanCLM, decodeJointEuclideanLinearMap,
    EuclideanSpace.basisFun_apply, Pi.single_apply]

theorem jointGradeCommonRowVector_coordinate {d n : ℕ}
    (a : GradeCommonOutputIndex d n) (s : ShapeSampleIndex d n) :
    jointGradeCommonRowVector (d := d) (n := n) a
      (jointSampleIndexEquivFin d n s) =
      if a.2 then
        gradeEvaluationImagRow (oversampledTorusGridPoint
          (gradeCommonBandwidth (d := d) (n := n)) a.1) s
      else
        gradeEvaluationRealRow (oversampledTorusGridPoint
          (gradeCommonBandwidth (d := d) (n := n)) a.1) s := by
  classical
  let x := oversampledTorusGridPoint (gradeCommonBandwidth (d := d) (n := n)) a.1
  simp only [jointGradeCommonRowVector, PiLp.toLp_apply]
  rw [jointGradeCommonGridFeatureCLM_apply]
  change (if a.2 then
      (jointGradeSynthesisCLM (d := d) (n := n)
        (EuclideanSpace.basisFun (Fin (JointSampleDimension d n)) ℝ
          (jointSampleIndexEquivFin d n s)) x).im
    else
      (jointGradeSynthesisCLM (d := d) (n := n)
        (EuclideanSpace.basisFun (Fin (JointSampleDimension d n)) ℝ
          (jointSampleIndexEquivFin d n s)) x).re) = _
  simp only [jointGradeSynthesisCLM, decodeJointEuclideanCLM_basis_eq_single,
    ContinuousLinearMap.comp_apply]
  rw [gradeDvpReconstruction_single_sample]
  cases ha : a.2 <;> cases hs : s.2.2 <;>
    simp [x, ha, hs, gradeEvaluationRealRow, gradeEvaluationImagRow,
      normalizedKernelCoefficient, Complex.mul_re, Complex.mul_im]

theorem jointGradeCommonRowVector_sq_sum_le {d n : ℕ}
    (a : GradeCommonOutputIndex d n) :
    (∑ i : Fin (JointSampleDimension d n),
      jointGradeCommonRowVector (d := d) (n := n) a i ^ 2) ≤
      (((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
        ((25 / 4 : ℝ) ^ d) := by
  classical
  let e := jointSampleIndexEquivFin d n
  have hsum :
      (∑ s : ShapeSampleIndex d n,
        jointGradeCommonRowVector (d := d) (n := n) a (e s) ^ 2) =
      ∑ i : Fin (JointSampleDimension d n),
        jointGradeCommonRowVector (d := d) (n := n) a i ^ 2 := by
    exact Fintype.sum_equiv e
      (fun s => jointGradeCommonRowVector (d := d) (n := n) a (e s) ^ 2)
      (fun i => jointGradeCommonRowVector (d := d) (n := n) a i ^ 2)
      (by intro s; rfl)
  calc
    _ = ∑ s : ShapeSampleIndex d n,
        jointGradeCommonRowVector (d := d) (n := n) a (e s) ^ 2 := hsum.symm
    _ ≤ (((Finset.univ : Finset (Fin d)).finsuppAntidiag n).card : ℝ) *
        ((25 / 4 : ℝ) ^ d) := by
      by_cases hb : a.2
      · calc
          _ = ∑ s : ShapeSampleIndex d n,
              gradeEvaluationImagRow
                (oversampledTorusGridPoint (gradeCommonBandwidth (d := d) (n := n)) a.1) s ^ 2 := by
                apply Finset.sum_congr rfl
                intro s hs
                rw [jointGradeCommonRowVector_coordinate]
                simp [hb]
          _ ≤ _ := gradeEvaluationImagRow_sq_sum_le
            (oversampledTorusGridPoint (gradeCommonBandwidth (d := d) (n := n)) a.1)
      · calc
          _ = ∑ s : ShapeSampleIndex d n,
              gradeEvaluationRealRow
                (oversampledTorusGridPoint (gradeCommonBandwidth (d := d) (n := n)) a.1) s ^ 2 := by
                apply Finset.sum_congr rfl
                intro s hs
                rw [jointGradeCommonRowVector_coordinate]
                simp [hb]
          _ ≤ _ := gradeEvaluationRealRow_sq_sum_le
            (oversampledTorusGridPoint (gradeCommonBandwidth (d := d) (n := n)) a.1)

@[simp] theorem decodeJointEuclideanCLM_basis_apply {d n : ℕ}
    (i : Fin (JointSampleDimension d n)) (a : ShapeSampleIndex d n) :
    decodeJointEuclideanCLM (d := d) (n := n)
      (EuclideanSpace.basisFun (Fin (JointSampleDimension d n)) ℝ i) a =
      if jointSampleIndexEquivFin d n a = i then 1 else 0 := by
  simp [decodeJointEuclideanCLM, decodeJointEuclideanLinearMap,
    EuclideanSpace.basisFun_apply, Pi.single_apply]

end BrownianSharp.AlignmentPaperLpJointDvp
