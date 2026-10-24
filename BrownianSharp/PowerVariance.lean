import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
Exact finite-grid moment variance bookkeeping. The Gaussian Hermite formula
and deterministic prefix estimates are separate inputs to the application;
this module supplies the actual variance identity and its pair-sum reduction.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BrownianSharp

noncomputable def normalizedPowerAverage {Ω ι : Type*} [Fintype ι]
    (Z : ι → Ω → ℝ) (p : ℕ) (M : ℝ) (ω : Ω) : ℝ :=
  (∑ i, Z i ω ^ p) / ((Fintype.card ι : ℝ) * M)

/-- The actual variance of a finite power average is the normalized sum of
all pair covariances; diagonal pairs are retained. -/
theorem normalizedPowerAverage_variance
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsFiniteMeasure P]
    (Z : ι → Ω → ℝ) (p : ℕ) (M : ℝ)
    (hLp : ∀ i, MemLp (fun ω => Z i ω ^ p) 2 P) :
    ProbabilityTheory.variance (normalizedPowerAverage Z p M) P =
      ((Fintype.card ι : ℝ) * M)⁻¹ ^ 2 *
        ∑ i, ∑ j, cov[fun ω => Z i ω ^ p, fun ω => Z j ω ^ p; P] := by
  have heq : normalizedPowerAverage Z p M =
      fun ω => (((Fintype.card ι : ℝ) * M)⁻¹) * (∑ i, Z i ω ^ p) := by
    funext ω
    simp [normalizedPowerAverage, div_eq_mul_inv, mul_comm]
  rw [heq, variance_const_mul, variance_fun_sum hLp]

/-- A normalized pair-covariance bound passes directly to the variance of
the actual random statistic, with all cardinality factors checked. -/
theorem normalizedPowerAverage_variance_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {P : Measure Ω} [IsFiniteMeasure P]
    (Z : ι → Ω → ℝ) (p : ℕ) (M : ℝ) (hM : 0 < M)
    (hLp : ∀ i, MemLp (fun ω => Z i ω ^ p) 2 P)
    (K : ι → ι → ℝ)
    (hK : ∀ i j,
      cov[fun ω => Z i ω ^ p, fun ω => Z j ω ^ p; P] / M ^ 2 ≤ K i j) :
    ProbabilityTheory.variance (normalizedPowerAverage Z p M) P ≤
      (Fintype.card ι : ℝ)⁻¹ ^ 2 * ∑ i, ∑ j, K i j := by
  rw [normalizedPowerAverage_variance Z p M hLp]
  have hsum : (∑ i, ∑ j,
      cov[fun ω => Z i ω ^ p, fun ω => Z j ω ^ p; P]) ≤
      M ^ 2 * (∑ i, ∑ j, K i j) := by
    simp_rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have h := (div_le_iff₀ (sq_pos_of_pos hM)).mp (hK i j)
    simpa [mul_comm] using h
  have hfactor : 0 ≤ (((Fintype.card ι : ℝ) * M)⁻¹) ^ 2 := sq_nonneg _
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  have hfactorEq : (((Fintype.card ι : ℝ) * M)⁻¹) ^ 2 * M ^ 2 =
      (Fintype.card ι : ℝ)⁻¹ ^ 2 := by
    field_simp
  calc
    _ ≤ (((Fintype.card ι : ℝ) * M)⁻¹) ^ 2 *
        (M ^ 2 * (∑ i, ∑ j, K i j)) :=
      mul_le_mul_of_nonneg_left hsum hfactor
    _ = _ := by rw [← mul_assoc, hfactorEq]

/-- If each marginal p-th moment is M, the normalized statistic has mean
one. Only integrability of the displayed powers is assumed. -/
theorem normalizedPowerAverage_mean
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {P : Measure Ω}
    (Z : ι → Ω → ℝ) (p : ℕ) (M : ℝ) (hM : M ≠ 0)
    (hInt : ∀ i, Integrable (fun ω => Z i ω ^ p) P)
    (hMoment : ∀ i, ∫ ω, Z i ω ^ p ∂P = M) :
    (∫ ω, normalizedPowerAverage Z p M ω ∂P) = 1 := by
  unfold normalizedPowerAverage
  rw [integral_div, integral_finsetSum _ (fun i _ => hInt i)]
  simp_rw [hMoment]
  have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
  simp [hcard, hM]

end BrownianSharp
