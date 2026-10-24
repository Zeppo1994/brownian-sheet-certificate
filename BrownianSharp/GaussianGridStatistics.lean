import BrownianSharp.GaussianRows
import BrownianSharp.Statistics
import BrownianSharp.PowerVariance
import Mathlib.Probability.Moments.MGFAnalytic

/-!
Actual marginal Gaussian moments and integrability for the finite-grid power
statistic. Row normalization is deterministic: the sum of squared entries is
one. No Gaussian moment identity is supplied as a hypothesis.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp

abbrev productStandardGaussian (κ : Type*) [Fintype κ] : Measure (κ → ℝ) :=
  Measure.pi fun _ : κ => gaussianReal 0 1

def standardGaussianMoment (p : ℕ) : ℝ := ∫ x : ℝ, x ^ p ∂gaussianReal 0 1

theorem productStandardGaussian_coordinates_independent (κ : Type*) [Fintype κ] :
    iIndepFun (fun i : κ => fun x : κ → ℝ => x i) (productStandardGaussian κ) := by
  exact iIndepFun_pi (fun _ => aemeasurable_id)

theorem productStandardGaussian_coordinate_law {κ : Type*} [Fintype κ] (i : κ) :
    (productStandardGaussian κ).map (fun x : κ → ℝ => x i) = gaussianReal 0 1 :=
  (measurePreserving_eval (fun _ : κ => gaussianReal 0 1) i).map_eq

theorem normalized_matrix_row_hasLaw {κ ι : Type*} [Fintype κ]
    (A : ι → κ → ℝ) (hnorm : ∀ i, ∑ k, A i k ^ 2 = 1) (i : ι) :
    HasLaw (fun x : κ → ℝ => ∑ k, A i k * x k)
      (gaussianReal 0 1) (productStandardGaussian κ) := by
  have hLaw := GaussianRows.row_law (fun k (x : κ → ℝ) => x k)
    (fun k => measurable_pi_apply k) (fun k => productStandardGaussian_coordinate_law k)
    (productStandardGaussian_coordinates_independent κ) (A i)
  rw [hnorm i] at hLaw
  refine ⟨(by fun_prop : Measurable (fun x : κ → ℝ => ∑ k, A i k * x k)).aemeasurable, ?_⟩
  convert hLaw using 1
  · rfl
  · norm_num

theorem standardGaussian_pow_integrable (p : ℕ) :
    Integrable (fun x : ℝ => x ^ p) (gaussianReal 0 1) := by
  have hzero : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 1)) := by
    rw [integrableExpSet_id_gaussianReal]
    simp
  exact integrable_pow_of_mem_interior_integrableExpSet hzero p

theorem normalized_matrix_row_power_integrable {κ ι : Type*} [Fintype κ]
    (A : ι → κ → ℝ) (hnorm : ∀ i, ∑ k, A i k ^ 2 = 1) (i : ι) (p : ℕ) :
    Integrable (fun x : κ → ℝ => (∑ k, A i k * x k) ^ p) (productStandardGaussian κ) := by
  exact (normalized_matrix_row_hasLaw A hnorm i).integrable_comp
    (standardGaussian_pow_integrable p)

theorem normalized_matrix_row_power_memLp_two {κ ι : Type*} [Fintype κ]
    (A : ι → κ → ℝ) (hnorm : ∀ i, ∑ k, A i k ^ 2 = 1) (i : ι) (p : ℕ) :
    MemLp (fun x : κ → ℝ => (∑ k, A i k * x k) ^ p) 2 (productStandardGaussian κ) := by
  apply (memLp_two_iff_integrable_sq
    (by fun_prop : Measurable (fun x : κ → ℝ => (∑ k, A i k * x k) ^ p)).aestronglyMeasurable).2
  simpa only [← pow_mul] using normalized_matrix_row_power_integrable A hnorm i (p * 2)

theorem normalized_matrix_row_power_mean {κ ι : Type*} [Fintype κ]
    (A : ι → κ → ℝ) (hnorm : ∀ i, ∑ k, A i k ^ 2 = 1) (i : ι) (p : ℕ) :
    (∫ x : κ → ℝ, (∑ k, A i k * x k) ^ p ∂productStandardGaussian κ) =
      standardGaussianMoment p := by
  exact (normalized_matrix_row_hasLaw A hnorm i).integral_comp
    (by fun_prop : Measurable (fun x : ℝ => x ^ p)).aestronglyMeasurable

/-- The normalized high-power statistic has its actual unit expectation. -/
theorem normalized_matrix_power_average_mean {κ ι : Type*}
    [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (hnorm : ∀ i, ∑ k, A i k ^ 2 = 1)
    (p : ℕ) (hM : standardGaussianMoment p ≠ 0) :
    (∫ x : κ → ℝ, normalizedPowerAverage
      (fun i x => ∑ k, A i k * x k) p (standardGaussianMoment p) x
      ∂productStandardGaussian κ) = 1 := by
  apply normalizedPowerAverage_mean _ p _ hM
  · exact fun i => normalized_matrix_row_power_integrable A hnorm i p
  · exact fun i => normalized_matrix_row_power_mean A hnorm i p

/-- Even powers give the same actual matrix statistic as the finite Lp norm. -/
theorem normalized_matrix_power_average_eq_moment {κ ι : Type*}
    [Fintype κ] [Fintype ι] [Nonempty ι]
    (A : ι → κ → ℝ) (p : ℕ) (hp : Even p) (x : κ → ℝ) :
    normalizedPowerAverage (fun i x => ∑ k, A i k * x k)
      p (standardGaussianMoment p) x =
        finiteGridMoment p A x / standardGaussianMoment p := by
  rw [finiteGridMoment_eq_raw_average_of_even p hp]
  change (∑ i, (∑ k, A i k * x k) ^ p) /
      ((Fintype.card ι : ℝ) * standardGaussianMoment p) =
    ((∑ i, (∑ k, A i k * x k) ^ p) / (Fintype.card ι : ℝ)) / standardGaussianMoment p
  ring

end BrownianSharp
