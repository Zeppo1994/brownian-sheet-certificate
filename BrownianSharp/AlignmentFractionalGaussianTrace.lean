import BrownianSharp.SmoothCoefficientEvents
import BrownianSharp.GaussianRows
import Mathlib.Probability.Moments.Covariance
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal RealInnerProductSpace
namespace BrownianSharp

/-- The Gaussian synthesis associated to a finite family in a real Hilbert space. -/
def fractionalGaussianSynthesis {κ H : Type*} [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : κ → H) (x : κ → ℝ) : H := ∑ i, x i • v i

/-- The squared norm observable associated to finite Gaussian synthesis. -/
def fractionalGaussianSynthesisEnergy {κ H : Type*} [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : κ → H) (x : κ → ℝ) : ℝ :=
  ‖fractionalGaussianSynthesis v x‖ ^ 2

/-- The finite Gaussian synthesis energy is integrable under the product
standard-Gaussian law. -/
theorem fractionalGaussianSynthesisEnergy_integrable
    {κ H : Type*} [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (v : κ → H) :
    Integrable (fractionalGaussianSynthesisEnergy v) (productStandardGaussian κ) := by
  let μ : Measure (κ → ℝ) := productStandardGaussian κ
  let G : κ → (κ → ℝ) → ℝ := fun i x => x i
  have hGgauss : ∀ i, HasGaussianLaw (G i) μ := by
    intro i
    apply GaussianRows.coordinate_gaussian
      (G := G) (hG := fun i => measurable_pi_apply i)
    · intro j
      dsimp [G, μ]
      exact productStandardGaussian_coordinate_law j
  have hcoordL2 : ∀ i, MemLp (G i) 2 μ := fun i => (hGgauss i).memLp_two
  have htermInt : ∀ i j, Integrable (fun x : κ → ℝ => G i x * G j x) μ := by
    intro i j
    exact (hcoordL2 i).integrable_mul (hcoordL2 j)
  have hpoint : ∀ x : κ → ℝ,
      fractionalGaussianSynthesisEnergy v x =
        ∑ i : κ, ∑ j : κ, inner ℝ (v i) (v j) * (G i x * G j x) := by
    intro x
    rw [fractionalGaussianSynthesisEnergy, ← real_inner_self_eq_norm_sq]
    change inner ℝ (∑ i, x i • v i) (∑ j, x j • v j) = _
    simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [G]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm (v j) (v i)]
    simp only [starRingEnd_apply, star_trivial]
    ring
  rw [show (fractionalGaussianSynthesisEnergy v) = fun x =>
    ∑ i : κ, ∑ j : κ, inner ℝ (v i) (v j) * (G i x * G j x) by
      funext x
      exact hpoint x]
  apply integrable_finsetSum Finset.univ
  intro i hi
  apply integrable_finsetSum Finset.univ
  intro j hj
  exact (htermInt i j).const_mul _

/-- The squared norm of the Hilbert-valued finite Gaussian synthesis has the exact
trace expectation, with no orthogonality assumption on the vectors. -/
theorem fractionalGaussianSynthesis_trace_integral
    {κ H : Type*} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (v : κ → H) :
    ∫ x : κ → ℝ, ‖fractionalGaussianSynthesis v x‖ ^ 2
      ∂productStandardGaussian κ = ∑ i, ‖v i‖ ^ 2 := by
  let μ : Measure (κ → ℝ) := productStandardGaussian κ
  let G : κ → (κ → ℝ) → ℝ := fun i x => x i
  have hInd : iIndepFun G μ := by
    dsimp [G, μ, productStandardGaussian]
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have hGmeas : ∀ i, Measurable (G i) := fun i => measurable_pi_apply i
  have hGlaw : ∀ i, μ.map (G i) = gaussianReal 0 1 := by
    intro i
    dsimp [G, μ]
    exact productStandardGaussian_coordinate_law i
  have hGgauss : ∀ i, HasGaussianLaw (G i) μ :=
    fun i => GaussianRows.coordinate_gaussian G hGmeas hGlaw i
  have hmean : ∀ i, ∫ x : κ → ℝ, G i x ∂μ = 0 := by
    intro i
    exact GaussianRows.coordinate_mean G hGmeas hGlaw i
  have hsqint : ∀ i, Integrable (fun x : κ → ℝ => (G i x) ^ 2) μ := by
    intro i
    exact (hGgauss i).memLp_two.integrable_sq
  have hcoordL2 : ∀ i, MemLp (G i) 2 μ := by
    intro i
    exact (hGgauss i).memLp_two
  have hdiag : ∀ i, ∫ x : κ → ℝ, (G i x) ^ 2 ∂μ = 1 := by
    intro i
    have heq := variance_of_integral_eq_zero (hGgauss i).aemeasurable (hmean i)
    rw [GaussianRows.coordinate_variance G hGmeas hGlaw i] at heq
    simpa [G] using heq.symm
  have hcross : ∀ i j, i ≠ j →
      ∫ x : κ → ℝ, G i x * G j x ∂μ = 0 := by
    intro i j hij
    have hind := hInd.indepFun hij
    rw [hind.integral_fun_mul_eq_mul_integral (hcoordL2 i).aestronglyMeasurable
      (hcoordL2 j).aestronglyMeasurable, hmean i, hmean j]
    ring
  have htermInt : ∀ i j, Integrable (fun x : κ → ℝ => G i x * G j x) μ := by
    intro i j
    exact (hcoordL2 i).integrable_mul (hcoordL2 j)
  have hpoint : ∀ x : κ → ℝ,
      ‖fractionalGaussianSynthesis v x‖ ^ 2 =
        ∑ i : κ, ∑ j : κ, inner ℝ (v i) (v j) * (G i x * G j x) := by
    intro x
    rw [← real_inner_self_eq_norm_sq]
    change inner ℝ (∑ i, x i • v i) (∑ j, x j • v j) = _
    simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [G]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [real_inner_comm (v j) (v i)]
    simp only [starRingEnd_apply, star_trivial]
    ring
  have hint : Integrable (fun x : κ → ℝ => ‖fractionalGaussianSynthesis v x‖ ^ 2) μ := by
    rw [show (fun x : κ → ℝ => ‖fractionalGaussianSynthesis v x‖ ^ 2) =
      fun x => ∑ i : κ, ∑ j : κ, inner ℝ (v i) (v j) * (G i x * G j x) by
        funext x
        exact hpoint x]
    apply integrable_finsetSum Finset.univ
    intro i hi
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact (htermInt i j).const_mul (inner ℝ (v i) (v j))
  rw [show productStandardGaussian κ = μ by rfl]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_finsetSum Finset.univ (fun i hi => by
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact (htermInt i j).const_mul (inner ℝ (v i) (v j)))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j hj => (htermInt i j).const_mul _)]
  rw [Finset.sum_eq_single i]
  · rw [show (fun x : κ → ℝ => inner ℝ (v i) (v i) * (G i x * G i x)) =
      fun x => ‖v i‖ ^ 2 * (G i x) ^ 2 by
        funext x
        rw [real_inner_self_eq_norm_sq]
        ring]
    rw [integral_const_mul, hdiag i]
    ring
  · intro j _ hij
    rw [integral_const_mul, hcross i j hij.symm]
    ring
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- Markov confinement for a finite Gaussian Hilbert synthesis. The retained
mass is at least one half in the ball of radius `sqrt (2 * (1 + trace))`;
the trace identity is exact and allows overlaps among the vectors. -/
theorem fractionalGaussianSynthesis_cutoff_mass
    {κ H : Type*} [Fintype κ] [DecidableEq κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (v : κ → H) :
    (1 / 2 : ℝ≥0∞) ≤
      (productStandardGaussian κ)
        {x | fractionalGaussianSynthesisEnergy v x ≤
          2 * (1 + ∑ i, ‖v i‖ ^ 2)} := by
  let E : (κ → ℝ) → ℝ := fractionalGaussianSynthesisEnergy v
  let μ : Measure (κ → ℝ) := productStandardGaussian κ
  have hcontS : Continuous (fractionalGaussianSynthesis v) := by
    unfold fractionalGaussianSynthesis
    apply continuous_finsetSum
    intro i hi
    exact (continuous_apply i).smul continuous_const
  have hmeas : Measurable E := by
    dsimp [E, fractionalGaussianSynthesisEnergy]
    exact ((continuous_norm.comp hcontS).pow 2).measurable
  have hint : Integrable E μ := by
    dsimp [E, μ, fractionalGaussianSynthesisEnergy]
    exact fractionalGaussianSynthesisEnergy_integrable v
  have hpos : ∀ x, 0 ≤ E x := by
    intro x
    dsimp [E, fractionalGaussianSynthesisEnergy]
    positivity
  have htrace : 0 ≤ ∑ i, ‖v i‖ ^ 2 := by positivity
  have hM : 0 < 1 + ∑ i, ‖v i‖ ^ 2 := by linarith
  have hmean : ∫ x, E x ∂μ ≤ 1 + ∑ i, ‖v i‖ ^ 2 := by
    rw [show E = fractionalGaussianSynthesisEnergy v by rfl]
    dsimp [fractionalGaussianSynthesisEnergy]
    rw [fractionalGaussianSynthesis_trace_integral v]
    linarith
  simpa [E, μ] using
    (gaussian_nonneg_energy_cutoff_mass μ E hmeas hint hpos hM hmean)

end BrownianSharp
