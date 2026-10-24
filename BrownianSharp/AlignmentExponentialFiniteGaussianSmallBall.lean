import BrownianSharp.AlignmentGaussianFiniteFeature
import BrownianSharp.AlignmentExponentialDiagonalDilation
import BrownianSharp.SmoothCoefficientEvents
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentExponentialFiniteGaussianSmallBall

open AlignmentGaussianFiniteFeature AlignmentExponentialDiagonalDilation

/-- Exact intertwining of diagonal coefficient dilation and feature scaling. -/
theorem finiteGaussianFeaturePath_diagonal_scale
    {α ι : Type*} [TopologicalSpace α] [CompactSpace α]
    [Fintype ι] (v : ι → C(α,ℝ)) (a : ι → ℝ) (z : ι → ℝ) :
    finiteGaussianFeaturePath v (fun i => a i * z i) =
      finiteGaussianFeaturePath (fun i => a i • v i) z := by
  ext x
  simp only [finiteGaussianFeaturePath_apply]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ContinuousMap.smul_apply, smul_eq_mul]
  ring

/-- A half-mass confinement event for a coordinatewise contracted finite
Gaussian feature field transfers to the original field with the diagonal
Gaussian volume factor. -/
theorem finiteGaussianFeaturePath_diagonal_half_mass
    {α ι : Type*} [TopologicalSpace α] [CompactSpace α]
    [Fintype ι] (v : ι → C(α,ℝ)) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1) {ρ : ℝ}
    (hhalf : (1 / 2 : ℝ≥0∞) ≤
      (BrownianSharp.productStandardGaussian ι)
        {z | ‖finiteGaussianFeaturePath (fun i => a i • v i) z‖ ≤ ρ}) :
    ENNReal.ofReal (∏ i, a i) * (1 / 2 : ℝ≥0∞) ≤
      (BrownianSharp.productStandardGaussian ι)
        {z | ‖finiteGaussianFeaturePath v z‖ ≤ ρ} := by
  let μ : Measure (ι → ℝ) := BrownianSharp.productStandardGaussian ι
  let F : (ι → ℝ) → C(α,ℝ) := finiteGaussianFeaturePath v
  let G : (ι → ℝ) → C(α,ℝ) := finiteGaussianFeaturePath (fun i => a i • v i)
  let D : (ι → ℝ) → (ι → ℝ) := fun z i => a i * z i
  let S : Set (ι → ℝ) := {z | ‖F z‖ ≤ ρ}
  let T : Set (ι → ℝ) := {z | ‖G z‖ ≤ ρ}
  have hscale (z : ι → ℝ) : F (D z) = G z := by
    exact finiteGaussianFeaturePath_diagonal_scale v a z
  have hS : MeasurableSet S := by
    apply measurableSet_le
    · exact (continuous_norm.comp (finiteGaussianFeaturePath_continuous v)).measurable
    · exact measurable_const
  have hpre : D ⁻¹' S = T := by
    ext z
    change ‖F (D z)‖ ≤ ρ ↔ ‖G z‖ ≤ ρ
    rw [hscale z]
  have hdil := productGaussian_diagonal_dilation_preimage_ge a ha ha1 hS
  change μ S ≥ ENNReal.ofReal (∏ i, a i) * μ (D ⁻¹' S) at hdil
  rw [hpre] at hdil
  change ENNReal.ofReal (∏ i, a i) * (1 / 2 : ℝ≥0∞) ≤ μ S
  calc
    ENNReal.ofReal (∏ i, a i) * (1 / 2 : ℝ≥0∞) ≤
        ENNReal.ofReal (∏ i, a i) * μ T :=
      mul_le_mul_right hhalf _
    _ ≤ μ S := hdil

/-- Markov's inequality followed by diagonal Gaussian dilation gives a
confidence bound for the unscaled finite feature field from an expectation
bound on its scaled version. -/
theorem finiteGaussianFeaturePath_smallball_of_scaled_mean
    {α ι : Type*} [TopologicalSpace α] [CompactSpace α]
    [Fintype ι] (v : ι → C(α,ℝ)) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1) {M : ℝ} (hM : 0 < M)
    (hint : Integrable
      (fun z : ι → ℝ => ‖finiteGaussianFeaturePath (fun i => a i • v i) z‖)
      (BrownianSharp.productStandardGaussian ι))
    (hmean : (∫ z : ι → ℝ,
      ‖finiteGaussianFeaturePath (fun i => a i • v i) z‖
        ∂BrownianSharp.productStandardGaussian ι) ≤ M) :
    ENNReal.ofReal (∏ i, a i) * (1 / 2 : ℝ≥0∞) ≤
      (BrownianSharp.productStandardGaussian ι)
        {z | ‖finiteGaussianFeaturePath v z‖ ≤ 2 * M} := by
  let μ : Measure (ι → ℝ) := BrownianSharp.productStandardGaussian ι
  let G : (ι → ℝ) → C(α,ℝ) := finiteGaussianFeaturePath (fun i => a i • v i)
  let E : (ι → ℝ) → ℝ := fun z => ‖G z‖
  have hmeas : Measurable E := by
    exact (continuous_norm.comp (finiteGaussianFeaturePath_continuous
      (fun i => a i • v i))).measurable
  have hpos : ∀ z, 0 ≤ E z := fun z => norm_nonneg _
  have hhalf : (1 / 2 : ℝ≥0∞) ≤ μ {z | E z ≤ 2 * M} :=
    gaussian_nonneg_energy_cutoff_mass μ E hmeas hint hpos hM hmean
  have hhalf' : (1 / 2 : ℝ≥0∞) ≤ μ
      {z | ‖finiteGaussianFeaturePath (fun i => a i • v i) z‖ ≤ 2*M} := by
    simpa [E, G] using hhalf
  have htrans := finiteGaussianFeaturePath_diagonal_half_mass v a ha ha1 hhalf'
  simpa [μ] using htrans

end BrownianSharp.AlignmentExponentialFiniteGaussianSmallBall
