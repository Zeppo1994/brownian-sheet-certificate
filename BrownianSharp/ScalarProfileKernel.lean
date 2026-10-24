import BrownianSharp.FejerMixture
import BrownianSharp.ScalarKernelBudget

/-! Uniform L1 bounds for actual continuous Fourier kernels sampled from a
compact C2 profile. The Fejer reconstruction proves the operator bound without
assuming a multiplier theorem. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp.ScalarKernelL1
open AddCircle

theorem norm_integral_le_of_profile_coefficients
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) {M R : ℝ}
    (hM : 0 ≤ M) (hDeriv : ∀ y, |iteratedDeriv 2 f y| ≤ M)
    (hR : 0 ≤ R) (hSupport : ∀ y, R < |y| → f y = 0)
    (N : ℕ) (hN : 1 ≤ N) (F : C(UnitAddCircle, ℂ))
    (hF : ∀ k : ℤ, fourierCoeff F k =
      (scalarProfileSample f N k.natAbs : ℂ)) :
    (∫ x : UnitAddCircle, ‖F x‖ ∂AddCircle.haarAddCircle) ≤
      2 * M * (R + 3)^2 := by
  obtain ⟨J, hJlo, hJhi⟩ := exists_scalarProfile_cutoffIndex hR N hN
  let c : ℕ → ℂ := fun k => (scalarProfileSample f N k : ℂ)
  have htail : ∀ k, J ≤ k → c k = 0 := by
    intro k hk
    have hJk : (J : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    simp only [c, Complex.ofReal_eq_zero]
    exact scalarProfileSample_eq_zero_of_outside hSupport N (by omega)
      (lt_of_lt_of_le hJlo hJk)
  have heq : F = fejerMixture J c := continuous_eq_fejerMixture F J c hF htail
  rw [heq]
  have hweight (j : ℕ) : ‖secondWeight c j‖ = |scalarProfileSecondWeight f N j| := by
    have he : secondWeight c j = (scalarProfileSecondWeight f N j : ℂ) := by
      simp [secondWeight, scalarProfileSecondWeight, c]
    rw [he, Complex.norm_real, Real.norm_eq_abs]
  calc
    _ ≤ ∑ j ∈ Finset.range J, ‖secondWeight c j‖ :=
      fejerMixture_norm_integral_le J c
    _ = ∑ j ∈ Finset.range J, |scalarProfileSecondWeight f N j| := by simp_rw [hweight]
    _ ≤ 2*M*(R+3)^2 := sum_abs_scalarProfileSecondWeight_le_radius hf hM hDeriv
      hR N J (by omega) (by nlinarith [(Nat.cast_nonneg N : (0:ℝ) ≤ (N:ℝ))])

/-- One constant bounds every scaled actual Fourier kernel of a fixed compact
C2 profile. This statement contains no analytic multiplier premise. -/
theorem exists_uniform_norm_integral_bound
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ), 1 ≤ N →
      ∀ F : C(UnitAddCircle, ℂ),
        (∀ k : ℤ, fourierCoeff F k = (scalarProfileSample f N k.natAbs : ℂ)) →
        (∫ x : UnitAddCircle, ‖F x‖ ∂AddCircle.haarAddCircle) ≤ C := by
  obtain ⟨M,hM,hDeriv⟩ := exists_iteratedDeriv_two_bound_of_compactSupport hf hfc
  obtain ⟨R,hR,hSupport⟩ := exists_radius_of_compactSupport hfc
  refine ⟨2*M*(R+3)^2, by positivity, ?_⟩
  intro N hN F hF
  exact norm_integral_le_of_profile_coefficients hf hM hDeriv hR hSupport N hN F hF

end BrownianSharp.ScalarKernelL1
