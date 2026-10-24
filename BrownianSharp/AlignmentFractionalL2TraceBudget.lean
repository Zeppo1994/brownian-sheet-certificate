import BrownianSharp.AlignmentFractionalL2Schur
import BrownianSharp.AlignmentFractionalPolynomialBands
import BrownianSharp.AlignmentNestedProjectionBasis
import BrownianSharp.AlignmentFractionalSheetMvNGram
import BrownianSharp.AlignmentFractionalL2OperatorSemigroup

/-! A finite orthogonal-increment trace budget for the actual fractional RL
operator. This turns the scalar integrated kernel-projection error into a
Hilbert--Schmidt bound on each finite source increment. -/

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace BoundedContinuousFunction

namespace BrownianSharp.AlignmentFractionalL2TraceBudget

open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentFractionalKernel
open BrownianSharp.AlignmentFractionalSemigroup
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalPolynomialProjectionRate
open BrownianSharp.AlignmentFractionalPolynomialBands
open BrownianSharp.AlignmentNestedProjectionBasis
open BrownianSharp.AlignmentFractionalSheetMvNGram

abbrev SourceL2 := AlignmentFractionalL2.UnitL2

private theorem clipUnit_of_mem (x : ℝ) (hx : x ∈ UnitInterval) : clipUnit x = ⟨x,hx⟩ := by
  rcases hx with ⟨hx0,hx1⟩
  apply Subtype.ext
  simp [clipUnit, max_eq_right hx0, min_eq_right hx1]

private theorem profileToL2_norm_sq (f : C(UnitInterval,ℝ)) :
    ‖profileToL2 f‖^2 =
      ∫ x, (f (clipUnit x))^2 ∂(volume.restrict UnitInterval) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [profileToL2_coe f] with x hx
  simp [hx, pow_two]

theorem increment_output_trace_le_kernel_residual
    {α : ℝ} (hα : 1/2 < α) {q n : ℕ} (hn : 1 ≤ n)
    (hC : ℝ) (hCpos : 0 < hC)
    (hres : ∀ t : ℝ, (ht0 : 0 ≤ t) → (ht1 : t ≤ 1) →
      ‖kernelVector α t hα ht0 ht1 -
        polynomialProjection q n (kernelVector α t hα ht0 ht1)‖^2 ≤
          hC * ((2:ℝ)^(-(2*α-1)))^n) :
    (∑ i : Fin (Module.finrank ℝ ↥(increment (piecewisePolynomials q) n)),
      ‖AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2 α hα
        (((incrementBasis (piecewisePolynomials q) n) i : SourceL2))‖^2) ≤
      hC * ((2:ℝ)^(-(2*α-1)))^n := by
  classical
  let U := piecewisePolynomials q
  let V := increment U n
  let b := incrementBasis U n
  let μ : Measure ℝ := volume.restrict UnitInterval
  let K : UnitInterval → SourceL2 := fun t => kernelVector α t.1 hα t.2.1 t.2.2
  let R : ℝ → ℝ := fun t =>
    ‖kernelVector α (clipUnit t).1 hα (clipUnit t).2.1 (clipUnit t).2.2 -
      polynomialProjection q n
        (kernelVector α (clipUnit t).1 hα (clipUnit t).2.1 (clipUnit t).2.2)‖^2
  have hpoint : ∀ t : UnitInterval,
      (∑ i : Fin (Module.finrank ℝ ↥V),
        (fractionalRL α hα (b i : SourceL2) t)^2) ≤ R t := by
    intro t
    have horth : Orthonormal ℝ (fun i : Fin (Module.finrank ℝ ↥V) => (b i : SourceL2)) := by
      constructor
      · intro i
        change ‖b i‖ = 1
        exact b.orthonormal.1 i
      · intro i j hij
        change inner ℝ (b i) (b j) = 0
        exact b.orthonormal.2 hij
    let y := K t - polynomialProjection q n (K t)
    have hbessel := horth.sum_inner_products_le (s := Finset.univ) y
    have hterm (i : Fin (Module.finrank ℝ ↥V)) :
        inner ℝ (b i : SourceL2) y = fractionalRL α hα (b i : SourceL2) t := by
      have hiV : (b i : SourceL2) ∈ V := (b i).property
      have hiorth : (b i : SourceL2) ∈ (U n)ᗮ := hiV.2
      have hzero : inner ℝ (b i : SourceL2) (polynomialProjection q n (K t)) = 0 :=
        (Submodule.mem_orthogonal' (U n) (b i : SourceL2)).mp hiorth _
          ((U n).starProjection_apply_mem (K t))
      have hpair : inner ℝ (b i : SourceL2) (K t) =
          fractionalRL α hα (b i : SourceL2) t := by
        rw [real_inner_comm]
        exact kernelVector_inner_eq_fractionalRL α hα (b i : SourceL2) t.1 t.2.1 t.2.2
      dsimp [y]
      rw [inner_sub_right, hzero, sub_zero]
      exact hpair
    have hnorm := hbessel
    have hsum : (∑ i : Fin (Module.finrank ℝ ↥V),
        (fractionalRL α hα (b i : SourceL2) t)^2) ≤ ‖y‖^2 := by
      have h' : ∑ i : Fin (Module.finrank ℝ ↥V),
          ‖inner ℝ (b i : SourceL2) y‖^2 ≤ ‖y‖^2 := by
        simpa using hbessel
      simpa [hterm, Real.norm_eq_abs, sq_abs] using h'
    simpa [R,y,K,clipUnit_of_mem] using hsum
  have hRcont : Continuous R := by
    have hKcont : Continuous (fun t : ℝ =>
        kernelVector α (clipUnit t).1 hα (clipUnit t).2.1 (clipUnit t).2.2) := by
      have hc := (translatedUnitKernelFamily α hα).continuous.comp clipUnit_continuous
      apply hc.congr
      intro t
      exact translatedUnitKernelFamily_eq_kernelVector α _ hα
        (clipUnit t).2.1 (clipUnit t).2.2
    exact (continuous_norm.comp (hKcont.sub
      ((polynomialProjection q n).continuous.comp hKcont))).pow 2
  have hRbound : ∀ t, R t ≤ hC * ((2:ℝ)^(-(2*α-1)))^n := by
    intro t
    exact hres (clipUnit t).1 (clipUnit t).2.1 (clipUnit t).2.2
  have hRint : Integrable R μ := by
    apply Integrable.of_bound hRcont.aestronglyMeasurable _
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hRbound t
  have hsumInt (i : Fin (Module.finrank ℝ ↥V)) :
      Integrable (fun t : ℝ => (fractionalRL α hα (b i : SourceL2)
        (clipUnit t))^2) μ := by
    let f := fractionalRL α hα (b i : SourceL2)
    have hcont : Continuous (fun t : ℝ => (f (clipUnit t))^2) :=
      (f.continuous.comp clipUnit_continuous).pow 2
    exact Integrable.of_bound hcont.aestronglyMeasurable (‖f‖^2)
      (Filter.Eventually.of_forall fun t => by
        calc
          ‖f (clipUnit t)^2‖ = |f (clipUnit t)|^2 := by simp [Real.norm_eq_abs]
          _ ≤ ‖f‖^2 := by
            exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2
              (by simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f (clipUnit t)))
  have hpoint' : ∀ᵐ t ∂μ,
      (∑ i : Fin (Module.finrank ℝ ↥V),
        (fractionalRL α hα (b i : SourceL2) (clipUnit t))^2) ≤ R t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht' : t ∈ UnitInterval := by simpa [UnitInterval] using ht
    have hh := hpoint ⟨t, ht'⟩
    have hclip := clipUnit_of_mem t ht'
    simpa [R, hclip] using hh
  have hsumInt' : Integrable (fun t : ℝ =>
      ∑ i : Fin (Module.finrank ℝ ↥V),
        (fractionalRL α hα (b i : SourceL2) (clipUnit t))^2) μ :=
    integrable_finset_sum Finset.univ (fun i hi => hsumInt i)
  have hsumEq : (∫ t, (∑ i : Fin (Module.finrank ℝ ↥V),
      (fractionalRL α hα (b i : SourceL2) (clipUnit t))^2) ∂μ) =
      ∑ i : Fin (Module.finrank ℝ ↥V),
        (∫ t, (fractionalRL α hα (b i : SourceL2) (clipUnit t))^2 ∂μ) := by
    rw [integral_finset_sum Finset.univ (fun i hi => hsumInt i)]
  have hsumle : (∫ t, (∑ i : Fin (Module.finrank ℝ ↥V),
      (fractionalRL α hα (b i : SourceL2) (clipUnit t))^2) ∂μ) ≤
      ∫ t, R t ∂μ := integral_mono_ae hsumInt' hRint hpoint'
  have hRle : (∫ t, R t ∂μ) ≤ hC * ((2:ℝ)^(-(2*α-1)))^n := by
    calc
      _ ≤ ∫ _ : ℝ, (hC * ((2:ℝ)^(-(2*α-1)))^n) ∂μ :=
        integral_mono_ae hRint (integrable_const _) (Filter.Eventually.of_forall hRbound)
      _ = hC * ((2:ℝ)^(-(2*α-1)))^n := by simp [μ, UnitInterval, Real.volume_Icc]
  have hnormsum : ∑ i : Fin (Module.finrank ℝ ↥V),
      ‖AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2 α hα
        (b i : SourceL2)‖^2 =
      ∑ i : Fin (Module.finrank ℝ ↥V),
        (∫ t, (fractionalRL α hα (b i : SourceL2) (clipUnit t))^2 ∂μ) := by
    apply Finset.sum_congr rfl
    intro i hi
    change ‖profileToL2 (fractionalRL α hα (b i : SourceL2))‖^2 = _
    rw [profileToL2_norm_sq]
  rw [hnormsum, ← hsumEq]
  exact hsumle.trans hRle

/-- An actual uniform squared Hilbert--Schmidt budget for every polynomial
orthogonal increment of the scalar RL operator. -/
theorem exists_increment_output_trace_bound {α : ℝ} (hα : 1/2 < α) :
    ∃ q : ℕ, ∃ C : ℝ, 0 < q ∧ 0 < C ∧
      ∀ n : ℕ, 1 ≤ n →
        (∑ i : Fin (Module.finrank ℝ ↥(increment (piecewisePolynomials q) n)),
          ‖AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2 α hα
            (((incrementBasis (piecewisePolynomials q) n) i : SourceL2))‖^2) ≤
          C * ((2:ℝ)^(-(2*α-1)))^n := by
  obtain ⟨q,C,hq,hC,hres⟩ :=
    exists_degree_causalKernel_polynomialProjection_dyadic_rate hα
  refine ⟨q,C,hq,hC,?_⟩
  intro n hn
  apply increment_output_trace_le_kernel_residual hα hn C hC
  intro t ht0 ht1
  have h := hres n hn t ht0 ht1
  rw [inverse_dyadic_rpow (2*α-1) n] at h
  simpa [causalKernelUnitVector, kernelVector, sub_eq_add_neg] using h

/-- Summing the actual grade traces gives the finite-window Hilbert--Schmidt
budget for the orthogonal source tail. -/
theorem exists_window_output_trace_bound {α : ℝ} (hα : 1/2 < α) :
    ∃ q : ℕ, ∃ C : ℝ, 0 < q ∧ 0 < C ∧
      ∀ N M : ℕ, 1 ≤ N →
        (∑ n ∈ Finset.Ico N M,
          ∑ i : Fin (Module.finrank ℝ ↥(increment (piecewisePolynomials q) n)),
            ‖AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2 α hα
              ((incrementBasis (piecewisePolynomials q) n) i : SourceL2)‖^2) ≤
          C * ∑ n ∈ Finset.Ico N M, ((2:ℝ)^(-(2*α-1)))^n := by
  obtain ⟨q,C,hq,hC,htrace⟩ := exists_increment_output_trace_bound hα
  refine ⟨q,C,hq,hC,?_⟩
  intro N M hN
  calc
    _ ≤ ∑ n ∈ Finset.Ico N M, C * ((2:ℝ)^(-(2*α-1)))^n := by
      apply Finset.sum_le_sum
      intro n hn
      have hmem := Finset.mem_Ico.mp hn
      exact htrace n (by omega)
    _ = C * ∑ n ∈ Finset.Ico N M, ((2:ℝ)^(-(2*α-1)))^n := by
      rw [Finset.mul_sum]

/-- The continuous-profile embedding into the probability-space `L²` has
operator norm at most one. -/
private theorem profileToL2_norm_le_one : ‖profileToL2‖ ≤ 1 := by
  let μ : Measure ℝ := volume.restrict UnitInterval
  letI : Fact (1 ≤ (2:ENNReal)) := ⟨by norm_num⟩
  have hLp : ‖(BoundedContinuousFunction.toLp (E := ℝ) (𝕜 := ℝ) (p := 2) μ)‖ ≤ 1 := by
    have hmass : μ Set.univ = 1 := by simp [μ, UnitInterval, Real.volume_Icc]
    have hmass' : (measureUnivNNReal μ : ℝ) = 1 := by
      rw [measureUnivNNReal, hmass]
      norm_num
    calc
      _ ≤ (measureUnivNNReal μ : ℝ) ^ (2:ENNReal).toReal⁻¹ :=
        BoundedContinuousFunction.toLp_norm_le μ
      _ = 1 := by rw [hmass']; norm_num
  have hExt : ‖AlignmentFractionalL2.extendUnitProfile‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    intro f
    change ‖(AlignmentFractionalL2.extendUnitProfile f : ℝ →ᵇ ℝ)‖ ≤ 1 * ‖f‖
    simp only [one_mul]
    rw [BoundedContinuousFunction.norm_le (norm_nonneg f)]
    intro x
    exact f.norm_coe_le_norm (clipUnit x)
  change ‖(BoundedContinuousFunction.toLp (E := ℝ) (𝕜 := ℝ) (p := 2) μ).comp
    AlignmentFractionalL2.extendUnitProfile‖ ≤ 1
  calc
    _ ≤ ‖(BoundedContinuousFunction.toLp (E := ℝ) (𝕜 := ℝ) (p := 2) μ)‖ *
        ‖AlignmentFractionalL2.extendUnitProfile‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 := by nlinarith [norm_nonneg (BoundedContinuousFunction.toLp
      (E := ℝ) (𝕜 := ℝ) (p := 2) μ), norm_nonneg AlignmentFractionalL2.extendUnitProfile]

/-- An actual source projection makes the scalar RL map into `L²` converge in
operator norm, with the rate inherited from the uniform kernel residual. -/
theorem fractionalRLOnL2_projection_error_bound {α : ℝ} (hα : 1/2 < α)
    (q n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hres : ∀ t : ℝ, (ht0 : 0 ≤ t) → (ht1 : t ≤ 1) →
      ‖kernelVector α t hα ht0 ht1 -
        polynomialProjection q n (kernelVector α t hα ht0 ht1)‖^2 ≤
          C * ((2:ℝ)^(-(2*α-1)))^n) :
    ‖AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2 α hα -
      (AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2 α hα).comp
        (polynomialProjection q n)‖ ≤ Real.sqrt (C * ((2:ℝ)^(-(2*α-1)))^n) := by
  let T := fractionalRL α hα
  let P := polynomialProjection q n
  let U := piecewisePolynomials q n
  let δ := Real.sqrt (C * ((2:ℝ)^(-(2*α-1)))^n)
  have hδ : 0 ≤ δ := Real.sqrt_nonneg _
  have hfeature : ∀ t : UnitInterval,
      ‖kernelVector α t.1 hα t.2.1 t.2.2 - P (kernelVector α t.1 hα t.2.1 t.2.2)‖ ≤ δ := by
    intro t
    have hs := hres t.1 t.2.1 t.2.2
    apply (sq_le_sq₀ (norm_nonneg _) hδ).1
    rw [Real.sq_sqrt (by positivity)]
    exact hs
  have hTerror : ‖T - T.comp P‖ ≤ δ := by
    apply ContinuousLinearMap.opNorm_le_bound _ hδ
    intro g
    apply (ContinuousMap.norm_le (T g - T (P g)) (mul_nonneg hδ (norm_nonneg g))).2
    intro t
    have hform : (T g - T (P g)) t =
        inner ℝ g (kernelVector α t.1 hα t.2.1 t.2.2 - P (kernelVector α t.1 hα t.2.1 t.2.2)) := by
      change fractionalRL α hα g t - fractionalRL α hα (P g) t = _
      rw [← kernelVector_inner_eq_fractionalRL α hα g t.1 t.2.1 t.2.2]
      rw [← kernelVector_inner_eq_fractionalRL α hα (P g) t.1 t.2.1 t.2.2]
      change inner ℝ (kernelVector α t.1 hα t.2.1 t.2.2) g -
        inner ℝ (kernelVector α t.1 hα t.2.1 t.2.2) (U.starProjection g) = _
      rw [show inner ℝ (kernelVector α t.1 hα t.2.1 t.2.2) g =
          inner ℝ g (kernelVector α t.1 hα t.2.1 t.2.2) from
            real_inner_comm g (kernelVector α t.1 hα t.2.1 t.2.2)]
      rw [show inner ℝ (kernelVector α t.1 hα t.2.1 t.2.2) (U.starProjection g) =
          inner ℝ (U.starProjection g) (kernelVector α t.1 hα t.2.1 t.2.2) from
            real_inner_comm (U.starProjection g) (kernelVector α t.1 hα t.2.1 t.2.2)]
      rw [U.inner_starProjection_left_eq_right]
      rw [inner_sub_right]
      rfl
    rw [hform, Real.norm_eq_abs]
    calc
      |inner ℝ g (kernelVector α t.1 hα t.2.1 t.2.2 -
          P (kernelVector α t.1 hα t.2.1 t.2.2))| ≤
          ‖g‖ * ‖kernelVector α t.1 hα t.2.1 t.2.2 -
            P (kernelVector α t.1 hα t.2.1 t.2.2)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖g‖ * δ := mul_le_mul_of_nonneg_left (hfeature t) (norm_nonneg _)
      _ = δ * ‖g‖ := by ring
  have hmap :
      AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2 α hα -
        (AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2 α hα).comp P =
      profileToL2.comp (T - T.comp P) := by
    ext g
    simp [AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2, T, P,
      ContinuousLinearMap.comp_apply, map_sub]
  rw [hmap]
  calc
    ‖profileToL2.comp (T - T.comp P)‖ ≤ ‖profileToL2‖ * ‖T-T.comp P‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * δ := calc
      _ ≤ 1 * ‖T-T.comp P‖ := mul_le_mul_of_nonneg_right
        profileToL2_norm_le_one (norm_nonneg (T-T.comp P))
      _ ≤ 1 * δ := by gcongr
    _ = δ := by ring

theorem exists_fractionalRLOnL2_projection_error_bound {α : ℝ} (hα : 1/2 < α) :
    ∃ q : ℕ, ∃ C : ℝ, 0 < q ∧ 0 < C ∧
      ∀ n : ℕ, 1 ≤ n →
        ‖AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2 α hα -
          (AlignmentFractionalL2OperatorSemigroup.fractionalRLOnL2 α hα).comp
            (polynomialProjection q n)‖ ≤
          Real.sqrt (C * ((2:ℝ)^(-(2*α-1)))^n) := by
  obtain ⟨q,C,hq,hC,hres⟩ :=
    exists_degree_causalKernel_polynomialProjection_dyadic_rate hα
  refine ⟨q,C,hq,hC,?_⟩
  intro n hn
  apply fractionalRLOnL2_projection_error_bound hα q n C hC.le
  intro t ht0 ht1
  have hh := hres n hn t ht0 ht1
  rw [inverse_dyadic_rpow (2*α-1) n] at hh
  simpa [causalKernelUnitVector, kernelVector, sub_eq_add_neg] using hh

end BrownianSharp.AlignmentFractionalL2TraceBudget
