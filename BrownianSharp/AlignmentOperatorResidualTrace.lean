import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace BrownianSharp.AlignmentOperatorResidualTrace

/-- A finite orthonormal family in the kernel of a candidate approximant
forces an integrated residual trace.  The pointwise Bessel bound is controlled
by the operator norm into `C(X)`, while the lower trace is supplied by an
independent lower bound on the images of the family. -/
theorem finite_orthonormal_residual_trace_bound
    {H X I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
    [BorelSpace X] [Fintype I] [DecidableEq I]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T A : H →L[ℝ] C(X,ℝ)) (e : I → H)
    (he : Orthonormal ℝ e) (hA : ∀ i, A (e i) = 0)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (henergy : (Fintype.card I : ℝ) * σ^2 ≤
      ∑ i : I, (∫ x, (T (e i) x)^2 ∂μ)) :
    (Fintype.card I : ℝ) * σ^2 ≤ ‖T-A‖^2 := by
  classical
  let E : H →L[ℝ] C(X,ℝ) := T-A
  have hpoint (x : X) : ∑ i : I, (E (e i) x)^2 ≤ ‖E‖^2 := by
    let φ : H →L[ℝ] ℝ := (ContinuousMap.evalCLM ℝ x).comp E
    have hφ : ‖φ‖ ≤ ‖E‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg E)
      intro g
      dsimp [φ]
      calc
        ‖(E g) x‖ ≤ ‖E g‖ := ContinuousMap.norm_coe_le_norm (E g) x
        _ ≤ ‖E‖ * ‖g‖ := E.le_opNorm g
    let q : H := φ.adjoint 1
    have hBessel := he.sum_inner_products_le (s := Finset.univ) q
    have hterm (i : I) : ‖⟪e i, q⟫_ℝ‖^2 = (E (e i) x)^2 := by
      have hi := ContinuousLinearMap.adjoint_inner_right φ (e i) (1:ℝ)
      change ⟪e i, q⟫_ℝ = ⟪φ (e i), (1:ℝ)⟫_ℝ at hi
      dsimp [φ] at hi
      rw [hi]
      simp [Real.inner_apply]
    have hq : ‖q‖ ≤ ‖E‖ := by
      calc
        ‖q‖ ≤ ‖φ.adjoint‖ := by
          calc
            _ ≤ ‖φ.adjoint‖ * ‖(1:ℝ)‖ := φ.adjoint.le_opNorm 1
            _ = ‖φ.adjoint‖ := by simp
        _ = ‖φ‖ := ContinuousLinearMap.adjoint.norm_map φ
        _ ≤ ‖E‖ := hφ
    have hsum : ∑ i : I, (E (e i) x)^2 ≤ ‖q‖^2 := by
      have hb := he.sum_inner_products_le (s := Finset.univ) q
      have hsum' : ∑ i : I, ‖⟪e i, q⟫_ℝ‖^2 ≤ ‖q‖^2 := by
        simpa using hb
      simpa only [hterm] using hsum'
    exact hsum.trans ((sq_le_sq₀ (norm_nonneg q) (norm_nonneg E)).2 hq)
  have hAeq (i : I) : E (e i) = T (e i) := by
    simp [E, hA i]
  have hInt (i : I) : Integrable (fun x => (E (e i) x)^2) μ := by
    apply Integrable.of_bound ((Continuous.measurable (E (e i)).continuous).pow_const 2).aestronglyMeasurable
      (‖E (e i)‖^2)
    filter_upwards with x
    have hx := ContinuousMap.norm_coe_le_norm (E (e i)) x
    have hx' : |(E (e i)) x| ≤ ‖E (e i)‖ := by
      simpa [Real.norm_eq_abs] using hx
    calc
      ‖(E (e i) x)^2‖ = |(E (e i) x)|^2 := by simp [Real.norm_eq_abs]
      _ ≤ ‖E (e i)‖^2 := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 hx'
  have hsumInt : Integrable (fun x => ∑ i : I, (E (e i) x)^2) μ := by
    exact integrable_finset_sum Finset.univ (fun i hi => hInt i)
  have hmono : ∫ x, (∑ i : I, (E (e i) x)^2) ∂μ ≤ ∫ x, (‖E‖^2:ℝ) ∂μ :=
    integral_mono_ae hsumInt (integrable_const _) (Filter.Eventually.of_forall hpoint)
  have hsumEq : (∫ x, (∑ i : I, (E (e i) x)^2) ∂μ) =
      ∑ i : I, (∫ x, (E (e i) x)^2 ∂μ) := by
    rw [integral_finset_sum Finset.univ (fun i hi => hInt i)]
  have hmass : μ Set.univ = 1 := measure_univ
  have hupper : ∑ i : I, (∫ x, (E (e i) x)^2 ∂μ) ≤ ‖E‖^2 := by
    calc
      _ = ∫ x, (∑ i : I, (E (e i) x)^2) ∂μ := hsumEq.symm
      _ ≤ ∫ x, (‖E‖^2:ℝ) ∂μ := hmono
      _ = ‖E‖^2 := by simp [hmass]
  have hlower : (Fintype.card I:ℝ)*σ^2 ≤
      ∑ i : I, (∫ x, (E (e i) x)^2 ∂μ) := by
    calc
      _ ≤ ∑ i : I, (∫ x, (T (e i) x)^2 ∂μ) := henergy
      _ = ∑ i : I, (∫ x, (E (e i) x)^2 ∂μ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hAeq i]
  exact hlower.trans hupper

end BrownianSharp.AlignmentOperatorResidualTrace
