import BrownianSharp.AlignmentFractionalTensorL2TraceBudget
import BrownianSharp.AlignmentFractionalTensorProjectionConvergence
import BrownianSharp.AlignmentHilbertTraceRefinement
import BrownianSharp.AlignmentFractionalApproximationNumbers
import BrownianSharp.AlignmentGeometricRanks

/-! Actual Hilbert `L²` approximation numbers for the isotropic tensor
Riemann--Liouville operator. -/

noncomputable section
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalTensorL2ApproximationUpper

open BrownianSharp.AlignmentFractionalTensorL2TraceBudget
open BrownianSharp.AlignmentFractionalTensorProjectionConvergence
open BrownianSharp.AlignmentFractionalApproximationNumbers
open BrownianSharp.AlignmentHilbertTraceRefinement
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalTensorL2Semigroup
open BrownianSharp.AlignmentFractionalGradedPolynomialFeature
open BrownianSharp.AlignmentGeometricRanks
open BrownianSharp.CameronMartin
open BrownianSharp

/-- The actual isotropic tensor RL operator has a dyadic approximation-number
bound. The source rank is the low-total-grade layer count; the trace budget
comes from the actual kernel coefficient energy. -/
theorem fractionalTensorRLToL2_approximationNumber_dyadic {d : ℕ}
    (hd : 2 ≤ d) {β : ℝ} (hβ : 1/2 < β) :
    ∃ q : ℕ, ∃ A ρ : ℝ, ∃ D : ℕ,
      0 < q ∧ 0 < A ∧ 0 < ρ ∧ ρ < 1 ∧
      ρ = Real.rpow 2 (-(2*β-1)) ∧ 0 < D ∧
      ∀ N : ℕ, 1 ≤ N →
        approximationNumber
          (fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => hβ))
          (2 * (D * Fintype.card (LayerIndex d N)) + 1) ≤
          ENNReal.ofReal (Real.sqrt
            ((A * ρ^N * ((N+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1)) /
              ((D * Fintype.card (LayerIndex d N) + 1:ℕ):ℝ))) := by
  classical
  obtain ⟨q,A,ρ,hq,hA,hρ0,hρ1,hρeq,htrace⟩ :=
    exists_fractionalTensor_grade_trace_bound_explicit (by omega : 0 < d) hβ
  obtain ⟨D,hD,hDcard⟩ :=
    polynomialTensorLowIndex_card_le_layer_multiple hd hq
  refine ⟨q,A,ρ,D,hq,hA,hρ0,hρ1,hρeq,hD,?_⟩
  intro N hN
  let T : UnitCubeL2 d →L[ℝ] UnitCubeL2 d :=
    fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => hβ)
  let Dn : ℕ := Nat.floor (D * (Fintype.card (LayerIndex d N) : ℝ))
  have henergy : ∀ M g : ℕ,
      (∑ a : {a : PolynomialTensorIndex d q M // polynomialTensorGrade a = g},
        fractionalTensorGradeCoefficient β hβ a.1) ≤
          A * ((g+1:ℕ):ℝ)^(d-1) * ρ^g := by
    intro M g
    exact htrace M g
  have henergyAt (M : ℕ) : ∀ g : ℕ,
      (∑ a : {a : PolynomialTensorIndex d q M // polynomialTensorGrade a = g},
        fractionalTensorGradeCoefficient β hβ a.1) ≤
          A * ((g+1:ℕ):ℝ)^(d-1) * ρ^g := fun g => henergy M g
  have hbudget : 0 ≤ A * ρ^N * ((N+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1) := by
    have hp := polynomialBudget_nonneg (le_of_lt hρ0) (d-1)
    positivity
  let Dn : ℕ := D * Fintype.card (LayerIndex d N)
  have hrefine : ∀ δ : ℝ, 0 < δ →
      ∃ (U V : Submodule ℝ (UnitCubeL2 d)) (_hU : FiniteDimensional ℝ U)
        (_hV : FiniteDimensional ℝ V),
        U ≤ V ∧
        Module.rank ℝ (LinearMap.range
          ((T.comp U.starProjection : UnitCubeL2 d →L[ℝ] UnitCubeL2 d) :
            UnitCubeL2 d →ₗ[ℝ] UnitCubeL2 d)) ≤ (Dn : Cardinal) ∧
        ‖T-T.comp V.starProjection‖ ≤ δ ∧
        ∃ b : Fin (Module.finrank ℝ V) → V, Orthonormal ℝ b ∧
          (∑ i, ‖T ((ContinuousLinearMap.id ℝ (UnitCubeL2 d)-U.starProjection)
            ((V.subtypeₗᵢ : V →ₗᵢ[ℝ] UnitCubeL2 d) (b i)))‖^2) ≤
              A * ρ^N * ((N+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1) := by
    intro δ hδ
    obtain ⟨M,hM,hNM,htail⟩ :=
      exists_polynomial_rectangle_projection_error_atLeast
        (d:=d) (by omega) q hq β hβ N δ hδ
    obtain ⟨U,V,hU,hV,hUV,hbase,⟨b,hb,htraceB,hUeq,hVeq⟩⟩ :=
      polynomialTensor_low_refinement_data_of_card_bound
        (d:=d) (q:=q) (M:=M) (N:=N) (by omega) hq D hD hDcard
        hβ (le_of_lt hA) hρ0 hρ1 (henergyAt M)
    refine ⟨U,V,hU,hV,hUV,?_,?_,⟨b,hb,htraceB⟩⟩
    · simpa [T, Dn] using hbase
    · simpa [T, hVeq] using htail
  have happrox := approximationNumber_le_of_nested_trace_refinements
    T Dn Dn (A * ρ^N * ((N+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1))
    hbudget hrefine
  simpa [T, Dn, two_mul, add_comm, add_left_comm, add_assoc] using happrox

end BrownianSharp.AlignmentFractionalTensorL2ApproximationUpper
