import BrownianSharp.AlignmentFractionalTensorL2TraceBudget
import BrownianSharp.AlignmentFractionalCubeL2ProjectionError

/-! Actual rectangular source projection convergence for the tensor RL map. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped ENNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalTensorProjectionConvergence
open AlignmentFractionalTensorL2TraceBudget AlignmentFractionalTensorOperator
  AlignmentFractionalGradedPolynomialFeature AlignmentNestedProjectionTensor
  AlignmentNestedProjectionFrame AlignmentNestedProjectionGrades AlignmentFractionalPolynomialSpaces
  AlignmentFractionalTensorL2Semigroup AlignmentFractionalCubeL2ProjectionError

local instance {d q M : ℕ} : FiniteDimensional ℝ
    (polynomialTensorRectangleSpace (d:=d) (q:=q) (M:=M)) :=
  polynomialTensorRectangleSpace_finite

theorem polynomial_rectangle_projection_eq {d q M : ℕ}
    (a : Fin d → ℝ) (ha : ∀ i,1/2<a i) (t : BrownianCubeAnchor d) :
    (polynomialTensorRectangleSpace (d:=d) (q:=q) (M:=M)).starProjection
      (tensorKernelFamily a ha t) =
      gradedPolynomialTensorProjectedKernel (fun _ : Fin d => q) M a ha t := by
  classical
  let e := fun _ : Fin d => gradedFrame (piecewisePolynomials q)
    (fun n => piecewisePolynomials_finiteDimensional q n) M
  have he : ∀ i, Orthonormal ℝ (e i) := fun _ =>
    gradedFrame_orthonormal (piecewisePolynomials q)
      (fun n => piecewisePolynomials_finiteDimensional q n)
      (piecewisePolynomials_le_succ q) M
  rw [gradedPolynomialTensorProjectedKernel_eq_sum]
  change (Submodule.span ℝ (Set.range (tensorFrame e))).starProjection
      (tensorKernelFamily a ha t) =
    ∑ z, ⟪tensorKernelFamily a ha t,tensorFrame e z⟫ • tensorFrame e z
  exact tensorFrame_span_starProjection_eq_sum e he _

theorem exists_polynomial_rectangle_projection_error {d : ℕ} (hd : 0<d)
    (q : ℕ) (hq : 0<q) (a : Fin d → ℝ) (ha : ∀ i,1/2<a i)
    (δ : ℝ) (hδ : 0<δ) :
    ∃ M : ℕ, 1 ≤ M ∧
      ‖fractionalTensorRLToL2 a ha -
        (fractionalTensorRLToL2 a ha).comp
          (polynomialTensorRectangleSpace (d:=d) (q:=q) (M:=M)).starProjection‖ ≤ δ := by
  obtain ⟨M,hM,herr⟩ := exists_gradedPolynomialTensorProjectedKernel_depth
    hd (fun _ : Fin d => q) (fun _ => hq) a ha hδ
  let U := polynomialTensorRectangleSpace (d:=d) (q:=q) (M:=M)
  letI : FiniteDimensional ℝ U := polynomialTensorRectangleSpace_finite
  refine ⟨M,hM,fractionalTensorRLToL2_projection_error_bound a ha U δ hδ.le ?_⟩
  intro t
  rw [polynomial_rectangle_projection_eq a ha t]
  exact herr t

theorem exists_polynomial_rectangle_projection_error_atLeast {d : ℕ} (hd : 0<d)
    (q : ℕ) (hq : 0<q) (β : ℝ) (hβ : 1/2<β)
    (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    ∃ M : ℕ, 1 ≤ M ∧ N ≤ M ∧
      ‖fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => hβ) -
        (fractionalTensorRLToL2 (fun _ : Fin d => β) (fun _ => hβ)).comp
          (polynomialTensorRectangleSpace (d:=d) (q:=q) (M:=M)).starProjection‖ ≤ δ := by
  obtain ⟨C,γ,hC,hγ,hbound⟩ := gradedPolynomialTensorProjectedKernel_uniform_rate
    hd (fun _ : Fin d => q) (fun _ => hq) (fun _ => β) (fun _ => hβ)
      β hβ (fun _ => le_rfl)
  have hb0 : 0 ≤ (2:ℝ)^(-γ) := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hb1 : (2:ℝ)^(-γ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have ht : Filter.Tendsto (fun m : ℕ => C * ((2:ℝ)^(-γ))^m)
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hb0 hb1)
  have he : ∀ᶠ m : ℕ in Filter.atTop, C * ((2:ℝ)^(-γ))^m < δ :=
    ht.eventually (gt_mem_nhds hδ)
  obtain ⟨M,⟨hM,hNM⟩,herr⟩ := (Filter.eventually_ge_atTop 1 |>.and
    (Filter.eventually_ge_atTop N) |>.and he).exists
  let U := polynomialTensorRectangleSpace (d:=d) (q:=q) (M:=M)
  refine ⟨M,hM,hNM,fractionalTensorRLToL2_projection_error_bound
    (fun _ : Fin d => β) (fun _ => hβ) U δ hδ.le ?_⟩
  intro t
  rw [polynomial_rectangle_projection_eq (fun _ : Fin d => β) (fun _ => hβ) t]
  exact (hbound M hM t).trans herr.le

end BrownianSharp.AlignmentFractionalTensorProjectionConvergence
