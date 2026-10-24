import BrownianSharp.AlignmentFractionalPolynomialTensorApproximation
import BrownianSharp.AlignmentNestedProjectionGrades

/-! A graded-frame presentation of the actual finite polynomial projection
feature. It has the same range and residual as the recursive-frame version,
but exposes grade-indexed coordinates for KGG approximation. -/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalGradedPolynomialFeature

open BrownianSharp
open BrownianSharp.AlignmentNestedProjectionBasis
open BrownianSharp.AlignmentNestedProjectionFrame
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentNestedProjectionTensor
open BrownianSharp.AlignmentNestedProjectionTensorApproximation
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalPolynomialTensorApproximation
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalTensorHolder
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalTensor
open BrownianSharp.AlignmentL2TensorProduct
open HaarQuarter
open BrownianSharp.CameronMartin

abbrev AxisL2 := AlignmentFractionalL2.UnitL2

private def gradedPolynomialFiltration {d : ℕ} (q : Fin d → ℕ) :
    Fin d → ℕ → Submodule ℝ AxisL2 :=
  fun i n => piecewisePolynomials (q i) n

private theorem gradedPolynomialFiltration_finite {d : ℕ} (q : Fin d → ℕ) :
    ∀ i n, FiniteDimensional ℝ ↥(gradedPolynomialFiltration q i n) := by
  intro i n
  exact piecewisePolynomials_finiteDimensional (q i) n

private theorem gradedPolynomialFiltration_nested {d : ℕ} (q : Fin d → ℕ) :
    ∀ i n, gradedPolynomialFiltration q i n ≤ gradedPolynomialFiltration q i (n+1) := by
  intro i n
  exact piecewisePolynomials_le_succ (q i) n

/-- The coordinate source frame with the filtration grade visible in its
index. -/
def polynomialGradedFrame {d : ℕ} (q : Fin d → ℕ) (N : ℕ) :
    ∀ i : Fin d, GradedFrameIndex (gradedPolynomialFiltration q i) N → AxisL2 :=
  fun i => gradedFrame (gradedPolynomialFiltration q i)
    (gradedPolynomialFiltration_finite q i) N

/-- Finite tensor coordinates indexed by the grades and within-grade basis
indices in each spatial coordinate. -/
def polynomialTensorGradedFrame {d : ℕ} (q : Fin d → ℕ) (N : ℕ) :
    (∀ i : Fin d, GradedFrameIndex (gradedPolynomialFiltration q i) N) → UnitCubeL2 d :=
  tensorFrame (polynomialGradedFrame q N)

/-- Tensor products of the coordinate graded frames form an orthonormal
family in the actual cube source Hilbert space. -/
theorem polynomialTensorGradedFrame_orthonormal {d : ℕ}
    (q : Fin d → ℕ) (N : ℕ) :
    Orthonormal ℝ (polynomialTensorGradedFrame q N) := by
  apply tensorFrame_orthonormal
  intro i
  exact gradedFrame_orthonormal (gradedPolynomialFiltration q i)
    (gradedPolynomialFiltration_finite q i)
    (gradedPolynomialFiltration_nested q i) N

/-- Number of coordinate basis vectors in one polynomial grade. -/
theorem polynomialGradeIndex_card_le {d : ℕ} (q : Fin d → ℕ)
    (i : Fin d) (g : ℕ) :
    Fintype.card (GradeIndex (gradedPolynomialFiltration q i) g) ≤ q i * 2^g := by
  exact gradeIndex_card_le_of_growth (gradedPolynomialFiltration q i)
    (gradedPolynomialFiltration_finite q i) (gradedPolynomialFiltration_nested q i)
    (A := q i) (fun n => by
      change Module.finrank ℝ ↥(piecewisePolynomials (q i) n) ≤ q i * 2^n
      exact piecewisePolynomials_finrank_le (q i) n) g

/-- Actual tensor RL feature projected coordinatewise onto the graded
piecewise-polynomial source spaces. -/
noncomputable def gradedPolynomialTensorProjectedKernel {d : ℕ}
    (q : Fin d → ℕ) (N : ℕ) (a : Fin d → ℝ)
    (ha : ∀ i, 1/2 < a i) : C(BrownianCubeAnchor d, UnitCubeL2 d) :=
  tensorFrameProjectedKernel (polynomialGradedFrame q N) a ha

private theorem axisGradedFrameProjection_eq_polynomialProjection
    {q : ℕ} (hq : 0 < q) (N : ℕ) (x : AxisL2) :
    axisFrameProjection (gradedFrame (piecewisePolynomials q)
      (fun n => piecewisePolynomials_finiteDimensional q n) N) x = polynomialProjection q N x := by
  let U : ℕ → Submodule ℝ AxisL2 := piecewisePolynomials q
  let W : Submodule ℝ AxisL2 := Submodule.span ℝ (Set.range
    (gradedFrame U (fun n => piecewisePolynomials_finiteDimensional q n) N))
  have hfinite : ∀ n, FiniteDimensional ℝ ↥(U n) :=
    fun n => piecewisePolynomials_finiteDimensional q n
  have hnested : ∀ n, U n ≤ U (n+1) := piecewisePolynomials_le_succ q
  have hspan : W = U N := by
    exact gradedFrame_span_eq U hfinite hnested N
  have hmem : W.starProjection x ∈ U N := by
    rw [← hspan]
    exact W.starProjection_apply_mem x
  have hres : x-W.starProjection x ∈ (U N)ᗮ := by
    rw [← hspan]
    exact W.sub_starProjection_mem_orthogonal x
  have hproj := (U N).eq_starProjection_of_mem_orthogonal hmem hres
  change W.starProjection x = (U N).starProjection x
  rw [hproj]

private theorem tensorFrameProjectedKernel_eq_of_axis_projections_eq
    {d : ℕ} {I J : Fin d → Type*} [∀ i, Fintype (I i)] [∀ i, Fintype (J i)]
    (e : ∀ i, I i → AxisL2) (f : ∀ i, J i → AxisL2)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i)
    (hproj : ∀ i x, axisFrameProjection (e i) x = axisFrameProjection (f i) x) :
    tensorFrameProjectedKernel e a ha = tensorFrameProjectedKernel f a ha := by
  apply ContinuousMap.ext
  intro t
  let μ : Fin d → Measure ℝ := fun _ => volume.restrict (Set.Icc (0:ℝ) 1)
  let T := tensorContinuous (μ := μ)
  change productToCube d (T (fun i => axisFrameProjection (e i)
      (translatedUnitKernelFamily (a i) (ha i) (cubeCoordinate i t)))) =
    productToCube d (T (fun i => axisFrameProjection (f i)
      (translatedUnitKernelFamily (a i) (ha i) (cubeCoordinate i t))))
  congr 1
  apply congrArg T
  funext i
  exact hproj i _

/-- The graded and recursive global frames span the same degree-truncated
piecewise-polynomial spaces, hence they produce exactly the same actual
tensor-kernel projection. -/
theorem gradedPolynomialTensorProjectedKernel_eq_recursive {d : ℕ}
    (q : Fin d → ℕ) (hq : ∀ i, 0 < q i) (N : ℕ)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i) :
    gradedPolynomialTensorProjectedKernel q N a ha =
      polynomialTensorProjectedKernel q N a ha := by
  apply tensorFrameProjectedKernel_eq_of_axis_projections_eq
    (polynomialGradedFrame q N)
    (fun i => nestedFrame (gradedPolynomialFiltration q i)
      (gradedPolynomialFiltration_finite q i) N) a ha
  intro i x
  change axisFrameProjection (gradedFrame (piecewisePolynomials (q i))
    (fun n => piecewisePolynomials_finiteDimensional (q i) n) N) x = _
  calc
    _ = polynomialProjection (q i) N x := by
      exact axisGradedFrameProjection_eq_polynomialProjection (hq i) N x
    _ = axisFrameProjection (nestedFrame (gradedPolynomialFiltration q i)
          (gradedPolynomialFiltration_finite q i) N) x := by
      rw [axisFrameProjection_nestedFrame_eq (gradedPolynomialFiltration q i)
        (gradedPolynomialFiltration_finite q i) (gradedPolynomialFiltration_nested q i) N]
      rfl

/-- Exact finite-coordinate expansion of the graded polynomial feature in
actual tensor-kernel inner products. This is the source-projection identity
needed by the generic KGG bridge. -/
theorem gradedPolynomialTensorProjectedKernel_eq_sum {d : ℕ}
    (q : Fin d → ℕ) (N : ℕ) (a : Fin d → ℝ)
    (ha : ∀ i, 1/2 < a i) (t : BrownianCubeAnchor d) :
    gradedPolynomialTensorProjectedKernel q N a ha t =
      ∑ z : (∀ i : Fin d, GradedFrameIndex (gradedPolynomialFiltration q i) N),
        ⟪tensorKernelFamily a ha t, polynomialTensorGradedFrame q N z⟫ •
          polynomialTensorGradedFrame q N z := by
  let e := polynomialGradedFrame q N
  have he : ∀ i, Orthonormal ℝ (e i) := fun i =>
    gradedFrame_orthonormal (gradedPolynomialFiltration q i)
      (gradedPolynomialFiltration_finite q i)
      (gradedPolynomialFiltration_nested q i) N
  change tensorFrameProjectedKernel e a ha t = _
  rw [tensorFrameProjectedKernel_eq_sum e he a ha t]
  rfl

/-- Uniform polynomial projection residual in the graded-coordinate
presentation. -/
theorem gradedPolynomialTensorProjectedKernel_uniform_rate {d : ℕ}
    (hd : 0 < d) (q : Fin d → ℕ) (hq : ∀ i, 0 < q i)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i)
    (r : ℝ) (hr : 1/2 < r) (hra : ∀ i, r ≤ a i) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ N : ℕ, 1 ≤ N → ∀ t : BrownianCubeAnchor d,
        ‖tensorKernelFamily a ha t - gradedPolynomialTensorProjectedKernel q N a ha t‖ ≤
          C * ((2:ℝ)^(-γ))^N := by
  obtain ⟨C,γ,hC,hγ,hbound⟩ :=
    polynomialTensorProjectedKernel_uniform_rate hd q hq a ha r hr hra
  refine ⟨C,γ,hC,hγ,?_⟩
  intro N hN t
  rw [gradedPolynomialTensorProjectedKernel_eq_recursive q hq N a ha]
  exact hbound N hN t

/-- An arbitrary prescribed uniform residual can be achieved for every
anisotropic order vector above one half, using a common polynomial depth. -/
theorem exists_gradedPolynomialTensorProjectedKernel_depth {d : ℕ}
    (hd : 0 < d) (q : Fin d → ℕ) (hq : ∀ i, 0 < q i)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i) {τ : ℝ} (hτ : 0 < τ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ t : BrownianCubeAnchor d,
      ‖tensorKernelFamily a ha t - gradedPolynomialTensorProjectedKernel q N a ha t‖ ≤ τ := by
  obtain ⟨N,hN,herr⟩ :=
    exists_polynomialTensorProjectedKernel_depth_of_orders hd q hq a ha hτ
  refine ⟨N,hN,?_⟩
  intro t
  rw [gradedPolynomialTensorProjectedKernel_eq_recursive q hq N a ha]
  exact herr t

/-- The graded finite polynomial tensor feature inherits the Hölder modulus
of the actual anisotropic RL kernel. -/
theorem gradedPolynomialTensorProjectedKernel_holder {d : ℕ}
    (hd : 0 < d) (q : Fin d → ℕ) (hq : ∀ i, 0 < q i)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i)
    (r : ℝ) (hr : 1/2 < r) (hra : ∀ i, r ≤ a i) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : BrownianCubeAnchor d,
        ‖gradedPolynomialTensorProjectedKernel q N a ha x -
          gradedPolynomialTensorProjectedKernel q N a ha y‖ ≤
            C * (dist x y)^(tensorHolderExponent r) := by
  obtain ⟨C,hC,hholder⟩ :=
    polynomialTensorProjectedKernel_holder hd q hq a ha r hr hra N
  refine ⟨C,hC,?_⟩
  intro x y
  simpa only [gradedPolynomialTensorProjectedKernel_eq_recursive q hq N a ha] using
    hholder x y
