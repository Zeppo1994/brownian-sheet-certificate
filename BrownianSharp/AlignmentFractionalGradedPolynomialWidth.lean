import BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
import BrownianSharp.FiniteOrthogonalCoordinates
import BrownianSharp.AlignmentAmbientWidth
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentFractionalGradedPolynomialFeature
import BrownianSharp.CubeDyadicGrid
import BrownianSharp.FinitePartitionExtension
import BrownianSharp.AlignmentFractionalGenericGradeCounts
import BrownianSharp.AlignmentFractionalPolynomialWeightedEnergy
import BrownianSharp.AlignmentFractionalPolynomialSpaces
import BrownianSharp.ShapeGrowth
import BrownianSharp.LayerIndex
import BrownianSharp.AlignmentFractionalPolynomialBands
import BrownianSharp.AlignmentFractionalPolynomialPublicEnergy
import BrownianSharp.AlignmentFractionalGenericKGGWidth
import BrownianSharp.AlignmentFractionalSharpBudgets
import BrownianSharp.CubeGridLogBudget

/-! A direct width bridge from actual fractional RL kernel features to the
finite graded-coordinate KGG approximation. This module does not depend on
the still-developing sharp isotropic width wrapper. -/

noncomputable section
set_option maxRecDepth 3000
set_option maxHeartbeats 800000
open scoped BigOperators RealInnerProductSpace Topology

namespace BrownianSharp.AlignmentFractionalGradedPolynomialWidth

open BrownianSharp
open BrownianSharp.AlignmentPeriodicWidthFeatureAssembly
open BrownianSharp.AlignmentPeriodicWidthLayerAlgebra
open BrownianSharp.AlignmentGeometricRanks
open HaarQuarter.TheoremD.Width
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalGradedPolynomialFeature
open BrownianSharp.AlignmentFractionalWeightedHaarCounts
open BrownianSharp.AlignmentNestedProjectionTensor
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalGenericGradeCounts
open BrownianSharp.AlignmentFractionalPaddingPermutation
open BrownianSharp.AlignmentNestedProjectionGrades
open BrownianSharp.AlignmentFractionalTensorHolder
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.CameronMartin
open HaarQuarter

/-- Exact squared norm of a masked finite feature row as the sum of its
squared coordinates in the selected fiber. -/
theorem coordinateLayerMask_norm_sq_eq_fiber_sum
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (σ : I → J) (j : J) (x : EuclideanSpace ℝ I) :
    ‖coordinateLayerMask σ j x‖^2 =
      ∑ i ∈ Finset.univ.filter (fun i : I => σ i = j), (x i)^2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [coordinateLayerMask_apply]
  rw [Finset.sum_filter]
  simp

/-- Convert a fiberwise coefficient-energy estimate directly into the row
radius premise consumed by the finite KGG layer theorem. -/
theorem coordinateLayerMask_norm_le_of_fiber_energy
    {I J : Type} [Fintype I] [Fintype J] [DecidableEq J]
    (σ : I → J) (j : J) (x : EuclideanSpace ℝ I) {R : ℝ}
    (hR : 0 ≤ R)
    (henergy : ∑ i ∈ Finset.univ.filter (fun i : I => σ i = j), (x i)^2 ≤ R^2) :
    ‖coordinateLayerMask σ j x‖ ≤ R := by
  have hsq : ‖coordinateLayerMask σ j x‖^2 ≤ R^2 := by
    rw [coordinateLayerMask_norm_sq_eq_fiber_sum]
    exact henergy
  exact (sq_le_sq₀ (norm_nonneg _) hR).1 hsq

private theorem finiteCoordinates_inner_projection
    {I H : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : I → H) (x y : H) :
    ⟪finiteOrthonormalCoordinates e x, finiteOrthonormalCoordinates e y⟫ =
      ⟪x, finiteOrthonormalProjection e y⟫ := by
  classical
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [finiteOrthonormalCoordinates, finiteOrthonormalProjection, dotProduct,
    inner_sum, inner_smul_right]

/-- The actual RL image width is controlled by its truncated finite feature
coordinates plus the supplied uniform projection residual. The only
finite-dimensional inputs are the coefficient-layer row and energy bounds;
the feature and operator are the manuscript's genuine tensor RL kernel and
integration map. -/
theorem fractional_tensor_RL_partition_KGG_width_bound
    {d L : ℕ} {I : Type} [Fintype I]
    (a₀ : Fin d → ℝ) (ha₀ : ∀ i, 1/2 < a₀ i)
    (e : I → UnitCubeL2 d) (he : Orthonormal ℝ e)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (htrunc : ∀ t : BrownianCubeAnchor d,
      ‖tensorKernelFamily a₀ ha₀ t -
        finiteOrthonormalProjection e (tensorKernelFamily a₀ ha₀ t)‖ ≤ τ)
    {G : Type} [Fintype G]
    (φ : G → C(BrownianCubeAnchor d, ℝ))
    (anchor : G → BrownianCubeAnchor d)
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1)
    (σ : I → Option (Fin L)) (R : Fin L → ℝ)
    (hR : ∀ j, 0 ≤ R j)
    (hrow : ∀ j g,
      ‖coordinateLayerMask σ (some j)
        (finiteOrthonormalCoordinates e
          (tensorKernelFamily a₀ ha₀ (anchor g)))‖ ≤ R j)
    {A₀ ρ q : ℝ} {k : ℕ} (hA₀ : 0 ≤ A₀)
    (hρ : 0 < ρ) (hq : 0 < q) (hq1 : q < 1) (hρq : ρ < q)
    (henergy : ∀ j, (R j)^2 ≤ A₀*((j.val+1:ℕ):ℝ)^k*ρ^(j.val))
    (D : ℕ) (hD : 0 < D)
    (hlow : Fintype.card {i : I // σ i = none} ≤ D)
    {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hosc : ∀ i t, φ i t ≠ 0 →
      ‖tensorKernelFamily a₀ ha₀ t -
        tensorKernelFamily a₀ ha₀ (anchor i)‖ ≤ δ) :
    kolmogorovWidth (Latest.fractionalIntegrationBall a₀)
      (D*Nat.ceil (1+(1-q)⁻¹)) ≤
      ENNReal.ofReal (τ + δ + Real.sqrt
        ((4*(10000:ℝ)^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
          polynomialBudget (ρ/q) k)) := by
  classical
  let feature : BrownianCubeAnchor d → UnitCubeL2 d := tensorKernelFamily a₀ ha₀
  let T := fractionalTensorRL a₀ ha₀
  let coord : BrownianCubeAnchor d → EuclideanSpace ℝ I :=
    fun t => finiteOrthonormalCoordinates e (feature t)
  have hT : ∀ g t, T g t = ⟪g, feature t⟫ := by
    intro g t
    change ⟪tensorKernelFamily a₀ ha₀ t, g⟫ =
      ⟪g, tensorKernelFamily a₀ ha₀ t⟫
    exact real_inner_comm _ _
  have hrow' : ∀ j g, ‖coordinateLayerMask σ (some j) (coord (anchor g))‖ ≤ R j := by
    intro j g
    simpa [coord, feature] using hrow j g
  have hosc' : ∀ i t, φ i t ≠ 0 → ‖coord t-coord (anchor i)‖ ≤ δ := by
    intro i t hne
    have hdiff : coord t-coord (anchor i) =
        finiteOrthonormalCoordinates e
          (tensorKernelFamily a₀ ha₀ t-tensorKernelFamily a₀ ha₀ (anchor i)) := by
      simp [coord, feature, finiteOrthonormalCoordinates, map_sub]
    rw [hdiff]
    exact (finiteOrthonormalCoordinates_norm_le e he _).trans (hosc i t hne)
  obtain ⟨W,hW,happrox⟩ :=
    partition_geometric_hilbert_layer_approximation
      coord φ anchor hφ hsum σ R hR hrow' hA₀ hρ hq hq1 hρq henergy D hD hlow hosc'
  let K : Set C(BrownianCubeAnchor d, ℝ) := T '' {g : UnitCubeL2 d | ‖g‖ ≤ 1}
  have hW' : Module.rank ℝ W ≤
      ((D*Nat.ceil (1+(1-q)⁻¹):ℕ):Cardinal) := by
    simpa only [Nat.cast_mul] using hW
  have hε : 0 ≤ τ + δ + Real.sqrt
      ((4*(10000:ℝ)^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
        polynomialBudget (ρ/q) k) := by
    exact add_nonneg (add_nonneg hτ hδ) (Real.sqrt_nonneg _)
  have hpoint : ∀ f ∈ K, ∃ y ∈ W,
      ‖f-y‖ ≤ τ + δ + Real.sqrt
        ((4*(10000:ℝ)^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
          polynomialBudget (ρ/q) k) := by
    intro f hf
    rcases hf with ⟨g,hg,rfl⟩
    let x : EuclideanSpace ℝ I := finiteOrthonormalCoordinates e g
    have hx : ‖x‖ ≤ 1 := by
      simpa [x] using (finiteOrthonormalCoordinates_norm_le e he g).trans hg
    obtain ⟨y,hy,hyerr⟩ := happrox x hx
    refine ⟨y,hy,?_⟩
    apply (ContinuousMap.norm_le (T g-y) hε).2
    intro t
    have hcoord : ⟪x,coord t⟫ =
        ⟪g,finiteOrthonormalProjection e (feature t)⟫ :=
      finiteCoordinates_inner_projection e g (feature t)
    have hsplit : T g t-y t =
        (⟪x,coord t⟫-y t) +
          ⟪g,feature t-finiteOrthonormalProjection e (feature t)⟫ := by
      rw [hT, hcoord]
      simp [inner_sub_right]
    change |(T g) t-y t| ≤ _
    rw [hsplit]
    calc
      _ ≤ |⟪x,coord t⟫-y t| +
          |⟪g,feature t-finiteOrthonormalProjection e (feature t)⟫| := abs_add_le _ _
      _ ≤ δ + Real.sqrt
          ((4*(10000:ℝ)^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
            polynomialBudget (ρ/q) k) + τ := by
        have hfirst := hyerr t
        have hsecond : |⟪g,feature t-finiteOrthonormalProjection e (feature t)⟫| ≤ τ := by
          calc
            _ ≤ ‖g‖*‖feature t-finiteOrthonormalProjection e (feature t)‖ :=
              abs_real_inner_le_norm _ _
            _ ≤ 1*τ := mul_le_mul hg (htrunc t) (norm_nonneg _) (by norm_num)
            _ = τ := by ring
        nlinarith
      _ = τ + δ + Real.sqrt
          ((4*(10000:ℝ)^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
            polynomialBudget (ρ/q) k) := by ring
  have herror : approximationError K W ≤ ENNReal.ofReal
      (τ + δ + Real.sqrt
        ((4*(10000:ℝ)^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
          polynomialBudget (ρ/q) k)) :=
    AlignmentAmbientWidth.approximationError_le_of_pointwise K W hε hpoint
  rw [fractionalIntegrationBall_eq_operator_image a₀ ha₀]
  unfold kolmogorovWidth
  exact (iInf_le
      (fun V : {V : Submodule ℝ C(BrownianCubeAnchor d,ℝ) //
        Module.rank ℝ V ≤ ((D*Nat.ceil (1+(1-q)⁻¹):ℕ):Cardinal)} =>
          approximationError K V.val) ⟨W,hW'⟩).trans herror

/-- The finite orthogonal projection onto the actual anisotropic graded
piecewise-polynomial tensor frame is exactly the graded projected kernel
already constructed from the RL feature. This converts its uniform
polynomial truncation estimate into the residual premise of the width bridge. -/
theorem polynomialGradedFrame_projection_eq_projectedKernel {d : ℕ}
    (q : Fin d → ℕ) (M : ℕ) (a : Fin d → ℝ)
    (ha : ∀ i, 1/2 < a i) (t : BrownianCubeAnchor d) :
    finiteOrthonormalProjection (polynomialTensorGradedFrame q M)
      (tensorKernelFamily a ha t) =
        gradedPolynomialTensorProjectedKernel q M a ha t := by
  rw [finiteOrthonormalProjection,
    gradedPolynomialTensorProjectedKernel_eq_sum q M a ha t]

/-- Polynomial-frame specialization of the actual RL KGG width bridge.
All order-dependent approximation work is exposed as the uniform actual
kernel-to-polynomial-projection residual; row and energy hypotheses retain
their literal graded-coordinate form for the anisotropic estimates. -/
theorem polynomial_fractional_tensor_RL_partition_KGG_width_bound
    {d L : ℕ} (q : Fin d → ℕ) (M : ℕ) (a₀ : Fin d → ℝ)
    (ha₀ : ∀ i, 1/2 < a₀ i) {τ : ℝ} (hτ : 0 ≤ τ)
    (htrunc : ∀ t : BrownianCubeAnchor d,
      ‖tensorKernelFamily a₀ ha₀ t -
        gradedPolynomialTensorProjectedKernel q M a₀ ha₀ t‖ ≤ τ)
    {G : Type} [Fintype G]
    (φ : G → C(BrownianCubeAnchor d, ℝ))
    (anchor : G → BrownianCubeAnchor d)
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1)
    (σ : (∀ i : Fin d, GradedFrameIndex (fun n =>
      AlignmentFractionalPolynomialSpaces.piecewisePolynomials (q i) n) M) →
        Option (Fin L)) (R : Fin L → ℝ)
    (hR : ∀ j, 0 ≤ R j)
    (hrow : ∀ j g,
      ‖coordinateLayerMask σ (some j)
        (finiteOrthonormalCoordinates
          (polynomialTensorGradedFrame q M)
          (tensorKernelFamily a₀ ha₀ (anchor g)))‖ ≤ R j)
    {A₀ ρ qrate : ℝ} {k : ℕ} (hA₀ : 0 ≤ A₀)
    (hρ : 0 < ρ) (hqrate : 0 < qrate) (hq1 : qrate < 1)
    (hρq : ρ < qrate)
    (henergy : ∀ j, (R j)^2 ≤ A₀*((j.val+1:ℕ):ℝ)^k*ρ^(j.val))
    (D : ℕ) (hD : 0 < D)
    (hlow : Fintype.card {i : (∀ i : Fin d, GradedFrameIndex (fun n =>
      AlignmentFractionalPolynomialSpaces.piecewisePolynomials (q i) n) M) //
        σ i = none} ≤ D)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hosc : ∀ i t, φ i t ≠ 0 →
      ‖tensorKernelFamily a₀ ha₀ t -
        tensorKernelFamily a₀ ha₀ (anchor i)‖ ≤ δ) :
    kolmogorovWidth (Latest.fractionalIntegrationBall a₀)
      (D*Nat.ceil (1+(1-qrate)⁻¹)) ≤
      ENNReal.ofReal (τ + δ + Real.sqrt
        ((4*(10000:ℝ)^2*A₀*Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
          polynomialBudget (ρ/qrate) k)) := by
  have htrunc' : ∀ t : BrownianCubeAnchor d,
      ‖tensorKernelFamily a₀ ha₀ t -
        finiteOrthonormalProjection (polynomialTensorGradedFrame q M)
          (tensorKernelFamily a₀ ha₀ t)‖ ≤ τ := by
    intro t
    rw [polynomialGradedFrame_projection_eq_projectedKernel q M a₀ ha₀ t]
    exact htrunc t
  exact fractional_tensor_RL_partition_KGG_width_bound a₀ ha₀
    (polynomialTensorGradedFrame q M)
    (polynomialTensorGradedFrame_orthonormal q M) hτ htrunc'
    φ anchor hφ hsum σ R hR hrow hA₀ hρ hqrate hq1 hρq henergy D hD hlow hδ hosc

/-- Actual RL width bound directly from natural-grade coefficient energies.
The low fibers are grades below `cutoff`; every higher grade is shifted to a
finite KGG layer. The only analytic inputs are the actual feature truncation,
partition oscillation, and gradewise squared-coordinate energy estimates. -/
theorem fractional_tensor_RL_width_of_grade_energy
    {d L : ℕ} {I : Type} [Fintype I]
    (a₀ : Fin d → ℝ) (ha₀ : ∀ i, 1/2 < a₀ i)
    (e : I → UnitCubeL2 d) (he : Orthonormal ℝ e)
    (grade : I → ℕ) (cutoff : ℕ)
    (hgradeMax : ∀ i, grade i < cutoff+L)
    {Cenergy ρ qrate τ : ℝ} {k : ℕ}
    (hC : 0 ≤ Cenergy) (hρ : 0 < ρ) (hq : 0 < qrate)
    (hq1 : qrate < 1) (hρq : ρ < qrate)
    (hτ : 0 ≤ τ)
    (htrunc : ∀ t : BrownianCubeAnchor d,
      ‖tensorKernelFamily a₀ ha₀ t -
        finiteOrthonormalProjection e (tensorKernelFamily a₀ ha₀ t)‖ ≤ τ)
    (hgradeEnergy : ∀ (n : ℕ) (g : BrownianCubeAnchor d),
      (∑ i : {i : I // grade i = n},
        (finiteOrthonormalCoordinates e (tensorKernelFamily a₀ ha₀ g) i.1)^2) ≤
          Cenergy*((n+1:ℕ):ℝ)^k*ρ^n)
    (D : ℕ) (hD : 0 < D)
    (hlow : Fintype.card {i : I // grade i < cutoff} ≤ D)
    {G : Type} [Fintype G]
    (φ : G → C(BrownianCubeAnchor d, ℝ))
    (anchor : G → BrownianCubeAnchor d)
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hosc : ∀ i t, φ i t ≠ 0 →
      ‖tensorKernelFamily a₀ ha₀ t -
        tensorKernelFamily a₀ ha₀ (anchor i)‖ ≤ δ) :
    kolmogorovWidth (Latest.fractionalIntegrationBall a₀)
      (D*Nat.ceil (1+(1-qrate)⁻¹)) ≤
      ENNReal.ofReal (τ + δ + Real.sqrt
        ((4*(10000:ℝ)^2*(Cenergy*((cutoff+1:ℕ):ℝ)^k*ρ^cutoff)*
          Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
          polynomialBudget (ρ/qrate) k)) := by
  classical
  let σ : I → Option (Fin L) := fun i =>
    if h : cutoff ≤ grade i then
      some ⟨grade i-cutoff, by have := hgradeMax i; omega⟩
    else none
  let R : Fin L → ℝ := fun j => Real.sqrt
    (Cenergy*((cutoff+j.val+1:ℕ):ℝ)^k*ρ^(cutoff+j.val))
  let A₀ : ℝ := Cenergy*((cutoff+1:ℕ):ℝ)^k*ρ^cutoff
  have hσsome (i : I) (j : Fin L) : σ i = some j ↔
      grade i = cutoff+j.val := by
    dsimp [σ]
    by_cases h : cutoff ≤ grade i
    · simp only [dif_pos h, Option.some.injEq]
      constructor
      · intro hij
        have hv := congrArg Fin.val hij
        have hv' : grade i = j.val+cutoff :=
          (Nat.sub_eq_iff_eq_add h).mp hv
        simpa [Nat.add_comm] using hv'
      · intro hij
        apply Fin.ext
        have hsub : grade i - cutoff = j.val := by
          rw [hij]
          exact Nat.add_sub_cancel_left cutoff j.val
        exact hsub
    · simp [dif_neg h]
      intro heq
      exact h (heq ▸ Nat.le_add_right cutoff j.val)
  have hσnone (i : I) : σ i = none ↔ grade i < cutoff := by
    dsimp [σ]
    by_cases h : cutoff ≤ grade i <;> simp [h] <;> omega
  have hlow' : Fintype.card {i : I // σ i = none} ≤ D := by
    have hequiv : {i : I // σ i = none} ≃ {i : I // grade i < cutoff} :=
      { toFun := fun x => ⟨x.1, (hσnone x.1).mp x.2⟩
        invFun := fun x => ⟨x.1, (hσnone x.1).mpr x.2⟩
        left_inv := by intro x; cases x; rfl
        right_inv := by intro x; cases x; rfl }
    exact (Fintype.card_congr hequiv).trans_le hlow
  have hR : ∀ j, 0 ≤ R j := fun j => Real.sqrt_nonneg _
  have hA₀ : 0 ≤ A₀ := by dsimp [A₀]; positivity
  have hrow : ∀ (j : Fin L) (g : G),
      ‖coordinateLayerMask σ (some j)
        (finiteOrthonormalCoordinates e
          (tensorKernelFamily a₀ ha₀ (anchor g)))‖ ≤ R j := by
    intro j g
    apply coordinateLayerMask_norm_le_of_fiber_energy σ (some j) _ (hR j)
    have hfiber : Finset.univ.filter (fun i : I => σ i = some j) =
        Finset.univ.filter (fun i : I => grade i = cutoff+j.val) := by
      ext i
      simp [hσsome]
    rw [hfiber]
    calc
      _ = ∑ i : {i : I // grade i = cutoff+j.val},
          (finiteOrthonormalCoordinates e
            (tensorKernelFamily a₀ ha₀ (anchor g)) i.1)^2 := by
        exact Finset.sum_subtype
          (Finset.univ.filter (fun i : I => grade i = cutoff+j.val))
          (by intro i; simp)
          (fun i =>
            (finiteOrthonormalCoordinates e
              (tensorKernelFamily a₀ ha₀ (anchor g)) i)^2)
      _ ≤ Cenergy*((cutoff+j.val+1:ℕ):ℝ)^k*ρ^(cutoff+j.val) :=
        hgradeEnergy (cutoff+j.val) (anchor g)
      _ = R j^2 := by
        dsimp [R]
        rw [Real.sq_sqrt]
        positivity
  have henergy : ∀ j : Fin L, (R j)^2 ≤
      A₀*((j.val+1:ℕ):ℝ)^k*ρ^(j.val) := by
    intro j
    have hrad : 0 ≤ Cenergy*((cutoff+j.val+1:ℕ):ℝ)^k*ρ^(cutoff+j.val) := by
      positivity
    have hsqrt := Real.sq_sqrt hrad
    have hcast : ((cutoff+j.val+1:ℕ):ℝ) ≤
        ((cutoff+1:ℕ):ℝ)*((j.val+1:ℕ):ℝ) := by
      push_cast
      nlinarith [mul_nonneg (show (0:ℝ) ≤ cutoff by positivity)
        (show (0:ℝ) ≤ j.val by positivity)]
    have hpow := pow_le_pow_left₀
      (by positivity : (0:ℝ) ≤ ((cutoff+j.val+1:ℕ):ℝ)) hcast k
    dsimp [R, A₀]
    rw [Real.sq_sqrt hrad, pow_add]
    calc
      Cenergy*((cutoff+j.val+1:ℕ):ℝ)^k*
          ((ρ:ℝ)^cutoff*ρ^j.val) ≤
        Cenergy*((cutoff+1:ℕ):ℝ)^k*((j.val+1:ℕ):ℝ)^k*
          ((ρ:ℝ)^cutoff*ρ^j.val) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            calc
              _ ≤ Cenergy*(((cutoff+1:ℕ):ℝ)*((j.val+1:ℕ):ℝ))^k :=
                mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (by positivity) hcast k) hC
              _ = _ := by rw [mul_pow]; ring
      _ = Cenergy*((cutoff+1:ℕ):ℝ)^k*(ρ:ℝ)^cutoff*
            ((j.val+1:ℕ):ℝ)^k*ρ^j.val := by ring
  exact fractional_tensor_RL_partition_KGG_width_bound
    a₀ ha₀ e he hτ htrunc
    φ anchor hφ hsum σ R hR hrow hA₀ hρ hq hq1 hρq henergy D hD hlow' hδ hosc

/-- The natural-grade energy bridge specialized to the genuine anisotropic
piecewise-polynomial tensor frame. The energy input is written in the same
inner-product coordinates as the weighted tensor-energy theorem; the frame
projection and the coefficient-coordinate conversion are discharged here. -/
theorem polynomial_fractional_tensor_RL_width_of_grade_energy
    {d M L : ℕ} (qdegree : Fin d → ℕ) (a₀ : Fin d → ℝ)
    (ha₀ : ∀ i, 1/2 < a₀ i) (grade :
      (∀ i : Fin d, GradedFrameIndex (fun n =>
        AlignmentFractionalPolynomialSpaces.piecewisePolynomials (qdegree i) n) M) → ℕ)
    (cutoff : ℕ) (hgradeMax : ∀ z, grade z < cutoff+L)
    {Cenergy ρ qrate τ : ℝ} {k : ℕ}
    (hC : 0 ≤ Cenergy) (hρ : 0 < ρ) (hq : 0 < qrate)
    (hq1 : qrate < 1) (hρq : ρ < qrate) (hτ : 0 ≤ τ)
    (htrunc : ∀ t : BrownianCubeAnchor d,
      ‖tensorKernelFamily a₀ ha₀ t -
        gradedPolynomialTensorProjectedKernel qdegree M a₀ ha₀ t‖ ≤ τ)
    (hgradeEnergy : ∀ (n : ℕ) (t : BrownianCubeAnchor d),
      (∑ z : {z : (∀ i : Fin d, GradedFrameIndex (fun m =>
          AlignmentFractionalPolynomialSpaces.piecewisePolynomials (qdegree i) m) M) //
            grade z = n},
        ⟪tensorKernelFamily a₀ ha₀ t,
          polynomialTensorGradedFrame qdegree M z.1⟫^2) ≤
        Cenergy*((n+1:ℕ):ℝ)^k*ρ^n)
    (D : ℕ) (hD : 0 < D)
    (hlow : Fintype.card {z : (∀ i : Fin d, GradedFrameIndex (fun m =>
      AlignmentFractionalPolynomialSpaces.piecewisePolynomials (qdegree i) m) M) //
        grade z < cutoff} ≤ D)
    {G : Type} [Fintype G]
    (φ : G → C(BrownianCubeAnchor d, ℝ))
    (anchor : G → BrownianCubeAnchor d)
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hosc : ∀ i t, φ i t ≠ 0 →
      ‖tensorKernelFamily a₀ ha₀ t -
        tensorKernelFamily a₀ ha₀ (anchor i)‖ ≤ δ) :
    kolmogorovWidth (Latest.fractionalIntegrationBall a₀)
      (D*Nat.ceil (1+(1-qrate)⁻¹)) ≤
      ENNReal.ofReal (τ + δ + Real.sqrt
        ((4*(10000:ℝ)^2*(Cenergy*((cutoff+1:ℕ):ℝ)^k*ρ^cutoff)*
          Real.log (2*(Fintype.card G:ℝ)+2)/(D:ℝ)) *
          polynomialBudget (ρ/qrate) k)) := by
  have hgradeEnergy' : ∀ (n : ℕ) (t : BrownianCubeAnchor d),
      (∑ z : {z : (∀ i : Fin d, GradedFrameIndex (fun m =>
          AlignmentFractionalPolynomialSpaces.piecewisePolynomials (qdegree i) m) M) //
            grade z = n},
        (finiteOrthonormalCoordinates (polynomialTensorGradedFrame qdegree M)
          (tensorKernelFamily a₀ ha₀ t) z.1)^2) ≤
        Cenergy*((n+1:ℕ):ℝ)^k*ρ^n := by
    intro n t
    simpa [finiteOrthonormalCoordinates, real_inner_comm] using hgradeEnergy n t
  have htrunc' : ∀ t : BrownianCubeAnchor d,
      ‖tensorKernelFamily a₀ ha₀ t -
        finiteOrthonormalProjection (polynomialTensorGradedFrame qdegree M)
          (tensorKernelFamily a₀ ha₀ t)‖ ≤ τ := by
    intro t
    rw [polynomialGradedFrame_projection_eq_projectedKernel qdegree M a₀ ha₀ t]
    exact htrunc t
  exact fractional_tensor_RL_width_of_grade_energy a₀ ha₀
    (polynomialTensorGradedFrame qdegree M)
    (polynomialTensorGradedFrame_orthonormal qdegree M)
    grade cutoff hgradeMax hC hρ hq hq1 hρq hτ htrunc' hgradeEnergy'
    D hD hlow φ anchor hφ hsum hδ hosc

/-- Concrete cube-grid version of the natural-grade width bridge. The
partition of unity and its mesh error are constructed internally from the
actual Holder modulus of the RL kernel feature. -/
theorem fractional_tensor_RL_grid_width_of_grade_energy
    {d L Ht : ℕ} {I : Type} [Fintype I]
    (a₀ : Fin d → ℝ) (ha₀ : ∀ i, 1/2 < a₀ i)
    (e : I → UnitCubeL2 d) (he : Orthonormal ℝ e)
    (grade : I → ℕ) (cutoff : ℕ)
    (hgradeMax : ∀ i, grade i < cutoff+L)
    {Cenergy ρ qrate τ Cmesh β : ℝ} {k : ℕ}
    (hCenergy : 0 ≤ Cenergy) (hρ : 0 < ρ) (hq : 0 < qrate)
    (hq1 : qrate < 1) (hρq : ρ < qrate)
    (hτ : 0 ≤ τ)
    (htrunc : ∀ t : BrownianCubeAnchor d,
      ‖tensorKernelFamily a₀ ha₀ t -
        finiteOrthonormalProjection e (tensorKernelFamily a₀ ha₀ t)‖ ≤ τ)
    (hgradeEnergy : ∀ (n : ℕ) (t : BrownianCubeAnchor d),
      (∑ i : {i : I // grade i = n},
        (finiteOrthonormalCoordinates e (tensorKernelFamily a₀ ha₀ t) i.1)^2) ≤
          Cenergy*((n+1:ℕ):ℝ)^k*ρ^n)
    (D : ℕ) (hD : 0 < D)
    (hlow : Fintype.card {i : I // grade i < cutoff} ≤ D)
    (hCmesh : 0 ≤ Cmesh) (hβ : 0 < β)
    (hholder : ∀ x y : BrownianCubeAnchor d,
      ‖tensorKernelFamily a₀ ha₀ x-tensorKernelFamily a₀ ha₀ y‖ ≤
        Cmesh*(dist x y)^β) :
    kolmogorovWidth (Latest.fractionalIntegrationBall a₀)
      (D*Nat.ceil (1+(1-qrate)⁻¹)) ≤
      ENNReal.ofReal (τ + Cmesh*(2*((2:ℝ)^Ht)⁻¹)^β + Real.sqrt
        ((4*(10000:ℝ)^2*(Cenergy*((cutoff+1:ℕ):ℝ)^k*ρ^cutoff)*
          Real.log (2*(Fintype.card (CubeDyadicGrid d Ht):ℝ)+2)/(D:ℝ)) *
          polynomialBudget (ρ/qrate) k)) := by
  classical
  let δ : ℝ := 2*((2:ℝ)^Ht)⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let U : CubeDyadicGrid d Ht → Set (BrownianCubeAnchor d) :=
    fun j => {x | ∀ i : Fin d, |x.val i-(cubeDyadicAnchor j).val i| < δ}
  have hUopen (j : CubeDyadicGrid d Ht) : IsOpen (U j) := by
    dsimp [U]
    simp only [Set.setOf_forall]
    apply isOpen_iInter_of_finite
    intro i
    have hc : Continuous (fun x : BrownianCubeAnchor d => x.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact isOpen_lt (continuous_abs.comp (hc.sub continuous_const)) continuous_const
  have hcover : (Set.univ : Set (BrownianCubeAnchor d)) ⊆ ⋃ j,U j := by
    intro x hx
    obtain ⟨j,hj⟩ := exists_cubeDyadicAnchor_near Ht x
    apply Set.mem_iUnion.mpr
    refine ⟨j,?_⟩
    intro i
    exact (hj i).trans (by
      dsimp [δ]
      have hp : (0:ℝ)<((2:ℝ)^Ht)⁻¹ := by positivity
      linarith)
  obtain ⟨φ,hφdata⟩ := PartitionOfUnity.exists_isSubordinate
    isClosed_univ U hUopen hcover
  let anchor : CubeDyadicGrid d Ht → BrownianCubeAnchor d := cubeDyadicAnchor
  have hφ : ∀ i t, 0 ≤ φ i t := fun i t => φ.nonneg i t
  have hsum : ∀ t, ∑ i, φ i t = 1 := fun t => partition_sum_one φ t
  have hosc : ∀ i t, φ i t ≠ 0 →
      ‖tensorKernelFamily a₀ ha₀ t-
        tensorKernelFamily a₀ ha₀ (anchor i)‖ ≤ Cmesh*δ^β := by
    intro i t hne
    have hxt : t ∈ U i := hφdata i
      (subset_closure (show t ∈ Function.support (φ i) from hne))
    have hcoord : ∀ j : Fin d, |t.val j-(anchor i).val j| ≤ δ := by
      intro j
      exact (hxt j).le
    have hdist : dist t (anchor i) ≤ δ := by
      rw [Subtype.dist_eq, dist_eq_norm]
      apply (pi_norm_le_iff_of_nonneg hδ.le).2
      intro j
      rw [Real.norm_eq_abs]
      exact hcoord j
    calc
      _ ≤ Cmesh*(dist t (anchor i))^β := hholder t (anchor i)
      _ ≤ Cmesh*δ^β := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (dist_nonneg) hdist hβ.le) hCmesh
      _ = Cmesh*δ^β := rfl
  have hmesh : 0 ≤ Cmesh*δ^β :=
    mul_nonneg hCmesh (Real.rpow_nonneg hδ.le _)
  simpa only [δ] using fractional_tensor_RL_width_of_grade_energy
    a₀ ha₀ e he grade cutoff hgradeMax hCenergy hρ hq hq1 hρq hτ htrunc
    hgradeEnergy D hD hlow φ anchor hφ hsum hmesh hosc

/-- Concrete cube-grid width theorem for the actual anisotropic polynomial
frame and its true tensor RL coefficient energies. -/
theorem polynomial_fractional_tensor_RL_grid_width_of_grade_energy
    {d M L Ht : ℕ} (qdegree : Fin d → ℕ) (a₀ : Fin d → ℝ)
    (ha₀ : ∀ i, 1/2 < a₀ i)
    (grade : (∀ i : Fin d, GradedFrameIndex (fun n =>
      AlignmentFractionalPolynomialSpaces.piecewisePolynomials (qdegree i) n) M) → ℕ)
    (cutoff : ℕ) (hgradeMax : ∀ z, grade z < cutoff+L)
    {Cenergy ρ qrate τ Cmesh β : ℝ} {k : ℕ}
    (hCenergy : 0 ≤ Cenergy) (hρ : 0 < ρ) (hq : 0 < qrate)
    (hq1 : qrate < 1) (hρq : ρ < qrate) (hτ : 0 ≤ τ)
    (htrunc : ∀ t : BrownianCubeAnchor d,
      ‖tensorKernelFamily a₀ ha₀ t -
        gradedPolynomialTensorProjectedKernel qdegree M a₀ ha₀ t‖ ≤ τ)
    (hgradeEnergy : ∀ (n : ℕ) (t : BrownianCubeAnchor d),
      (∑ z : {z : (∀ i : Fin d, GradedFrameIndex (fun m =>
          AlignmentFractionalPolynomialSpaces.piecewisePolynomials (qdegree i) m) M) //
            grade z = n},
        ⟪tensorKernelFamily a₀ ha₀ t,
          polynomialTensorGradedFrame qdegree M z.1⟫^2) ≤
        Cenergy*((n+1:ℕ):ℝ)^k*ρ^n)
    (D : ℕ) (hD : 0 < D)
    (hlow : Fintype.card {z : (∀ i : Fin d, GradedFrameIndex (fun m =>
      AlignmentFractionalPolynomialSpaces.piecewisePolynomials (qdegree i) m) M) //
        grade z < cutoff} ≤ D)
    (hCmesh : 0 ≤ Cmesh) (hβ : 0 < β)
    (hholder : ∀ x y : BrownianCubeAnchor d,
      ‖tensorKernelFamily a₀ ha₀ x-tensorKernelFamily a₀ ha₀ y‖ ≤
        Cmesh*(dist x y)^β) :
    kolmogorovWidth (Latest.fractionalIntegrationBall a₀)
      (D*Nat.ceil (1+(1-qrate)⁻¹)) ≤
      ENNReal.ofReal (τ + Cmesh*(2*((2:ℝ)^Ht)⁻¹)^β + Real.sqrt
        ((4*(10000:ℝ)^2*(Cenergy*((cutoff+1:ℕ):ℝ)^k*ρ^cutoff)*
          Real.log (2*(Fintype.card (CubeDyadicGrid d Ht):ℝ)+2)/(D:ℝ)) *
          polynomialBudget (ρ/qrate) k)) := by
  have henergy' : ∀ (n : ℕ) (t : BrownianCubeAnchor d),
      (∑ z : {z : (∀ i : Fin d, GradedFrameIndex (fun m =>
          AlignmentFractionalPolynomialSpaces.piecewisePolynomials (qdegree i) m) M) //
            grade z = n},
        (finiteOrthonormalCoordinates (polynomialTensorGradedFrame qdegree M)
          (tensorKernelFamily a₀ ha₀ t) z.1)^2) ≤
        Cenergy*((n+1:ℕ):ℝ)^k*ρ^n := by
    intro n t
    simpa [finiteOrthonormalCoordinates, real_inner_comm] using hgradeEnergy n t
  have htrunc' : ∀ t : BrownianCubeAnchor d,
      ‖tensorKernelFamily a₀ ha₀ t -
        finiteOrthonormalProjection (polynomialTensorGradedFrame qdegree M)
          (tensorKernelFamily a₀ ha₀ t)‖ ≤ τ := by
    intro t
    rw [polynomialGradedFrame_projection_eq_projectedKernel qdegree M a₀ ha₀ t]
    exact htrunc t
  exact fractional_tensor_RL_grid_width_of_grade_energy a₀ ha₀
    (polynomialTensorGradedFrame qdegree M)
    (polynomialTensorGradedFrame_orthonormal qdegree M)
    grade cutoff hgradeMax hCenergy hρ hq hq1 hρq hτ htrunc' henergy'
    D hD hlow hCmesh hβ hholder

/-- Every coordinate grade in the finite polynomial tensor frame is bounded
by its truncation depth, and hence the weighted floor grade has an explicit
finite cutoff whenever the order coefficients are nonnegative. -/
theorem polynomial_tensor_weightedGrade_lt_cutoff
    {d M L : ℕ} (qdegree : Fin d → ℕ) (α : Fin d → ℝ) (r : ℝ)
    (hr : 0 < r) (hα : ∀ i, 0 ≤ α i)
    (hcut : (M:ℝ) * (∑ i : Fin d, α i / r) < L) :
    ∀ z : (∀ i : Fin d, GradedFrameIndex (fun n =>
      AlignmentFractionalPolynomialSpaces.piecewisePolynomials (qdegree i) n) M),
      weightedProfileGrade α r (profileNat (fun i => (z i).1)) < L := by
  intro z
  change Nat.floor (∑ i : Fin d, (α i / r) * ((z i).1.val:ℝ)) < L
  have hgrade (i : Fin d) : ((z i).1.val : ℝ) ≤ M := by
    exact_mod_cast (Nat.lt_succ_iff.mp (z i).1.isLt)
  have hterm (i : Fin d) : (α i / r) * ((z i).1.val:ℝ) ≤ (α i / r) * (M:ℝ) :=
    mul_le_mul_of_nonneg_left (hgrade i) (div_nonneg (hα i) hr.le)
  have hsum : (∑ i : Fin d, (α i / r) * ((z i).1.val:ℝ)) ≤
      (M:ℝ) * (∑ i : Fin d, α i / r) := by
    calc
      _ ≤ ∑ i : Fin d, (α i / r) * (M:ℝ) := Finset.sum_le_sum fun i hi => hterm i
      _ = (M:ℝ) * (∑ i : Fin d, α i / r) := by
        calc
          _ = ∑ i : Fin d, (M:ℝ) * (α i / r) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = _ := by rw [Finset.mul_sum]
  have hsum' : (∑ i : Fin d, (α i / r) * ((z i).1.val:ℝ)) < (L:ℝ) :=
    hsum.trans_lt hcut
  have hfloor : Nat.floor (∑ i : Fin d, (α i / r) * ((z i).1.val:ℝ)) < L := by
    have hfloorle := Nat.floor_le (show 0 ≤ ∑ i : Fin d,
      (α i / r) * ((z i).1.val:ℝ) from Finset.sum_nonneg fun i hi =>
        mul_nonneg (div_nonneg (hα i) hr.le) (by positivity))
    exact_mod_cast (lt_of_le_of_lt hfloorle hsum')
  exact hfloor

/-- Polynomial nested frames inherit the optimal dyadic cardinal growth used
by the weighted low-fiber estimate. -/
theorem polynomial_gradeIndex_card_le (q : ℕ) (hq : 0 < q) (g : ℕ) :
    Fintype.card (GradeIndex (fun n =>
      AlignmentFractionalPolynomialSpaces.piecewisePolynomials q n) g) ≤ q * 2^g := by
  apply gradeIndex_card_le_of_growth
    (U := fun n => AlignmentFractionalPolynomialSpaces.piecewisePolynomials q n)
  · intro n
    exact AlignmentFractionalPolynomialSpaces.piecewisePolynomials_finiteDimensional q n
  · intro n
    exact AlignmentFractionalPolynomialSpaces.piecewisePolynomials_le_succ q n
  · intro n
    exact AlignmentFractionalPolynomialSpaces.piecewisePolynomials_finrank_le q n

/-- Cumulative low-grade dimension bound for a tensor polynomial frame with
possibly different degree parameters in each coordinate. -/
theorem polynomial_tensor_weightedLowFiber_card_le_minimumMultiplicity
    {ν e M n : ℕ} {r : ℝ} (hr : 0 < r) (hν : 0 < ν)
    (α : Fin (ν+e) → ℝ) (degree : Fin (ν+e) → ℕ)
    (hdegree : ∀ i, 0 < degree i)
    (hm : Latest.minimumMultiplicity α r ν) :
    let hcard : (minimumIndexSet α r).card = ν := by
      unfold Latest.minimumMultiplicity at hm
      simpa [minimumIndexSet] using hm.2
    let ep := minimumCoordinatePermutation α r hcard
    let w : Fin e → ℝ := fun j => α (ep (Fin.natAdd ν j)) / r
    (Fintype.card {z : (∀ i : Fin (ν+e), GradedFrameIndex (fun m =>
      AlignmentFractionalPolynomialSpaces.piecewisePolynomials (degree i) m) M) //
        weightedProfileGrade α r (profileNat (fun i => (z i).1)) ≤ n} : ℝ) ≤
      (∏ i : Fin (ν+e), (degree i : ℝ)) *
        (Real.rpow 2 (n + 2) * (((n+1:ℕ):ℝ)^(ν-1) *
          ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹)) := by
  classical
  have hA : ∀ i g, Fintype.card (GradeIndex (fun m =>
      AlignmentFractionalPolynomialSpaces.piecewisePolynomials (degree i) m) g) ≤
      degree i * 2^g := by
    intro i g
    exact polynomial_gradeIndex_card_le (degree i) (hdegree i) g
  simpa using productGrade_weightedLowFiber_card_le_minimumMultiplicity
    (hr := hr) (hν := hν)
    (U := fun i m => AlignmentFractionalPolynomialSpaces.piecewisePolynomials
      (degree i) m) (α := α) (A := degree) hA hm

/-- Uniform low-rank multiplier for polynomial frames. It converts the
weighted profile count into the active hyperbolic layer count, with a fixed
multiplier depending only on the polynomial degrees and inactive-order
geometric factor. -/
theorem polynomial_tensor_weightedLowFiber_layer_multiple
    {ν e : ℕ} (hν : 2 ≤ ν) {r : ℝ} (hr : 0 < r)
    (α : Fin (ν+e) → ℝ) (degree : Fin (ν+e) → ℕ)
    (hdegree : ∀ i, 0 < degree i)
    (hm : Latest.minimumMultiplicity α r ν) :
    ∃ A : ℕ, 0 < A ∧ ∀ M n : ℕ,
        Fintype.card {z : (∀ i : Fin (ν+e), GradedFrameIndex (fun m =>
          AlignmentFractionalPolynomialSpaces.piecewisePolynomials (degree i) m) M) //
            weightedProfileGrade α r (profileNat (fun i => (z i).1)) ≤ n} ≤
          A * Fintype.card (LayerIndex ν n) := by
  classical
  let hcard : (minimumIndexSet α r).card = ν := by
    unfold Latest.minimumMultiplicity at hm
    simpa [minimumIndexSet] using hm.2
  let ep := minimumCoordinatePermutation α r hcard
  let w : Fin e → ℝ := fun j => α (ep (Fin.natAdd ν j)) / r
  let G : ℝ := ∏ j : Fin e, (1-Real.rpow 2 (-(w j-1)))⁻¹
  let K : ℝ := (∏ i : Fin (ν+e), (degree i : ℝ))*G
  let A : ℕ := Nat.ceil (4*K*(Nat.factorial (ν-1):ℝ)) + 1
  have hw : ∀ j, 1 < w j := by
    intro j
    dsimp [w]
    rw [one_lt_div₀ hr]
    exact minimumCoordinatePermutation_inactive_lt α r hcard hm.1 j
  have hG : 0 < G := by
    dsimp [G]
    apply Finset.prod_pos
    intro j hj
    have hp : Real.rpow 2 (-(w j-1)) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith [hw j])
    exact inv_pos.mpr (sub_pos.mpr hp)
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (Finset.prod_pos fun i hi => by exact_mod_cast hdegree i) hG
  have hA : 0 < A := by dsimp [A]; omega
  refine ⟨A,hA,?_⟩
  intro M n
  have hlow := polynomial_tensor_weightedLowFiber_card_le_minimumMultiplicity
    (M := M) (n := n) hr (by omega : 0 < ν) α degree hdegree hm
  have hpoly : ((n+1:ℕ):ℝ)^(ν-1) ≤
      (Nat.factorial (ν-1):ℝ) * (hyperbolicCount ν n:ℝ) := by
    have hh := hyperbolicCount_lower_shift (d:=ν) (by omega : 1≤ν) n
    have hf : 0 < (Nat.factorial (ν-1):ℝ) := by positivity
    simpa [mul_comm] using (div_le_iff₀ hf).mp hh
  have hceil : 4*K*(Nat.factorial (ν-1):ℝ) ≤ (A:ℝ) := by
    dsimp [A]
    have hc := Nat.le_ceil (4*K*(Nat.factorial (ν-1):ℝ))
    have hc' : (Nat.ceil (4*K*(Nat.factorial (ν-1):ℝ)):ℝ) ≤
        (Nat.ceil (4*K*(Nat.factorial (ν-1):ℝ)) + 1:ℕ) := by exact_mod_cast (by omega)
    exact le_trans hc hc'
  have hcardLayer : (Fintype.card (LayerIndex ν n):ℝ) =
      2^n*(hyperbolicCount ν n:ℝ) := by
    rw [layerIndex_card ν n (by omega : 0<ν)]
    simp [hyperbolicCount]
  have hboundReal :
      (Fintype.card {z : (∀ i : Fin (ν+e), GradedFrameIndex (fun m =>
        AlignmentFractionalPolynomialSpaces.piecewisePolynomials (degree i) m) M) //
          weightedProfileGrade α r (profileNat (fun i => (z i).1)) ≤ n} : ℝ) ≤
        (A:ℝ)*(Fintype.card (LayerIndex ν n):ℝ) := by
    calc
      _ ≤ (∏ i : Fin (ν+e), (degree i:ℝ)) *
          (Real.rpow 2 (n+2) * (((n+1:ℕ):ℝ)^(ν-1)*G)) := hlow
      _ ≤ (4*K*(Nat.factorial (ν-1):ℝ)) *
          (2^n*(hyperbolicCount ν n:ℝ)) := by
            have hrpow : Real.rpow 2 ((n:ℝ)+2) = 4*(2:ℝ)^n := by
              calc
                Real.rpow 2 ((n:ℝ)+2) = Real.rpow 2 (n:ℝ)*Real.rpow 2 2 := by
                  exact Real.rpow_add (by norm_num : (0:ℝ) < 2) _ _
                _ = 4*(2:ℝ)^n := by
                  have hn : (2:ℝ)^n = Real.rpow 2 (n:ℝ) :=
                    (Real.rpow_natCast (2:ℝ) n).symm
                  rw [← hn]
                  norm_num
                  ring
            calc
              _ ≤ (∏ i : Fin (ν+e), (degree i:ℝ)) *
                  (4*(2:ℝ)^n*(((n+1:ℕ):ℝ)^(ν-1)*G)) := by
                    rw [hrpow]
                    
              _ = (4*K*(2:ℝ)^n)*((n+1:ℕ):ℝ)^(ν-1) := by
                    ring
              _ ≤ (4*K*(2:ℝ)^n)*((Nat.factorial (ν-1):ℝ)*
                  (hyperbolicCount ν n:ℝ)) :=
                    mul_le_mul_of_nonneg_left hpoly
                      (mul_nonneg (mul_nonneg (by norm_num) hK.le) (by positivity))
              _ = (4*K*(Nat.factorial (ν-1):ℝ)) *
                    ((2:ℝ)^n*(hyperbolicCount ν n:ℝ)) := by ring
      _ ≤ (A:ℝ)*(Fintype.card (LayerIndex ν n):ℝ) := by
            rw [hcardLayer]
            apply mul_le_mul_of_nonneg_right hceil
            exact mul_nonneg (by positivity)
              (le_of_lt (hyperbolicCount_pos (d:=ν) (n:=n) (by omega)))
  exact_mod_cast hboundReal

/-- The genuine anisotropic polynomial tensor feature admits one fixed
coordinatewise polynomial frame whose exact weighted grade energies obey the
active-order exponent uniformly in truncation depth, grade, and anchor. -/
theorem exists_polynomial_tensor_weighted_grade_energy_data
    {ν e : ℕ} (hν : 0 < ν) (r : ℝ) (hr : 1/2 < r)
    (α : Fin (ν+e) → ℝ) (hα : ∀ i, 1/2 < α i)
    (hm : Latest.minimumMultiplicity α r ν) :
    ∃ qdegree : Fin (ν+e) → ℕ, (∀ i, 0 < qdegree i) ∧
      ∃ Cenergy : ℝ, 0 < Cenergy ∧
      ∀ M n : ℕ, ∀ t : BrownianCubeAnchor (ν+e),
        (∑ z : {z : (∀ i : Fin (ν+e), GradedFrameIndex (fun m =>
          AlignmentFractionalPolynomialSpaces.piecewisePolynomials (qdegree i) m) M) //
            weightedProfileGrade α r (profileNat (fun i => (z i).1)) = n},
          ⟪tensorKernelFamily α hα t, polynomialTensorGradedFrame qdegree M z.1⟫^2) ≤
        Cenergy * (((n+1:ℕ):ℝ)^(ν-1) *
          (Real.rpow 2 (-(2*r-1)))^n) := by
  classical
  obtain ⟨ep,w,qdegree,A,Cenergy,hw,hmin,hin,hdegree,hA,hCenergy,henergy⟩ :=
    AlignmentFractionalPolynomialPublicEnergy.polynomialTensor_weightedGrade_energy_public_frame_le
      hν r hr α hα hm
  exact ⟨qdegree,hdegree,Cenergy,hCenergy,henergy⟩

/-- For arbitrary anisotropic orders with minimum multiplicity `ν`, the
actual tensor RL integration ball has the sharp dyadic Kolmogorov-width
upper bound. The finite polynomial frame supplies the grade energy, while
the cube-grid KGG argument and weighted layer count supply the rank profile. -/
theorem polynomial_fractional_tensor_RL_dyadic_width
    {ν e : ℕ} (hν : 2 ≤ ν) {r : ℝ} (hr : 1/2 < r)
    (α : Fin (ν+e) → ℝ) (hα : ∀ i, 1/2 < α i)
    (hm : Latest.minimumMultiplicity α r ν) :
    ∃ A : ℕ, 0 < A ∧ ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ,
      kolmogorovWidth (Latest.fractionalIntegrationBall α)
        (A * Fintype.card (LayerIndex ν n)) ≤
          ENNReal.ofReal (B*(2:ℝ)^(-r*n)*Real.sqrt (n+1:ℝ)) := by
  classical
  let d := ν+e
  have hd : 2 ≤ d := by dsimp [d]; omega
  have hrpos : 0 < r := by linarith
  obtain ⟨qdegree,hqdegree,Cenergy,hCenergy,hgradeEnergy⟩ :=
    exists_polynomial_tensor_weighted_grade_energy_data
      (by omega : 0 < ν) r hr α hα hm
  obtain ⟨Cproj,γ,hCproj,hγ,hres⟩ :=
    gradedPolynomialTensorProjectedKernel_uniform_rate (by omega : 0<d) qdegree hqdegree
      α hα r hr hm.1
  let bproj : ℝ := (2:ℝ)^(-γ)
  have hbproj : 0 < bproj := by dsimp [bproj]; positivity
  have hbproj1 : bproj < 1 := by
    dsimp [bproj]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  obtain ⟨Cmesh,hCmeshPos,hholder⟩ :=
    tensorKernelFamily_holder (by omega : 0<d) α hα r hr hm.1
  let β := tensorHolderExponent r
  have hβ : 0 < β := by
    dsimp [β,tensorHolderExponent]
    exact lt_min (by linarith) (by norm_num)
  let ρ : ℝ := (2:ℝ)^(-(2*r-1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by
    dsimp [ρ]
    apply Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
    linarith
  let qrate : ℝ := (ρ+1)/2
  have hqrate : 0 < qrate := by dsimp [qrate]; linarith
  have hqrate1 : qrate < 1 := by dsimp [qrate]; linarith
  have hρq : ρ < qrate := by dsimp [qrate]; linarith
  have hρeq : ρ = (2:ℝ)^(-(2*r-1)) := rfl
  let k : ℕ := ν-1
  have hk : k = ν-1 := rfl
  obtain ⟨Cdim,hCdim,hlowall⟩ :=
    polynomial_tensor_weightedLowFiber_layer_multiple hν hrpos α qdegree hqdegree hm
  have hδ : 0 < (1/(Nat.factorial (ν-1):ℝ)) := by positivity
  have hrankLower : ∀ n : ℕ,
      (1/(Nat.factorial (ν-1):ℝ))*(2:ℝ)^n*((n+1:ℕ):ℝ)^k ≤
        (Cdim:ℝ)*(Fintype.card (LayerIndex ν n):ℝ) := by
    intro n
    have hcount := hyperbolicCount_lower_shift (d:=ν) (by omega : 1≤ν) n
    have hfac : 0 < (Nat.factorial (ν-1):ℝ) := by positivity
    have hdiv : ((n+1:ℕ):ℝ)^k/(Nat.factorial (ν-1):ℝ) ≤
        (hyperbolicCount ν n:ℝ) := by simpa [k] using hcount
    have hcard : (Fintype.card (LayerIndex ν n):ℝ) =
        (2:ℝ)^n*(hyperbolicCount ν n:ℝ) := by
      rw [layerIndex_card ν n (by omega : 0<ν)]
      simp [hyperbolicCount]
    have hCdim1 : 1 ≤ (Cdim:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hCdim)
    rw [hcard]
    calc
      _ = (2:ℝ)^n *
          (((n+1:ℕ):ℝ)^k/(Nat.factorial (ν-1):ℝ)) := by ring
      _ ≤ (2:ℝ)^n*(hyperbolicCount ν n:ℝ) :=
          mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ ≤ (Cdim:ℝ)*((2:ℝ)^n*(hyperbolicCount ν n:ℝ)) := by
          have hnonneg : 0 ≤ (2:ℝ)^n*(hyperbolicCount ν n:ℝ) :=
            mul_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)
          nlinarith
  have hlogGrid : ∀ H : ℕ,
      Real.log (2*(Fintype.card (CubeDyadicGrid d H):ℝ)+2) ≤
        ((d:ℝ)+2)*((H+1:ℕ):ℝ) := by
    intro H
    simpa [Nat.cast_add] using cubeDyadicGrid_log_bound d H
  obtain ⟨Kmesh,hKmesh,hmesh⟩ :=
    AlignmentFractionalSharpBudgets.exists_linear_depth_mesh_budget hβ hrpos
  have hprofile : ∀ n M H τ, 1 ≤ M → 0 ≤ τ → Cproj*bproj^M ≤ τ →
      kolmogorovWidth (Latest.fractionalIntegrationBall α)
        (Cdim*(Nat.ceil (1+(1-qrate)⁻¹))*Fintype.card (LayerIndex ν n)) ≤
       ENNReal.ofReal (τ + Cmesh*(2*((2:ℝ)^H)⁻¹)^β +
        Real.sqrt ((4*(10000:ℝ)^2*((n+2:ℕ):ℝ)^k*ρ^(n+1)*
          Real.log (2*(Fintype.card (CubeDyadicGrid d H):ℝ)+2)/
            ((Cdim:ℝ)*(Fintype.card (LayerIndex ν n):ℝ)))*
          (Cenergy*polynomialBudget (ρ/qrate) k))) := by
    intro n M H τ hM hτ hsmall
    obtain ⟨Acoord,hAcoord⟩ := exists_nat_gt
      (∑ i : Fin (ν+e), α i/r)
    have hAcoordNonneg : 0 ≤ (∑ i : Fin (ν+e), α i/r) := by
      apply Finset.sum_nonneg
      intro i hi
      exact div_nonneg (le_trans (le_of_lt hrpos) (hm.1 i)) hrpos.le
    let L : ℕ := M*Acoord+1
    have hcut : (M:ℝ)*(∑ i : Fin (ν+e), α i/r) < L := by
      dsimp [L]
      have hsum : (∑ i : Fin (ν+e), α i/r) < (Acoord:ℝ) := by exact_mod_cast hAcoord
      have hmterm : (M:ℝ)*(∑ i : Fin (ν+e), α i/r) ≤ (M:ℝ)*(Acoord:ℝ) :=
        mul_le_mul_of_nonneg_left hsum.le (by positivity)
      have : (M:ℝ)*(Acoord:ℝ) < (M*Acoord+1:ℕ) := by
        have hcast : (M*Acoord+1:ℕ) = (M:ℝ)*(Acoord:ℝ)+1 := by push_cast; ring
        rw [hcast]
        linarith
      exact lt_of_le_of_lt hmterm this
    have hgrade : ∀ z : (∀ i : Fin (ν+e), GradedFrameIndex
        (fun m => piecewisePolynomials (qdegree i) m) M),
        weightedProfileGrade α r (profileNat (fun i => (z i).1)) < L :=
      polynomial_tensor_weightedGrade_lt_cutoff qdegree α r hrpos
        (fun i => le_trans (le_of_lt hrpos) (hm.1 i)) hcut
    have hgradeMax : ∀ z : (∀ i : Fin (ν+e), GradedFrameIndex
        (fun m => piecewisePolynomials (qdegree i) m) M), weightedProfileGrade α r
        (profileNat (fun i => (z i).1)) < (n+1)+L := by
      intro z
      exact lt_of_lt_of_le (hgrade z) (by omega)
    let grade := fun z : (∀ i : Fin (ν+e), GradedFrameIndex
        (fun m => piecewisePolynomials (qdegree i) m) M) =>
          weightedProfileGrade α r (profileNat (fun i => (z i).1))
    have hlow : Fintype.card {z : (∀ i : Fin (ν+e), GradedFrameIndex
        (fun m => piecewisePolynomials (qdegree i) m) M) // grade z < n+1} ≤
          Cdim*Fintype.card (LayerIndex ν n) := by
      simpa [grade] using hlowall M n
    have hD : 0 < Cdim*Fintype.card (LayerIndex ν n) := by
      apply Nat.mul_pos hCdim
      rw [layerIndex_card ν n (by omega : 0<ν)]
      apply Nat.mul_pos
      · positivity
      · exact Nat.choose_pos (by omega)
    have hEnergy : ∀ (g : ℕ) (t : BrownianCubeAnchor (ν+e)),
        (∑ z : {z : (∀ i : Fin (ν+e), GradedFrameIndex
          (fun m => piecewisePolynomials (qdegree i) m) M) // grade z = g},
          ⟪tensorKernelFamily α hα t, polynomialTensorGradedFrame qdegree M z.1⟫^2) ≤
          Cenergy*((g+1:ℕ):ℝ)^k*ρ^g := by
      intro g t
      simpa [grade,k,ρ,mul_assoc] using hgradeEnergy M g t
    have htrunc : ∀ t : BrownianCubeAnchor (ν+e),
        ‖tensorKernelFamily α hα t -
          gradedPolynomialTensorProjectedKernel qdegree M α hα t‖ ≤ τ := by
      intro t
      have hbound := hres M hM t
      exact hbound.trans (by simpa [bproj] using hsmall)
    have hmeshHolder : ∀ x y : BrownianCubeAnchor (ν+e),
        ‖tensorKernelFamily α hα x-tensorKernelFamily α hα y‖ ≤
          Cmesh*(dist x y)^β := by
      simpa [β] using hholder
    have hwidth := polynomial_fractional_tensor_RL_grid_width_of_grade_energy
      (Ht:=H) qdegree α hα grade (n+1) hgradeMax hCenergy.le hρ hqrate hqrate1 hρq hτ
      htrunc hEnergy (Cdim*Fintype.card (LayerIndex ν n)) hD hlow
      hCmeshPos.le hβ hmeshHolder
    have hradEq :
        (4*(10000:ℝ)^2*(Cenergy*((n+1+1:ℕ):ℝ)^k*ρ^(n+1))*
          Real.log (2*(Fintype.card (CubeDyadicGrid d H):ℝ)+2) /
            ((Cdim*Fintype.card (LayerIndex ν n):ℕ):ℝ) *
          polynomialBudget (ρ/qrate) k) =
        (4*(10000:ℝ)^2*((n+1+1:ℕ):ℝ)^k*ρ^(n+1)*
          Real.log (2*(Fintype.card (CubeDyadicGrid d H):ℝ)+2) /
            ((Cdim*Fintype.card (LayerIndex ν n):ℕ):ℝ) *
          (Cenergy*polynomialBudget (ρ/qrate) k)) := by ring
    rw [hradEq] at hwidth
    simpa [d,grade,ρ,qrate,k,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,
      mul_assoc,add_assoc,add_comm,add_left_comm] using hwidth
  exact BrownianSharp.AlignmentFractionalGenericKGGWidth.dyadic_width_of_KGG_profile
    (K:=Latest.fractionalIntegrationBall α) (Cproj:=Cproj) (bproj:=bproj)
    (Cmesh:=Cmesh) (β:=β) (r:=r) (ρ:=ρ) (qrate:=qrate)
    (δ:=1/(Nat.factorial (ν-1):ℝ)) (Llog:=(d:ℝ)+2) (Cenergy:=Cenergy)
    (Cdim:=Cdim) (k:=k) hd hν hCproj hbproj hbproj1
    hCmeshPos.le hCenergy.le hβ hrpos hρ hρ1 hqrate hqrate1 hρq hρeq hk hCdim hδ
    (by positivity) hrankLower hlogGrid ⟨Kmesh,hKmesh,hmesh⟩ hprofile

end BrownianSharp.AlignmentFractionalGradedPolynomialWidth
