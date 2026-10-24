import BrownianSharp.AlignmentNestedProjectionTensorApproximation
import BrownianSharp.AlignmentFractionalPolynomialConvergence
import BrownianSharp.AlignmentFractionalPolynomialSpaces
import BrownianSharp.AlignmentFractionalTensorHolder

/-! Uniform finite-rank approximation of the actual anisotropic RL tensor
kernel by tensor products of nested piecewise-polynomial source spaces. -/

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory
open Filter
open scoped Topology
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalPolynomialTensorApproximation

open BrownianSharp
open BrownianSharp.AlignmentNestedProjectionBasis
open BrownianSharp.AlignmentNestedProjectionFrame
open BrownianSharp.AlignmentNestedProjectionTensor
open BrownianSharp.AlignmentNestedProjectionTensorApproximation
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalTensor
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalPolynomialConvergence
open BrownianSharp.AlignmentFractionalTensorHolder
open BrownianSharp.AlignmentL2TensorProduct
open HaarQuarter
open BrownianSharp.CameronMartin

abbrev AxisL2 := AlignmentFractionalL2.UnitL2

private def polynomialFiltration {d : ℕ} (q : Fin d → ℕ) :
    Fin d → ℕ → Submodule ℝ AxisL2 :=
  fun i n => piecewisePolynomials (q i) n

private theorem polynomialFiltration_finite {d : ℕ} (q : Fin d → ℕ) :
    ∀ i n, FiniteDimensional ℝ ↥(polynomialFiltration q i n) := by
  intro i n
  exact piecewisePolynomials_finiteDimensional (q i) n

private theorem polynomialFiltration_nested {d : ℕ} (q : Fin d → ℕ) :
    ∀ i n, polynomialFiltration q i n ≤ polynomialFiltration q i (n+1) := by
  intro i n
  exact piecewisePolynomials_le_succ (q i) n

/-- The actual tensor RL kernel projected onto the tensor product of the
coordinatewise polynomial spaces of degree less than `q i`, at common depth
`N`. Its coefficient span is the finite tensor frame from the nested
filtrations. -/
noncomputable def polynomialTensorProjectedKernel {d : ℕ}
    (q : Fin d → ℕ) (N : ℕ) (a : Fin d → ℝ)
    (ha : ∀ i, 1/2 < a i) : C(BrownianCubeAnchor d, UnitCubeL2 d) :=
  tensorFrameProjectedKernel
    (fun i => nestedFrame (polynomialFiltration q i) (polynomialFiltration_finite q i) N)
    a ha

private theorem polynomialTensorProjectedKernel_eq_frameProjection
    {d : ℕ} (q : Fin d → ℕ) (N : ℕ) (a : Fin d → ℝ)
    (ha : ∀ i, 1/2 < a i) (t : BrownianCubeAnchor d) :
    polynomialTensorProjectedKernel q N a ha t =
      (Submodule.span ℝ (Set.range (tensorFrame
        (fun i => nestedFrame (polynomialFiltration q i)
          (polynomialFiltration_finite q i) N)))).starProjection
        (tensorKernelFamily a ha t) := by
  let e : ∀ i, FrameIndex (polynomialFiltration q i) N → AxisL2 :=
    fun i => nestedFrame (polynomialFiltration q i) (polynomialFiltration_finite q i) N
  have he : ∀ i, Orthonormal ℝ (e i) := fun i =>
    nestedFrame_orthonormal (polynomialFiltration q i)
      (polynomialFiltration_finite q i) (polynomialFiltration_nested q i) N
  change tensorFrameProjectedKernel e a ha t = _
  rw [tensorFrameProjectedKernel_eq_sum e he a ha t,
    tensorFrame_span_starProjection_eq_sum e he (tensorKernelFamily a ha t)]

/-- Orthogonal projection is contractive, so the finite polynomial tensor
feature inherits the same Holder modulus as the actual tensor RL feature. -/
theorem polynomialTensorProjectedKernel_holder {d : ℕ} (hd : 0 < d)
    (q : Fin d → ℕ) (hq : ∀ i, 0 < q i)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i)
    (r : ℝ) (hr : 1/2 < r) (hra : ∀ i, r ≤ a i)
    (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x y : BrownianCubeAnchor d,
        ‖polynomialTensorProjectedKernel q N a ha x -
          polynomialTensorProjectedKernel q N a ha y‖ ≤
            C * (dist x y)^(tensorHolderExponent r) := by
  obtain ⟨C,hC,hactual⟩ := tensorKernelFamily_holder hd a ha r hr hra
  refine ⟨C,hC,?_⟩
  intro x y
  rw [polynomialTensorProjectedKernel_eq_frameProjection q N a ha x,
    polynomialTensorProjectedKernel_eq_frameProjection q N a ha y]
  let W : Submodule ℝ (UnitCubeL2 d) := Submodule.span ℝ (Set.range (tensorFrame
    (fun i => nestedFrame (polynomialFiltration q i)
      (polynomialFiltration_finite q i) N)))
  have hproj : ‖W.starProjection‖ ≤ 1 := W.starProjection_norm_le
  calc
    ‖W.starProjection (tensorKernelFamily a ha x) -
        W.starProjection (tensorKernelFamily a ha y)‖ =
        ‖W.starProjection (tensorKernelFamily a ha x - tensorKernelFamily a ha y)‖ := by
          rw [map_sub]
    _ ≤ ‖W.starProjection‖ *
          ‖tensorKernelFamily a ha x - tensorKernelFamily a ha y‖ :=
          W.starProjection.le_opNorm _
    _ ≤ 1 * (C*(dist x y)^(tensorHolderExponent r)) := by
          apply mul_le_mul hproj (hactual x y) (norm_nonneg _) (by norm_num)
    _ = C*(dist x y)^(tensorHolderExponent r) := by ring

private def scalarPolynomialProjectionConstant (a : ℝ) : ℝ :=
  ((Real.Gamma a)⁻¹)^2 * (2 + (2:ℝ)^(2*a-1)/(2*a-1))

private theorem scalarPolynomialProjectionConstant_nonneg {a : ℝ}
    (ha : 1/2 < a) : 0 ≤ scalarPolynomialProjectionConstant a := by
  unfold scalarPolynomialProjectionConstant
  have hden : 0 < 2*a-1 := by linarith
  have hpow : 0 ≤ (2:ℝ)^(2*a-1) := Real.rpow_nonneg (by norm_num) _
  positivity

private theorem inverse_dyadic_rpow (β : ℝ) (N : ℕ) :
    (1/(2:ℝ)^N)^β = ((2:ℝ)^(-β))^N := by
  have hbase : 1/(2:ℝ)^N = (2:ℝ)^(-(N:ℝ)) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]
    simp [one_div]
  rw [hbase,← Real.rpow_mul (by norm_num : (0:ℝ)≤2)]
  rw [show -(N:ℝ)*β=(-β)*(N:ℝ) by ring,
    Real.rpow_mul (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]

private theorem sqrt_pow_eq {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    Real.sqrt (x^N)=(Real.sqrt x)^N := by
  have hsq : (Real.sqrt x)^2=x := Real.sq_sqrt hx
  have hp : x^N=((Real.sqrt x)^N)^2 := by
    calc
      x^N = ((Real.sqrt x)^2)^N := by rw [hsq]
      _ = (Real.sqrt x)^(2*N) := by rw [← pow_mul]
      _ = (Real.sqrt x)^(N*2) := by congr 1 <;> omega
      _ = ((Real.sqrt x)^N)^2 := by rw [pow_mul]
  rw [hp,Real.sqrt_sq_eq_abs,abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg x) N)]

private theorem polynomial_projection_residual_norm_le
    {q : ℕ} (hq : 0 < q) {a : ℝ} (ha : 1/2 < a)
    (N : ℕ) (hN : 1 ≤ N) (t : UnitInterval) :
    ‖translatedUnitKernelFamily a ha t -
      polynomialProjection q N (translatedUnitKernelFamily a ha t)‖ ≤
      Real.sqrt (scalarPolynomialProjectionConstant a *
        (1/(2:ℝ)^N)^(min (2*a-1) 1)) := by
  rw [translatedUnitKernelFamily_eq_kernelVector a t.1 ha t.2.1 t.2.2]
  have h := polynomialProjection_error_norm_sq_le_coarse hq ha t.2.1 t.2.2 hN
  have hnonneg : 0 ≤ scalarPolynomialProjectionConstant a *
      (1/(2:ℝ)^N)^(min (2*a-1) 1) := by
    apply mul_nonneg (scalarPolynomialProjectionConstant_nonneg ha)
    exact Real.rpow_nonneg (by positivity) _
  have hsqrt := Real.sq_sqrt hnonneg
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [hsqrt]
  exact h

/-- At every common dyadic depth, the tensor product of the degree-`q i`
polynomial source projections approximates the actual anisotropic RL kernel.
The rate depends on the least coordinate order, while the coordinate degrees
may be chosen independently. -/
theorem polynomialTensorProjectedKernel_uniform_rate {d : ℕ} (hd : 0 < d)
    (q : Fin d → ℕ) (hq : ∀ i, 0 < q i)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i)
    (r : ℝ) (hr : 1/2 < r) (hra : ∀ i, r ≤ a i) :
    ∃ C γ : ℝ, 0 < C ∧ 0 < γ ∧
      ∀ N : ℕ, 1 ≤ N → ∀ t : BrownianCubeAnchor d,
        ‖tensorKernelFamily a ha t - polynomialTensorProjectedKernel q N a ha t‖ ≤
          C * ((2:ℝ)^(-γ))^N := by
  let β : ℝ := min (2*r-1) 1
  let γ : ℝ := β/2
  let rateBase : ℝ := (2:ℝ)^(-γ)
  let K : ℝ := 1 + ∑ i : Fin d, ‖fullKernelVector (a i) (ha i)‖
  let B : ℝ := (d:ℝ) * K^(d-1)
  let A : ℝ := ∑ i : Fin d, Real.sqrt (scalarPolynomialProjectionConstant (a i))
  have hβ : 0 < β := lt_min (by linarith) (by norm_num)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hroot : Real.sqrt ((2:ℝ)^(-β)) = rateBase := by
    dsimp [rateBase, γ]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  refine ⟨1+B*A,γ,by positivity,hγ,?_⟩
  intro N hN t
  have hbase0 : 0 ≤ 1/(2:ℝ)^N := by positivity
  have hbase1 : 1/(2:ℝ)^N ≤ 1 := by
    apply (div_le_one (by positivity : (0:ℝ)<2^N)).2
    exact one_le_pow₀ (by norm_num)
  have hscalar (i : Fin d) :
      Real.sqrt (scalarPolynomialProjectionConstant (a i) *
        (1/(2:ℝ)^N)^(min (2*a i-1) 1)) ≤
      Real.sqrt (scalarPolynomialProjectionConstant (a i)) * rateBase^N := by
    have hexp : β ≤ min (2*a i-1) 1 :=
      min_le_min (by linarith [hra i]) le_rfl
    have hpow := Real.rpow_le_rpow_of_exponent_ge' hbase0 hbase1
      (show 0 ≤ β by exact hβ.le) hexp
    calc
      _ ≤ Real.sqrt (scalarPolynomialProjectionConstant (a i) *
          (1/(2:ℝ)^N)^β) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hpow
          (scalarPolynomialProjectionConstant_nonneg (ha i)))
      _ = Real.sqrt (scalarPolynomialProjectionConstant (a i)) * rateBase^N := by
        rw [Real.sqrt_mul (scalarPolynomialProjectionConstant_nonneg (ha i)),
          inverse_dyadic_rpow,
          sqrt_pow_eq (Real.rpow_nonneg (by norm_num) _), hroot]
  have hsum :
      (∑ i : Fin d, Real.sqrt (scalarPolynomialProjectionConstant (a i) *
        (1/(2:ℝ)^N)^(min (2*a i-1) 1))) ≤ A*rateBase^N := by
    calc
      _ ≤ ∑ i : Fin d, Real.sqrt (scalarPolynomialProjectionConstant (a i))*rateBase^N :=
        Finset.sum_le_sum fun i hi => hscalar i
      _ = A*rateBase^N := by rw [← Finset.sum_mul]
  have hnorm (i : Fin d) (t' : BrownianCubeAnchor d) :
      ‖translatedUnitKernelFamily (a i) (ha i) (cubeCoordinate i t')‖ ≤ K := by
    have h := translatedUnitKernelFamily_norm_le (a i) (ha i) (cubeCoordinate i t')
    have hsum : ‖fullKernelVector (a i) (ha i)‖ ≤
        ∑ j : Fin d, ‖fullKernelVector (a j) (ha j)‖ :=
      Finset.single_le_sum (f := fun j : Fin d => ‖fullKernelVector (a j) (ha j)‖)
        (s := Finset.univ) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    dsimp [K]
    exact h.trans (by linarith [hsum])
  have herror (i : Fin d) (t' : BrownianCubeAnchor d) :
      ‖translatedUnitKernelFamily (a i) (ha i) (cubeCoordinate i t') -
        axisFrameProjection
          (nestedFrame (polynomialFiltration q i)
            (polynomialFiltration_finite q i) N)
          (translatedUnitKernelFamily (a i) (ha i) (cubeCoordinate i t'))‖ ≤
        Real.sqrt (scalarPolynomialProjectionConstant (a i) *
          (1/(2:ℝ)^N)^(min (2*a i-1) 1)) := by
    rw [axisFrameProjection_nestedFrame_eq (polynomialFiltration q i)
      (polynomialFiltration_finite q i) (polynomialFiltration_nested q i) N]
    simpa [polynomialFiltration, polynomialProjection] using
      polynomial_projection_residual_norm_le (hq i) (ha i) N hN (cubeCoordinate i t')
  have hgeneral := tensorKernel_frameProjection_error_le
    (d:=d) hd
    (e:=fun i => nestedFrame (polynomialFiltration q i)
      (polynomialFiltration_finite q i) N)
    (he:=fun i => nestedFrame_orthonormal (polynomialFiltration q i)
      (polynomialFiltration_finite q i) (polynomialFiltration_nested q i) N)
    a ha hK
    (fun i => Real.sqrt (scalarPolynomialProjectionConstant (a i) *
      (1/(2:ℝ)^N)^(min (2*a i-1) 1)))
    (fun i => Real.sqrt_nonneg _)
    hnorm herror t
  have hbound :
      ‖tensorKernelFamily a ha t - polynomialTensorProjectedKernel q N a ha t‖ ≤
        B*(A*rateBase^N) := by
    change ‖tensorKernelFamily a ha t -
        tensorFrameProjectedKernel
          (fun i => nestedFrame (polynomialFiltration q i)
            (polynomialFiltration_finite q i) N) a ha t‖ ≤ _
    calc
      _ ≤ B * ∑ i : Fin d, Real.sqrt (scalarPolynomialProjectionConstant (a i) *
            (1/(2:ℝ)^N)^(min (2*a i-1) 1)) := by
          simpa [B,K] using hgeneral
      _ ≤ B*(A*rateBase^N) := mul_le_mul_of_nonneg_left hsum hB
  change ‖tensorKernelFamily a ha t - polynomialTensorProjectedKernel q N a ha t‖ ≤
    (1+B*A) * ((2:ℝ)^(-γ))^N
  calc
    _ ≤ B*(A*((2:ℝ)^(-γ))^N) := by simpa [rateBase] using hbound
    _ ≤ (1+B*A)*((2:ℝ)^(-γ))^N := by
      have hp : 0 ≤ ((2:ℝ)^(-γ))^N := pow_nonneg (Real.rpow_nonneg (by norm_num) _) _
      nlinarith

/-- Given any positive tolerance, one common polynomial depth makes the actual
tensor-kernel projection uniformly accurate over the entire spatial cube. -/
theorem exists_polynomialTensorProjectedKernel_depth {d : ℕ} (hd : 0 < d)
    (q : Fin d → ℕ) (hq : ∀ i, 0 < q i)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i)
    (r : ℝ) (hr : 1/2 < r) (hra : ∀ i, r ≤ a i)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ t : BrownianCubeAnchor d,
      ‖tensorKernelFamily a ha t - polynomialTensorProjectedKernel q N a ha t‖ ≤ τ := by
  obtain ⟨C,γ,hC,hγ,hbound⟩ :=
    polynomialTensorProjectedKernel_uniform_rate hd q hq a ha r hr hra
  have hrate0 : 0 ≤ (2:ℝ)^(-γ) := Real.rpow_nonneg (by norm_num) _
  have hrate1 : (2:ℝ)^(-γ) < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0:ℝ)<2)]
    exact Or.inl ⟨by norm_num,by linarith⟩
  have hpow : Tendsto (fun N : ℕ => C*((2:ℝ)^(-γ))^N) atTop (𝓝 0) := by
    simpa only [mul_comm, mul_zero] using
      Tendsto.mul_const C (tendsto_pow_atTop_nhds_zero_of_lt_one hrate0 hrate1)
  have hevent : ∀ᶠ N : ℕ in atTop, C*((2:ℝ)^(-γ))^N < τ :=
    hpow.eventually (Iio_mem_nhds hτ)
  obtain ⟨N0,hN0⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨N0+1,by omega,?_⟩
  intro t
  have hsmall := hN0 (N0+1) (by omega)
  exact (hbound (N0+1) (by omega) t).trans hsmall.le

/-- The common lower order required by the rate argument exists for every
finite vector of coordinate orders strictly above one half. -/
theorem exists_common_order_lower_bound {d : ℕ} (hd : 0 < d)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i) :
    ∃ r : ℝ, 1/2 < r ∧ ∀ i, r ≤ a i := by
  classical
  let S : Finset ℝ := Finset.univ.image a
  have hS : S.Nonempty := by
    refine ⟨a ⟨0,hd⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0,hd⟩,Finset.mem_univ _,rfl⟩
  let r : ℝ := S.min' hS
  have hrmem : r ∈ S := by exact Finset.min'_mem S hS
  have hr : 1/2 < r := by
    rcases Finset.mem_image.mp hrmem with ⟨i,hi,hir⟩
    rw [← hir]
    exact ha i
  refine ⟨r,hr,?_⟩
  intro i
  exact Finset.min'_le S (a i)
    (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)

/-- Every anisotropic order vector with coordinates above one half admits a
common polynomial projection depth for any prescribed uniform error. -/
theorem exists_polynomialTensorProjectedKernel_depth_of_orders {d : ℕ}
    (hd : 0 < d) (q : Fin d → ℕ) (hq : ∀ i, 0 < q i)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ t : BrownianCubeAnchor d,
      ‖tensorKernelFamily a ha t - polynomialTensorProjectedKernel q N a ha t‖ ≤ τ := by
  obtain ⟨r,hr,hra⟩ := exists_common_order_lower_bound hd a ha
  exact exists_polynomialTensorProjectedKernel_depth hd q hq a ha r hr hra hτ

end BrownianSharp.AlignmentFractionalPolynomialTensorApproximation

