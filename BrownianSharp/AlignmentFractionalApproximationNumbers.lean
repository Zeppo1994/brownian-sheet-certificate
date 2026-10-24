import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.Dimension.Basic
import BrownianSharp.Projection
import BrownianSharp.AlignmentGaussianGradedTotalBudget
import BrownianSharp.AlignmentGeometricRanks
import Mathlib.Tactic

/-! Strict-rank bounded-linear approximation numbers for bounded operators.
This definition matches the manuscript's rank convention and is shared with
the finite-rank trace lower-bound route. -/

noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
open scoped ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalApproximationNumbers
universe u
open BrownianSharp.AlignmentFractionalSharpBudgets
open BrownianSharp.AlignmentGeometricRanks

/-- Strict-rank bounded-linear approximation number, using the manuscript's
convention `rank A < k`. -/
def approximationNumber {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T : X →L[ℝ] Y) (k : ℕ) : ℝ≥0∞ :=
  ⨅ A : {A : X →L[ℝ] Y //
      Module.rank ℝ (LinearMap.range (A.1 : X →ₗ[ℝ] Y)) < (k : Cardinal)},
    ENNReal.ofReal ‖T - A.1‖

/-- Any explicit strict-rank approximant bounds the approximation number. -/
theorem approximationNumber_le_of_approximant
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (T A : X →L[ℝ] Y) {k : ℕ}
    (hA : Module.rank ℝ (LinearMap.range (A : X →ₗ[ℝ] Y)) < (k : Cardinal)) :
    approximationNumber T k ≤ ENNReal.ofReal ‖T-A‖ := by
  unfold approximationNumber
  exact iInf_le (fun B : {B : X →L[ℝ] Y //
    Module.rank ℝ (LinearMap.range (B.1 : X →ₗ[ℝ] Y)) < (k : Cardinal)} =>
      ENNReal.ofReal ‖T-B.1‖) ⟨A,hA⟩

/-- A finite-dimensional source projection yields a bounded linear
approximation whenever the representing feature vectors are uniformly close
to the projected source space. This is the linear-operator analogue of the
usual Hilbert-feature Kolmogorov-width bridge. -/
theorem approximationNumber_le_of_feature_projection
    {H α : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace α] [CompactSpace α]
    (T : H →L[ℝ] C(α,ℝ)) (v : C(α,H))
    (hT : ∀ g x, T g x = ⟪g,v x⟫)
    (U : Submodule ℝ H) [FiniteDimensional ℝ U]
    {k : ℕ} (hU : Module.rank ℝ U < (k : Cardinal))
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hres : ∀ x, ‖v x-U.starProjection (v x)‖ ≤ δ) :
    approximationNumber T k ≤ ENNReal.ofReal δ := by
  classical
  let A : H →L[ℝ] C(α,ℝ) := T.comp U.starProjection
  have hrange : LinearMap.range (A : H →ₗ[ℝ] C(α,ℝ)) ≤
      U.map T.toLinearMap := by
    intro y hy
    obtain ⟨x,rfl⟩ := hy
    apply Submodule.mem_map.mpr
    refine ⟨U.starProjection x, U.starProjection_apply_mem x, ?_⟩
    rfl
  have hrank : Module.rank ℝ (LinearMap.range (A : H →ₗ[ℝ] C(α,ℝ))) <
      (k : Cardinal) := by
    have hle : Module.rank ℝ (LinearMap.range (A : H →ₗ[ℝ] C(α,ℝ))) ≤
        Module.rank ℝ U :=
      (Submodule.rank_mono hrange).trans (rank_map_le T.toLinearMap U)
    exact hle.trans_lt hU
  have herror : ‖T-A‖ ≤ δ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro g
    apply (ContinuousMap.norm_le ((T-A) g) (by positivity)).2
    intro x
    have hformula : (T-A) g x = ⟪g, v x-U.starProjection (v x)⟫ := by
      change T g x - T (U.starProjection g) x = _
      rw [hT g x, hT (U.starProjection g) x]
      rw [U.inner_starProjection_left_eq_right]
      rw [inner_sub_right]
    rw [hformula, Real.norm_eq_abs]
    calc
      |⟪g, v x-U.starProjection (v x)⟫| ≤
          ‖g‖*‖v x-U.starProjection (v x)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖g‖*δ := mul_le_mul_of_nonneg_left (hres x) (norm_nonneg _)
      _ = δ*‖g‖ := by ring
  exact approximationNumber_le_of_approximant T A hrank |>.trans
    (ENNReal.ofReal_le_ofReal herror)

/-- Finite-frame truncation estimate: projecting onto coordinates with grade
at most `n` costs at most the full-frame residual plus the square root of the
remaining coefficient energy. -/
theorem finite_orthonormal_grade_truncation_bound
    {I H : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (e : I → H) (he : Orthonormal ℝ e) (grade : I → ℕ)
    (n : ℕ) (x : H) {τ E : ℝ} (hτ : 0 ≤ τ) (hE : 0 ≤ E)
    (hfull : ‖x-finiteOrthonormalProjection e x‖ ≤ τ)
    (henergy : (∑ i ∈ Finset.univ.filter (fun i => n < grade i),
        ⟪x,e i⟫^2) ≤ E) :
    ‖x-(∑ i ∈ Finset.univ.filter (fun i => grade i ≤ n),
        ⟪x,e i⟫ • e i)‖ ≤ τ+Real.sqrt E := by
  classical
  let hi : Finset I := Finset.univ.filter (fun i => n < grade i)
  let lo : Finset I := Finset.univ.filter (fun i => grade i ≤ n)
  let lowProj : H := ∑ i ∈ lo, ⟪x,e i⟫ • e i
  let highProj : H := ∑ i ∈ hi, ⟪x,e i⟫ • e i
  have hsplit : lowProj+highProj=finiteOrthonormalProjection e x := by
    dsimp [lowProj, highProj, lo, hi, finiteOrthonormalProjection]
    have hs := Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun i : I => n < grade i) (fun i => ⟪x,e i⟫ • e i)
    have hnot : (fun i : I => ¬ n < grade i) = (fun i => grade i ≤ n) := by
      funext i
      apply propext
      omega
    simpa only [hnot, add_comm] using hs
  have hhighsq : ‖highProj‖^2 = ∑ i ∈ hi, ⟪x,e i⟫^2 := by
    rw [show highProj = ∑ i ∈ hi, ⟪x,e i⟫ • e i by rfl]
    rw [← real_inner_self_eq_norm_sq, he.inner_sum]
    simp [pow_two]
  have hhigh : ‖highProj‖ ≤ Real.sqrt E := by
    have hsq : ‖highProj‖^2 ≤ E := by
      rw [hhighsq]
      exact henergy
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg E)).1
    rw [Real.sq_sqrt hE]
    exact hsq
  have hidentity : x-lowProj=(x-finiteOrthonormalProjection e x)+highProj := by
    rw [← hsplit]
    abel
  calc
    ‖x-lowProj‖ ≤ ‖x-finiteOrthonormalProjection e x‖+‖highProj‖ := by
      rw [hidentity]
      exact norm_add_le _ _
    _ ≤ τ+Real.sqrt E := add_le_add hfull hhigh
    _ = τ+Real.sqrt E := rfl

/-- Sum a nonnegative finite-frame grade profile above a cutoff. The bound is
uniform in the frame depth; only the per-grade envelope matters. -/
theorem finite_grade_profile_tail_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (grade : I → ℕ) (coeff : I → ℝ)
    {n L k : ℕ} {C q : ℝ}
    (hC : 0 ≤ C) (hq0 : 0 < q) (hq1 : q < 1)
    (hgrade : ∀ i, grade i < L)
    (hcoeff : ∀ i, 0 ≤ coeff i)
    (henergy : ∀ g,
      (∑ i : {i : I // grade i = g}, coeff i.1) ≤
        C * ((g+1:ℕ):ℝ)^k * q^g) :
    (∑ i ∈ Finset.univ.filter (fun i : I => n < grade i), coeff i) ≤
      C * q^n * ((n+1:ℕ):ℝ)^k * polynomialBudget q k := by
  classical
  let S := Finset.univ.filter (fun i : I => n < grade i)
  have hmaps : ∀ i ∈ S, grade i ∈ Finset.range L := by
    intro i hi
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_range.mpr (hgrade i)
  have hdecomp : (∑ i ∈ S, coeff i) =
      ∑ g ∈ Finset.range L, ∑ i ∈ S with grade i = g, coeff i :=
    (Finset.sum_fiberwise_of_maps_to hmaps coeff).symm
  have hfiber (g : ℕ) :
      (∑ i ∈ S with grade i = g, coeff i) ≤
        if n < g then C * ((g+1:ℕ):ℝ)^k * q^g else 0 := by
    by_cases hng : n < g
    · have heq : S.filter (fun i : I => grade i = g) =
          Finset.univ.filter (fun i : I => grade i = g) := by
        ext i
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun hi => hi.2
        · intro hi
          exact ⟨by rw [hi]; exact hng, hi⟩
      rw [heq]
      have hsub : (∑ i : {i : I // grade i = g}, coeff i.1) =
          ∑ i ∈ Finset.univ.filter (fun i : I => grade i = g), coeff i :=
        (Finset.sum_subtype
        (Finset.univ.filter (fun i : I => grade i = g))
        (by intro i; simp) coeff).symm
      rw [← hsub]
      simpa [hng] using henergy g
    · have heq : S.filter (fun i : I => grade i = g) = ∅ := by
        ext i
        simp [S]
        intro hni hig
        exact hng (hig ▸ hni)
      rw [heq]
      simp [hng]
  have hbound := calc
      (∑ i ∈ S, coeff i) ≤
          ∑ g ∈ Finset.range L,
            (if n < g then C * ((g+1:ℕ):ℝ)^k * q^g else 0) := by
        rw [hdecomp]
        exact Finset.sum_le_sum fun g hg => hfiber g
      _ = ∑ g ∈ (Finset.range L).filter (fun g => n < g),
            C * ((g+1:ℕ):ℝ)^k * q^g := by
        rw [← Finset.sum_filter]
  have hfilter : (Finset.range L).filter (fun g => n < g) =
      Finset.Ico (n+1) L := by
    ext g
    simp [Finset.mem_Ico]
    omega
  rw [hfilter, Finset.sum_Ico_eq_sum_range] at hbound
  have htail := BrownianSharp.AlignmentGaussianGradedTotalBudget.strict_shifted_polynomial_tail_le
    hq0 hq1 k n (L-(n+1))
  have hnonneg : 0 ≤ q^n * ((n+1:ℕ):ℝ)^k * polynomialBudget q k := by
    exact mul_nonneg (mul_nonneg (pow_nonneg hq0.le _) (by positivity))
      (polynomialBudget_nonneg hq0.le k)
  calc
    _ ≤ C * (∑ j ∈ Finset.range (L-(n+1)),
          ((n+1+j+1:ℕ):ℝ)^k*q^(n+1+j)) := by
      simpa [S, Finset.mul_sum, mul_assoc, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hbound
    _ ≤ C * (q^n * ((n+1:ℕ):ℝ)^k * polynomialBudget q k) :=
      mul_le_mul_of_nonneg_left htail hC
    _ = C * q^n * ((n+1:ℕ):ℝ)^k * polynomialBudget q k := by ring

/-- An actual rank-controlled linear approximation from a finite graded
feature frame. The approximating source subspace is the span of all frame
vectors of grade at most `n`; the high-grade energy is measured in the same
finite frame, and the full-frame residual may be made small by choosing a
deep rectangular truncation. -/
theorem approximationNumber_le_of_finite_grade_frame
    {H α I : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace α] [CompactSpace α]
    [Fintype I] [DecidableEq I]
    (T : H →L[ℝ] C(α,ℝ)) (v : C(α,H))
    (hT : ∀ g x, T g x = ⟪g,v x⟫)
    (e : I → H) (he : Orthonormal ℝ e) (grade : I → ℕ)
    {n k : ℕ} (hcount : Fintype.card {i : I // grade i ≤ n} < k)
    {τ E : ℝ} (hτ : 0 ≤ τ) (hE : 0 ≤ E)
    (hfull : ∀ x, ‖v x-finiteOrthonormalProjection e (v x)‖ ≤ τ)
    (henergy : ∀ x,
      (∑ i ∈ Finset.univ.filter (fun i : I => n < grade i),
        ⟪v x,e i⟫^2) ≤ E) :
    approximationNumber T k ≤ ENNReal.ofReal (τ+Real.sqrt E) := by
  classical
  let I₀ := {i : I // grade i ≤ n}
  let e₀ : I₀ → H := fun i => e i.1
  let U : Submodule ℝ H := Submodule.span ℝ (Set.range e₀)
  letI : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range e₀)
  have he₀ : Orthonormal ℝ e₀ := he.comp (fun i : I₀ => i.1) Subtype.val_injective
  have hUrank : Module.rank ℝ U < (k : Cardinal) := by
    have hspan : Module.rank ℝ U ≤ Cardinal.mk (Set.range e₀) := rank_span_le _
    have hrange : Cardinal.mk (Set.range e₀) ≤ Cardinal.mk I₀ := Cardinal.mk_range_le
    have hcast : Cardinal.mk I₀ < (k : Cardinal) := by
      simpa [I₀, Cardinal.mk_fintype] using hcount
    exact (hspan.trans hrange).trans_lt hcast
  have hprojection (x : H) :
      U.starProjection x = finiteOrthonormalProjection e₀ x := by
    let q : H := finiteOrthonormalProjection e₀ x
    have hmem : q ∈ U := by
      dsimp [q, finiteOrthonormalProjection]
      apply Submodule.sum_mem
      intro i hi
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
    have horth : x-q ∈ Uᗮ := by
      rw [Submodule.mem_orthogonal']
      intro z hz
      refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
      · rintro y ⟨i,rfl⟩
        exact finiteProjection_residual_orthogonal e₀ x
          (orthonormal_iff_ite.mp he₀) i
      · simp
      · intro y z hy hz hpy hpz
        rw [inner_add_right, hpy, hpz]
        simp
      · intro c y hy hpy
        rw [inner_smul_right, hpy]
        simp
    have hp := U.eq_starProjection_of_mem_orthogonal hmem horth
    simpa [q] using hp
  have hres : ∀ x, ‖v x-U.starProjection (v x)‖ ≤ τ+Real.sqrt E := by
    intro x
    rw [hprojection]
    let lo := Finset.univ.filter (fun i : I => grade i ≤ n)
    have hsub : finiteOrthonormalProjection e₀ (v x) =
        ∑ i ∈ lo, ⟪v x,e i⟫ • e i := by
      dsimp [finiteOrthonormalProjection, e₀, lo, I₀]
      exact (Finset.sum_subtype
        (Finset.univ.filter (fun i : I => grade i ≤ n))
        (by intro i; simp)
        (fun i => ⟪v x,e i⟫ • e i)).symm
    rw [hsub]
    exact finite_orthonormal_grade_truncation_bound e he grade n (v x) hτ hE
      (hfull x) (henergy x)
  exact approximationNumber_le_of_feature_projection T v hT U hUrank
    (add_nonneg hτ (Real.sqrt_nonneg E)) hres

end BrownianSharp.AlignmentFractionalApproximationNumbers
