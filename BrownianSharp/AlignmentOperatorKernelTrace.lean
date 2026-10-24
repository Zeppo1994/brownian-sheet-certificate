import BrownianSharp.AlignmentOperatorResidualTrace
import BrownianSharp.AlignmentFractionalApproximationNumbers
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace BrownianSharp.AlignmentOperatorKernelTrace

/-- The rank of a restriction to a finite-dimensional source subspace is
strictly below k whenever the original operator has rank below k. -/
theorem restricted_range_finrank_lt
    {H Y : Type*} [AddCommGroup H] [Module ℝ H]
    [AddCommGroup Y] [Module ℝ Y]
    (V : Submodule ℝ H) [FiniteDimensional ℝ V]
    (A : H →ₗ[ℝ] Y) {k : ℕ}
    (hA : Module.rank ℝ (LinearMap.range A) < (k : Cardinal)) :
    Module.finrank ℝ (LinearMap.range (A.comp V.subtype)) < k := by
  have hcomp : Module.rank ℝ (LinearMap.range (A.comp V.subtype)) < (k : Cardinal) :=
    (LinearMap.rank_comp_le_left V.subtype A).trans_lt hA
  exact (FiniteDimensional.finrank_lt_iff_rank_lt).2 hcomp

/-- The restriction of a rank-q operator to a D-dimensional source subspace
has a kernel of dimension at least D-q.  An orthonormal basis of this kernel,
viewed in the ambient Hilbert space, is killed by the approximant. -/
theorem exists_orthonormal_kernel_family
    {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace X]
    (V : Submodule ℝ H) [FiniteDimensional ℝ V]
    (A : H →L[ℝ] C(X,ℝ))
    {D q : ℕ} (hD : Module.finrank ℝ V = D)
    (hR : Module.finrank ℝ
      (LinearMap.range ((A : H →ₗ[ℝ] C(X,ℝ)).comp V.subtype)) ≤ q)
    (hqD : q ≤ D) :
    ∃ e : Fin (Module.finrank ℝ
      (LinearMap.ker ((A : H →ₗ[ℝ] C(X,ℝ)).comp V.subtype))) → V,
      Orthonormal ℝ e ∧ (∀ i, A (e i) = 0) ∧
      D - q ≤ Module.finrank ℝ
        (LinearMap.ker ((A : H →ₗ[ℝ] C(X,ℝ)).comp V.subtype)) := by
  classical
  let f : V →ₗ[ℝ] C(X,ℝ) :=
    (A : H →ₗ[ℝ] C(X,ℝ)).comp V.subtype
  let K : Submodule ℝ V := LinearMap.ker f
  have hdim := f.finrank_range_add_finrank_ker
  have hR' : Module.finrank ℝ (LinearMap.range f) ≤ q := by
    simpa [f] using hR
  have hker : D - q ≤ Module.finrank ℝ K := by
    have heq : Module.finrank ℝ (LinearMap.range f) +
        Module.finrank ℝ K = D := by
      simpa [K] using hdim.trans (by rw [hD])
    omega
  let b : OrthonormalBasis (Fin (Module.finrank ℝ K)) ℝ K :=
    stdOrthonormalBasis ℝ K
  let e : Fin (Module.finrank ℝ K) → V := fun i => (b i : V)
  have he : Orthonormal ℝ e := by
    have hb : Orthonormal ℝ b := b.orthonormal
    rw [orthonormal_iff_ite] at hb
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪b i, b j⟫_ℝ = if i = j then 1 else 0
    exact hb i j
  have hkill (i : Fin (Module.finrank ℝ K)) : A ((e i : V) : H) = 0 := by
    change (A : H →ₗ[ℝ] C(X,ℝ)) ((e i : V) : H) = 0
    change f (b i : V) = 0
    exact (b i).2
  exact ⟨e, he, hkill, hker⟩

/-- Trace lower bound for approximation by a rank-q operator.  It applies when
the target has a uniform L² lower energy on every unit vector in a
D-dimensional source subspace.  The proof chooses an orthonormal basis of the
kernel of the approximant restricted to that subspace. -/
theorem finite_rank_residual_trace_lower
    {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T A : H →L[ℝ] C(X,ℝ))
    (V : Submodule ℝ H) [FiniteDimensional ℝ V]
    {D q : ℕ} (hD : Module.finrank ℝ V = D)
    (hR : Module.finrank ℝ
      (LinearMap.range ((A : H →ₗ[ℝ] C(X,ℝ)).comp V.subtype)) ≤ q)
    (hqD : q ≤ D)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (henergy : ∀ v : V, ‖(v : H)‖ = 1 →
      σ^2 ≤ ∫ x, (T (v : H) x)^2 ∂μ) :
    ((D-q:ℕ):ℝ) * σ^2 ≤ ‖T-A‖^2 := by
  classical
  obtain ⟨eV, heV, hkillV, hker⟩ := exists_orthonormal_kernel_family V A hD hR hqD
  let e : Fin (Module.finrank ℝ
    (LinearMap.ker ((A : H →ₗ[ℝ] C(X,ℝ)).comp V.subtype))) → H := fun i => (eV i : H)
  have he : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪eV i, eV j⟫_ℝ = if i = j then 1 else 0
    exact (orthonormal_iff_ite.mp heV) i j
  have hkill (i : Fin (Module.finrank ℝ
      (LinearMap.ker ((A : H →ₗ[ℝ] C(X,ℝ)).comp V.subtype)))) : A (e i) = 0 := by
    exact hkillV i
  let I := Fin (Module.finrank ℝ
    (LinearMap.ker ((A : H →ₗ[ℝ] C(X,ℝ)).comp V.subtype)))
  have hsum : (Fintype.card I:ℝ) * σ^2 ≤
      ∑ i : I, (∫ x, (T (e i) x)^2 ∂μ) := by
    calc
      _ = ∑ i : I, σ^2 := by simp
      _ ≤ ∑ i : I, (∫ x, (T (e i) x)^2 ∂μ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hunit : ‖(eV i : H)‖ = 1 := he.norm_eq_one i
        exact henergy (eV i) hunit
  have htrace := BrownianSharp.AlignmentOperatorResidualTrace.finite_orthonormal_residual_trace_bound
    μ T A e he hkill σ hσ hsum
  have hdim : (D-q:ℕ) ≤ Fintype.card I := by
    simpa [I] using hker
  have hreal : ((D-q:ℕ):ℝ) ≤ (Fintype.card I:ℝ) := by exact_mod_cast hdim
  nlinarith [mul_le_mul_of_nonneg_right hreal (sq_nonneg σ)]

/-- Strict-rank approximation form: every candidate of manuscript rank `< k`
has the operator-norm error forced by the L² lower energy on a D-dimensional
source subspace. -/
theorem strict_rank_residual_trace_lower
    {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : H →L[ℝ] C(X,ℝ))
    (V : Submodule ℝ H) [FiniteDimensional ℝ V]
    {D k : ℕ} (hD : Module.finrank ℝ V = D) (hk : 1 ≤ k) (hkD : k ≤ D)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (henergy : ∀ v : V, ‖(v : H)‖ = 1 →
      σ^2 ≤ ∫ x, (T (v : H) x)^2 ∂μ)
    (A : H →L[ℝ] C(X,ℝ))
    (hA : Module.rank ℝ (LinearMap.range (A : H →ₗ[ℝ] C(X,ℝ))) < (k : Cardinal)) :
    ((D-(k-1):ℕ):ℝ) * σ^2 ≤ ‖T-A‖^2 := by
  have hR' := restricted_range_finrank_lt V (A : H →ₗ[ℝ] C(X,ℝ)) hA
  have hR : Module.finrank ℝ
      (LinearMap.range ((A : H →ₗ[ℝ] C(X,ℝ)).comp V.subtype)) ≤ k-1 := by omega
  have hqD : k-1 ≤ D := by omega
  exact finite_rank_residual_trace_lower μ T A V hD hR hqD σ hσ henergy

/-- Corresponding lower bound for the manuscript's strict-rank approximation
number, obtained by taking the infimum over the preceding candidate-wise
estimate. -/
theorem approximationNumber_lower_of_subspace_trace
    {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (T : H →L[ℝ] C(X,ℝ))
    (V : Submodule ℝ H) [FiniteDimensional ℝ V]
    {D k : ℕ} (hD : Module.finrank ℝ V = D) (hk : 1 ≤ k) (hkD : k ≤ D)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (henergy : ∀ v : V, ‖(v : H)‖ = 1 →
      σ^2 ≤ ∫ x, (T (v : H) x)^2 ∂μ) :
    ENNReal.ofReal (σ * Real.sqrt ((D-(k-1):ℕ):ℝ)) ≤
      BrownianSharp.AlignmentFractionalApproximationNumbers.approximationNumber T k := by
  classical
  let η : ℝ := σ * Real.sqrt ((D-(k-1):ℕ):ℝ)
  have hη : 0 ≤ η := mul_nonneg hσ (Real.sqrt_nonneg _)
  unfold BrownianSharp.AlignmentFractionalApproximationNumbers.approximationNumber
  apply le_iInf
  intro A
  have hsq := strict_rank_residual_trace_lower μ T V hD hk hkD σ hσ henergy A.1 A.2
  have hd0 : 0 ≤ ((D-(k-1):ℕ):ℝ) := Nat.cast_nonneg _
  have hηsq : η^2 ≤ ‖T-A.1‖^2 := by
    dsimp [η]
    rw [mul_pow, Real.sq_sqrt hd0]
    nlinarith [hsq]
  have hnorm : η ≤ ‖T-A.1‖ :=
    (sq_le_sq₀ hη (norm_nonneg (T-A.1))).1 hηsq
  exact ENNReal.ofReal_le_ofReal hnorm

end BrownianSharp.AlignmentOperatorKernelTrace
