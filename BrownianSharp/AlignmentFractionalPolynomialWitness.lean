import BrownianSharp.AlignmentFractionalPolynomialSpaces
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! Evaluation bridges and approximation witnesses in the actual source spaces. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BrownianSharp.AlignmentFractionalPolynomialWitness
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalDyadicProjection
abbrev SourceL2 := BrownianSharp.AlignmentFractionalL2.UnitL2

theorem finite_sum_smul_coeFn_ae {ι : Type*} [Fintype ι]
    (v : ι → SourceL2) (f : ι → ℝ → ℝ) (c : ι → ℝ)
    (hv : ∀ i, (v i : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)] f i) :
    ((∑ i, c i • v i : SourceL2) : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
      (fun x => ∑ i, c i * f i x) := by
  have hs := Lp.coeFn_fun_finsetSum (Finset.univ : Finset ι) (fun i => c i • v i)
  have ht : ∀ᵐ x ∂volume.restrict (Set.Icc (0:ℝ) 1),
      ∀ i, (c i • v i : SourceL2) x = c i * f i x := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (c i) (v i), hv i] with x hx hfx
    simpa [smul_eq_mul, hfx] using hx
  filter_upwards [hs, ht] with x hs ht
  rw [hs]
  exact Finset.sum_congr rfl (fun i hi => ht i)

def polynomialOnCell (q n : ℕ) (j : Fin (2^n)) (p : (Polynomial ℝ)) : SourceL2 :=
  ∑ ell : Fin q, p.coeff ell.val • cellMonomial n j ell.val

theorem polynomialOnCell_mem (q n : ℕ) (j : Fin (2^n)) (p : (Polynomial ℝ)) :
    polynomialOnCell q n j p ∈ piecewisePolynomials q n := by
  apply Submodule.sum_mem
  intro ell hell
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j,ell),rfl⟩)

theorem polynomialOnCell_coeFn (q n : ℕ) (j : Fin (2^n))
    (p : (Polynomial ℝ)) (hp : p.degree < (q : WithBot ℕ)) :
    (polynomialOnCell q n j p : ℝ → ℝ) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
      (sourceDyadicCell n j).indicator (fun x => p.eval x) := by
  have hs := finite_sum_smul_coeFn_ae
    (fun ell : Fin q => cellMonomial n j ell.val)
    (fun ell => cellMonomialFunction n j ell.val)
    (fun ell => p.coeff ell.val) (fun ell => cellMonomial_coeFn n j ell.val)
  filter_upwards [hs] with x hx
  change (polynomialOnCell q n j p) x = _
  rw [show polynomialOnCell q n j p =
    ∑ ell : Fin q, p.coeff ell.val • cellMonomial n j ell.val from rfl, hx]
  by_cases h : x ∈ sourceDyadicCell n j
  · simp only [cellMonomialFunction, Set.indicator_of_mem h]
    rw [Polynomial.eval_eq_sum]
    exact Polynomial.sum_fin (fun ell c => c*x^ell) (by simp) hp
  · simp [cellMonomialFunction, h]

theorem shiftedPower_degree_lt (b : ℝ) {k q : ℕ} (hk : k < q) :
    ((Polynomial.C b - Polynomial.X)^k).degree < (q : WithBot ℕ) := by
  have hb : (Polynomial.C b - Polynomial.X).degree ≤ (1 : WithBot ℕ) := by
    calc
      _ ≤ max (Polynomial.C b).degree Polynomial.X.degree := Polynomial.degree_sub_le _ _
      _ ≤ 1 := max_le (Polynomial.degree_C_le.trans (by norm_num)) (by simp)
  have hpow := Polynomial.degree_pow_le_of_le k hb
  have hpow' : ((Polynomial.C b - Polynomial.X)^k).degree ≤ (k : WithBot ℕ) := by
    simpa using hpow
  exact hpow'.trans_lt (by exact_mod_cast hk)

theorem polynomialOnCell_shiftedPower_coeFn (q n : ℕ)
    (j : Fin (2^n)) (b : ℝ) {k : ℕ} (hk : k < q) :
    (polynomialOnCell q n j ((Polynomial.C b - Polynomial.X)^k) : ℝ → ℝ)
      =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
        (sourceDyadicCell n j).indicator (fun x => (b-x)^k) := by
  simpa using polynomialOnCell_coeFn q n j
    ((Polynomial.C b - Polynomial.X)^k) (shiftedPower_degree_lt b hk)

theorem polynomialProjection_residual_le (q n : ℕ) (x y : SourceL2)
    (hy : y ∈ piecewisePolynomials q n) :
    ‖x - polynomialProjection q n x‖ ≤ ‖x-y‖ := by
  rw [polynomialProjection, Submodule.starProjection_minimal]
  have hbdd : BddBelow (Set.range
      (fun y : piecewisePolynomials q n => ‖x - (y : SourceL2)‖)) :=
    ⟨0, Set.forall_mem_range.mpr (fun y => norm_nonneg _)⟩
  exact ciInf_le hbdd ⟨y,hy⟩

end BrownianSharp.AlignmentFractionalPolynomialWitness
