import BrownianSharp.AlignmentFractionalPolynomialWitness
import Mathlib.Analysis.Calculus.Taylor

/-! Literal finite L² witnesses for cellwise Taylor polynomials. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace BrownianSharp.AlignmentFractionalPolynomialTaylorWitness
open BrownianSharp.AlignmentFractionalPolynomialSpaces
open BrownianSharp.AlignmentFractionalPolynomialWitness
open BrownianSharp.AlignmentFractionalDyadicProjection
abbrev SourceL2 := BrownianSharp.AlignmentFractionalL2.UnitL2

def shiftedPolynomialVector (q n : ℕ) (j : Fin (2^n)) (b : ℝ)
    (c : Fin q → ℝ) : SourceL2 :=
  ∑ k : Fin q, c k • polynomialOnCell q n j ((Polynomial.C b - Polynomial.X)^k.val)

theorem shiftedPolynomialVector_mem (q n : ℕ) (j : Fin (2^n)) (b : ℝ)
    (c : Fin q → ℝ) :
    shiftedPolynomialVector q n j b c ∈ piecewisePolynomials q n := by
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.smul_mem _ _ (polynomialOnCell_mem q n j _)

theorem shiftedPolynomialVector_coeFn (q n : ℕ) (j : Fin (2^n)) (b : ℝ)
    (c : Fin q → ℝ) :
    (shiftedPolynomialVector q n j b c : ℝ → ℝ)
      =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
        (sourceDyadicCell n j).indicator (fun u => ∑ k : Fin q, c k * (b-u)^k.val) := by
  have hs := finite_sum_smul_coeFn_ae
    (fun k : Fin q => polynomialOnCell q n j ((Polynomial.C b - Polynomial.X)^k.val))
    (fun k => (sourceDyadicCell n j).indicator (fun u => (b-u)^k.val)) c
    (fun k => polynomialOnCell_shiftedPower_coeFn q n j b k.isLt)
  filter_upwards [hs] with u hu
  unfold shiftedPolynomialVector
  rw [hu]
  by_cases h : u ∈ sourceDyadicCell n j <;> simp [h]

def cellTaylorVector (q n : ℕ) (j : Fin (2^n))
    (f : ℝ → ℝ) (s : Set ℝ) (x₀ offset scale : ℝ) : SourceL2 :=
  shiftedPolynomialVector q n j (offset-x₀)
    (fun k => scale * (k.val.factorial : ℝ)⁻¹ * iteratedDerivWithin k.val f s x₀)

theorem cellTaylorVector_mem (q n : ℕ) (j : Fin (2^n))
    (f : ℝ → ℝ) (s : Set ℝ) (x₀ offset scale : ℝ) :
    cellTaylorVector q n j f s x₀ offset scale ∈ piecewisePolynomials q n :=
  shiftedPolynomialVector_mem _ _ _ _ _

theorem cellTaylorVector_coeFn (q n : ℕ) (j : Fin (2^n)) (hq : 0 < q)
    (f : ℝ → ℝ) (s : Set ℝ) (x₀ offset scale : ℝ) :
    (cellTaylorVector q n j f s x₀ offset scale : ℝ → ℝ)
      =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)]
        (sourceDyadicCell n j).indicator
          (fun u => scale * taylorWithinEval f (q-1) s x₀ (offset-u)) := by
  have hs := shiftedPolynomialVector_coeFn q n j (offset-x₀)
    (fun k => scale * (k.val.factorial : ℝ)⁻¹ * iteratedDerivWithin k.val f s x₀)
  filter_upwards [hs] with u hu
  unfold cellTaylorVector
  rw [hu]
  by_cases h : u ∈ sourceDyadicCell n j
  · simp only [Set.indicator_of_mem h, taylor_within_apply]
    have hqm : q-1+1=q := by omega
    rw [hqm, ← Fin.sum_univ_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [smul_eq_mul]
    rw [show offset-x₀-u = offset-u-x₀ by ring]
    ring
  · simp [h]

end BrownianSharp.AlignmentFractionalPolynomialTaylorWitness
