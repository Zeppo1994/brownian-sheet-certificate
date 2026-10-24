import BrownianSharp.AlignmentFractionalTensorL2ApproximationUpper
import BrownianSharp.AlignmentTensorApproximationUpperRate
import BrownianSharp.AlignmentFractionalApproximationRates
import BrownianSharp.AlignmentFractionalApproximationNumbers
import BrownianSharp.AlignmentGeometricRanks
import BrownianSharp.LayerIndex
import Mathlib.Tactic

/-! All-index approximation-number upper rate for the actual isotropic
fractional tensor map into `L²`, from its finite graded trace refinements. -/

noncomputable section
open scoped ENNReal

namespace BrownianSharp.AlignmentFractionalTensorL2ApproximationAllIndex

open BrownianSharp
open BrownianSharp.AlignmentFractionalApproximationNumbers
open BrownianSharp.AlignmentFractionalApproximationRates
open BrownianSharp.AlignmentFractionalTensorL2ApproximationUpper
open BrownianSharp.AlignmentFractionalTensorL2Semigroup
open BrownianSharp.AlignmentTensorApproximationUpperRate
open BrownianSharp.AlignmentGeometricRanks

/-- The actual isotropic tensor Riemann--Liouville map into `L²` has the
sharp all-index approximation-number upper rate. -/
theorem fractionalTensorRLToL2_approximationNumber_all_index
    {d : ℕ} (hd : 2 ≤ d) {β : ℝ} (hβ : 1/2 < β) :
    ∃ C : ℝ, 0 < C ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧
      ∀ k : ℕ, k₀ ≤ k →
        approximationNumber
          (fractionalTensorRLToL2
            (fun _ : Fin d => β) (fun _ => hβ)) k ≤
          ENNReal.ofReal (C * (k:ℝ)^(-β) *
            (Real.log (k:ℝ))^(β*((d-1:ℕ):ℝ))) := by
  classical
  obtain ⟨q,A,ρ,D,hq,hA,hρ0,hρ1,hρeq,hD,hdyd⟩ :=
    fractionalTensorRLToL2_approximationNumber_dyadic hd hβ
  let T := fractionalTensorRLToL2
    (fun _ : Fin d => β) (fun _ => hβ)
  let f : ℕ → ℝ≥0∞ := fun k => approximationNumber T k
  have hmono : ∀ ⦃i j : ℕ⦄, i ≤ j → f j ≤ f i := by
    intro i j hij
    exact approximationNumber_antitone T hij
  let B : ℝ := A * polynomialBudget ρ (d-1)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (le_of_lt hA) (polynomialBudget_nonneg (le_of_lt hρ0) (d-1))
  have hfactorial_pos : 0 < (Nat.factorial (d-1):ℝ) := by positivity
  let K : ℝ := 1 + Real.sqrt (B * (Nat.factorial (d-1):ℝ))
  have hK : 0 < K := by dsimp [K]; positivity
  have htwo : ∀ N : ℕ,
      Real.sqrt ((A * ρ^N * ((N+1:ℕ):ℝ)^(d-1) *
          polynomialBudget ρ (d-1)) /
          ((D * Fintype.card (LayerIndex d N) + 1:ℕ):ℝ)) ≤
        K * (2:ℝ)^(-β*(N:ℝ)) := by
    intro N
    have hcardpos : 0 < (Fintype.card (LayerIndex d N):ℝ) := by
      rw [layerIndex_card d N (by omega : 0 < d)]
      have hc : 0 < Nat.choose (N+d-1) (d-1) := by
        apply Nat.choose_pos
        omega
      exact_mod_cast (Nat.mul_pos (pow_pos (by omega : 0 < 2) N) hc)
    have hden : (Fintype.card (LayerIndex d N):ℝ) ≤
        ((D * Fintype.card (LayerIndex d N) + 1:ℕ):ℝ) := by
      have hD' : 1 ≤ D := hD
      norm_cast
      nlinarith [Nat.mul_le_mul_right (Fintype.card (LayerIndex d N)) hD']
    have hrhopow : ρ^N = (2:ℝ)^(-((2*β-1)*(N:ℝ))) := by
      calc
        ρ^N = (Real.rpow 2 (-(2*β-1)))^N := by rw [hρeq]
        _ = Real.rpow (Real.rpow 2 (-(2*β-1))) (N:ℝ) :=
          (Real.rpow_natCast _ _).symm
        _ = Real.rpow 2 ((-(2*β-1))*(N:ℝ)) :=
          (Real.rpow_mul (by norm_num : (0:ℝ)≤2) _ _).symm
        _ = (2:ℝ)^(-((2*β-1)*(N:ℝ))) := by congr 1 <;> ring
    have hnumerator_nonneg :
        0 ≤ A * (2:ℝ)^(-((2*β-1)*(N:ℝ))) *
          ((N+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1) := by
      have hbase : 0 ≤ (2:ℝ)^(-((2*β-1)*(N:ℝ))) := by positivity
      have hpoly : 0 ≤ ((N+1:ℕ):ℝ)^(d-1) := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hA) hbase) hpoly)
        (polynomialBudget_nonneg (le_of_lt hρ0) (d-1))
    have hnumerator_eq :
        A * ρ^N * ((N+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1) =
        A * (2:ℝ)^(-((2*β-1)*(N:ℝ))) *
          ((N+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1) := by
      rw [hrhopow]
    have hdiv :
        (A * ρ^N * ((N+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1)) /
            ((D * Fintype.card (LayerIndex d N) + 1:ℕ):ℝ) ≤
          (B * (2:ℝ)^(-((2*β-1)*(N:ℝ))) *
            ((N+1:ℕ):ℝ)^((d-1:ℕ):ℝ)) /
            (Fintype.card (LayerIndex d N):ℝ) := by
      rw [hnumerator_eq]
      have hpolyexp : ((N+1:ℕ):ℝ)^(d-1) =
          ((N+1:ℕ):ℝ)^((d-1:ℕ):ℝ) := by
        rw [← Real.rpow_natCast]
      have hnum :
          A * (2:ℝ)^(-((2*β-1)*(N:ℝ))) *
              ((N+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1) =
            B * (2:ℝ)^(-((2*β-1)*(N:ℝ))) *
              ((N+1:ℕ):ℝ)^((d-1:ℕ):ℝ) := by
        dsimp [B]
        rw [hpolyexp]
        ring
      rw [hnum]
      exact div_le_div_of_nonneg_left (by positivity) hcardpos hden
    have hβpos : 0 < β := by linarith
    have htail := weighted_tail_div_layer_le (N:=N) hd B β hB hβpos
    have htail' :
        B * (2:ℝ)^(-((2*β-1)*(N:ℝ))) *
            ((N+1:ℕ):ℝ)^((d-1:ℕ):ℝ) /
            (Fintype.card (LayerIndex d N):ℝ) ≤
          (B * (Nat.factorial (d-1):ℝ)) *
            (2:ℝ)^(-2*β*(N:ℝ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using htail
    have hratio :
        (A * ρ^N * ((N+1:ℕ):ℝ)^(d-1) * polynomialBudget ρ (d-1)) /
            ((D * Fintype.card (LayerIndex d N) + 1:ℕ):ℝ) ≤
          (B * (Nat.factorial (d-1):ℝ)) *
            (2:ℝ)^(-2*β*(N:ℝ)) := hdiv.trans htail'
    have hpow : ((2:ℝ)^(-β*(N:ℝ)))^2 =
        (2:ℝ)^(-2*β*(N:ℝ)) := by
      calc
        _ = Real.rpow (Real.rpow 2 (-β*(N:ℝ))) (2:ℝ) :=
          (Real.rpow_natCast _ 2).symm
        _ = Real.rpow 2 ((-β*(N:ℝ))*2) :=
          (Real.rpow_mul (by norm_num : (0:ℝ)≤2) _ _).symm
        _ = _ := by congr 1 <;> ring
    have hroot :
        Real.sqrt ((A * ρ^N * ((N+1:ℕ):ℝ)^(d-1) *
          polynomialBudget ρ (d-1)) /
          ((D * Fintype.card (LayerIndex d N) + 1:ℕ):ℝ)) ≤
        Real.sqrt (B * (Nat.factorial (d-1):ℝ)) * (2:ℝ)^(-β*(N:ℝ)) := by
      have hright : 0 ≤ Real.sqrt (B * (Nat.factorial (d-1):ℝ)) *
          (2:ℝ)^(-β*(N:ℝ)) := by positivity
      apply (Real.sqrt_le_iff).2
      constructor
      · exact hright
      · rw [mul_pow, Real.sq_sqrt (mul_nonneg hB (le_of_lt hfactorial_pos)), hpow]
        exact hratio
    calc
      _ ≤ Real.sqrt (B * (Nat.factorial (d-1):ℝ)) * (2:ℝ)^(-β*(N:ℝ)) := hroot
      _ ≤ K * (2:ℝ)^(-β*(N:ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp [K]
        linarith [Real.sqrt_nonneg (B * (Nat.factorial (d-1):ℝ))]
  have hLayer : ∀ N : ℕ, 1 ≤ N →
      f (2*D * Fintype.card (LayerIndex d N) + 1) ≤
        ENNReal.ofReal (K * (2:ℝ)^(-β*(N:ℝ))) := by
    intro N hN
    have hidx : 2*D * Fintype.card (LayerIndex d N) + 1 =
        2 * (D * Fintype.card (LayerIndex d N)) + 1 := by ring
    rw [hidx]
    exact (hdyd N hN).trans (ENNReal.ofReal_le_ofReal (htwo N))
  obtain ⟨C,hC,k₀,hk₀,hupper⟩ :=
    all_index_upper_of_layer_bound hd β K (by linarith : 0 < β) (by positivity)
      (2*D) 1 (by omega) f hmono hLayer
  refine ⟨C,hC,k₀,hk₀,?_⟩
  intro k hk
  simpa [f,T] using hupper k hk

end BrownianSharp.AlignmentFractionalTensorL2ApproximationAllIndex
