import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentFiniteOverlapRpow

/-- Finite-overlap transfer for nonnegative `ℓᵖ` budgets. Each output is
bounded by `A` times the sum of its neighboring inputs, and both the row and
column degrees of the relation are at most `N`. -/
theorem finite_overlap_rpow_sum_le
    {S T : Type*} [Fintype S] [Fintype T]
    (R : S → T → Prop) [DecidableRel R]
    (A : ℝ≥0∞) (N : ℕ) (hN : 0 < N) (p : ℝ) (hp : 1 ≤ p)
    (hrow : ∀ s, (Finset.univ.filter (R s)).card ≤ N)
    (hcol : ∀ t, (Finset.univ.filter (fun s => R s t)).card ≤ N)
    (a : S → ℝ≥0∞) (b : T → ℝ≥0∞)
    (hpoint : ∀ s, a s ≤ A * ∑ t ∈ Finset.univ.filter (R s), b t) :
    (∑ s, a s ^ p) ≤ (A * (N : ℝ≥0∞)) ^ p * ∑ t, b t ^ p := by
  classical
  have hlocal (s : S) :
      a s ^ p ≤ A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
        ∑ t ∈ Finset.univ.filter (R s), b t ^ p := by
    have hsum := ENNReal.rpow_sum_le_const_mul_sum_rpow
      (Finset.univ.filter (R s)) b hp
    have hcard : ((Finset.univ.filter (R s)).card : ℝ≥0∞) ^ (p - 1) ≤
        (N : ℝ≥0∞) ^ (p - 1) := by
      apply ENNReal.rpow_le_rpow
      · exact_mod_cast hrow s
      · linarith
    calc
      a s ^ p ≤ (A * ∑ t ∈ Finset.univ.filter (R s), b t) ^ p :=
        ENNReal.rpow_le_rpow (hpoint s) (by linarith)
      _ = A ^ p * (∑ t ∈ Finset.univ.filter (R s), b t) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
      _ ≤ A ^ p * ((Finset.univ.filter (R s)).card : ℝ≥0∞) ^ (p - 1) *
            ∑ t ∈ Finset.univ.filter (R s), b t ^ p := by
        rw [mul_assoc]
        gcongr
      _ ≤ A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
            ∑ t ∈ Finset.univ.filter (R s), b t ^ p := by
        calc
          A ^ p * ((Finset.univ.filter (R s)).card : ℝ≥0∞) ^ (p - 1) *
              ∑ t ∈ Finset.univ.filter (R s), b t ^ p ≤
            A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
              ∑ t ∈ Finset.univ.filter (R s), b t ^ p := by
            gcongr
          _ = _ := by rfl
  calc
    (∑ s, a s ^ p) ≤
        ∑ s, A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
          ∑ t ∈ Finset.univ.filter (R s), b t ^ p :=
      Finset.sum_le_sum fun s hs => hlocal s
    _ = (A ^ p * (N : ℝ≥0∞) ^ (p - 1)) *
          ∑ t, (Finset.univ.filter (fun s => R s t)).card * b t ^ p := by
      let C : ℝ≥0∞ := A ^ p * (N : ℝ≥0∞) ^ (p - 1)
      calc
        ∑ s, C * (∑ t ∈ Finset.univ.filter (R s), b t ^ p) =
            C * ∑ s, ∑ t ∈ Finset.univ.filter (R s), b t ^ p := by
          rw [Finset.mul_sum]
        _ = C * ∑ t, ∑ s ∈ Finset.univ.filter (fun s => R s t), b t ^ p := by
          congr 1
          have hswap :
          (∑ s, ∑ t ∈ Finset.univ.filter (R s), b t ^ p) =
            ∑ t, ∑ s ∈ Finset.univ.filter (fun s => R s t), b t ^ p := by
            simp_rw [Finset.sum_filter]
            rw [Finset.sum_comm]
          exact hswap
        _ = C * ∑ t, (Finset.univ.filter (fun s => R s t)).card * b t ^ p := by
          congr 1
          apply Finset.sum_congr rfl
          intro t ht
          simp
    _ ≤ A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
          ∑ t, (N : ℝ≥0∞) * b t ^ p := by
      gcongr with t
      exact_mod_cast hcol t
    _ = (A * (N : ℝ≥0∞)) ^ p * ∑ t, b t ^ p := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
      have hN : (N : ℝ≥0∞) ^ (p - 1) * (N : ℝ≥0∞) =
          (N : ℝ≥0∞) ^ p := by
        calc
          (N : ℝ≥0∞) ^ (p - 1) * (N : ℝ≥0∞) =
              (N : ℝ≥0∞) ^ (p - 1) * (N : ℝ≥0∞) ^ (1 : ℝ) := by simp
          _ = (N : ℝ≥0∞) ^ ((p - 1) + 1) := by
            rw [ENNReal.rpow_add _ _ (by exact_mod_cast (Nat.ne_of_gt hN)) (by simp)]
          _ = (N : ℝ≥0∞) ^ p := by congr 1 <;> simp
      calc
        A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
            ∑ t, (N : ℝ≥0∞) * b t ^ p =
            A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
              ((N : ℝ≥0∞) * ∑ t, b t ^ p) := by rw [← Finset.mul_sum]
        _ = A ^ p * ((N : ℝ≥0∞) ^ (p - 1) * (N : ℝ≥0∞)) *
              ∑ t, b t ^ p := by ring
        _ = A ^ p * (N : ℝ≥0∞) ^ p * ∑ t, b t ^ p := by rw [hN]

end BrownianSharp.AlignmentFiniteOverlapRpow

end
