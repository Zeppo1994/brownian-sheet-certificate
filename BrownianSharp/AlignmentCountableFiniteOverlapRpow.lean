import BrownianSharp.AlignmentFiniteOverlapRpow
import Mathlib.Analysis.MeanInequalities

noncomputable section
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentCountableFiniteOverlapRpow

/-- Countable finite-overlap transfer. `row` and `col` are the exact finite
neighborhoods in the relation, so no support or summability hypotheses are
needed; all sums are `ENNReal` `tsum`s. -/
theorem countable_overlap_rpow_tsum_le
    {S T : Type*} [Countable S] [Countable T]
    (R : S → T → Prop) [DecidableRel R]
    (row : S → Finset T) (col : T → Finset S)
    (hrowSpec : ∀ s t, t ∈ row s ↔ R s t)
    (hcolSpec : ∀ s t, s ∈ col t ↔ R s t)
    (A : ℝ≥0∞) (N : ℕ) (hN : 0 < N) (p : ℝ) (hp : 1 ≤ p)
    (hrow : ∀ s, (row s).card ≤ N) (hcol : ∀ t, (col t).card ≤ N)
    (a : S → ℝ≥0∞) (b : T → ℝ≥0∞)
    (hpoint : ∀ s, a s ≤ A * ∑' t, if R s t then b t else 0) :
    (∑' s, a s ^ p) ≤ (A * (N : ℝ≥0∞)) ^ p * ∑' t, b t ^ p := by
  classical
  have hlocal (s : S) : a s ^ p ≤
      A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
        ∑' t, if R s t then b t ^ p else 0 := by
    have hrowSum :
        (∑' t, if R s t then b t else 0) = ∑ t ∈ row s, b t := by
      calc
        (∑' t, if R s t then b t else 0) =
            ∑ t ∈ row s, (if R s t then b t else 0) :=
          tsum_eq_sum (f := fun t : T => if R s t then b t else 0)
            (L := SummationFilter.unconditional T) (s := row s) (fun t ht =>
              if_neg (fun hrt => ht ((hrowSpec s t).2 hrt)))
        _ = ∑ t ∈ row s, b t := by
          apply Finset.sum_congr rfl
          intro t ht
          have hrt : R s t := (hrowSpec s t).1 ht
          simp [hrt]
    have hrowPow :
        (∑ t ∈ row s, b t) ^ p ≤
          ((row s).card : ℝ≥0∞) ^ (p - 1) * ∑ t ∈ row s, b t ^ p :=
      ENNReal.rpow_sum_le_const_mul_sum_rpow (row s) b hp
    have hrowPowTsum :
        (∑ t ∈ row s, b t ^ p) = ∑' t, if R s t then b t ^ p else 0 := by
      symm
      calc
        (∑' t, if R s t then b t ^ p else 0) =
            ∑ t ∈ row s, (if R s t then b t ^ p else 0) :=
          tsum_eq_sum (f := fun t : T => if R s t then b t ^ p else 0)
            (L := SummationFilter.unconditional T) (s := row s) (fun t ht =>
              if_neg (fun hrt => ht ((hrowSpec s t).2 hrt)))
        _ = ∑ t ∈ row s, b t ^ p := by
          apply Finset.sum_congr rfl
          intro t ht
          have hrt : R s t := (hrowSpec s t).1 ht
          simp [hrt]
    calc
      a s ^ p ≤ (A * (∑' t, if R s t then b t else 0)) ^ p :=
        ENNReal.rpow_le_rpow (hpoint s) (by linarith)
      _ = A ^ p * (∑ t ∈ row s, b t) ^ p := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), hrowSum]
      _ ≤ A ^ p * ((row s).card : ℝ≥0∞) ^ (p - 1) *
            ∑ t ∈ row s, b t ^ p := by
        rw [mul_assoc]
        gcongr
      _ ≤ A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
            ∑ t ∈ row s, b t ^ p := by
        gcongr
        · exact_mod_cast hrow s
      _ = A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
            ∑' t, if R s t then b t ^ p else 0 := by rw [hrowPowTsum]
  calc
    (∑' s, a s ^ p) ≤
        ∑' s, A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
          (∑' t, if R s t then b t ^ p else 0) :=
      ENNReal.tsum_le_tsum hlocal
    _ = A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
          ∑' s, ∑' t, if R s t then b t ^ p else 0 := by
      rw [ENNReal.tsum_mul_left]
    _ = A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
          ∑' t, ∑' s, if R s t then b t ^ p else 0 := by
      rw [ENNReal.tsum_comm]
    _ = A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
          ∑' t, (col t).card * b t ^ p := by
      congr 1
      apply tsum_congr
      intro t
      have hcolTsum :
          (∑' s, if R s t then b t ^ p else 0) = ∑ s ∈ col t, b t ^ p :=
        calc
          (∑' s, if R s t then b t ^ p else 0) =
              ∑ s ∈ col t, (if R s t then b t ^ p else 0) :=
            tsum_eq_sum (f := fun s : S => if R s t then b t ^ p else 0)
              (L := SummationFilter.unconditional S) (s := col t) (fun s hs =>
                if_neg (fun hst => hs ((hcolSpec s t).2 hst)))
          _ = ∑ s ∈ col t, b t ^ p := by
            apply Finset.sum_congr rfl
            intro s hs
            have hst : R s t := (hcolSpec s t).1 hs
            simp [hst]
      rw [hcolTsum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
          ∑' t, (N : ℝ≥0∞) * b t ^ p := by
      gcongr with t
      exact_mod_cast hcol t
    _ = (A * (N : ℝ≥0∞)) ^ p * ∑' t, b t ^ p := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
      calc
        A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
            ∑' t, (N : ℝ≥0∞) * b t ^ p =
            A ^ p * (N : ℝ≥0∞) ^ (p - 1) *
              ((N : ℝ≥0∞) * ∑' t, b t ^ p) := by rw [ENNReal.tsum_mul_left]
        _ = A ^ p * ((N : ℝ≥0∞) ^ (p - 1) * (N : ℝ≥0∞)) *
              ∑' t, b t ^ p := by ring
        _ = A ^ p * (N : ℝ≥0∞) ^ p * ∑' t, b t ^ p := by
          congr 1
          have hpow : (N : ℝ≥0∞) ^ (p - 1) * (N : ℝ≥0∞) =
              (N : ℝ≥0∞) ^ p := by
            have hNne : (N : ℝ≥0∞) ≠ 0 := by
              exact_mod_cast (Nat.ne_of_gt hN)
            have hNtop : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
            calc
              (N : ℝ≥0∞) ^ (p - 1) * (N : ℝ≥0∞) =
                  (N : ℝ≥0∞) ^ (p - 1) * (N : ℝ≥0∞) ^ 1 := by simp
              _ = (N : ℝ≥0∞) ^ ((p - 1) + 1) := by
                simpa [sub_add_cancel] using
                  (ENNReal.rpow_add (x := (N : ℝ≥0∞)) (p - 1) 1 hNne hNtop).symm
              _ = (N : ℝ≥0∞) ^ p := by congr 1 <;> linarith
          rw [hpow]

end BrownianSharp.AlignmentCountableFiniteOverlapRpow

end
