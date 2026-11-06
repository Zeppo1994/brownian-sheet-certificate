import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Sharp finite support-label counting, using the elementary weighted
powerset identity rather than a factorial estimate. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperSparseSupportCount

theorem sparse_support_count_le {D r : ℕ} (hr : 1 ≤ r) (hrD : r ≤ D) :
    (((Finset.univ : Finset (Finset (Fin D))).filter
      (fun A => A.card ≤ r)).card : ℝ) ≤
        Real.exp (r : ℝ) * ((D : ℝ) / (r : ℝ)) ^ r := by
  classical
  let S : Finset (Fin D) := Finset.univ
  let L := S.powerset.filter (fun A => A.card ≤ r)
  let x : ℝ := (r : ℝ) / (D : ℝ)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (by omega : 0 < D)
  have hx0 : 0 < x := div_pos hr0 hD0
  have hx1 : x ≤ 1 := (div_le_one hD0).2 (by exact_mod_cast hrD)
  have hweight : (L.card : ℝ) * x ^ r ≤ ∑ A ∈ S.powerset, x ^ A.card := by
    calc
      (L.card : ℝ) * x ^ r = ∑ A ∈ L, x ^ r := by simp
      _ ≤ ∑ A ∈ L, x ^ A.card := by
        apply Finset.sum_le_sum
        intro A hA
        exact pow_le_pow_of_le_one hx0.le hx1 (Finset.mem_filter.mp hA).2
      _ ≤ ∑ A ∈ S.powerset, x ^ A.card := by
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun A hA hnot => pow_nonneg hx0.le _)
  have hsum : (∑ A ∈ S.powerset, x ^ A.card) = (1+x)^D := by
    simpa [S] using (Finset.prod_one_add (f := fun _ : Fin D => x) S).symm
  have hexp : (1+x)^D ≤ Real.exp (r : ℝ) := by
    calc
      (1+x)^D ≤ (Real.exp x)^D := by
        apply pow_le_pow_left₀ (by positivity)
        simpa [add_comm] using Real.add_one_le_exp x
      _ = Real.exp ((D : ℝ)*x) := (Real.exp_nat_mul x D).symm
      _ = Real.exp (r : ℝ) := by congr 1; dsimp [x]; field_simp
  have hbound := hweight.trans (hsum.le.trans hexp)
  have hcard : (L.card : ℝ) ≤ Real.exp (r : ℝ) / x^r :=
    (le_div_iff₀ (pow_pos hx0 _)).2 hbound
  have hinv : Real.exp (r : ℝ) / x^r =
      Real.exp (r : ℝ) * ((D : ℝ)/(r : ℝ))^r := by
    rw [div_eq_mul_inv, ← inv_pow]
    congr 1
    dsimp [x]
    rw [inv_div]
  rw [hinv] at hcard
  simpa [L, S] using hcard

end BrownianSharp.AlignmentPaperSparseSupportCount
