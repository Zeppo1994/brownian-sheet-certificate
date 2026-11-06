import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-! Finite shape aggregation at the actual Lp energy level. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperFiniteShapeEnergy

theorem sum_energy_le_card_square_budget {ι : Type*} [Fintype ι]
    (E : ι → ℝ) (hE : ∀ i, 0 ≤ E i) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    (∑ i, E i) ≤ (Fintype.card ι : ℝ)^(1-p/2) *
      (∑ i, (E i)^(2/p))^(p/2) := by
  classical
  have hq : 1 ≤ 2/p := (le_div_iff₀ hp).mpr (by simpa only [one_mul] using hp2)
  have h := Real.rpow_sum_le_const_mul_sum_rpow
    (Finset.univ : Finset ι) (f := E) hq
  simp only [abs_of_nonneg (hE _), Finset.card_univ] at h
  have hs : 0 ≤ ∑ i, E i := Finset.sum_nonneg (fun i _ => hE i)
  have ht : 0 ≤ ∑ i, (E i)^(2/p) := Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (hE _) _)
  have hpow := Real.rpow_le_rpow (Real.rpow_nonneg hs _) h (show 0 ≤ p/2 by positivity)
  have hcancel : (2/p)*(p/2) = (1:ℝ) := by field_simp
  have hexponent : (2/p-1)*(p/2) = 1-p/2 := by field_simp
  rw [← Real.rpow_mul hs, hcancel, Real.rpow_one,
    Real.mul_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) ht,
    ← Real.rpow_mul (Nat.cast_nonneg _), hexponent] at hpow
  exact hpow
end BrownianSharp.AlignmentPaperFiniteShapeEnergy
