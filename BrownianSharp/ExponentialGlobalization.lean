import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Finite initial scales can be absorbed in a positive exponential constant. -/
noncomputable section
namespace BrownianSharp

/-- A finite family of probabilities strictly below one admits a common
positive exponential constant against arbitrary positive dimensions. -/
theorem finite_exponential_bound (I : Finset ℕ) (P D : ℕ → ℝ)
    (hD : ∀ n ∈ I, 0 < D n) (hP : ∀ n ∈ I, P n < 1) :
    ∃ b : ℝ, 0 < b ∧ ∀ n ∈ I, P n ≤ Real.exp (-b * D n) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert n I hn ih =>
    obtain ⟨b, hb, hbound⟩ := ih (fun k hk => hD k (Finset.mem_insert_of_mem hk))
      (fun k hk => hP k (Finset.mem_insert_of_mem hk))
    let c := (1-P n)/(D n)
    have hDn := hD n (Finset.mem_insert_self _ _)
    have hPn := hP n (Finset.mem_insert_self _ _)
    have hc : 0 < c := div_pos (by linarith) hDn
    refine ⟨min b c, lt_min hb hc, ?_⟩
    intro k hk
    rcases Finset.mem_insert.mp hk with hkn | hk
    · subst k
      have hmul := mul_le_mul_of_nonneg_right (min_le_right b c) hDn.le
      have hcancel : c * D n = 1-P n := by dsimp [c]; field_simp
      have he := Real.add_one_le_exp (-(min b c) * D n)
      nlinarith
    · exact (hbound k hk).trans (Real.exp_le_exp.mpr
        (by nlinarith [mul_le_mul_of_nonneg_right (min_le_left b c) (hD k (Finset.mem_insert_of_mem hk)).le]))

/-- An eventual exponential bound, together with strict probability less than
one at every initial scale, gives a bound at all positive requested scales. -/
theorem eventual_exponential_bound_global (P D : ℕ → ℝ) (N₀ N : ℕ)
    (hD : ∀ n, N₀ ≤ n → 0 < D n)
    (hP : ∀ n, N₀ ≤ n → P n < 1)
    {b : ℝ} (hb : 0 < b)
    (hbound : ∀ n, N ≤ n → P n ≤ Real.exp (-b * D n)) :
    ∃ c : ℝ, 0 < c ∧ ∀ n, N₀ ≤ n → P n ≤ Real.exp (-c * D n) := by
  let I := (Finset.range N).filter (N₀ ≤ ·)
  obtain ⟨c, hc, hfinite⟩ := finite_exponential_bound I P D
    (fun n hn => hD n (Finset.mem_filter.mp hn).2)
    (fun n hn => hP n (Finset.mem_filter.mp hn).2)
  refine ⟨min b c, lt_min hb hc, ?_⟩
  intro n hn
  by_cases hN : N ≤ n
  · exact (hbound n hN).trans (Real.exp_le_exp.mpr
      (by nlinarith [mul_le_mul_of_nonneg_right (min_le_left b c) (hD n hn).le]))
  · have hin : n ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hn⟩
    exact (hfinite n hin).trans (Real.exp_le_exp.mpr
      (by nlinarith [mul_le_mul_of_nonneg_right (min_le_right b c) (hD n hn).le]))

end BrownianSharp
