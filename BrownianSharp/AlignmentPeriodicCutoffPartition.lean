import BrownianSharp.AlignmentPeriodicAdmissibleCutoff
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPeriodicCutoffPartition
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff

def tensorMultiplier {d : ℕ} (φ : AdmissibleCutoff)
    (s : Fin d → ℕ) (k : Fin d → ℤ) : ℝ :=
  ∏ i, scalarBlock φ (s i) (k i : ℝ)

theorem scalarBlock_eq_zero_of_abs_le_lower (φ : AdmissibleCutoff)
    (s : ℕ) (hs : 0 < s) {ξ : ℝ} (hξ : |ξ| ≤ (2 : ℝ) ^ (s - 1)) :
    scalarBlock φ s ξ = 0 := by
  have hlow : φ.value (ξ / (2 : ℝ) ^ (s - 1)) = 1 := by
    apply φ.one_of_abs_le_one
    rw [abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ (s - 1))]
    exact (div_le_one₀ (by positivity)).2 hξ
  have hhigh : φ.value (ξ / (2 : ℝ) ^ s) = 1 := by
    apply φ.one_of_abs_le_one
    rw [abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ s)]
    apply (div_le_one₀ (by positivity)).2
    exact hξ.trans (pow_le_pow_right₀ (by norm_num) (by omega))
  simp [scalarBlock, Nat.ne_of_gt hs, hlow, hhigh]

theorem tensorMultiplier_eq_zero_outside_box {d : ℕ}
    (φ : AdmissibleCutoff) (s : Fin d → ℕ) (k : Fin d → ℤ)
    (hk : k ∉ SmoothResolution.frequencyBox s) :
    tensorMultiplier φ s k = 0 := by
  classical
  have hnot : ¬∀ i, k i ∈ Finset.Icc (-((2 : ℤ) ^ (s i + 1)))
      ((2 : ℤ) ^ (s i + 1)) := by
    simpa only [SmoothResolution.frequencyBox, Fintype.mem_piFinset] using hk
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  have hout : (2 : ℝ) ^ (s i + 1) ≤ |(k i : ℝ)| := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hi
    rcases hi with hi | hi
    · have h : (k i : ℝ) < -((2 : ℝ) ^ (s i + 1)) := by exact_mod_cast hi
      exact (by linarith : (2 : ℝ) ^ (s i + 1) ≤ -(k i : ℝ)).trans (neg_le_abs _)
    · have h : (2 : ℝ) ^ (s i + 1) < (k i : ℝ) := by exact_mod_cast hi
      exact h.le.trans (le_abs_self _)
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (scalarBlock_eq_zero_of_two_pow_le_abs φ (s i) hout)

theorem tensorMultiplier_hasSum {d : ℕ} (φ : AdmissibleCutoff) (k : Fin d → ℤ) :
    HasSum (fun s : Fin d → ℕ => tensorMultiplier φ s k) 1 := by
  classical
  have hp := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have hall : ∀ᶠ N : ℕ in Filter.atTop, ∀ i, |(k i : ℝ)| ≤ (2 : ℝ) ^ N :=
    Filter.eventually_all.mpr (fun i => hp.eventually_ge_atTop _)
  obtain ⟨N, hN⟩ := hall.exists
  let S := Fintype.piFinset (fun _ : Fin d => Finset.range (N + 1))
  have hzero : ∀ s ∉ S, tensorMultiplier φ s k = 0 := by
    intro s hs
    have hnot : ¬∀ i, s i ∈ Finset.range (N + 1) := by simpa [S] using hs
    obtain ⟨i, hi⟩ := not_forall.mp hnot
    have hsi : N + 1 ≤ s i := by simpa only [Finset.mem_range, not_lt] using hi
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact scalarBlock_eq_zero_of_abs_le_lower φ (s i) (by omega)
      ((hN i).trans (pow_le_pow_right₀ (by norm_num) (by omega)))
  have hsum : ∑ s ∈ S, tensorMultiplier φ s k = 1 := by
    unfold S tensorMultiplier
    rw [← Finset.prod_univ_sum (fun _ : Fin d => Finset.range (N + 1))
      (fun i n => scalarBlock φ n (k i : ℝ))]
    have hi : ∀ i, ∑ t ∈ Finset.range (N + 1),
        scalarBlock φ t (k i : ℝ) = 1 := by
      intro i
      rw [scalarBlock_sum]
      apply φ.one_of_abs_le_one
      rw [abs_div, abs_of_pos (by positivity : 0 < (2 : ℝ) ^ N)]
      exact (div_le_one₀ (by positivity)).2 (hN i)
    simp_rw [hi]
    simp
  simpa only [hsum] using hasSum_sum_of_ne_finset_zero hzero

end BrownianSharp.AlignmentPeriodicCutoffPartition
