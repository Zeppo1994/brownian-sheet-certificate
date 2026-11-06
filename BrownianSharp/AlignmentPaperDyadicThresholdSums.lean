import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

/-! Depth-independent low/high dyadic threshold sums for the actual kernel
Hörmander estimates. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperDyadicThresholdSums

private theorem finite_inverse_dyadic_sum_le_two (S : Finset ℕ) :
    (∑ s ∈ S, (1/2:ℝ)^s) ≤ 2 := by
  classical
  by_cases hS : S.Nonempty
  · let N := S.max' hS
    have hsub : S ⊆ Finset.range (N+1) := by
      intro s hs
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' S s hs))
    calc
      _ ≤ ∑ s ∈ Finset.range (N+1), (1/2:ℝ)^s := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro s hs hnot
        positivity
      _ ≤ 2 := by
        rw [geom_sum_eq (by norm_num : (1/2:ℝ) ≠ 1)]
        have hpow : 0 ≤ (1/2:ℝ)^(N+1) := by positivity
        norm_num
        nlinarith
  · have : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    simp [this]

theorem low_dyadic_threshold_sum_le_two (S : Finset ℕ) {a : ℝ} (ha : 0 < a) :
    (∑ s ∈ S.filter (fun s => a*(2:ℝ)^s ≤ 1), a*(2:ℝ)^s) ≤ 2 := by
  classical
  let L := S.filter (fun s => a*(2:ℝ)^s ≤ 1)
  by_cases hL : L.Nonempty
  · let N := L.max' hL
    have hN : a*(2:ℝ)^N ≤ 1 :=
      (Finset.mem_filter.mp (Finset.max'_mem L hL)).2
    have hsub : L ⊆ Finset.range (N+1) := by
      intro s hs
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_max' L s hs))
    change (∑ s ∈ L, a*(2:ℝ)^s) ≤ 2
    calc
      _ ≤ ∑ s ∈ Finset.range (N+1), a*(2:ℝ)^s := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro s hs hnot
        positivity
      _ = a*((2:ℝ)^(N+1)-1) := by
        rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (2:ℝ) ≠ 1)]
        norm_num
      _ ≤ 2 := by
        rw [pow_succ]
        nlinarith
  · have : L = ∅ := Finset.not_nonempty_iff_eq_empty.mp hL
    change (∑ s ∈ L, a*(2:ℝ)^s) ≤ 2
    simp [this]

theorem high_dyadic_threshold_sum_le_two (S : Finset ℕ) {a : ℝ} (ha : 0 < a) :
    (∑ s ∈ S.filter (fun s => 1 < a*(2:ℝ)^s), (a*(2:ℝ)^s)⁻¹) ≤ 2 := by
  classical
  let H := S.filter (fun s => 1 < a*(2:ℝ)^s)
  by_cases hH : H.Nonempty
  · let N := H.min' hH
    have hN : 1 < a*(2:ℝ)^N :=
      (Finset.mem_filter.mp (Finset.min'_mem H hH)).2
    have hmin : ∀ s ∈ H, N ≤ s := fun s hs => Finset.min'_le H s hs
    have hinj : Set.InjOn (fun s : ℕ => s-N) (H : Set ℕ) := by
      intro i hi j hj heq
      have hiN := hmin i hi
      have hjN := hmin j hj
      change i-N = j-N at heq
      omega
    have hsum : (∑ s ∈ H, (1/2:ℝ)^(s-N)) ≤ 2 := by
      rw [← Finset.sum_image hinj]
      exact finite_inverse_dyadic_sum_le_two _
    have hfactor : ∀ s ∈ H,
        (a*(2:ℝ)^s)⁻¹ = (a*(2:ℝ)^N)⁻¹ * (1/2:ℝ)^(s-N) := by
      intro s hs
      have hpow : (2:ℝ)^s = (2:ℝ)^N * (2:ℝ)^(s-N) := by
        rw [← pow_add, Nat.add_sub_of_le (hmin s hs)]
      rw [hpow]
      simp only [one_div, inv_pow, mul_inv_rev]
      ring
    have hfacpos : 0 ≤ (a*(2:ℝ)^N)⁻¹ := by positivity
    have hfacone : (a*(2:ℝ)^N)⁻¹ ≤ 1 :=
      (inv_le_one₀ (by positivity : 0 < a*(2:ℝ)^N)).2 hN.le
    change (∑ s ∈ H, (a*(2:ℝ)^s)⁻¹) ≤ 2
    calc
      _ = (a*(2:ℝ)^N)⁻¹ * ∑ s ∈ H, (1/2:ℝ)^(s-N) := by
        simp_rw [Finset.sum_congr rfl hfactor]
        rw [Finset.mul_sum]
      _ ≤ (a*(2:ℝ)^N)⁻¹ * 2 := mul_le_mul_of_nonneg_left hsum hfacpos
      _ ≤ 2 := by linarith
  · have : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hH
    change (∑ s ∈ H, (a*(2:ℝ)^s)⁻¹) ≤ 2
    simp [this]

end BrownianSharp.AlignmentPaperDyadicThresholdSums
