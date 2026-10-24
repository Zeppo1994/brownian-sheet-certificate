import BrownianSharp.AlignmentHilbertDictionary
import Mathlib.Topology.PartitionOfUnity

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp.AlignmentHilbertDictionary
variable {α G H : Type} [TopologicalSpace α] [CompactSpace α] [Fintype G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def partitionReconstruction (φ : G → C(α, ℝ)) : (G → ℝ) →L[ℝ] C(α, ℝ) :=
  ∑ i, (ContinuousLinearMap.proj i).smulRight (φ i)

theorem partitionReconstruction_apply (φ : G → C(α, ℝ)) (z : G → ℝ) (t : α) :
    partitionReconstruction φ z t = ∑ i, φ i t * z i := by
  simp [partitionReconstruction, mul_comm]

theorem partitionReconstruction_contractile (φ : G → C(α, ℝ))
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1) (z : G → ℝ) :
    ‖partitionReconstruction φ z‖ ≤ ‖z‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg z)).2
  intro t
  rw [partitionReconstruction_apply]
  calc
    ‖∑ i, φ i t * z i‖ ≤ ∑ i, ‖φ i t * z i‖ := norm_sum_le _ _
    _ ≤ ∑ i, φ i t * ‖z‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφ i t)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z i) (hφ i t)
    _ = ‖z‖ := by rw [← Finset.sum_mul, hsum, one_mul]

/-- A continuous Hilbert-feature field can be approximated from any positive
sampling partition. The cost is exactly its feature oscillation plus the KGG
finite dictionary bound; the rank does not depend on the Hilbert dimension. -/
theorem partition_feature_approximation
    (v : α → H) (φ : G → C(α, ℝ)) (a : G → α)
    (hφ : ∀ i t, 0 ≤ φ i t) (hsum : ∀ t, ∑ i, φ i t = 1)
    (m : ℕ) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ)
    (hv : ∀ i, ‖v (a i)‖ ≤ R)
    (hosc : ∀ i t, φ i t ≠ 0 → ‖v t-v (a i)‖ ≤ δ) :
    ∃ W : Submodule ℝ C(α, ℝ), Module.rank ℝ W ≤ (m : Cardinal) ∧
      ∀ x : H, ‖x‖ ≤ 1 → ∃ y ∈ W, ∀ t,
        ‖⟪x, v t⟫ - y t‖ ≤ δ + 10000 * R * Real.sqrt
          (Real.log (2 * (Fintype.card G : ℝ) + 2) / ((m : ℝ) + 1)) := by
  classical
  obtain ⟨V, hV, happ⟩ := hilbert_dictionary_approximation m (fun i => v (a i)) R hR hv
  let E := partitionReconstruction φ
  refine ⟨V.map E.toLinearMap, (rank_map_le _ _).trans hV, ?_⟩
  intro x hx
  obtain ⟨z, hz, herr⟩ := happ x hx
  refine ⟨E z, Submodule.mem_map.mpr ⟨z, hz, rfl⟩, ?_⟩
  intro t
  let f : G → ℝ := fun i => ⟪x, v (a i)⟫
  have hlocal : ‖⟪x, v t⟫ - E f t‖ ≤ δ := by
    have hid : ⟪x, v t⟫ - E f t =
        ∑ i, φ i t * ⟪x, v t-v (a i)⟫ := by
      simp only [E, partitionReconstruction_apply, inner_sub_right]
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, hsum, one_mul]
    rw [hid]
    calc
      ‖∑ i, φ i t * ⟪x, v t-v (a i)⟫‖ ≤
          ∑ i, ‖φ i t * ⟪x, v t-v (a i)⟫‖ := norm_sum_le _ _
      _ ≤ ∑ i, φ i t * δ := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hz : φ i t = 0
        · simp [hz, hδ]
        · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hφ i t)]
          apply mul_le_mul_of_nonneg_left _ (hφ i t)
          exact (norm_inner_le_norm _ _).trans
            ((mul_le_mul hx (hosc i t hz) (norm_nonneg _) (by norm_num)).trans (by simp))
      _ = δ := by rw [← Finset.sum_mul, hsum, one_mul]
  calc
    ‖⟪x, v t⟫ - E z t‖ ≤ ‖⟪x, v t⟫-E f t‖ + ‖E f t-E z t‖ := by simpa only [dist_eq_norm] using (dist_triangle (⟪x, v t⟫ : ℝ) (E f t) (E z t))
    _ ≤ δ + ‖E (f-z)‖ := by
      apply add_le_add hlocal
      simpa only [map_sub, ContinuousMap.sub_apply] using
        (ContinuousMap.norm_coe_le_norm (E (f-z)) t)
    _ ≤ δ + _ := add_le_add_right
      ((partitionReconstruction_contractile φ hφ hsum (f-z)).trans herr) δ

end BrownianSharp.AlignmentHilbertDictionary
