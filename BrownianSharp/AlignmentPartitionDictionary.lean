import BrownianSharp.GaussianDictionaryApproximation
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
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

end BrownianSharp.AlignmentHilbertDictionary
