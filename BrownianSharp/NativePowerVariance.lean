import BrownianSharp.NativeGoodStatistics
import BrownianSharp.GaussianPairCovariance
import BrownianSharp.ShellVariance

/-! The actual native high-power statistic variance is bounded by its actual
common-prefix correlation kernel. All Gaussian laws and moments are discharged. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

theorem nativeGoodPowerStatistic_variance_le_pairKernel {d n : ℕ}
    (hd : 0 < d) (k : ℕ) :
    ProbabilityTheory.variance (nativeGoodPowerStatistic d n (2 * k))
      (productStandardGaussian (LayerIndex d n)) ≤
    (Fintype.card (NativeGoodGrid d n) : ℝ)⁻¹ ^ 2 *
      ∑ i : NativeGoodGrid d n, ∑ j : NativeGoodGrid d n,
        highPowerPairKernel (2 * k) (nativeRowCorrelation i.val j.val) := by
  letI := nativeGoodGrid_nonempty (d := d) (n := n) hd
  let G : LayerIndex d n → (LayerIndex d n → ℝ) → ℝ := fun a x => x a
  have hG (a : LayerIndex d n) : Measurable (G a) := measurable_pi_apply a
  have hLaw (a : LayerIndex d n) :
      (productStandardGaussian (LayerIndex d n)).map (G a) = gaussianReal 0 1 :=
    productStandardGaussian_coordinate_law a
  have hIndep : iIndepFun G (productStandardGaussian (LayerIndex d n)) :=
    productStandardGaussian_coordinates_independent _
  have hM : 0 < standardGaussianMoment (2 * k) := by
    unfold standardGaussianMoment
    rw [standardGaussian_evenMoment]
    positivity
  have hLp (i : NativeGoodGrid d n) :
      MemLp (fun x : LayerIndex d n → ℝ => (∑ a, nativeGoodMatrix d n i a * x a) ^ (2 * k))
        2 (productStandardGaussian (LayerIndex d n)) :=
    normalized_matrix_row_power_memLp_two _ (nativeGoodMatrix_unit_rows hd) i (2 * k)
  apply normalizedPowerAverage_variance_le _ (2 * k) _ hM hLp
  intro i j
  have h := normalizedGaussianRows_actualCovariance_bound G hG hLaw hIndep
    (nativeGoodMatrix d n i) (nativeGoodMatrix d n j)
    (nativeGoodMatrix_unit_rows hd i) (nativeGoodMatrix_unit_rows hd j) k (hLp i) (hLp j)
  have hdot : (∑ a, nativeGoodMatrix d n i a * nativeGoodMatrix d n j a) =
      nativeRowCorrelation i.val j.val := nativeStandardMatrix_dot _ i j
  rw [hdot] at h
  have hkernel : ((4 * k : ℝ) * |nativeRowCorrelation i.val j.val|) ^ 2 *
      Real.exp ((4 * k : ℝ) * |nativeRowCorrelation i.val j.val|) =
      highPowerPairKernel (2 * k) (nativeRowCorrelation i.val j.val) := by
    unfold highPowerPairKernel
    push_cast
    rw [mul_pow, sq_abs]
    congr 1 <;> ring
  rw [hkernel] at h
  exact h

end BrownianSharp
