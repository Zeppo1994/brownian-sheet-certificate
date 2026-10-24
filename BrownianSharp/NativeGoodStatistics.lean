import BrownianSharp.NativeGoodGrid
import BrownianSharp.NativeMatrix
import BrownianSharp.GridConfinement

/-! The manuscript's actual normalized high-power statistic, with its
expectation, nondegeneracy and integrability discharged on the proved good grid. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

def nativeGoodMatrix (d n : ℕ) : NativeGoodGrid d n → LayerIndex d n → ℝ :=
  nativeStandardMatrix (fun q : NativeGoodGrid d n => q.val)

def nativeGoodPowerStatistic (d n p : ℕ) (x : LayerIndex d n → ℝ) : ℝ :=
  normalizedPowerAverage (fun q x => ∑ a, nativeGoodMatrix d n q a * x a)
    p (standardGaussianMoment p) x

def nativeGoodRootStatistic (d n p : ℕ) (x : LayerIndex d n → ℝ) : ℝ :=
  nativeGoodPowerStatistic d n p x ^ (1 / (p : ℝ))

theorem nativeGoodGrid_variance_pos {d n : ℕ} (hd : 0 < d)
    (q : NativeGoodGrid d n) : 0 < nativeLayerRowVariance q.val :=
  (half_pos (nativeVarianceMeanLowerBound_pos hd)).trans_le q.property

theorem nativeGoodMatrix_unit_rows {d n : ℕ} (hd : 0 < d) (q : NativeGoodGrid d n) :
    ∑ a, nativeGoodMatrix d n q a ^ 2 = 1 :=
  nativeStandardMatrix_unit_rows _ (nativeGoodGrid_variance_pos hd) q

theorem nativeGoodMatrix_nonzero {d n : ℕ} (hd : 0 < d) :
    ∃ q a, nativeGoodMatrix d n q a ≠ 0 := by
  letI := nativeGoodGrid_nonempty (d := d) (n := n) hd
  exact nativeStandardMatrix_nonzero _ (nativeGoodGrid_variance_pos hd)

theorem nativeGoodPowerStatistic_mean {d n p : ℕ} (hd : 0 < d)
    (hM : standardGaussianMoment p ≠ 0) :
    (∫ x, nativeGoodPowerStatistic d n p x ∂productStandardGaussian (LayerIndex d n)) = 1 := by
  letI := nativeGoodGrid_nonempty (d := d) (n := n) hd
  exact nativeStandardMatrix_power_mean _ (nativeGoodGrid_variance_pos hd) p hM

theorem nativeGoodPowerStatistic_memLp_two {d n p : ℕ} (hd : 0 < d) :
    MemLp (nativeGoodPowerStatistic d n p) 2 (productStandardGaussian (LayerIndex d n)) :=
  nativeStandardMatrix_power_memLp_two _ (nativeGoodGrid_variance_pos hd) p

theorem nativeGoodPowerStatistic_nonneg {d n p : ℕ} (heven : Even p)
    (hM : 0 < standardGaussianMoment p) (x : LayerIndex d n → ℝ) :
    0 ≤ nativeGoodPowerStatistic d n p x := by
  unfold nativeGoodPowerStatistic normalizedPowerAverage
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro i _
    exact heven.pow_nonneg _
  · positivity

theorem nativeGoodRootStatistic_eq {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p)
    (x : LayerIndex d n → ℝ) :
    nativeGoodRootStatistic d n p x =
      letI := nativeGoodGrid_nonempty (d := d) (n := n) hd
      finiteGridRoot p (nativeGoodMatrix d n) x /
        standardGaussianMoment p ^ (1 / (p : ℝ)) := by
  letI := nativeGoodGrid_nonempty (d := d) (n := n) hd
  exact normalized_matrix_power_root_eq p hp heven _ hM x

end BrownianSharp
