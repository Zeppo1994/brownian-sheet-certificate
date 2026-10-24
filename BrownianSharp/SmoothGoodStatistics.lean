import BrownianSharp.SmoothGaussian
import BrownianSharp.ActualConcentration

set_option maxHeartbeats 800000

/-! The manuscript's normalized smooth-layer moment/root statistics on the
proved positive-density good grid, together with the conditional PV tails and
the deterministic uniform-confinement bridge. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BrownianSharp

private theorem smoothProductGaussian_coeff_memLp_two (κ : Type*) [Fintype κ] :
    MemLp (id : (κ → ℝ) → κ → ℝ) 2 (productStandardGaussian κ) := by
  apply MeasureTheory.memLp_pi_iff.mpr
  intro k
  exact (GaussianRows.coordinate_gaussian
    (fun (j : κ) (x : κ → ℝ) => x j)
    (fun j => measurable_pi_apply j)
    (fun j => productStandardGaussian_coordinate_law j) k).memLp_two

def smoothGoodPowerStatistic (d n p : ℕ)
    (x : LayerIndex d n → ℝ) : ℝ :=
  normalizedPowerAverage
    (fun q x => ∑ a, smoothGoodMatrix d n q a * x a)
    p (standardGaussianMoment p) x

def smoothGoodRootStatistic (d n p : ℕ)
    (x : LayerIndex d n → ℝ) : ℝ :=
  smoothGoodPowerStatistic d n p x ^ (1 / (p : ℝ))

theorem smoothGoodPowerStatistic_mean {d n p : ℕ} (hd : 0 < d)
    (hM : standardGaussianMoment p ≠ 0) :
    (∫ x : LayerIndex d n → ℝ,
      smoothGoodPowerStatistic d n p x
        ∂productStandardGaussian (LayerIndex d n)) = 1 := by
  letI := smoothGoodGrid_nonempty (d := d) (n := n) hd
  exact smoothGoodMatrix_power_mean hd hM

theorem smoothGoodPowerStatistic_memLp_two {d n p : ℕ} (hd : 0 < d) :
    MemLp (smoothGoodPowerStatistic d n p) 2
      (productStandardGaussian (LayerIndex d n)) :=
  smoothGoodMatrix_power_memLp_two hd

theorem smoothGoodPowerStatistic_nonneg {d n p : ℕ} (heven : Even p)
    (hM : 0 < standardGaussianMoment p) (x : LayerIndex d n → ℝ) :
    0 ≤ smoothGoodPowerStatistic d n p x :=
  smoothGoodMatrix_power_nonneg heven hM x

theorem smoothGoodRootStatistic_eq {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p)
    (x : LayerIndex d n → ℝ) :
    smoothGoodRootStatistic d n p x =
      (letI := smoothGoodGrid_nonempty (d := d) (n := n) hd
      finiteGridRoot p (smoothGoodMatrix d n) x /
        standardGaussianMoment p ^ (1 / (p : ℝ))) := by
  letI := smoothGoodGrid_nonempty (d := d) (n := n) hd
  exact normalized_matrix_power_root_eq p hp heven
    (smoothGoodMatrix d n) hM x

theorem smoothGoodRootStatistic_memLp_two {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p) :
    MemLp (smoothGoodRootStatistic d n p) 2
      (productStandardGaussian (LayerIndex d n)) := by
  letI := smoothGoodGrid_nonempty (d := d) (n := n) hd
  have h := (finiteGridRoot_memLp_two_of_coeff_memLp
    (smoothProductGaussian_coeff_memLp_two (LayerIndex d n)) p hp
      (smoothGoodMatrix d n)).const_mul
      ((standardGaussianMoment p ^ (1 / (p : ℝ)))⁻¹)
  have heq : smoothGoodRootStatistic d n p = fun x =>
      (standardGaussianMoment p ^ (1 / (p : ℝ)))⁻¹ *
        finiteGridRoot p (smoothGoodMatrix d n) x := by
    funext x
    rw [smoothGoodRootStatistic_eq hd hp heven hM]
    ring
  rw [heq]
  exact h

theorem smoothGoodRootStatistic_nonneg {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p)
    (x : LayerIndex d n → ℝ) : 0 ≤ smoothGoodRootStatistic d n p x := by
  rw [smoothGoodRootStatistic]
  exact Real.rpow_nonneg (smoothGoodMatrix_power_nonneg heven hM x) _

/-- Under the explicit set-level Ehrhard premise, the actual smooth moment
and its actual p-root satisfy the variance-sensitive lower tails. -/
theorem smoothGoodStatistics_variance_sensitive_tail {d n p : ℕ}
    (hd : 0 < d) (hp : 2 ≤ p) (heven : Even p)
    (hEhrhard : Concentration.GaussianEhrhard (LayerIndex d n → ℝ)
      (productStandardGaussian (LayerIndex d n))) :
    VarianceSensitiveLowerTail (productStandardGaussian (LayerIndex d n))
      (smoothGoodPowerStatistic d n p) (Real.pi / 4096) ∧
    VarianceSensitiveLowerTail (productStandardGaussian (LayerIndex d n))
      (smoothGoodRootStatistic d n p) (Real.pi / 4096) := by
  letI := smoothGoodGrid_nonempty (d := d) (n := n) hd
  have hnorm : ∀ q : SmoothGoodGrid d n,
      ∑ a : LayerIndex d n, smoothGoodMatrix d n q a ^ 2 = 1 :=
    smoothGoodMatrix_unit_rows hd
  have h := normalized_finiteGridMoment_and_root_variance_sensitive_tail
    p hp heven (smoothGoodMatrix d n) hnorm hEhrhard
  have hmoment : smoothGoodPowerStatistic d n p = fun x =>
      finiteGridMoment p (smoothGoodMatrix d n) x /
        standardGaussianMoment p := by
    funext x
    exact normalized_matrix_power_average_eq_moment
      (smoothGoodMatrix d n) p heven x
  have hroot : smoothGoodRootStatistic d n p = fun x =>
      (finiteGridMoment p (smoothGoodMatrix d n) x /
        standardGaussianMoment p) ^ (1 / (p : ℝ)) := by
    funext x
    change smoothGoodPowerStatistic d n p x ^ _ = _
    rw [hmoment]
  have hU := h.1
  have hR := h.2
  rw [← hmoment] at hU
  rw [← hroot] at hR
  exact ⟨hU, hR⟩

/-- Standardization converts a uniform bound on the unnormalized smooth
coefficient rows to the finite-grid root event. -/
theorem smooth_uniform_event_subset_normalized_root_event {d n : ℕ}
    (hd : 0 < d) (p : ℕ) (hp : 2 ≤ p) (heven : Even p)
    (hM : 0 < standardGaussianMoment p) {ε R : ℝ}
    (hε : 0 ≤ ε)
    (hthreshold : ε / Real.sqrt (smoothVarianceMeanLowerBound d n / 2) ≤
      R * (standardGaussianMoment p) ^ (1 / (p : ℝ))) :
    {x : LayerIndex d n → ℝ |
      ∀ q : SmoothGoodGrid d n,
        |∑ a : LayerIndex d n,
          smoothLayerAtom smoothAtom q.1 a * x a| ≤ ε} ⊆
    {x | smoothGoodRootStatistic d n p x ≤ R} := by
  letI := smoothGoodGrid_nonempty (d := d) (n := n) hd
  intro x hx
  change smoothGoodRootStatistic d n p x ≤ R
  rw [smoothGoodRootStatistic_eq hd hp heven hM]
  have hv0 : 0 < smoothVarianceMeanLowerBound d n / 2 :=
    half_pos (smoothVarianceMeanLowerBound_pos hd)
  have hroot : finiteGridRoot p (smoothGoodMatrix d n) x ≤
      ε / Real.sqrt (smoothVarianceMeanLowerBound d n / 2) := by
    apply finiteGridRoot_le_of_rows_le p hp (smoothGoodMatrix d n) x (by positivity)
    intro q
    have hvq : smoothVarianceMeanLowerBound d n / 2 ≤
        smoothLayerVariance q.1 := q.2
    have hrow : |∑ a : LayerIndex d n,
        smoothStandardMatrix (fun q : SmoothGoodGrid d n => q.1) q a * x a| ≤
          ε / Real.sqrt (smoothVarianceMeanLowerBound d n / 2) := by
      change |∑ a : LayerIndex d n,
        (smoothLayerAtom smoothAtom q.1 a /
          Real.sqrt (smoothLayerVariance q.1)) * x a| ≤ _
      have hsum :
          (∑ a : LayerIndex d n,
            (smoothLayerAtom smoothAtom q.1 a /
              Real.sqrt (smoothLayerVariance q.1)) * x a) =
            (∑ a : LayerIndex d n,
              smoothLayerAtom smoothAtom q.1 a * x a) /
                Real.sqrt (smoothLayerVariance q.1) := by
        calc
          _ = ∑ a : LayerIndex d n,
              (smoothLayerAtom smoothAtom q.1 a * x a) /
                Real.sqrt (smoothLayerVariance q.1) := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  ring
          _ = _ := by rw [← Finset.sum_div]
      rw [hsum, abs_div,
        abs_of_pos (Real.sqrt_pos.mpr (smoothGoodGrid_variance_pos hd q))]
      calc
        _ ≤ ε / Real.sqrt (smoothLayerVariance q.1) :=
          div_le_div_of_nonneg_right (hx q) (Real.sqrt_nonneg _)
        _ ≤ _ := div_le_div_of_nonneg_left hε (Real.sqrt_pos.mpr hv0)
          (Real.sqrt_le_sqrt hvq)
    simpa [smoothGoodMatrix] using hrow
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hM _)).2
  exact hroot.trans hthreshold

end BrownianSharp
