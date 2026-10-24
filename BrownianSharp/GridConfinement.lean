import BrownianSharp.NativeMatrix
import BrownianSharp.TwoStageConfinement

/-! Deterministic conversion from actual uniform confinement to the normalized
p-root event used by the two concentration applications. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

theorem finiteGridRoot_nonneg {κ ι : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) (x : κ → ℝ) : 0 ≤ finiteGridRoot p A x := by
  letI : Fact (1 ≤ (p : ENNReal)) := ⟨by exact_mod_cast (show 1 ≤ p by omega)⟩
  unfold finiteGridRoot
  exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)

theorem finiteGridRoot_le_of_rows_le {κ ι : Type*}
    [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (A : ι → κ → ℝ) (x : κ → ℝ)
    {R : ℝ} (hR : 0 ≤ R) (hx : ∀ i, |∑ k, A i k * x k| ≤ R) :
    finiteGridRoot p A x ≤ R := by
  apply le_of_pow_le_pow_left₀ (by omega : p ≠ 0) hR
  rw [finiteGridRoot_pow_eq_moment p hp A]
  unfold finiteGridMoment
  have hc : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hc).2
  calc
    _ ≤ ∑ _i : ι, R ^ p := by
      apply Finset.sum_le_sum
      intro i _
      exact pow_le_pow_left₀ (abs_nonneg _) (hx i) p
    _ = _ := by simp [mul_comm]

theorem normalized_matrix_power_root_eq {κ ι : Type*}
    [Fintype κ] [Fintype ι] [Nonempty ι]
    (p : ℕ) (hp : 2 ≤ p) (heven : Even p) (A : ι → κ → ℝ)
    (hM : 0 < standardGaussianMoment p) (x : κ → ℝ) :
    (normalizedPowerAverage (fun i x => ∑ k, A i k * x k)
      p (standardGaussianMoment p) x) ^ (1 / (p : ℝ)) =
      finiteGridRoot p A x / (standardGaussianMoment p) ^ (1 / (p : ℝ)) := by
  rw [normalized_matrix_power_average_eq_moment A p heven]
  rw [← finiteGridRoot_pow_eq_moment p hp A]
  rw [Real.div_rpow (pow_nonneg (finiteGridRoot_nonneg p hp A x) p) hM.le]
  rw [one_div, Real.pow_rpow_inv_natCast (finiteGridRoot_nonneg p hp A x) (by omega : p ≠ 0)]

theorem native_uniform_event_subset_normalized_root_event {d n : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (q : ι → MidpointGridIndex d n)
    (p : ℕ) (hp : 2 ≤ p) (heven : Even p)
    (hM : 0 < standardGaussianMoment p) {v₀ ε R : ℝ} (hv₀ : 0 < v₀)
    (hv : ∀ i, v₀ ≤ nativeLayerRowVariance (q i)) (hε : 0 ≤ ε)
    (hthreshold : ε / Real.sqrt v₀ ≤ R *
      (standardGaussianMoment p) ^ (1 / (p : ℝ))) :
    {x : LayerIndex d n → ℝ |
      ∀ i, |∑ a, nativeLayerRowCoefficient (q i) a * x a| ≤ ε} ⊆
    {x | (normalizedPowerAverage (fun i x => ∑ a, nativeStandardMatrix q i a * x a)
      p (standardGaussianMoment p) x) ^ (1 / (p : ℝ)) ≤ R} := by
  intro x hx
  change _ ≤ R
  rw [normalized_matrix_power_root_eq p hp heven _ hM]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hM _)).2
  exact (finiteGridRoot_le_of_rows_le p hp _ x (by positivity)
    (nativeStandardMatrix_bound_of_native_bound q hv₀ hv hε x hx)).trans hthreshold

end BrownianSharp
