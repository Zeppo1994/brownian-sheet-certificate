import BrownianSharp.NativeGaussian
import BrownianSharp.GaussianGridStatistics

/-! Exact normalized native coefficient rows on any deterministic positive-variance grid. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

/-- Deterministic standardized matrix of actual Haar layer evaluations. -/
def nativeStandardMatrix {d n : ℕ} {ι : Type*}
    (q : ι → MidpointGridIndex d n) (i : ι) (a : LayerIndex d n) : ℝ :=
  nativeLayerRowCoefficient (q i) a / Real.sqrt (nativeLayerRowVariance (q i))

theorem nativeStandardMatrix_unit_rows {d n : ℕ} {ι : Type*}
    (q : ι → MidpointGridIndex d n)
    (hv : ∀ i, 0 < nativeLayerRowVariance (q i)) (i : ι) :
    ∑ a, nativeStandardMatrix q i a ^ 2 = 1 := by
  simp only [nativeStandardMatrix, div_pow, ← Finset.sum_div]
  rw [Real.sq_sqrt (hv i).le]
  change nativeLayerRowVariance (q i) / nativeLayerRowVariance (q i) = 1
  exact div_self (hv i).ne'

theorem nativeStandardMatrix_dot {d n : ℕ} {ι : Type*}
    (q : ι → MidpointGridIndex d n) (i j : ι) :
    (∑ a, nativeStandardMatrix q i a * nativeStandardMatrix q j a) =
      nativeRowCorrelation (q i) (q j) := by
  simp only [nativeStandardMatrix, nativeRowCorrelation, div_mul_div_comm,
    Finset.sum_div]

theorem nativeStandardMatrix_evaluation {d n : ℕ} {ι Ω : Type*}
    (q : ι → MidpointGridIndex d n) (G : LayerIndex d n → Ω → ℝ)
    (i : ι) (ω : Ω) :
    (∑ a, nativeStandardMatrix q i a * G a ω) = standardizedNativeRow G (q i) ω := by
  simp only [nativeStandardMatrix, standardizedNativeRow, GaussianRows.row,
    div_mul_eq_mul_div, Finset.sum_div]

theorem nativeStandardMatrix_row_hasLaw {d n : ℕ} {ι : Type*}
    (q : ι → MidpointGridIndex d n)
    (hv : ∀ i, 0 < nativeLayerRowVariance (q i)) (i : ι) :
    HasLaw (fun x : LayerIndex d n → ℝ => ∑ a, nativeStandardMatrix q i a * x a)
      (gaussianReal 0 1) (productStandardGaussian (LayerIndex d n)) :=
  normalized_matrix_row_hasLaw _ (nativeStandardMatrix_unit_rows q hv) i

theorem nativeStandardMatrix_power_mean {d n : ℕ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (q : ι → MidpointGridIndex d n)
    (hv : ∀ i, 0 < nativeLayerRowVariance (q i))
    (p : ℕ) (hM : standardGaussianMoment p ≠ 0) :
    (∫ x : LayerIndex d n → ℝ,
      normalizedPowerAverage (fun i x => ∑ a, nativeStandardMatrix q i a * x a)
        p (standardGaussianMoment p) x ∂productStandardGaussian (LayerIndex d n)) = 1 :=
  normalized_matrix_power_average_mean _ (nativeStandardMatrix_unit_rows q hv) p hM

theorem nativeStandardMatrix_power_memLp_two {d n : ℕ} {ι : Type*}
    [Fintype ι] (q : ι → MidpointGridIndex d n)
    (hv : ∀ i, 0 < nativeLayerRowVariance (q i)) (p : ℕ) :
    MemLp (normalizedPowerAverage (fun i x => ∑ a, nativeStandardMatrix q i a * x a)
      p (standardGaussianMoment p)) 2 (productStandardGaussian (LayerIndex d n)) := by
  unfold normalizedPowerAverage
  have h := (memLp_finsetSum Finset.univ (fun i _ => normalized_matrix_row_power_memLp_two
    _ (nativeStandardMatrix_unit_rows q hv) i p)).const_mul
      (((Fintype.card ι : ℝ) * standardGaussianMoment p)⁻¹)
  simpa only [Finset.sum_const_zero, div_eq_mul_inv, mul_comm] using h

/-- An actual positive-variance row contains a nonzero coefficient. -/
theorem nativeStandardMatrix_nonzero {d n : ℕ} {ι : Type*} [Nonempty ι]
    (q : ι → MidpointGridIndex d n)
    (hv : ∀ i, 0 < nativeLayerRowVariance (q i)) :
    ∃ i a, nativeStandardMatrix q i a ≠ 0 := by
  classical
  obtain ⟨i⟩ := ‹Nonempty ι›
  by_contra h
  push_neg at h
  have hn := nativeStandardMatrix_unit_rows q hv i
  simp only [h, zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero] at hn
  norm_num at hn

/-- A coefficient vector below the unstandardized uniform threshold has
all standardized native evaluations below the advertised variance-floor scale. -/
theorem nativeStandardMatrix_bound_of_native_bound {d n : ℕ} {ι : Type*}
    (q : ι → MidpointGridIndex d n) {v₀ ε : ℝ} (hv₀ : 0 < v₀)
    (hv : ∀ i, v₀ ≤ nativeLayerRowVariance (q i)) (hε : 0 ≤ ε)
    (x : LayerIndex d n → ℝ)
    (hx : ∀ i, |∑ a, nativeLayerRowCoefficient (q i) a * x a| ≤ ε) (i : ι) :
    |∑ a, nativeStandardMatrix q i a * x a| ≤ ε / Real.sqrt v₀ := by
  rw [nativeStandardMatrix_evaluation q (fun a (_ : Unit) => x a) i ()]
  unfold standardizedNativeRow GaussianRows.row
  rw [abs_div, abs_of_pos (Real.sqrt_pos.mpr (hv₀.trans_le (hv i)))]
  calc
    _ ≤ ε / Real.sqrt (nativeLayerRowVariance (q i)) :=
      div_le_div_of_nonneg_right (hx i) (Real.sqrt_nonneg _)
    _ ≤ ε / Real.sqrt v₀ := div_le_div_of_nonneg_left hε
      (Real.sqrt_pos.mpr hv₀) (Real.sqrt_le_sqrt (hv i))

end BrownianSharp
