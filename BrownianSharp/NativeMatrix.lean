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
