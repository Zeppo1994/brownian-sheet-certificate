import BrownianSharp.NativeGoodStatistics
import BrownianSharp.SheetProductComparison
import BrownianSharp.Interpolation

/-! Exact constants connecting the normalized-root event to the manuscript's
sharp native radius and to the original full Brownian sheet. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp
open HaarQuarter

def nativeRadiusConstant (d : ℕ) (c κ : ℝ) : ℝ :=
  c * Real.sqrt κ / (8 * (2 : ℝ) ^ (2 * d))

theorem nativeRadiusConstant_pos (d : ℕ) {c κ : ℝ} (hc : 0 < c) (hκ : 0 < κ) :
    0 < nativeRadiusConstant d c κ := by
  unfold nativeRadiusConstant
  positivity

theorem native_sharpRadius_standardized_threshold {d n p : ℕ}
    (hd : 2 ≤ d) (hn : 0 < n) (hp : 2 ≤ p) {c κ : ℝ}
    (hc : 0 < c) (hκ : 0 < κ) (hpLower : κ * (n : ℝ) ≤ 2 * (p : ℝ))
    (hMoment : c * Real.sqrt (p : ℝ) ≤ standardGaussianMoment p ^ (1 / (p : ℝ))) :
    sharpRadius d (nativeRadiusConstant d c κ) n /
        Real.sqrt (nativeVarianceMeanLowerBound d n / 2) ≤
      (1 / 4 : ℝ) * standardGaussianMoment p ^ (1 / (p : ℝ)) := by
  let T : ℝ := (2 : ℝ) ^ n
  let A : ℝ := (2 : ℝ) ^ (2 * d)
  let S : ℝ := hyperbolicCount d n
  have hT : 0 < T := by dsimp [T]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hS : 0 < S := by
    dsimp [S, hyperbolicCount]
    exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + d - 1)
  have hfloor : nativeVarianceMeanLowerBound d n / 2 = S / (2 * T * A ^ 2) := by
    dsimp [nativeVarianceMeanLowerBound, S, hyperbolicCount, T, A]
    rw [show n + 4 * d = n + (2 * d) * 2 by omega, pow_add, pow_mul]
    ring
  have hv : 0 < nativeVarianceMeanLowerBound d n / 2 :=
    half_pos (nativeVarianceMeanLowerBound_pos (by omega))
  have hrad : sharpRadius d (nativeRadiusConstant d c κ) n ^ 2 =
      c ^ 2 * κ * (n : ℝ) * S / (64 * A ^ 2 * T) := by
    unfold sharpRadius nativeRadiusConstant
    rw [mul_pow, div_pow, mul_pow, Real.sq_sqrt hκ.le,
      Real.sq_sqrt (by positivity : 0 ≤ (n : ℝ) * hyperbolicCount d n / (2 : ℝ) ^ n)]
    dsimp [S, A, T]
    ring
  have hsmall : sharpRadius d (nativeRadiusConstant d c κ) n ^ 2 ≤
      (nativeVarianceMeanLowerBound d n / 2) * (c * Real.sqrt (p : ℝ) / 4) ^ 2 := by
    rw [hrad, hfloor, div_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ p)]
    have hmul := mul_le_mul_of_nonneg_left hpLower
      (show 0 ≤ c ^ 2 * S / (64 * A ^ 2 * T) by positivity)
    convert hmul using 1 <;> ring
  have hrad0 : 0 ≤ sharpRadius d (nativeRadiusConstant d c κ) n :=
    (sharpRadius_pos hd (nativeRadiusConstant_pos d hc hκ) hn).le
  have hroot : 0 < Real.sqrt (nativeVarianceMeanLowerBound d n / 2) := Real.sqrt_pos.mpr hv
  have hbound : sharpRadius d (nativeRadiusConstant d c κ) n ≤
      Real.sqrt (nativeVarianceMeanLowerBound d n / 2) * (c * Real.sqrt (p : ℝ) / 4) := by
    have hs := Real.sq_sqrt hv.le
    have hp0 : 0 ≤ c * Real.sqrt (p : ℝ) / 4 := by positivity
    have hsq : sharpRadius d (nativeRadiusConstant d c κ) n ^ 2 ≤
        (Real.sqrt (nativeVarianceMeanLowerBound d n / 2) *
          (c * Real.sqrt (p : ℝ) / 4)) ^ 2 := by
      rw [mul_pow, hs]
      exact hsmall
    exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
      (mul_nonneg hroot.le hp0) hsq
  calc
    _ ≤ c * Real.sqrt (p : ℝ) / 4 := (div_le_iff₀ hroot).2 (by simpa [mul_comm] using hbound)
    _ ≤ _ := by linarith

/-- The only remaining probabilistic input here is the normalized root event
bound. Every scale factor and the original-sheet projection are proved. -/
theorem original_sheet_sharpRadius_bound_of_native_root_bound
    {d n p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (hd : 2 ≤ d) (hn : 0 < n)
    (hp : 2 ≤ p) (heven : Even p) {c κ Q : ℝ}
    (hc : 0 < c) (hκ : 0 < κ) (hM : 0 < standardGaussianMoment p)
    (hpLower : κ * (n : ℝ) ≤ 2 * (p : ℝ))
    (hMoment : c * Real.sqrt (p : ℝ) ≤ standardGaussianMoment p ^ (1 / (p : ℝ)))
    (hroot : (productStandardGaussian (LayerIndex d n)).real
      {x | nativeGoodRootStatistic d n p x ≤ 1 / 4} ≤ Q) :
    P.real {ω | ‖B.path ω‖ ≤ sharpRadius d (nativeRadiusConstant d c κ) n} ≤ Q := by
  letI := nativeGoodGrid_nonempty (d := d) (n := n) (by omega : 0 < d)
  let ε := sharpRadius d (nativeRadiusConstant d c κ) n
  have hε : 0 ≤ ε := (sharpRadius_pos hd (nativeRadiusConstant_pos d hc hκ) hn).le
  have hv₀ : 0 < nativeVarianceMeanLowerBound d n / 2 :=
    half_pos (nativeVarianceMeanLowerBound_pos (by omega))
  have hthreshold := native_sharpRadius_standardized_threshold hd hn hp hc hκ hpLower hMoment
  have hsub := native_uniform_event_subset_normalized_root_event
    (fun q : NativeGoodGrid d n => q.val) p hp heven hM hv₀
    (fun q => q.property) hε hthreshold
  change {x : LayerIndex d n → ℝ |
      ∀ i : NativeGoodGrid d n, |∑ a, nativeLayerRowCoefficient i.val a * x a| ≤ ε} ⊆
    {x | nativeGoodRootStatistic d n p x ≤ 1 / 4} at hsub
  have hcomp := original_sheet_product_native_comparison (n := n)
    (by omega : 0 < d) B (fun q : NativeGoodGrid d n => q.val) hε
  have hcompReal := ENNReal.toReal_mono (measure_ne_top _ _) hcomp
  exact hcompReal.trans ((measureReal_mono hsub).trans hroot)

end BrownianSharp
