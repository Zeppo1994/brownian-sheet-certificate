import BrownianSharp.NativeVarianceBound
import BrownianSharp.NativeStatisticProperties
import BrownianSharp.NativeScale
import BrownianSharp.EventualBudget
import BrownianSharp.ConfinementFromRemainder
import BrownianSharp.ScaleClosure

/-! The complete manuscript Brownian proof route, conditional only on the
classical finite-dimensional Gaussian Ehrhard theorem. All native-row,
moment, shell, variance, concentration-calculus, comparison and scale inputs
are proved. This conditional theorem is not the unconditional certificate. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp
open HaarQuarter

def ProductGaussianEhrhard : Prop :=
  ∀ (κ : Type) [Fintype κ], Concentration.GaussianEhrhard (κ → ℝ)
    (productStandardGaussian κ)

def nativeConfinementExponent (d : ℕ) : ℝ :=
  (Real.pi / 4096) / (16 * (4 * nativeVarianceConstant d + 1))

theorem nativeConfinementExponent_pos (d : ℕ) : 0 < nativeConfinementExponent d := by
  unfold nativeConfinementExponent
  have := nativeVarianceConstant_pos d
  positivity

theorem nativeGoodRoot_confinement_of_ehrhard {d : ℕ} (hd : 2 ≤ d)
    (hEhrhard : ∀ n : ℕ, Concentration.GaussianEhrhard (LayerIndex d n → ℝ)
      (productStandardGaussian (LayerIndex d n))) :
    ∃ N : ℕ, 2 * d ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        {x | nativeGoodRootStatistic d n (gradeEvenPower (nativeMomentSlope d) n) x ≤ 1 / 4} ≤
      Real.exp (-nativeConfinementExponent d * nativeDimension d n) := by
  have hd0 : 0 < d := by omega
  let κ := nativeMomentSlope d
  let C := nativeVarianceConstant d
  let c : ℝ := Real.pi / 4096
  have hκ : 0 < κ := nativeMomentSlope_pos d
  have hκone : κ ≤ 1 := nativeMomentSlope_le_one d
  have hC : 0 < C := nativeVarianceConstant_pos d
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨Nb, hNb⟩ := eventually_root_repair_budgets hd0 hκ hκone hC
    (show 0 < c / 4 by positivity)
  obtain ⟨Np, hNp⟩ := eventually_gradeEvenPower_bounds hκ
  let N := max (2 * d) (max Nb Np)
  refine ⟨N, le_max_left _ _, ?_⟩
  intro n hnN
  have hn : 0 < n := by have : 2 * d ≤ n := (le_max_left _ _).trans hnN; omega
  have hnb : Nb ≤ n := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hnN
  have hnp : Np ≤ n := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hnN
  obtain ⟨hp2, hsmall, hremainder, _, hlarge⟩ := hNb n hnb
  have hpBound := (hNp n hnp).1
  let p := gradeEvenPower κ n
  have heven : Even p := gradeEvenPower_even κ n
  have hM : 0 < standardGaussianMoment p := by
    obtain ⟨k, hk⟩ := heven
    have hpk : p = 2 * k := by omega
    rw [hpk]
    exact standardGaussianMoment_even_pos k
  have hD : 0 < nativeDimension d n :=
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ n).trans_le (nativeDimension_ge_dyadic d n hd0)
  have hvar := nativeGoodPowerStatistic_variance_bound hd hn heven hpBound
  have htail := nativeGoodStatistics_variance_sensitive_tail hd0 hp2 heven (hEhrhard n)
  have hconf := two_stage_confinement_of_exponential_remainder
    (productStandardGaussian (LayerIndex d n)) (nativeGoodPowerStatistic d n p)
    (p : ℝ) C (nativeDimension d n) c (by exact_mod_cast hp2) hC hD hc
    (nativeGoodPowerStatistic_continuous d n p).measurable
    (nativeGoodPowerStatistic_nonneg heven hM)
    (nativeGoodPowerStatistic_memLp_two hd0)
    (nativeGoodRootStatistic_memLp_two hd0 hp2 heven hM)
    (nativeGoodPowerStatistic_mean hd0 hM.ne')
    (nativeGoodPowerStatistic_variance_pos hd0 hp2 heven hM)
    (nativeGoodRootStatistic_variance_pos hd0 hp2 heven hM)
    hvar hsmall hremainder hlarge htail.1 htail.2
  exact hconf

theorem discreteSheetBound_of_productGaussianEhrhard (hEhrhard : ProductGaussianEhrhard) :
    DiscreteSheetBound := by
  intro d hd Ω _ P _ B
  have hκ := nativeMomentSlope_pos d
  obtain ⟨Nr, hNr, hroot⟩ := nativeGoodRoot_confinement_of_ehrhard hd
    (fun n => hEhrhard (LayerIndex d n))
  obtain ⟨Np, hNp⟩ := eventually_gradeEvenPower_bounds hκ
  let N := max Nr Np
  refine ⟨nativeRadiusConstant d (1 / 2) (nativeMomentSlope d), nativeConfinementExponent d,
    nativeRadiusConstant_pos d (by norm_num) hκ, nativeConfinementExponent_pos d,
    N, hNr.trans (le_max_left _ _), ?_⟩
  intro n hnN
  have hnr : Nr ≤ n := (le_max_left _ _).trans hnN
  have hnp : Np ≤ n := (le_max_right _ _).trans hnN
  obtain ⟨_, hpLower, hp2⟩ := hNp n hnp
  let p := gradeEvenPower (nativeMomentSlope d) n
  have heven : Even p := gradeEvenPower_even _ _
  have hM : 0 < standardGaussianMoment p := by
    obtain ⟨k, hk⟩ := heven
    have hpk : p = 2 * k := by omega
    rw [hpk]
    exact standardGaussianMoment_even_pos k
  have hn : 0 < n := by have : 2 * d ≤ n := hNr.trans hnr; omega
  apply original_sheet_sharpRadius_bound_of_native_root_bound B hd hn hp2 heven
    (by norm_num : (0 : ℝ) < 1 / 2) hκ hM
  · nlinarith [hpLower]
  · simpa only [Real.rpow_eq_pow, one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one, p] using
      standardGaussianMoment_evenOrder_root_lower heven hp2
  · exact hroot n hnr

theorem sharpLog_of_productGaussianEhrhard (hEhrhard : ProductGaussianEhrhard) :
    SharpLogStatement :=
  discreteSheetBound_implies_sharpLog (discreteSheetBound_of_productGaussianEhrhard hEhrhard)

theorem sharpProbability_of_productGaussianEhrhard (hEhrhard : ProductGaussianEhrhard) :
    SharpProbabilityStatement :=
  discreteSheetBound_implies_sharpProbability (discreteSheetBound_of_productGaussianEhrhard hEhrhard)

end BrownianSharp
