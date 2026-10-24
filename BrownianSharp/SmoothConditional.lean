import BrownianSharp.SmoothVarianceBound
import BrownianSharp.NativeStatisticProperties
import BrownianSharp.EventualBudget
import BrownianSharp.ConfinementFromRemainder

/-! Conditional finite-dimensional Ehrhard assembly for the concrete smooth
layer. Every row, variance, shell sum, and root-repair input is proved here;
only the stated Gaussian Ehrhard premise is external. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

def smoothConfinementExponent (d : ℕ) : ℝ :=
  (Real.pi / 4096) / (16 * (4 * smoothVarianceConstant d + 1))

theorem smoothConfinementExponent_pos (d : ℕ) : 0 < smoothConfinementExponent d := by
  unfold smoothConfinementExponent
  have := smoothVarianceConstant_pos d
  positivity

theorem smoothGoodPowerStatistic_continuous (d n p : ℕ) :
    Continuous (smoothGoodPowerStatistic d n p) := by
  unfold smoothGoodPowerStatistic normalizedPowerAverage
  fun_prop

theorem smoothGoodRootStatistic_continuous {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p) :
    Continuous (smoothGoodRootStatistic d n p) := by
  letI := smoothGoodGrid_nonempty (d := d) (n := n) hd
  have heq : smoothGoodRootStatistic d n p = fun x =>
      finiteGridRoot p (smoothGoodMatrix d n) x / standardGaussianMoment p ^ (1 / (p : ℝ)) :=
    funext (smoothGoodRootStatistic_eq hd hp heven hM)
  rw [heq]
  exact (Concentration.finiteGridRoot_continuous p hp _).div_const _

theorem smoothGoodRootStatistic_zero {d n p : ℕ} (hp : 0 < p) :
    smoothGoodRootStatistic d n p 0 = 0 := by
  rw [smoothGoodRootStatistic, smoothGoodPowerStatistic]
  simp [normalizedPowerAverage, hp.ne']

theorem smoothGoodRootStatistic_exists_pos {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p) :
    ∃ x, 0 < smoothGoodRootStatistic d n p x := by
  letI := smoothGoodGrid_nonempty (d := d) (n := n) hd
  obtain ⟨x, hx⟩ := Concentration.finiteGridRoot_exists_pos_of_nonzero_entry
    p hp (smoothGoodMatrix d n) (smoothGoodMatrix_nonzero hd)
  refine ⟨x, ?_⟩
  rw [smoothGoodRootStatistic_eq hd hp heven hM]
  exact div_pos hx (Real.rpow_pos_of_pos hM _)

theorem smoothGoodRootStatistic_variance_pos {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p) :
    0 < ProbabilityTheory.variance (smoothGoodRootStatistic d n p)
      (productStandardGaussian (LayerIndex d n)) := by
  apply productGaussian_variance_pos_of_continuous_nonconstant _
    (smoothGoodRootStatistic_memLp_two hd hp heven hM)
    (smoothGoodRootStatistic_continuous hd hp heven hM)
    (smoothGoodRootStatistic_zero (by omega))
  obtain ⟨x, hx⟩ := smoothGoodRootStatistic_exists_pos hd hp heven hM
  exact ⟨x, hx.ne'⟩

theorem smoothGoodPowerStatistic_zero {d n p : ℕ} (hp : 0 < p) :
    smoothGoodPowerStatistic d n p 0 = 0 := by
  simp [smoothGoodPowerStatistic, normalizedPowerAverage, hp.ne']

theorem smoothGoodPowerStatistic_variance_pos {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p) :
    0 < ProbabilityTheory.variance (smoothGoodPowerStatistic d n p)
      (productStandardGaussian (LayerIndex d n)) := by
  apply productGaussian_variance_pos_of_continuous_nonconstant _
    (smoothGoodPowerStatistic_memLp_two hd)
    (smoothGoodPowerStatistic_continuous d n p)
    (smoothGoodPowerStatistic_zero (by omega))
  obtain ⟨x, hx⟩ := smoothGoodRootStatistic_exists_pos hd hp heven hM
  refine ⟨x, ?_⟩
  intro hz
  have hrootzero : smoothGoodRootStatistic d n p x = 0 := by
    rw [smoothGoodRootStatistic, hz]
    exact Real.zero_rpow (by positivity : (1 / (p : ℝ)) ≠ 0)
  linarith

theorem smoothGoodRoot_confinement_of_ehrhard {d : ℕ} (hd : 2 ≤ d)
    (hEhrhard : ∀ n : ℕ, Concentration.GaussianEhrhard (LayerIndex d n → ℝ)
      (productStandardGaussian (LayerIndex d n))) :
    ∃ N : ℕ, 2 * d ≤ N ∧ ∀ n : ℕ, N ≤ n →
      (productStandardGaussian (LayerIndex d n)).real
        {x | smoothGoodRootStatistic d n (gradeEvenPower (smoothMomentSlope d) n) x ≤ 1 / 4} ≤
      Real.exp (-smoothConfinementExponent d * nativeDimension d n) := by
  have hd0 : 0 < d := by omega
  let κ := smoothMomentSlope d
  let C := smoothVarianceConstant d
  let c : ℝ := Real.pi / 4096
  have hκ : 0 < κ := smoothMomentSlope_pos d
  have hκone : κ ≤ 1 := smoothMomentSlope_le_one d
  have hC : 0 < C := smoothVarianceConstant_pos d
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
  have hvar := smoothGoodPowerStatistic_variance_bound hd hn heven hpBound
  have htail := smoothGoodStatistics_variance_sensitive_tail hd0 hp2 heven (hEhrhard n)
  have hconf := two_stage_confinement_of_exponential_remainder
    (productStandardGaussian (LayerIndex d n)) (smoothGoodPowerStatistic d n p)
    (p : ℝ) C (nativeDimension d n) c (by exact_mod_cast hp2) hC hD hc
    (smoothGoodPowerStatistic_continuous d n p).measurable
    (smoothGoodPowerStatistic_nonneg heven hM)
    (smoothGoodPowerStatistic_memLp_two hd0)
    (smoothGoodRootStatistic_memLp_two hd0 hp2 heven hM)
    (smoothGoodPowerStatistic_mean hd0 hM.ne')
    (smoothGoodPowerStatistic_variance_pos hd0 hp2 heven hM)
    (smoothGoodRootStatistic_variance_pos hd0 hp2 heven hM)
    hvar hsmall hremainder hlarge htail.1 htail.2
  exact hconf

end BrownianSharp
