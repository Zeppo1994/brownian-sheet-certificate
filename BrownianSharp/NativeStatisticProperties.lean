import BrownianSharp.NativeGoodStatistics
import BrownianSharp.ActualConcentration

/-! All elementary side conditions for both concentration applications on the
actual native good-grid statistic. Ehrhard remains a displayed geometric input. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

/-- Full Gaussian support rules out zero variance for a continuous observable
that is zero at the origin and nonzero somewhere. -/
theorem productGaussian_variance_pos_of_continuous_nonconstant
    {κ : Type*} [Fintype κ] (X : (κ → ℝ) → ℝ)
    (hX : MemLp X 2 (productStandardGaussian κ)) (hc : Continuous X)
    (hzero : X 0 = 0) (hne : ∃ x, X x ≠ 0) :
    0 < ProbabilityTheory.variance X (productStandardGaussian κ) := by
  letI : Measure.IsOpenPosMeasure (productStandardGaussian κ) :=
    GaussianDensity.volume_absolutelyContinuous_standardGaussian.isOpenPosMeasure
  by_contra h
  have hz : ProbabilityTheory.variance X (productStandardGaussian κ) = 0 :=
    le_antisymm (le_of_not_gt h) (variance_nonneg _ _)
  have hae := ae_eq_integral_of_variance_eq_zero hX hz
  have heq := (Continuous.ae_eq_iff_eq (productStandardGaussian κ) hc continuous_const).mp hae
  obtain ⟨x, hx⟩ := hne
  have h0 := congrFun heq 0
  have h1 := congrFun heq x
  exact hx (by simpa [hzero] using h1.trans h0.symm)

theorem productStandardGaussian_coeff_memLp_two (κ : Type*) [Fintype κ] :
    MemLp (id : (κ → ℝ) → κ → ℝ) 2 (productStandardGaussian κ) := by
  apply MeasureTheory.memLp_pi_iff.mpr
  intro k
  exact (GaussianRows.coordinate_gaussian
    (fun (j : κ) (x : κ → ℝ) => x j)
    (fun j => measurable_pi_apply j)
    (fun j => productStandardGaussian_coordinate_law j) k).memLp_two

theorem nativeGoodRootStatistic_memLp_two {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p) :
    MemLp (nativeGoodRootStatistic d n p) 2 (productStandardGaussian (LayerIndex d n)) := by
  letI := nativeGoodGrid_nonempty (d := d) (n := n) hd
  have h := (finiteGridRoot_memLp_two_of_coeff_memLp
    (productStandardGaussian_coeff_memLp_two (LayerIndex d n)) p hp
      (nativeGoodMatrix d n)).const_mul ((standardGaussianMoment p ^ (1 / (p : ℝ)))⁻¹)
  have heq : nativeGoodRootStatistic d n p = fun x =>
      (standardGaussianMoment p ^ (1 / (p : ℝ)))⁻¹ * finiteGridRoot p (nativeGoodMatrix d n) x := by
    funext x
    rw [nativeGoodRootStatistic_eq hd hp heven hM]
    ring
  rw [heq]
  exact h

theorem nativeGoodRootStatistic_continuous {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p) :
    Continuous (nativeGoodRootStatistic d n p) := by
  letI := nativeGoodGrid_nonempty (d := d) (n := n) hd
  have heq : nativeGoodRootStatistic d n p = fun x =>
      finiteGridRoot p (nativeGoodMatrix d n) x / standardGaussianMoment p ^ (1 / (p : ℝ)) :=
    funext (nativeGoodRootStatistic_eq hd hp heven hM)
  rw [heq]
  exact (Concentration.finiteGridRoot_continuous p hp _).div_const _

theorem nativeGoodPowerStatistic_zero {d n p : ℕ} (hp : 0 < p) :
    nativeGoodPowerStatistic d n p 0 = 0 := by
  simp [nativeGoodPowerStatistic, normalizedPowerAverage, hp.ne']

theorem nativeGoodRootStatistic_zero {d n p : ℕ} (hp : 0 < p) :
    nativeGoodRootStatistic d n p 0 = 0 := by
  rw [nativeGoodRootStatistic, nativeGoodPowerStatistic_zero hp]
  exact Real.zero_rpow (by positivity : (1 / (p : ℝ)) ≠ 0)

theorem nativeGoodRootStatistic_exists_pos {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p) :
    ∃ x, 0 < nativeGoodRootStatistic d n p x := by
  letI := nativeGoodGrid_nonempty (d := d) (n := n) hd
  obtain ⟨x, hx⟩ := Concentration.finiteGridRoot_exists_pos_of_nonzero_entry
    p hp (nativeGoodMatrix d n) (nativeGoodMatrix_nonzero hd)
  refine ⟨x, ?_⟩
  rw [nativeGoodRootStatistic_eq hd hp heven hM]
  exact div_pos hx (Real.rpow_pos_of_pos hM _)

theorem nativeGoodRootStatistic_variance_pos {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p) :
    0 < ProbabilityTheory.variance (nativeGoodRootStatistic d n p)
      (productStandardGaussian (LayerIndex d n)) := by
  apply productGaussian_variance_pos_of_continuous_nonconstant _
    (nativeGoodRootStatistic_memLp_two hd hp heven hM)
    (nativeGoodRootStatistic_continuous hd hp heven hM)
    (nativeGoodRootStatistic_zero (by omega))
  obtain ⟨x, hx⟩ := nativeGoodRootStatistic_exists_pos hd hp heven hM
  exact ⟨x, hx.ne'⟩

theorem nativeGoodPowerStatistic_continuous (d n p : ℕ) :
    Continuous (nativeGoodPowerStatistic d n p) := by
  unfold nativeGoodPowerStatistic normalizedPowerAverage
  fun_prop

theorem nativeGoodPowerStatistic_variance_pos {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p) (hM : 0 < standardGaussianMoment p) :
    0 < ProbabilityTheory.variance (nativeGoodPowerStatistic d n p)
      (productStandardGaussian (LayerIndex d n)) := by
  apply productGaussian_variance_pos_of_continuous_nonconstant _
    (nativeGoodPowerStatistic_memLp_two hd) (nativeGoodPowerStatistic_continuous d n p)
    (nativeGoodPowerStatistic_zero (by omega))
  obtain ⟨x, hx⟩ := nativeGoodRootStatistic_exists_pos hd hp heven hM
  refine ⟨x, ?_⟩
  intro hz
  have hrootzero : nativeGoodRootStatistic d n p x = 0 := by
    unfold nativeGoodRootStatistic
    rw [hz]
    exact Real.zero_rpow (by positivity : (1 / (p : ℝ)) ≠ 0)
  linarith

theorem nativeGoodStatistics_variance_sensitive_tail {d n p : ℕ} (hd : 0 < d)
    (hp : 2 ≤ p) (heven : Even p)
    (hEhrhard : Concentration.GaussianEhrhard (LayerIndex d n → ℝ)
      (productStandardGaussian (LayerIndex d n))) :
    VarianceSensitiveLowerTail (productStandardGaussian (LayerIndex d n))
      (nativeGoodPowerStatistic d n p) (Real.pi / 4096) ∧
    VarianceSensitiveLowerTail (productStandardGaussian (LayerIndex d n))
      (nativeGoodRootStatistic d n p) (Real.pi / 4096) := by
  letI := nativeGoodGrid_nonempty (d := d) (n := n) hd
  have heq : nativeGoodPowerStatistic d n p = fun x =>
      finiteGridMoment p (nativeGoodMatrix d n) x / standardGaussianMoment p := by
    funext x
    exact normalized_matrix_power_average_eq_moment _ p heven x
  have h := normalized_finiteGridMoment_and_root_variance_sensitive_tail
    p hp heven _ (nativeGoodMatrix_unit_rows hd) hEhrhard
  change VarianceSensitiveLowerTail (productStandardGaussian (LayerIndex d n))
      (nativeGoodPowerStatistic d n p) (Real.pi / 4096) ∧
    VarianceSensitiveLowerTail (productStandardGaussian (LayerIndex d n))
      (fun x => nativeGoodPowerStatistic d n p x ^ (1 / (p : ℝ))) (Real.pi / 4096)
  rw [heq]
  exact h

end BrownianSharp
