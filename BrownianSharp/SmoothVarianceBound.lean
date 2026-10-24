import BrownianSharp.SmoothGoodStatistics
import BrownianSharp.SmoothShellSum
import BrownianSharp.GenericShellAverage
import BrownianSharp.GaussianPairCovariance
import BrownianSharp.ShellVariance

/-! Variance control for the actual normalized smooth-layer Gaussian statistic.
The pair sum is bounded on the proved positive-density grid by the actual
smooth-row correlations and their common-prefix shells. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

def smoothGoodFactor (d : ℕ) : ℝ := 2 ^ (d + 1)

def smoothGoodDensity (d : ℕ) : ℝ := 1 / smoothGoodFactor d

def smoothMomentSlope (d : ℕ) : ℝ :=
  min 1 (Real.log 2 / (4 * smoothGoodFactor d * (Nat.factorial (d - 1) : ℝ)))

def smoothVarianceConstant (d : ℕ) : ℝ :=
  (4 * (smoothGoodFactor d * (Nat.factorial (d - 1) : ℝ)) ^ 2 * Real.sqrt 2 *
    shellPolynomialBudget (d - 1)) / smoothGoodDensity d ^ 2 + 1

theorem smoothGoodFactor_pos (d : ℕ) : 0 < smoothGoodFactor d := by
  unfold smoothGoodFactor
  positivity

theorem smoothGoodDensity_pos (d : ℕ) : 0 < smoothGoodDensity d := by
  unfold smoothGoodDensity
  exact one_div_pos.mpr (smoothGoodFactor_pos d)

theorem smoothMomentSlope_pos (d : ℕ) : 0 < smoothMomentSlope d := by
  unfold smoothMomentSlope
  apply lt_min (by norm_num)
  exact div_pos (Real.log_pos (by norm_num)) (by
    have := smoothGoodFactor_pos d
    positivity)

theorem smoothMomentSlope_le_one (d : ℕ) : smoothMomentSlope d ≤ 1 := min_le_left _ _

theorem smoothVarianceConstant_pos (d : ℕ) : 0 < smoothVarianceConstant d := by
  have hbudget : 0 ≤ shellPolynomialBudget (d - 1) :=
    tsum_nonneg (fun _ => by positivity)
  unfold smoothVarianceConstant
  positivity

private def smoothGoodRowsEquiv (d n : ℕ) :
    SmoothGoodGrid d n ≃ GenericGoodRows (smoothGoodRowPredicate (d := d) (n := n)) where
  toFun q := ⟨q.1, q.2⟩
  invFun q := ⟨q.1, q.2⟩
  left_inv q := by cases q; rfl
  right_inv q := by cases q; rfl

theorem smoothGoodPairKernel_average_bound {d n p : ℕ}
    (hd : 2 ≤ d) (hn : 0 < n)
    (hp : (p : ℝ) ≤ smoothMomentSlope d * ((n : ℝ) + 1)) :
    (Fintype.card (SmoothGoodGrid d n) : ℝ)⁻¹ ^ 2 *
      (∑ i : SmoothGoodGrid d n, ∑ j : SmoothGoodGrid d n,
        highPowerPairKernel p (smoothRowCorrelation i.1 j.1)) ≤
      smoothVarianceConstant d * (p : ℝ) ^ 2 / nativeDimension d n := by
  classical
  let good := smoothGoodRowPredicate (d := d) (n := n)
  let rho := smoothRowCorrelation (d := d) (n := n)
  let e := smoothGoodRowsEquiv d n
  have hgrid : 0 < (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    simp [MidpointGridIndex, MidpointGridCoordinate, Fintype.card_pi]
  have hfrac : smoothGoodDensity d ≤
      (Fintype.card (SmoothGoodGrid d n) : ℝ) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    have h := smoothGoodGrid_fraction_lower (d := d) (n := n) (by omega : 0 < d)
    simpa [smoothGoodDensity, smoothGoodFactor, div_eq_mul_inv] using h
  have hdensity : smoothGoodDensity d *
      (Fintype.card (MidpointGridIndex d n) : ℝ) ≤
      (Fintype.card (GenericGoodRows good) : ℝ) := by
    rw [show (Fintype.card (GenericGoodRows good) : ℝ) =
      (Fintype.card (SmoothGoodGrid d n) : ℝ) by
        exact_mod_cast Fintype.card_congr e]
    exact (le_div_iff₀ hgrid).mp hfrac
  have hbelow : ∀ q q', good q → good q' →
      midpointCommonPrefixGrade (fun i => (q i, q' i)) < n → rho q q' = 0 := by
    intro q q' hq hq' hgrade
    let c := midpointCommonPrefixCaps q q'
    have hc : c.sum (fun _ z => z) < n := by
      simpa [c, midpointCommonPrefixGrade] using hgrade
    have hpref : MidpointCommonPrefixProfile q q' c := by
      simpa [c] using midpointCommonPrefixCaps_profile q q'
    exact smoothRowCorrelation_eq_zero_of_prefix_grade_lt (by omega : 0 < d)
      q q' c hpref hc hq hq'
  have hcap : ∀ h q q', good q → good q' →
      midpointCommonPrefixGrade (fun i => (q i, q' i)) = n + h →
      |rho q q'| ≤ shapeOverlapCap d n h (smoothGoodFactor d) := by
    intro h q q' hq hq' hgrade
    exact smoothGoodRowCorrelation_abs_le_overlapCap (by omega : 0 < d)
      q q' hq hq' hgrade
  have hagg := genericGoodPairKernel_average_le_of_density
    (by omega : 0 < d) hd hn (smoothGoodFactor_pos d)
    (min_le_right _ _) hp (smoothGoodDensity_pos d) good rho hbelow hcap hdensity
  have hsum :
      (∑ x : GenericGoodPair good,
        highPowerPairKernel p (rho x.1.1 x.2.1)) =
      ∑ i : SmoothGoodGrid d n, ∑ j : SmoothGoodGrid d n,
        highPowerPairKernel p (smoothRowCorrelation i.1 j.1) := by
    rw [Fintype.sum_prod_type]
    symm
    apply Fintype.sum_equiv e
    intro i
    apply Fintype.sum_equiv e
    intro j
    rfl
  rw [hsum] at hagg
  have hpaircard :
      (Fintype.card (GenericGoodPair good) : ℝ) =
        (Fintype.card (SmoothGoodGrid d n) : ℝ) ^ 2 := by
    simp [GenericGoodPair, Fintype.card_prod, show
      (Fintype.card (GenericGoodRows good) : ℝ) =
        (Fintype.card (SmoothGoodGrid d n) : ℝ) by exact_mod_cast Fintype.card_congr e,
      pow_two]
  rw [hpaircard] at hagg
  let C₀ : ℝ := (4 * (smoothGoodFactor d * (Nat.factorial (d - 1) : ℝ)) ^ 2 *
    Real.sqrt 2 * shellPolynomialBudget (d - 1)) / smoothGoodDensity d ^ 2
  have hC₀ : 0 ≤ C₀ := by
    have hbudget : 0 ≤ shellPolynomialBudget (d - 1) :=
      tsum_nonneg (fun _ => by positivity)
    dsimp [C₀]
    positivity
  have hD : 0 < nativeDimension d n := by
    unfold nativeDimension hyperbolicCount
    have hc : 0 < Nat.choose (n + d - 1) (d - 1) := Nat.choose_pos (by omega)
    positivity
  have hden : nativeDimension d n ≤
      (2 : ℝ) ^ n * ((n : ℝ) + 1) ^ (d - 1) :=
    mul_le_mul_of_nonneg_left (hyperbolicCount_upper_shift (by omega : 1 ≤ d) n) (by positivity)
  calc
    _ = (∑ i : SmoothGoodGrid d n, ∑ j : SmoothGoodGrid d n,
        highPowerPairKernel p (smoothRowCorrelation i.1 j.1)) /
        (Fintype.card (SmoothGoodGrid d n) : ℝ) ^ 2 := by ring
    _ ≤ C₀ * (p : ℝ) ^ 2 /
        ((2 : ℝ) ^ n * ((n : ℝ) + 1) ^ (d - 1)) := by
      convert hagg using 1 <;> dsimp [C₀, smoothGoodFactor, smoothGoodDensity] <;> ring
    _ ≤ C₀ * (p : ℝ) ^ 2 / nativeDimension d n :=
      div_le_div_of_nonneg_left (by positivity) hD hden
    _ ≤ smoothVarianceConstant d * (p : ℝ) ^ 2 / nativeDimension d n := by
      apply div_le_div_of_nonneg_right _ hD.le
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      dsimp [smoothVarianceConstant, C₀]
      linarith

theorem smoothGoodPowerStatistic_variance_le_pairKernel {d n : ℕ}
    (hd : 0 < d) (k : ℕ) :
    ProbabilityTheory.variance (smoothGoodPowerStatistic d n (2 * k))
      (productStandardGaussian (LayerIndex d n)) ≤
    (Fintype.card (SmoothGoodGrid d n) : ℝ)⁻¹ ^ 2 *
      ∑ i : SmoothGoodGrid d n, ∑ j : SmoothGoodGrid d n,
        highPowerPairKernel (2 * k) (smoothRowCorrelation i.1 j.1) := by
  letI := smoothGoodGrid_nonempty (d := d) (n := n) hd
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
  have hLp (i : SmoothGoodGrid d n) :
      MemLp (fun x : LayerIndex d n → ℝ =>
        (∑ a, smoothGoodMatrix d n i a * x a) ^ (2 * k))
        2 (productStandardGaussian (LayerIndex d n)) :=
    normalized_matrix_row_power_memLp_two _ (smoothGoodMatrix_unit_rows hd) i (2 * k)
  apply normalizedPowerAverage_variance_le _ (2 * k) _ hM hLp
  intro i j
  have h := normalizedGaussianRows_actualCovariance_bound G hG hLaw hIndep
    (smoothGoodMatrix d n i) (smoothGoodMatrix d n j)
    (smoothGoodMatrix_unit_rows hd i) (smoothGoodMatrix_unit_rows hd j) k (hLp i) (hLp j)
  have hdot := smoothGoodMatrix_power_covariance i j
  rw [hdot] at h
  have hkernel : ((4 * k : ℝ) * |smoothRowCorrelation i.1 j.1|) ^ 2 *
      Real.exp ((4 * k : ℝ) * |smoothRowCorrelation i.1 j.1|) =
      highPowerPairKernel (2 * k) (smoothRowCorrelation i.1 j.1) := by
    unfold highPowerPairKernel
    push_cast
    rw [mul_pow, sq_abs]
    congr 1 <;> ring
  rw [hkernel] at h
  exact h

theorem smoothGoodPowerStatistic_variance_bound {d n p : ℕ}
    (hd : 2 ≤ d) (hn : 0 < n) (heven : Even p)
    (hp : (p : ℝ) ≤ smoothMomentSlope d * ((n : ℝ) + 1)) :
    ProbabilityTheory.variance (smoothGoodPowerStatistic d n p)
      (productStandardGaussian (LayerIndex d n)) ≤
        smoothVarianceConstant d * (p : ℝ) ^ 2 / nativeDimension d n := by
  obtain ⟨k, hk⟩ := heven
  have hpk : p = 2 * k := by omega
  rw [hpk] at hp ⊢
  exact (smoothGoodPowerStatistic_variance_le_pairKernel (by omega : 0 < d) k).trans
    (smoothGoodPairKernel_average_bound hd hn hp)

end BrownianSharp
