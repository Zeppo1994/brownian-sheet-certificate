import BrownianSharp.NativePowerVariance
import BrownianSharp.NativeShellSum
import BrownianSharp.EventualRates

/-! The manuscript's actual variance estimate, including the good-set density,
all ordered pairs, all common-prefix shells and diagonal terms. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

def nativeGoodFactor (d : ℕ) : ℝ := 2 * (4 : ℝ) ^ d

def nativeGoodDensity (d : ℕ) : ℝ := 1 / nativeGoodFactor d

def nativeMomentSlope (d : ℕ) : ℝ :=
  min 1 (Real.log 2 / (4 * nativeGoodFactor d * (Nat.factorial (d - 1) : ℝ)))

def nativeVarianceConstant (d : ℕ) : ℝ :=
  (4 * (nativeGoodFactor d * (Nat.factorial (d - 1) : ℝ)) ^ 2 * Real.sqrt 2 *
    shellPolynomialBudget (d - 1)) / nativeGoodDensity d ^ 2 + 1

theorem nativeGoodFactor_pos (d : ℕ) : 0 < nativeGoodFactor d := by
  unfold nativeGoodFactor
  positivity

theorem nativeGoodDensity_pos (d : ℕ) : 0 < nativeGoodDensity d := by
  unfold nativeGoodDensity
  exact one_div_pos.mpr (nativeGoodFactor_pos d)

theorem nativeMomentSlope_pos (d : ℕ) : 0 < nativeMomentSlope d := by
  unfold nativeMomentSlope
  apply lt_min (by norm_num)
  exact div_pos (Real.log_pos (by norm_num)) (by
    have := nativeGoodFactor_pos d
    positivity)

theorem nativeMomentSlope_le_one (d : ℕ) : nativeMomentSlope d ≤ 1 := min_le_left _ _

theorem nativeVarianceConstant_pos (d : ℕ) : 0 < nativeVarianceConstant d := by
  have hbudget : 0 ≤ shellPolynomialBudget (d - 1) := tsum_nonneg (fun _ => by positivity)
  unfold nativeVarianceConstant
  positivity

theorem nativeShellVarianceFloor_eq_actual (d n : ℕ) :
    nativeShellVarianceFloor d n (nativeGoodFactor d) = nativeVarianceMeanLowerBound d n / 2 := by
  have hpow : (2 : ℝ) ^ (n + 4 * d) = (2 : ℝ) ^ (n + 2 * d) * (4 : ℝ) ^ d := by
    rw [show n + 4 * d = n + 2 * d + 2 * d by omega, pow_add]
    congr 1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  unfold nativeShellVarianceFloor nativeVarianceMeanLowerBound nativeGoodFactor hyperbolicCount
  rw [hpow]
  ring

def nativeGoodRowsEquiv (d n : ℕ) :
    NativeGoodGrid d n ≃ NativeGoodRows d n (nativeShellVarianceFloor d n (nativeGoodFactor d)) where
  toFun q := ⟨q.val, (nativeShellVarianceFloor_eq_actual d n).le.trans q.property⟩
  invFun q := ⟨q.val, (nativeShellVarianceFloor_eq_actual d n).symm.le.trans q.property⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl

theorem nativeGoodPairKernel_average_bound {d n p : ℕ}
    (hd : 2 ≤ d) (hn : 0 < n)
    (hp : (p : ℝ) ≤ nativeMomentSlope d * ((n : ℝ) + 1)) :
    (Fintype.card (NativeGoodGrid d n) : ℝ)⁻¹ ^ 2 *
      (∑ i : NativeGoodGrid d n, ∑ j : NativeGoodGrid d n,
        highPowerPairKernel p (nativeRowCorrelation i.val j.val)) ≤
      nativeVarianceConstant d * (p : ℝ) ^ 2 / nativeDimension d n := by
  classical
  let e := nativeGoodRowsEquiv d n
  have hcard : Fintype.card (NativeGoodRows d n
      (nativeShellVarianceFloor d n (nativeGoodFactor d))) = Fintype.card (NativeGoodGrid d n) :=
    (Fintype.card_congr e).symm
  have hgrid : 0 < (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    simp [MidpointGridIndex, MidpointGridCoordinate, Fintype.card_pi]
  have hfrac : nativeGoodDensity d ≤
      (Fintype.card (NativeGoodGrid d n) : ℝ) / Fintype.card (MidpointGridIndex d n) := by
    simpa [nativeGoodDensity, nativeGoodFactor] using nativeGoodGrid_fraction_lower (by omega : 0 < d)
  have hdensity : nativeGoodDensity d * (Fintype.card (MidpointGridIndex d n) : ℝ) ≤
      Fintype.card (NativeGoodRows d n (nativeShellVarianceFloor d n (nativeGoodFactor d))) := by
    rw [hcard]
    exact (le_div_iff₀ hgrid).mp hfrac
  have hagg := nativeGoodPairKernel_average_le_of_density (by omega : 0 < d) hd hn
    (nativeGoodFactor_pos d) (min_le_right _ _) hp (nativeGoodDensity_pos d) hdensity
  have hsum : (∑ x : NativeGoodPair d n (nativeShellVarianceFloor d n (nativeGoodFactor d)),
      highPowerPairKernel p (nativeRowCorrelation x.1.val x.2.val)) =
      ∑ i : NativeGoodGrid d n, ∑ j : NativeGoodGrid d n,
        highPowerPairKernel p (nativeRowCorrelation i.val j.val) := by
    rw [Fintype.sum_prod_type]
    symm
    apply Fintype.sum_equiv e
    intro i
    apply Fintype.sum_equiv e
    intro j
    rfl
  rw [hsum] at hagg
  have hpaircard : (Fintype.card (NativeGoodPair d n
      (nativeShellVarianceFloor d n (nativeGoodFactor d))) : ℝ) =
      (Fintype.card (NativeGoodGrid d n) : ℝ) ^ 2 := by
    simp [NativeGoodPair, Fintype.card_prod, hcard, pow_two]
  rw [hpaircard] at hagg
  let C₀ := (4 * (nativeGoodFactor d * (Nat.factorial (d - 1) : ℝ)) ^ 2 *
      Real.sqrt 2 * shellPolynomialBudget (d - 1)) / nativeGoodDensity d ^ 2
  have hC₀ : 0 ≤ C₀ := by
    have hbudget : 0 ≤ shellPolynomialBudget (d - 1) := tsum_nonneg (fun _ => by positivity)
    dsimp [C₀]
    positivity
  have hD : 0 < nativeDimension d n := by
    unfold nativeDimension hyperbolicCount
    have hc : 0 < Nat.choose (n + d - 1) (d - 1) := Nat.choose_pos (by omega)
    positivity
  have hden : nativeDimension d n ≤ (2 : ℝ) ^ n * ((n : ℝ) + 1) ^ (d - 1) :=
    mul_le_mul_of_nonneg_left (hyperbolicCount_upper_shift (by omega : 1 ≤ d) n) (by positivity)
  calc
    _ = (∑ i : NativeGoodGrid d n, ∑ j : NativeGoodGrid d n,
        highPowerPairKernel p (nativeRowCorrelation i.val j.val)) /
        (Fintype.card (NativeGoodGrid d n) : ℝ) ^ 2 := by ring
    _ ≤ C₀ * (p : ℝ) ^ 2 / ((2 : ℝ) ^ n * ((n : ℝ) + 1) ^ (d - 1)) := by
      convert hagg using 1 <;> dsimp [C₀] <;> ring
    _ ≤ C₀ * (p : ℝ) ^ 2 / nativeDimension d n :=
      div_le_div_of_nonneg_left (by positivity) hD hden
    _ ≤ nativeVarianceConstant d * (p : ℝ) ^ 2 / nativeDimension d n := by
      apply div_le_div_of_nonneg_right _ hD.le
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      dsimp [nativeVarianceConstant, C₀]
      linarith

theorem nativeGoodPowerStatistic_variance_bound {d n p : ℕ}
    (hd : 2 ≤ d) (hn : 0 < n) (heven : Even p)
    (hp : (p : ℝ) ≤ nativeMomentSlope d * ((n : ℝ) + 1)) :
    ProbabilityTheory.variance (nativeGoodPowerStatistic d n p)
      (productStandardGaussian (LayerIndex d n)) ≤
        nativeVarianceConstant d * (p : ℝ) ^ 2 / nativeDimension d n := by
  obtain ⟨k, hk⟩ := heven
  have hpk : p = 2 * k := by omega
  rw [hpk] at hp ⊢
  exact (nativeGoodPowerStatistic_variance_le_pairKernel (by omega : 0 < d) k).trans
    (nativeGoodPairKernel_average_bound hd hn hp)

end BrownianSharp
