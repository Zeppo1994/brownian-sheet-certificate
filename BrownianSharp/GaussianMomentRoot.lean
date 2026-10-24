import BrownianSharp.Moments
import BrownianSharp.GaussianGridStatistics

/-!
Lower bound on the root growth of the even standard Gaussian moments.
The proof uses the exact moment formula from `Moments` and the elementary
factorial block bound `(k+1)^k k! ≤ (2k)!`.
-/

open MeasureTheory ProbabilityTheory

namespace BrownianSharp

/-- The even standard Gaussian moment dominates `(k/2)^k`. -/
theorem standardGaussian_evenMoment_lower (k : ℕ) :
    ((k : ℝ) / 2) ^ k ≤
      ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal) := by
  rw [standardGaussian_evenMoment_factorial]
  have hfacNat : Nat.factorial k * (k + 1) ^ k ≤ Nat.factorial (2 * k) := by
    have h := Nat.factorial_mul_pow_le_factorial (m := k) (n := k)
    have hidx : k + k = 2 * k := by omega
    simpa [hidx] using h
  have hfac : (Nat.factorial k : ℝ) * ((k + 1 : ℝ) ^ k) ≤ (Nat.factorial (2 * k) : ℝ) := by
    exact_mod_cast hfacNat
  have hpow : (k : ℝ) ^ k ≤ (k + 1 : ℝ) ^ k := by
    gcongr
    exact_mod_cast Nat.le_succ k
  have hprod : ((k : ℝ) / 2) ^ k *
      ((2 : ℝ) ^ k * (Nat.factorial k : ℝ)) ≤ (Nat.factorial (2 * k) : ℝ) := by
    calc
      ((k : ℝ) / 2) ^ k * ((2 : ℝ) ^ k * (Nat.factorial k : ℝ)) =
          (k : ℝ) ^ k * (Nat.factorial k : ℝ) := by
            rw [div_pow]
            field_simp
      _ ≤ (k + 1 : ℝ) ^ k * (Nat.factorial k : ℝ) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
      _ ≤ (Nat.factorial (2 * k) : ℝ) := by
        calc
          _ = (Nat.factorial k : ℝ) * (k + 1 : ℝ) ^ k := by ring
          _ ≤ _ := hfac
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ k * (Nat.factorial k : ℝ))).2
  exact hprod

/-- A concrete root-growth lower bound for every even standard Gaussian moment:
`M_(2k)^(1/(2k)) ≥ (1/2) sqrt(2k)`. -/
theorem standardGaussian_evenMoment_root_lower (k : ℕ) (hk : 1 ≤ k) :
    Real.rpow
        (∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal))
        ((2 * (k : ℝ))⁻¹) ≥ Real.sqrt (2 * (k : ℝ)) / 2 := by
  let B : ℝ := Real.sqrt (2 * (k : ℝ)) / 2
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hk0 : (2 * (k : ℝ)) ≠ 0 := by
    have : 0 < (k : ℝ) := by exact_mod_cast hk
    positivity
  have hBsq : B ^ 2 = (k : ℝ) / 2 := by
    dsimp [B]
    rw [div_pow, Real.sq_sqrt (by positivity)]
    ring
  have hBpow : B ^ (2 * k) = ((k : ℝ) / 2) ^ k := by
    calc
      B ^ (2 * k) = (B ^ 2) ^ k := pow_mul B 2 k
      _ = ((k : ℝ) / 2) ^ k := by rw [hBsq]
  have hmoment := standardGaussian_evenMoment_lower k
  have hpowle : B ^ (2 * k) ≤
      ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal) := by
    rw [hBpow]
    exact hmoment
  have hmon := Real.rpow_le_rpow (by positivity : 0 ≤ B ^ (2 * k)) hpowle
      (by positivity : 0 ≤ (2 * (k : ℝ))⁻¹)
  calc
    Real.sqrt (2 * (k : ℝ)) / 2 = B := rfl
    _ = (B ^ (2 * k) : ℝ) ^ ((2 * (k : ℝ))⁻¹) := by
      rw [← Real.rpow_natCast B (2 * k)]
      rw [← show ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) by push_cast; ring]
      have hknat : 2 * k ≠ 0 := by omega
      have hy : ((2 * k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hknat
      exact (Real.rpow_rpow_inv hB0 hy).symm
    _ ≤ _ := hmon


/-- Every even standard Gaussian moment is strictly positive. -/
theorem standardGaussianMoment_even_pos (k : ℕ) :
    0 < standardGaussianMoment (2 * k) := by
  rw [standardGaussianMoment, standardGaussian_evenMoment]
  positivity

/-- The root lower bound in the notation used by the native-grid statistic. -/
theorem standardGaussianMoment_even_root_lower (k : ℕ) (hk : 1 ≤ k) :
    Real.rpow (standardGaussianMoment (2 * k)) ((2 * (k : ℝ))⁻¹) ≥
      Real.sqrt (2 * (k : ℝ)) / 2 := by
  simpa [standardGaussianMoment] using standardGaussian_evenMoment_root_lower k hk

/-- Root growth for any positive even order `p`, stated directly for the
moment function consumed by the native power statistic. -/
theorem standardGaussianMoment_evenOrder_root_lower {p : ℕ}
    (hpEven : Even p) (hpTwo : 2 ≤ p) :
    Real.rpow (standardGaussianMoment p) ((p : ℝ)⁻¹) ≥ Real.sqrt (p : ℝ) / 2 := by
  obtain ⟨k, rfl⟩ := hpEven
  have hk : 1 ≤ k := by omega
  have h := standardGaussian_evenMoment_root_lower k hk
  convert h using 1
  · simp only [standardGaussianMoment]
    rw [show k + k = 2 * k by omega]
    rw [Nat.cast_mul, Nat.cast_ofNat]
  · rw [show k + k = 2 * k by omega]
    rw [Nat.cast_mul, Nat.cast_ofNat]

end BrownianSharp
