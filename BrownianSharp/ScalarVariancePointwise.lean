import BrownianSharp.LayerBlockSummability
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Pointwise low/high geometric majorants for the actual scalar atom variance. -/
noncomputable section
open scoped ENNReal
namespace BrownianSharp.ScalarVariancePointwise
open AtomicTensorFactorization LayerBlockSummability

theorem scalar_low_real_bound {r C : ℝ} {K s k : ℕ} (hr : 0 ≤ r) (hk : k ≤ s) :
    (2:ℝ)^(2*r*(k:ℝ))*scalarVarianceEnvelope K C s k ≤
      (5*(2:ℝ)^(2*r*(s:ℝ)))*(1/2:ℝ)^(s-k) := by
  have hweight : (2:ℝ)^(2*r*(k:ℝ)) ≤ (2:ℝ)^(2*r*(s:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have hks : (k:ℝ) ≤ (s:ℝ) := by exact_mod_cast hk
    nlinarith
  have hratio : (2:ℝ)^k/(2:ℝ)^s = (1/2:ℝ)^(s-k) := by
    have heq : s = k+(s-k) := (Nat.add_sub_of_le hk).symm
    conv_lhs => rw [heq, pow_add]
    rw [div_mul_eq_div_div, div_self (by positivity : (2:ℝ)^k ≠ 0)]
    simp [one_div, inv_pow]
  simp only [scalarVarianceEnvelope, if_pos hk]
  rw [hratio]
  nlinarith [mul_le_mul_of_nonneg_right hweight (by positivity : 0 ≤ (1/2:ℝ)^(s-k))]

theorem scalar_low_bound {r C : ℝ} {K s k : ℕ} (hr : 0 ≤ r) (hk : k ≤ s) :
    scalarWeightedVariance r K C s k ≤
      ENNReal.ofReal (5*(2:ℝ)^(2*r*(s:ℝ))) * (1/2:ENNReal)^(s-k) := by
  have h := ENNReal.ofReal_le_ofReal (scalar_low_real_bound (C:=C) (K:=K) hr hk)
  have heq : ENNReal.ofReal ((5*(2:ℝ)^(2*r*(s:ℝ)))*(1/2:ℝ)^(s-k)) =
      ENNReal.ofReal (5*(2:ℝ)^(2*r*(s:ℝ))) * (1/2:ENNReal)^(s-k) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2)]
    norm_num
  rw [← heq]
  exact h

private theorem inverse_square_bound (K k : ℕ) (hk : 1 ≤ k) :
    ((((2*Real.pi*(2:ℝ)^(k-1))^K)⁻¹)^2) ≤
      (2:ℝ)^(-2*(K:ℝ)*((k:ℝ)-1)) := by
  have hbase : (2:ℝ)^(k-1) ≤ 2*Real.pi*(2:ℝ)^(k-1) := by
    nlinarith [Real.one_le_pi_div_two, (show (0:ℝ)<2^(k-1) by positivity)]
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ)≤2^(k-1)) hbase K
  have hinv := one_div_le_one_div_of_le (by positivity : (0:ℝ)<((2:ℝ)^(k-1))^K) hp
  have hsq := pow_le_pow_left₀ (by positivity : (0:ℝ)≤1/(2*Real.pi*2^(k-1))^K) hinv 2
  have heq : ((1 / (((2:ℝ)^(k-1))^K))^2) =
      (2:ℝ)^(-2*(K:ℝ)*((k:ℝ)-1)) := by
    calc
      _ = ((2:ℝ)^((k-1)*(K*2)))⁻¹ := by
        simp only [one_div, inv_pow, ← pow_mul, Nat.mul_assoc]
      _ = (2:ℝ)^(-(((k-1)*(K*2):ℕ):ℝ)) := by
        rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2), Real.rpow_natCast]
      _ = _ := by
        congr 1
        rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hk]
        norm_num
        ring
  rw [heq] at hsq
  simpa only [one_div] using hsq

theorem scalar_high_real_bound {r C : ℝ} {K s k : ℕ}
    (hK : 1 ≤ K) (hk : s < k) :
    (2:ℝ)^(2*r*(k:ℝ))*scalarVarianceEnvelope K C s k ≤
      (C^2*(2:ℝ)^(2*(K:ℝ)+3+2*r*(s:ℝ))) *
        ((2:ℝ)^(2*r-(2*(K:ℝ)-1)))^(k-s) := by
  have hden := inverse_square_bound K k (by omega)
  have hcount : (2:ℝ)^(k+2)+1 ≤ (2:ℝ)^(k+3) := by
    rw [pow_add, pow_add]
    norm_num
    have : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
    nlinarith
  have hL : ((2*K-1:ℕ):ℝ) = 2*(K:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*K)]
    push_cast
    ring
  have hpow :
      (2:ℝ)^(2*r*(k:ℝ)) * ((C^2 * (2:ℝ)^((2*K-1)*s)) *
        (2:ℝ)^(k+3) * (2:ℝ)^(-2*(K:ℝ)*((k:ℝ)-1))) =
      (C^2*(2:ℝ)^(2*(K:ℝ)+3+2*r*(s:ℝ))) *
        ((2:ℝ)^(2*r-(2*(K:ℝ)-1)))^(k-s) := by
    rw [← Real.rpow_natCast (2:ℝ) ((2*K-1)*s),
      ← Real.rpow_natCast (2:ℝ) (k+3),
      ← Real.rpow_natCast ((2:ℝ)^(2*r-(2*(K:ℝ)-1))) (k-s),
      ← Real.rpow_mul (by positivity : (0:ℝ)≤2)]
    have hexp : 2*r*(k:ℝ) + (((2*K-1)*s:ℕ):ℝ) + ((k+3:ℕ):ℝ) +
        (-2*(K:ℝ)*((k:ℝ)-1)) =
        (2*(K:ℝ)+3+2*r*(s:ℝ)) + (2*r-(2*(K:ℝ)-1))*((k-s:ℕ):ℝ) := by
      rw [Nat.cast_mul, hL, Nat.cast_add, Nat.cast_sub (by omega : s ≤ k)]
      norm_num
      ring
    calc
      _ = C^2 * ((2:ℝ)^(2*r*(k:ℝ)) * (2:ℝ)^(((2*K-1)*s:ℕ):ℝ) *
        (2:ℝ)^((k+3:ℕ):ℝ) * (2:ℝ)^(-2*(K:ℝ)*((k:ℝ)-1))) := by ring
      _ = C^2 * (2:ℝ)^(2*r*(k:ℝ) + (((2*K-1)*s:ℕ):ℝ) + ((k+3:ℕ):ℝ) +
        (-2*(K:ℝ)*((k:ℝ)-1))) := by
          simp only [Real.rpow_add (by norm_num : (0:ℝ)<2)]
      _ = _ := by
        rw [hexp, Real.rpow_add (by norm_num : (0:ℝ)<2)]
        ring
  simp only [scalarVarianceEnvelope, if_neg (by omega : ¬ k ≤ s)]
  calc
    _ ≤ (2:ℝ)^(2*r*(k:ℝ)) * ((C^2 * (2:ℝ)^((2*K-1)*s)) *
        (2:ℝ)^(k+3) * (2:ℝ)^(-2*(K:ℝ)*((k:ℝ)-1))) := by
      gcongr
    _ = _ := hpow

theorem scalar_high_bound {r C : ℝ} {K s k : ℕ}
    (hK : 1 ≤ K) (hk : s < k) :
    scalarWeightedVariance r K C s k ≤
      ENNReal.ofReal (C^2*(2:ℝ)^(2*(K:ℝ)+3+2*r*(s:ℝ))) *
        (ENNReal.ofReal ((2:ℝ)^(2*r-(2*(K:ℝ)-1))))^(k-s) := by
  have h := ENNReal.ofReal_le_ofReal (scalar_high_real_bound (C:=C) (r:=r) hK hk)
  have heq : ENNReal.ofReal
      ((C^2*(2:ℝ)^(2*(K:ℝ)+3+2*r*(s:ℝ))) *
        ((2:ℝ)^(2*r-(2*(K:ℝ)-1)))^(k-s)) =
      ENNReal.ofReal (C^2*(2:ℝ)^(2*(K:ℝ)+3+2*r*(s:ℝ))) *
        (ENNReal.ofReal ((2:ℝ)^(2*r-(2*(K:ℝ)-1))))^(k-s) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity)]
  rw [← heq]
  exact h

end BrownianSharp.ScalarVariancePointwise
