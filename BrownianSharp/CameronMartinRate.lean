import BrownianSharp.CameronMartinCover
import BrownianSharp.PeriodicEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Exponential confinement to the Cameron--Martin entropy rate

The result below carries the exact finite-grid confinement family as its only
analytic input.  All dimension crossing, Gaussian cutoff mass, radius
normalization, and dyadic entropy-index calculations are proved here.
-/

open MeasureTheory ProbabilityTheory HaarQuarter BrownianSharp
open scoped NNReal ENNReal

namespace BrownianSharp.CameronMartinRate

/-- The exponential cutoff mass is smaller than the dyadic cover budget for
all native dimensions at least `k`. -/
theorem dyadic_exponential_mass_lt
    {k s : ℕ} (hk : 2 ≤ k) {b D : ℝ} (hb : 0 < b)
    (hD : (s : ℝ) * (k : ℝ) ≤ D) (hfactor : 2 ≤ b * (s : ℝ)) :
    ((2 ^ (k - 1) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Real.exp (-b * D)) <
      (3 / 4 : ℝ≥0∞) := by
  have hkR : 2 ≤ (k : ℝ) := by exact_mod_cast hk
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    linarith
  have hpow : (2 : ℝ) ^ k ≤ Real.exp (k : ℝ) := by
    calc
      (2 : ℝ) ^ k ≤ (Real.exp 1) ^ k := pow_le_pow_left₀ (by norm_num) hexp1 k
      _ = Real.exp (k : ℝ) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
  have hprev : ((2 ^ (k - 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ k := by
    have hnat : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    exact_mod_cast hnat
  have hprod : ((2 ^ (k - 1) : ℕ) : ℝ) * Real.exp (-b * D) < (3 / 4 : ℝ) := by
    have hbkD : 2 * (k : ℝ) ≤ b * D := by
      calc
        2 * (k : ℝ) ≤ (b * (s : ℝ)) * (k : ℝ) := by nlinarith [hkR, hfactor]
        _ ≤ b * D := by
          calc
            (b * (s : ℝ)) * (k : ℝ) = b * ((s : ℝ) * (k : ℝ)) := by ring
            _ ≤ b * D := mul_le_mul_of_nonneg_left hD hb.le
    have hExpMono : Real.exp ((k : ℝ) + -b * D) ≤ Real.exp (-(k : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith [hbkD])
    have hmul : ((2 ^ (k - 1) : ℕ) : ℝ) * Real.exp (-b * D) ≤
        Real.exp (k : ℝ) * Real.exp (-b * D) :=
      mul_le_mul_of_nonneg_right (hprev.trans hpow) (Real.exp_nonneg _)
    have hprod' : Real.exp (k : ℝ) * Real.exp (-b * D) =
        Real.exp ((k : ℝ) + -b * D) := by rw [← Real.exp_add]
    have hexp2 : (3 : ℝ) < Real.exp 2 := by
      have h := Real.add_one_lt_exp (by norm_num : (2 : ℝ) ≠ 0)
      linarith
    have hinv : Real.exp (-2) < (1 / 3 : ℝ) := by
      rw [Real.exp_neg]
      have h := one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 3) hexp2
      simpa [one_div] using h
    calc
      _ ≤ Real.exp (k : ℝ) * Real.exp (-b * D) := hmul
      _ = Real.exp ((k : ℝ) + -b * D) := hprod'
      _ ≤ Real.exp (-(k : ℝ)) := hExpMono
      _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
      _ < (3 / 4 : ℝ) := by linarith
  have hcast : ((2 ^ (k - 1) : ℕ) : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp (-b * D)) =
      ENNReal.ofReal (((2 ^ (k - 1) : ℕ) : ℝ) * Real.exp (-b * D)) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  rw [hcast]
  have hthree : ENNReal.ofReal (3 / 4 : ℝ) = (3 / 4 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4)]
    rw [ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
  rw [← hthree]
  exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 hprod

end BrownianSharp.CameronMartinRate
