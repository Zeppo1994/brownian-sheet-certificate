import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.AlignmentWidthRates
import Mathlib.Tactic

noncomputable section
open scoped ENNReal

namespace BrownianSharp.AlignmentOperatorWidthIndexShift

open BrownianSharp
open BrownianSharp.Latest
open BrownianSharp.AlignmentWidthRates

/-! A rank `< k` width uses the old rank `≤ k-1` width.  This helper
transfers an eventual two-sided rate at index `k-1` to the same rate at `k`.
The proof is deliberately kept independent of the operator and ambient space,
so it can be reused for the Cameron--Martin, periodic, and RL operators. -/

theorem rate_succ_comparable {r a : ℝ} (hr : 0 < r) (ha : 0 ≤ a)
    {k : ℕ} (hk : 3 ≤ k) :
    2 ^ (-a) * logarithmicIndexRate r a k ≤
        logarithmicIndexRate r a (k - 1) ∧
      logarithmicIndexRate r a (k - 1) ≤
        2 ^ r * logarithmicIndexRate r a k := by
  have hkR : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hx : (0:ℝ) < k := by linarith
  have hy : (0:ℝ) < (k:ℝ)-1 := by linarith
  have hyx : (k:ℝ)-1 ≤ k := by linarith
  have hyhalf : k/2 ≤ (k:ℝ)-1 := by linarith
  have hlogx : 0 < Real.log (k:ℝ) := Real.log_pos (by linarith)
  have hlogy : 0 < Real.log ((k:ℝ)-1) := Real.log_pos (by linarith)
  have hlogcomp : Real.log (k:ℝ) ≤ 2 * Real.log ((k:ℝ)-1) := by
    have hsquare : (k:ℝ) ≤ ((k:ℝ)-1)^2 := by nlinarith
    have h := Real.log_le_log hx hsquare
    rw [Real.log_pow] at h
    norm_num at h ⊢
    exact h
  have hloghalf : Real.log (k:ℝ)/2 ≤ Real.log ((k:ℝ)-1) := by linarith
  have hpowlo : (k:ℝ)^(-r) ≤ ((k:ℝ)-1)^(-r) :=
    Real.rpow_le_rpow_of_nonpos hy hyx (by linarith)
  have hpowhi : ((k:ℝ)-1)^(-r) ≤ 2^r*(k:ℝ)^(-r) := by
    have hratio : (k:ℝ)/((k:ℝ)-1) ≤ 2 := by
      apply (div_le_iff₀ hy).2
      nlinarith
    have hratioPos : 0 ≤ (k:ℝ)/((k:ℝ)-1) := by positivity
    have hratioPow := Real.rpow_le_rpow hratioPos hratio hr.le
    have hfactor : ((k:ℝ)-1)^(-r) =
        (k:ℝ)^(-r) * ((k:ℝ)/((k:ℝ)-1))^r := by
      rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_neg_eq_inv_rpow,
        Real.div_rpow hx.le hy.le]
      rw [Real.inv_rpow hy.le, Real.inv_rpow hx.le]
      field_simp
    rw [hfactor]
    calc
      (k:ℝ)^(-r) * ((k:ℝ)/((k:ℝ)-1))^r ≤
          (k:ℝ)^(-r) * 2^r := by
        exact mul_le_mul_of_nonneg_left hratioPow (Real.rpow_nonneg hx.le _)
      _ = 2^r * (k:ℝ)^(-r) := by ring
  have hlogpowlo : (Real.log (k:ℝ)/2)^a ≤
      (Real.log ((k:ℝ)-1))^a :=
    Real.rpow_le_rpow (by positivity) hloghalf ha
  have hlogpowhi : (Real.log ((k:ℝ)-1))^a ≤ (Real.log (k:ℝ))^a :=
    Real.rpow_le_rpow hlogy.le (Real.log_le_log hy hyx) ha
  have hlogfactor : (Real.log (k:ℝ)/2)^a =
      2^(-a)*(Real.log (k:ℝ))^a := by
    calc
      (Real.log (k:ℝ)/2)^a = (Real.log (k:ℝ))^a / (2:ℝ)^a :=
        Real.div_rpow hlogx.le (by norm_num : (0:ℝ)≤2) a
      _ = ((2:ℝ)^a)⁻¹ * (Real.log (k:ℝ))^a := by ring
      _ = 2^(-a)*(Real.log (k:ℝ))^a := by
        calc
          ((2:ℝ)^a)⁻¹ * (Real.log (k:ℝ))^a =
              (2⁻¹)^a * (Real.log (k:ℝ))^a := by
            rw [Real.inv_rpow (by norm_num : (0:ℝ)≤2) a]
          _ = 2^(-a)*(Real.log (k:ℝ))^a := by
            rw [← Real.rpow_neg_eq_inv_rpow]
  constructor
  · unfold logarithmicIndexRate
    simp only [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    calc
      2^(-a) * ((k:ℝ)^(-r) * (Real.log (k:ℝ))^a) =
          (k:ℝ)^(-r) * (Real.log (k:ℝ)/2)^a := by rw [hlogfactor]; ring
      _ ≤ ((k:ℝ)-1)^(-r) * (Real.log (k:ℝ)/2)^a :=
        mul_le_mul_of_nonneg_right hpowlo (Real.rpow_nonneg (by positivity) _)
      _ ≤ ((k:ℝ)-1)^(-r) * (Real.log ((k:ℝ)-1))^a :=
        mul_le_mul_of_nonneg_left hlogpowlo (Real.rpow_nonneg hy.le _)
  · unfold logarithmicIndexRate
    simp only [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
    calc
      ((k:ℝ)-1)^(-r) * (Real.log ((k:ℝ)-1))^a ≤
          (2^r*(k:ℝ)^(-r)) * (Real.log (k:ℝ))^a :=
        mul_le_mul hpowhi hlogpowhi
          (Real.rpow_nonneg hlogy.le _)
          (mul_nonneg (Real.rpow_nonneg (by norm_num : 0≤(2:ℝ)) _)
            (Real.rpow_nonneg hx.le _))
      _ = 2^r*((k:ℝ)^(-r)*(Real.log (k:ℝ))^a) := by ring

theorem twoSided_width_index_shift
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (r a : ℝ) (hr : 0 < r) (ha : 0 ≤ a)
    (c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (k₀ : ℕ) (hk₀ : 3 ≤ k₀)
    (hwidth : ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal (c * logarithmicIndexRate r a (k - 1)) ≤
          HaarQuarter.TheoremD.Width.kolmogorovWidth K (k - 1) ∧
        HaarQuarter.TheoremD.Width.kolmogorovWidth K (k - 1) ≤
          ENNReal.ofReal (C * logarithmicIndexRate r a (k - 1))) :
    ∃ c' C' : ℝ, 0 < c' ∧ 0 < C' ∧
      ∀ k : ℕ, k₀ ≤ k →
        ENNReal.ofReal (c' * logarithmicIndexRate r a k) ≤
            HaarQuarter.TheoremD.Width.kolmogorovWidth K (k - 1) ∧
          HaarQuarter.TheoremD.Width.kolmogorovWidth K (k - 1) ≤
            ENNReal.ofReal (C' * logarithmicIndexRate r a k) := by
  refine ⟨c * 2 ^ (-a), C * 2 ^ r, mul_pos hc (Real.rpow_pos_of_pos (by norm_num) _),
    mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro k hk
  have hk3 : 3 ≤ k := hk₀.trans hk
  obtain ⟨hl, hu⟩ := rate_succ_comparable hr ha hk3
  constructor
  · have h := (hwidth k hk).1
    have hreal : c * 2 ^ (-a) * logarithmicIndexRate r a k ≤
        c * logarithmicIndexRate r a (k-1) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hl hc.le
    exact (ENNReal.ofReal_le_ofReal hreal).trans h
  · have hreal : C * logarithmicIndexRate r a (k-1) ≤
        C * 2 ^ r * logarithmicIndexRate r a k := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hu hC.le
    exact (hwidth k hk).2.trans (ENNReal.ofReal_le_ofReal hreal)

end BrownianSharp.AlignmentOperatorWidthIndexShift
