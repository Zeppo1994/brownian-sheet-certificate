import BrownianSharp.AlignmentIntegerEvenOrderJetConstraints
import Mathlib.Tactic

/-! Explicit dyadic frequency loss for repeated order-two integration. -/

noncomputable section

namespace BrownianSharp.AlignmentIntegerEvenOrderSigma

open BrownianSharp.AlignmentOrdinaryIntegrationLower

/-- Dimension-independent (for fixed order) block constants. -/
def evenOrderSigmaConst (m : ℕ) : ℝ :=
  ((5 * Real.pi * (m+2:ℝ))^(2*m))⁻¹

def evenOrderSigmaRate (m : ℕ) : ℝ :=
  ((2:ℝ)^(2*m))⁻¹

theorem evenOrderSigmaConst_pos (m : ℕ) : 0 < evenOrderSigmaConst m := by
  apply inv_pos.mpr
  positivity

theorem evenOrderSigmaRate_pos (m : ℕ) : 0 < evenOrderSigmaRate m := by
  apply inv_pos.mpr
  positivity

/-- On the block `K=D=(m+2)2^s`, the m-step homogeneous loss is bounded below
by a fixed constant times a geometric dyadic profile. -/
theorem evenOrder_block_sigma_lower (m s : ℕ) :
    ((((halfFrequency ((m+2)*2^s + (m+2)*2^s))^2)⁻¹)^m) ≥
      evenOrderSigmaConst m * evenOrderSigmaRate m ^ s := by
  let X : ℝ := (m+2:ℝ) * (2:ℝ)^s
  let ν : ℕ := (m+2)*2^s + (m+2)*2^s
  have hX : 0 < X := by
    dsimp [X]
    positivity
  have hX2 : 2 ≤ X := by
    dsimp [X]
    have hm : (2:ℝ) ≤ (m:ℝ)+2 := by exact_mod_cast (show 2 ≤ m+2 by omega)
    have hp : (1:ℝ) ≤ (2:ℝ)^s := one_le_pow₀ (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ (m:ℝ)+2)]
  have hcast : (ν:ℝ) = 2*X := by
    dsimp [ν, X]
    push_cast
    ring
  have hraw : (ν:ℝ) + (1/2:ℝ) ≤ 5*X := by
    rw [hcast]
    nlinarith [hX2]
  have hfreq : halfFrequency ν ≤ 5*Real.pi*X := by
    rw [halfFrequency, hcast]
    have hpi := Real.pi_pos
    have hmul := mul_le_mul_of_nonneg_right hraw (le_of_lt hpi)
    nlinarith [hmul]
  have hfreqpos : 0 < halfFrequency ν := by
    dsimp [halfFrequency]
    positivity
  have hfreqmaxpos : 0 < 5*Real.pi*X := by positivity
  have hsq : (halfFrequency ν)^2 ≤ (5*Real.pi*X)^2 := by
    nlinarith [hfreq, hfreqpos, hfreqmaxpos]
  have hinv : (5*Real.pi*X)⁻¹ ≤ (halfFrequency ν)⁻¹ :=
    (inv_le_inv₀ hfreqmaxpos hfreqpos).2 hfreq
  have hpowle : ((5*Real.pi*X)⁻¹)^(2*m) ≤
      ((halfFrequency ν)⁻¹)^(2*m) := by
    exact pow_le_pow_left₀ (by positivity) hinv (2*m)
  have hfactor : (5*Real.pi*X)^(2*m) =
      (5*Real.pi*(m+2:ℝ))^(2*m) * (2:ℝ)^(2*m*s) := by
    have hx' : 5*Real.pi*X =
        (5*Real.pi*(m+2:ℝ)) * (2:ℝ)^s := by
      dsimp [X]
      ring
    rw [hx', mul_pow]
    calc
      (5*Real.pi*(m+2:ℝ))^(2*m) * ((2:ℝ)^s)^(2*m) =
          (5*Real.pi*(m+2:ℝ))^(2*m) * (2:ℝ)^(s*(2*m)) := by
            rw [← pow_mul]
      _ = (5*Real.pi*(m+2:ℝ))^(2*m) * (2:ℝ)^(2*m*s) := by
        rw [Nat.mul_comm s (2*m)]
  have hright : ((5*Real.pi*X)⁻¹)^(2*m) =
      evenOrderSigmaConst m * evenOrderSigmaRate m ^ s := by
    calc
      ((5*Real.pi*X)⁻¹)^(2*m) = ((5*Real.pi*X)^(2*m))⁻¹ := by
        rw [inv_pow]
      _ = ((5*Real.pi*(m+2:ℝ))^(2*m) * (2:ℝ)^(2*m*s))⁻¹ := by
        rw [hfactor]
      _ = evenOrderSigmaConst m * evenOrderSigmaRate m ^ s := by
        rw [evenOrderSigmaConst, evenOrderSigmaRate]
        field_simp [pow_ne_zero, Real.pi_ne_zero]
        rw [one_div, pow_mul, inv_pow]
        have hA : (2:ℝ)^(2*m) ≠ 0 := pow_ne_zero _ (by norm_num)
        exact (mul_inv_cancel₀ (pow_ne_zero _ hA)).symm
  have hlhs : (((halfFrequency ν)^2)⁻¹)^m =
      ((halfFrequency ν)⁻¹)^(2*m) := by
    simp [← inv_pow, ← pow_mul]
  calc
    evenOrderSigmaConst m * evenOrderSigmaRate m ^ s =
        ((5*Real.pi*X)⁻¹)^(2*m) := hright.symm
    _ ≤ ((halfFrequency ν)⁻¹)^(2*m) := hpowle
    _ = (((halfFrequency ν)^2)⁻¹)^m := hlhs.symm

/-- Product of the coordinate block floors on a grade-`N` profile. -/
theorem evenOrder_block_product_sigma_lower {d N : ℕ} (m : ℕ)
    (hd : 0 < d) (s : Fin d → ℕ) (hs : (∑ i : Fin d, s i) = N) :
    evenOrderSigmaConst m ^ d * evenOrderSigmaRate m ^ N ≤
      ∏ i : Fin d,
        (((halfFrequency ((m+2)*2^(s i) + (m+2)*2^(s i)))^2)⁻¹)^m := by
  have hprod :
      evenOrderSigmaConst m ^ d * evenOrderSigmaRate m ^ N =
        ∏ i : Fin d, (evenOrderSigmaConst m * evenOrderSigmaRate m ^ (s i)) := by
    rw [← hs, Finset.prod_mul_distrib]
    simp [Finset.prod_pow_eq_pow_sum]
  rw [hprod]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact mul_nonneg (evenOrderSigmaConst_pos m).le
      (pow_nonneg (evenOrderSigmaRate_pos m).le _)
  · intro i hi
    exact evenOrder_block_sigma_lower m (s i)

end BrownianSharp.AlignmentIntegerEvenOrderSigma
