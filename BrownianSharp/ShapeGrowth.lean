import BrownianSharp.Interpolation
import Mathlib.Data.Nat.Choose.Bounds

/-! Exact polynomial bounds on native weak-composition counts and overlap
caps. The constants are explicit and depend only on dimension. -/
namespace BrownianSharp

theorem hyperbolicCount_pos {d n : ℕ} (hd : 1 ≤ d) : 0 < hyperbolicCount d n := by
  dsimp [hyperbolicCount]
  exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + d - 1)

theorem hyperbolicCount_upper_shift {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    hyperbolicCount d n ≤ ((n : ℝ) + 1) ^ (d - 1) := by
  have h := Nat.choose_add_le_add_one_pow n (d - 1)
  have htop : n + (d - 1) = n + d - 1 := by omega
  rw [htop] at h
  dsimp [hyperbolicCount]
  exact_mod_cast h

theorem hyperbolicCount_lower_shift {d : ℕ} (hd : 1 ≤ d) (n : ℕ) :
    ((n : ℝ) + 1) ^ (d - 1) / (Nat.factorial (d - 1) : ℝ) ≤ hyperbolicCount d n := by
  have h := Nat.pow_le_choose (d - 1) (n + d - 1) (α := ℝ)
  have htop : n + d - 1 + 1 - (d - 1) = n + 1 := by omega
  simpa [htop, hyperbolicCount] using h

theorem hyperbolicCount_add_upper_product {d : ℕ} (hd : 1 ≤ d) (n h : ℕ) :
    hyperbolicCount d (n + h) ≤ ((n : ℝ) + 1) ^ (d - 1) *
      ((h : ℝ) + 1) ^ (d - 1) := by
  calc
    _ ≤ (((n + h : ℕ) : ℝ) + 1) ^ (d - 1) := hyperbolicCount_upper_shift hd _
    _ ≤ (((n : ℝ) + 1) * ((h : ℝ) + 1)) ^ (d - 1) := by
      apply pow_le_pow_left₀ (by positivity)
      push_cast
      nlinarith
    _ = _ := mul_pow _ _ _

theorem hyperbolicCount_ratio_le {d : ℕ} (hd : 1 ≤ d) (n h : ℕ) :
    hyperbolicCount d h / hyperbolicCount d n ≤
      (Nat.factorial (d - 1) : ℝ) *
        (((h : ℝ) + 1) / ((n : ℝ) + 1)) ^ (d - 1) := by
  have hS := hyperbolicCount_pos (n := n) hd
  have hf : 0 < (Nat.factorial (d - 1) : ℝ) := by positivity
  have hn : 0 < (n : ℝ) + 1 := by positivity
  have hlo := hyperbolicCount_lower_shift hd n
  have hup := hyperbolicCount_upper_shift hd h
  rw [div_pow]
  apply (div_le_iff₀ hS).2
  have hlow : ((n : ℝ) + 1) ^ (d - 1) ≤
      hyperbolicCount d n * (Nat.factorial (d - 1) : ℝ) :=
    (div_le_iff₀ hf).mp hlo
  have hfrac : 1 ≤ hyperbolicCount d n * (Nat.factorial (d - 1) : ℝ) /
      ((n : ℝ) + 1) ^ (d - 1) :=
    (le_div_iff₀ (pow_pos hn _)).2 (by simpa using hlow)
  have hmul := mul_le_mul_of_nonneg_left hfrac (by positivity : 0 ≤ ((h : ℝ) + 1) ^ (d - 1))
  calc
    hyperbolicCount d h ≤ ((h : ℝ) + 1) ^ (d - 1) := hup
    _ ≤ (Nat.factorial (d - 1) : ℝ) *
        (((h : ℝ) + 1) ^ (d - 1) / ((n : ℝ) + 1) ^ (d - 1)) *
          hyperbolicCount d n := by
          convert hmul using 1 <;> ring

noncomputable def shapeOverlapCap (d n h : ℕ) (L : ℝ) : ℝ :=
  L * min (hyperbolicCount d n) (hyperbolicCount d h) / hyperbolicCount d n

theorem shapeOverlapCap_le_constant {d : ℕ} (hd : 1 ≤ d) (n h : ℕ)
    {L : ℝ} (hL : 0 ≤ L) : shapeOverlapCap d n h L ≤ L := by
  unfold shapeOverlapCap
  apply (div_le_iff₀ (hyperbolicCount_pos hd)).2
  exact mul_le_mul_of_nonneg_left (min_le_left _ _) hL

theorem shapeOverlapCap_le_polynomial {d : ℕ} (hd : 1 ≤ d) (n h : ℕ)
    {L : ℝ} (hL : 0 ≤ L) :
    shapeOverlapCap d n h L ≤ L * (Nat.factorial (d - 1) : ℝ) *
      (((h : ℝ) + 1) / ((n : ℝ) + 1)) ^ (d - 1) := by
  calc
    _ ≤ L * (hyperbolicCount d h / hyperbolicCount d n) := by
      unfold shapeOverlapCap
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (min_le_right _ _) hL)
        (hyperbolicCount_pos hd).le
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (hyperbolicCount_ratio_le hd n h) hL
      simpa [mul_assoc] using h

theorem shapeOverlapCap_nonneg {d : ℕ} (hd : 1 ≤ d) (n h : ℕ)
    {L : ℝ} (hL : 0 ≤ L) : 0 ≤ shapeOverlapCap d n h L := by
  unfold shapeOverlapCap
  exact div_nonneg (mul_nonneg hL
    (le_min (hyperbolicCount_pos hd).le (hyperbolicCount_pos hd).le))
      (hyperbolicCount_pos hd).le

/-- The q-th-power cap also has the linear bound used in the exponential
factor, by splitting at h=n and retaining the exact min(S_n,S_h). -/
theorem shapeOverlapCap_le_linear {d : ℕ} (hd : 2 ≤ d) (n h : ℕ)
    {L : ℝ} (hL : 0 ≤ L) :
    shapeOverlapCap d n h L ≤ L * (Nat.factorial (d - 1) : ℝ) *
      (((h : ℝ) + 1) / ((n : ℝ) + 1)) := by
  have hd1 : 1 ≤ d := by omega
  have hf : 1 ≤ (Nat.factorial (d - 1) : ℝ) := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos (d - 1))
  let x := ((h : ℝ) + 1) / ((n : ℝ) + 1)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  by_cases hhn : h ≤ n
  · have hx1 : x ≤ 1 := by
      dsimp [x]
      apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).2
      exact_mod_cast Nat.add_le_add_right hhn 1
    have hpow : x ^ (d - 1) ≤ x := by
      simpa using pow_le_pow_of_le_one hx0 hx1 (show 1 ≤ d - 1 by omega)
    exact (shapeOverlapCap_le_polynomial hd1 n h hL).trans
      (mul_le_mul_of_nonneg_left hpow (by positivity))
  · have hx1 : 1 ≤ x := by
      dsimp [x]
      apply (one_le_div (by positivity : (0 : ℝ) < n + 1)).2
      have hnh : n ≤ h := by omega
      exact_mod_cast Nat.add_le_add_right hnh 1
    have hprod : 1 ≤ (Nat.factorial (d - 1) : ℝ) * x := one_le_mul_of_one_le_of_one_le hf hx1
    calc
      _ ≤ L := shapeOverlapCap_le_constant hd1 n h hL
      _ ≤ L * (Nat.factorial (d - 1) : ℝ) * x := by
        have hmul := mul_le_mul_of_nonneg_left hprod hL
        simpa [mul_assoc] using hmul

end BrownianSharp
