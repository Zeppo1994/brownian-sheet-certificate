import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

/-!
# All-radius interpolation for the Brownian sharp scale

This file isolates the deterministic Step 8 passage from a discrete scale
estimate to all radii.  It does not formalize the probabilistic estimate at
the scales, the construction of the scales, or the Brownian sheet.  Those
remain explicit inputs below.
-/

namespace BrownianSharp

/-- A scale estimate interpolates to all radii when adjacent scales have
bounded ratio, their reciprocal logarithm is O(n), and their scale strength
dominates `radius⁻² * n^k`.  `profile` represents the negative log small-ball
probability; its monotonicity is stated explicitly. -/
theorem interpolate_discrete_scales
    (profile : ℝ → ℝ) (radius dimension : ℕ → ℝ) (k N : ℕ) (a b C : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hC : 0 < C)
    (hradius : ∀ n : ℕ, (N : ℝ) ≤ n → 0 < radius n)
    (hadjacent : ∀ n : ℕ, (N : ℝ) ≤ n →
      radius n / Real.sqrt 2 ≤ radius (n + 1))
    (hlog : ∀ n : ℕ, (N : ℝ) ≤ n →
      Real.log ((radius (n + 1))⁻¹) ≤ C * n)
    (hdimension : ∀ n : ℕ, (N : ℝ) ≤ n →
      a * (radius n)⁻¹ ^ 2 * (n : ℝ) ^ k ≤ dimension n)
    (hscale : ∀ n : ℕ, (N : ℝ) ≤ n → b * dimension n ≤ profile (radius n))
    (hmono : ∀ x y : ℝ, 0 < x → x ≤ y → profile y ≤ profile x)
    (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (hεle1 : ε ≤ 1)
    (hbracket : ∃ n : ℕ, (N : ℝ) ≤ n ∧ radius (n + 1) < ε ∧ ε ≤ radius n) :
    (a * b / (2 * C ^ k)) * ε⁻¹ ^ 2 * (Real.log (ε⁻¹)) ^ k ≤ profile ε := by
  obtain ⟨n, hnN, hlow, hupp⟩ := hbracket
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by exact_mod_cast hN) hnN
  have hrn : 0 < radius n := hradius n hnN
  have hn1 : (N : ℝ) ≤ (n + 1 : ℕ) := by
    exact_mod_cast (le_trans (show N ≤ n by exact_mod_cast hnN) (Nat.le_succ n))
  have hrnext : 0 < radius (n + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hradius (n + 1) hn1
  have hlogε : 0 ≤ Real.log (ε⁻¹) := Real.log_nonneg (by rw [one_le_inv₀ hε]; exact hεle1)
  have hlogbound : Real.log (ε⁻¹) ≤ C * n := by
    calc
      Real.log (ε⁻¹) ≤ Real.log ((radius (n + 1))⁻¹) := by
        apply Real.log_le_log (by positivity)
        simpa [one_div] using one_div_le_one_div_of_le hrnext hlow.le
      _ ≤ C * n := hlog n hnN
  have hlogpow : (Real.log (ε⁻¹)) ^ k ≤ (C * n) ^ k :=
    pow_le_pow_left₀ hlogε hlogbound k
  have hratio : radius n ≤ Real.sqrt 2 * ε := by
    have h := le_trans (hadjacent n hnN) hlow.le
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hm := (div_le_iff₀ hs).mp h
    nlinarith [hm]
  have hratioSq : (radius n) ^ 2 ≤ 2 * ε ^ 2 := by
    have hsqrt : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hmul : (radius n) ^ 2 ≤ (Real.sqrt 2 * ε) ^ 2 := by
      calc
        (radius n) ^ 2 = radius n * radius n := by ring
        _ ≤ radius n * (Real.sqrt 2 * ε) :=
          mul_le_mul_of_nonneg_left hratio hrn.le
        _ ≤ (Real.sqrt 2 * ε) * (Real.sqrt 2 * ε) :=
          mul_le_mul_of_nonneg_right hratio (by positivity)
        _ = (Real.sqrt 2 * ε) ^ 2 := by ring
    nlinarith [hmul]
  have hinv : (2 : ℝ)⁻¹ * ε⁻¹ ^ 2 ≤ (radius n)⁻¹ ^ 2 := by
    calc
      (2 : ℝ)⁻¹ * ε⁻¹ ^ 2 = (2 * ε ^ 2)⁻¹ := by field_simp
      _ ≤ ((radius n) ^ 2)⁻¹ := by
        simpa [one_div] using
          one_div_le_one_div_of_le (by positivity) hratioSq
      _ = (radius n)⁻¹ ^ 2 := by rw [inv_pow]
  have hscale' : b * dimension n ≤ profile ε := by
    exact le_trans (hscale n hnN) (hmono _ _ hε hupp)
  have hlogpow' : (Real.log (ε⁻¹)) ^ k ≤ C ^ k * (n : ℝ) ^ k := by
    calc
      (Real.log (ε⁻¹)) ^ k ≤ (C * (n : ℝ)) ^ k := pow_le_pow_left₀ hlogε hlogbound k
      _ = C ^ k * (n : ℝ) ^ k := mul_pow C (n : ℝ) k
  have hproduct : ε⁻¹ ^ 2 * (Real.log (ε⁻¹)) ^ k ≤
      2 * (radius n)⁻¹ ^ 2 * (C ^ k * (n : ℝ) ^ k) := by
    have hinv' : ε⁻¹ ^ 2 ≤ 2 * (radius n)⁻¹ ^ 2 := by nlinarith [hinv]
    exact mul_le_mul hinv' hlogpow' (by positivity) (by positivity)
  have hnumeric : (a * b / (2 * C ^ k)) * ε⁻¹ ^ 2 *
      (Real.log (ε⁻¹)) ^ k ≤ b * (a * (radius n)⁻¹ ^ 2 * (n : ℝ) ^ k) := by
    have hcoef : 0 ≤ a * b / (2 * C ^ k) := by positivity
    have hCp : 0 < C ^ k := pow_pos hC k
    calc
      (a * b / (2 * C ^ k)) * ε⁻¹ ^ 2 * (Real.log (ε⁻¹)) ^ k =
          (a * b / (2 * C ^ k)) *
            (ε⁻¹ ^ 2 * (Real.log (ε⁻¹)) ^ k) := by ring
      _ ≤ (a * b / (2 * C ^ k)) *
            (2 * (radius n)⁻¹ ^ 2 * (C ^ k * (n : ℝ) ^ k)) :=
          mul_le_mul_of_nonneg_left hproduct hcoef
      _ = b * (a * (radius n)⁻¹ ^ 2 * (n : ℝ) ^ k) := by
          field_simp [ne_of_gt hCp]
  have hdim := hdimension n hnN
  exact le_trans hnumeric (le_trans
    (mul_le_mul_of_nonneg_left hdim (le_of_lt hb)) hscale')

end BrownianSharp

namespace BrownianSharp

/-- The number of total-grade `n` hyperbolic Haar rectangles in dimension `d`. -/
def hyperbolicCount (d n : ℕ) : ℝ :=
  (Nat.choose (n + d - 1) (d - 1) : ℕ)

/-- Native block dimension at total Haar grade `n`. -/
def nativeDimension (d n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * hyperbolicCount d n

/-- Candidate confinement radius from the total-grade block. -/
noncomputable def sharpRadius (d : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  a * Real.sqrt ((n : ℝ) * hyperbolicCount d n / (2 : ℝ) ^ n)

/-- Pascal's multiplicative identity gives the exact ratio of neighboring
hyperbolic counts. -/
theorem hyperbolicCount_succ_mul (d n : ℕ) (hd : 1 ≤ d) :
    hyperbolicCount d n * (n + d) =
      hyperbolicCount d (n + 1) * (n + 1) := by
  unfold hyperbolicCount
  have hnat := Nat.choose_mul_succ_eq (n + d - 1) (d - 1)
  have htop : n + d - 1 + 1 = n + d := by omega
  have hrem : n + d - (d - 1) = n + 1 := by omega
  have hshape : n + 1 + d - 1 = n + d := by omega
  rw [hshape]
  exact_mod_cast (by rw [htop, hrem] at hnat; exact hnat)

/-- The elementary lower bound on a fixed-column binomial coefficient. -/
theorem hyperbolicCount_lower {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) :
    (n : ℝ) ^ (d - 1) / (Nat.factorial (d - 1) : ℝ) ≤ hyperbolicCount d n := by
  have hchoose := Nat.pow_le_choose (d - 1) (n + d - 1) (α := ℝ)
  have htop : n + d - 1 + 1 - (d - 1) = n + 1 := by omega
  have hchoose' :
      ((n + 1 : ℕ) : ℝ) ^ (d - 1) / (Nat.factorial (d - 1) : ℝ) ≤
        hyperbolicCount d n := by
    simpa [hyperbolicCount, htop] using hchoose
  have hnle : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ n) hnle (d - 1)
  have hfactorial : 0 ≤ (Nat.factorial (d - 1) : ℝ) := by positivity
  calc
    (n : ℝ) ^ (d - 1) / (Nat.factorial (d - 1) : ℝ) ≤
        ((n : ℝ) + 1) ^ (d - 1) / (Nat.factorial (d - 1) : ℝ) :=
      div_le_div_of_nonneg_right hpow hfactorial
    _ ≤ hyperbolicCount d n := by simpa using hchoose'

/-- The exact native dimension dominates the polynomial factor required by
the sharp exponent. -/
theorem nativeDimension_scale_lower {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) :
    (a ^ 2 / (Nat.factorial (d - 1) : ℝ) ^ 2) *
        (sharpRadius d a n)⁻¹ ^ 2 * (n : ℝ) ^ (2 * (d - 1) + 1) ≤
      nativeDimension d n := by
  let S := hyperbolicCount d n
  let f : ℝ := (Nat.factorial (d - 1) : ℕ)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hS : 0 < S := by
    dsimp [S, hyperbolicCount]
    exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + d - 1)
  have hpow2 : 0 < (2 : ℝ) ^ n := by positivity
  have hradSq : (sharpRadius d a n) ^ 2 = a ^ 2 * ((n : ℝ) * S / (2 : ℝ) ^ n) := by
    unfold sharpRadius
    rw [mul_pow, Real.sq_sqrt (div_nonneg (mul_nonneg hnR.le hS.le) hpow2.le)]
  have hrPos : 0 < sharpRadius d a n := by
    unfold sharpRadius
    apply mul_pos ha
    apply Real.sqrt_pos.2
    positivity
  have hidentity : nativeDimension d n =
      a ^ 2 * (sharpRadius d a n)⁻¹ ^ 2 * (n : ℝ) * S ^ 2 := by
    unfold nativeDimension
    rw [inv_pow, hradSq]
    field_simp [ha.ne', ne_of_gt hnR, ne_of_gt hS, ne_of_gt hpow2,
      ne_of_gt hrPos]
    ring
  have hcount : (n : ℝ) ^ (d - 1) / f ≤ S := by
    simpa [S, f] using hyperbolicCount_lower hd hn
  have hfactorial : 0 < f := by dsimp [f]; positivity
  have hcountSq : ((n : ℝ) ^ (d - 1) / f) ^ 2 ≤ S ^ 2 :=
    pow_le_pow_left₀ (by positivity) hcount 2
  have hcountPoly : (n : ℝ) ^ (2 * (d - 1) + 1) / f ^ 2 ≤
      (n : ℝ) * S ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hcountSq hnR.le
    have hexp : (n : ℝ) * ((n : ℝ) ^ (d - 1) / f) ^ 2 =
        (n : ℝ) ^ (2 * (d - 1) + 1) / f ^ 2 := by
      rw [div_pow, ← pow_mul]
      have hmulPow : (n : ℝ) * (n : ℝ) ^ ((d - 1) * 2) =
          (n : ℝ) ^ ((d - 1) * 2 + 1) := by
        rw [pow_succ]
        ring
      have heq : (d - 1) * 2 + 1 = 2 * (d - 1) + 1 := by omega
      field_simp [ne_of_gt hfactorial]
      rw [hmulPow, heq]
    simpa [hexp] using hmul
  have hcoeff : 0 ≤ a ^ 2 * (sharpRadius d a n)⁻¹ ^ 2 := by positivity
  calc
    (a ^ 2 / f ^ 2) * (sharpRadius d a n)⁻¹ ^ 2 *
        (n : ℝ) ^ (2 * (d - 1) + 1) =
        (a ^ 2 * (sharpRadius d a n)⁻¹ ^ 2) *
          ((n : ℝ) ^ (2 * (d - 1) + 1) / f ^ 2) := by
            field_simp [ne_of_gt hfactorial]
    _ ≤ (a ^ 2 * (sharpRadius d a n)⁻¹ ^ 2) * ((n : ℝ) * S ^ 2) :=
      mul_le_mul_of_nonneg_left hcountPoly hcoeff
    _ = nativeDimension d n := by
      calc
        a ^ 2 * (sharpRadius d a n)⁻¹ ^ 2 * ((n : ℝ) * S ^ 2) =
            a ^ 2 * (sharpRadius d a n)⁻¹ ^ 2 * (n : ℝ) * S ^ 2 := by ring
        _ = nativeDimension d n := hidentity.symm

/-- The reciprocal logarithm of the next actual scale is bounded linearly
in its grade, with the scale prefactor kept explicit. -/
theorem sharpRadius_log_inverse_bound {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n)
    {a : ℝ} (ha : 0 < a) :
    Real.log ((sharpRadius d a (n + 1))⁻¹) ≤
      (1 + |Real.log a|) * n := by
  let S := hyperbolicCount d (n + 1)
  let num := ((n + 1 : ℕ) : ℝ) * S
  let den := (2 : ℝ) ^ (n + 1)
  let z := num / den
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hnum : 1 ≤ num := by
    have hS : 1 ≤ S := by
      dsimp [S, hyperbolicCount]
      exact_mod_cast (show 1 ≤ Nat.choose (n + 1 + d - 1) (d - 1) by
        have hp := Nat.choose_pos (by omega : d - 1 ≤ n + 1 + d - 1)
        omega)
    dsimp [num]
    have hn1 : 1 ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
    nlinarith
  have hnumpos : 0 < num := lt_of_lt_of_le (by norm_num) hnum
  have hden : 0 < den := by dsimp [den]; positivity
  have hz : 0 < z := by dsimp [z]; exact div_pos hnumpos hden
  have hloga : Real.log ((sharpRadius d a (n + 1))⁻¹) =
      -Real.log a - Real.log z / 2 := by
    dsimp [sharpRadius, z, num, den, S]
    rw [Real.log_inv,
      Real.log_mul ha.ne' (ne_of_gt (Real.sqrt_pos.2 hz)), Real.log_sqrt hz.le]
    ring
  have hlognum : 0 ≤ Real.log num := Real.log_nonneg hnum
  have hlogden : Real.log den = (n + 1 : ℝ) * Real.log 2 := by
    dsimp [den]
    rw [Real.log_pow]
    norm_cast
  have hlogz : -Real.log den ≤ Real.log z := by
    rw [show z = num / den by rfl, Real.log_div hnumpos.ne' hden.ne']
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (x := (2 : ℝ)) (by norm_num) (by norm_num)
    linarith
  have habs : 0 ≤ |Real.log a| := abs_nonneg _
  rw [hloga]
  rw [hlogden] at hlogz
  have hbound : -Real.log a - Real.log z / 2 ≤
      |Real.log a| + ((n + 1 : ℝ) * Real.log 2) / 2 := by
    have hneg : -Real.log z / 2 ≤ ((n + 1 : ℝ) * Real.log 2) / 2 := by
      nlinarith [hlogz]
    calc
      -Real.log a - Real.log z / 2 ≤ |Real.log a| - Real.log z / 2 := by
        linarith [neg_le_abs (Real.log a)]
      _ ≤ |Real.log a| + ((n + 1 : ℝ) * Real.log 2) / 2 := by linarith
  have hnlarge : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hfinal : |Real.log a| + ((n + 1 : ℝ) * Real.log 2) / 2 ≤
      (1 + |Real.log a|) * n := by
    nlinarith [habs, hlog2pos.le, hlog2lt.le]
  exact le_trans hbound hfinal

/-- Exact square-scale ratio.  The proof is algebraic and keeps the actual
binomial coefficient used by the Brownian-sheet block. -/
theorem sharpRadius_sq_ratio {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) {a : ℝ} (ha : 0 < a) :
    (sharpRadius d a (n + 1)) ^ 2 /
        (sharpRadius d a n) ^ 2 = (n + d : ℝ) / (2 * n) := by
  have hcount := hyperbolicCount_succ_mul d n (by omega)
  have hcountpos : 0 < hyperbolicCount d n := by
    unfold hyperbolicCount
    exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + d - 1)
  have hcountpos' : 0 < hyperbolicCount d (n + 1) := by
    unfold hyperbolicCount
    exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + 1 + d - 1)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (2 : ℝ) ^ n := by positivity
  unfold sharpRadius
  rw [mul_pow, mul_pow]
  rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by positivity) hcountpos'.le) (by positivity)),
    Real.sq_sqrt (div_nonneg (mul_nonneg hnR.le hcountpos.le) hden.le)]
  have hcountR : hyperbolicCount d n * (n + d) =
      hyperbolicCount d (n + 1) * (n + 1) := by exact_mod_cast hcount
  have hpow : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
  rw [hpow]
  field_simp [ha.ne', ne_of_gt hnR, ne_of_gt hden, ne_of_gt hcountpos,
    ne_of_gt hcountpos']
  simp only [Nat.cast_add, Nat.cast_one] at *
  ring_nf at hcountR ⊢
  linarith [hcountR]

/-- A vanishing decreasing scale admits the half-open adjacent-scale bracket
used for all-radius interpolation.  The first crossing is selected
internally, so endpoint radii are covered by the upper endpoint of an
interval. -/
theorem exists_adjacent_scale_bracket {r : ℕ → ℝ} (N : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hεN : ε ≤ r N)
    (hvanish : ∀ δ : ℝ, 0 < δ → ∃ m, N ≤ m ∧ r m < δ) :
    ∃ n, N ≤ n ∧ r (n + 1) < ε ∧ ε ≤ r n := by
  obtain ⟨M, hMN, hMr⟩ := hvanish ε hε
  have hMgt : N < M := by
    by_contra h
    have hEq : M = N := le_antisymm (by omega) hMN
    rw [hEq] at hMr
    linarith
  let P : ℕ → Prop := fun m => N < m ∧ r m < ε
  have hP : ∃ m, P m := by
    exact ⟨M, hMgt, hMr⟩
  let m := Nat.find hP
  have hm : N < m ∧ r m < ε := Nat.find_spec hP
  let n := m - 1
  have hnN : N ≤ n := by dsimp [n]; omega
  have hnext : n + 1 = m := by dsimp [n]; omega
  have hlow : r (n + 1) < ε := by simpa [hnext] using hm.2
  have hupp : ε ≤ r n := by
    by_contra hnot
    have hlt : r n < ε := lt_of_not_ge hnot
    have hNlt : N < n := by
      by_contra hnlt
      have hEq : n = N := by omega
      have hltN : r N < ε := by simpa [hEq] using hlt
      exact (not_lt_of_ge hεN) hltN
    have hPn : P n := ⟨hNlt, hlt⟩
    have hmin := Nat.find_min' hP hPn
    dsimp [n, m] at hmin
    omega
  exact ⟨n, hnN, hlow, hupp⟩

/-- Positivity of the actual total-grade confinement radius. -/
theorem sharpRadius_pos {d n : ℕ} (hd : 2 ≤ d) {a : ℝ} (ha : 0 < a)
    (hn : 0 < n) : 0 < sharpRadius d a n := by
  unfold sharpRadius
  apply mul_pos ha
  apply Real.sqrt_pos.2
  have hc : 0 < hyperbolicCount d n := by
    unfold hyperbolicCount
    exact_mod_cast Nat.choose_pos (by omega : d - 1 ≤ n + d - 1)
  positivity

/-- The neighboring actual radii decrease and lose at most a factor `sqrt 2`
once `n ≥ 2d`. -/
theorem sharpRadius_adjacent_bounds {d n : ℕ} (hd : 2 ≤ d)
    (hn : 0 < n) (hnd : 2 * d ≤ n) {a : ℝ} (ha : 0 < a) :
    sharpRadius d a n / Real.sqrt 2 ≤ sharpRadius d a (n + 1) ∧
      sharpRadius d a (n + 1) ≤ sharpRadius d a n ∧
      sharpRadius d a (n + 1) ≤ Real.sqrt ((3 : ℝ) / 4) * sharpRadius d a n := by
  let x := sharpRadius d a n
  let y := sharpRadius d a (n + 1)
  have hx : 0 < x := by dsimp [x]; exact sharpRadius_pos hd ha hn
  have hy : 0 < y := by
    dsimp [y]
    exact sharpRadius_pos hd ha (by omega)
  have hr := sharpRadius_sq_ratio hd hn ha
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hndR : 2 * (d : ℝ) ≤ n := by exact_mod_cast hnd
  have hdR : 0 ≤ (d : ℝ) := by positivity
  have hdle : (d : ℝ) ≤ n / 2 := by nlinarith
  have hfracLow : (1 : ℝ) / 2 ≤ (n + d) / (2 * n) := by
    apply (le_div_iff₀ (by positivity)).2
    nlinarith [hdR]
  have hfracUp : (n + d) / (2 * n) ≤ (3 : ℝ) / 4 := by
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hratioLow : (1 : ℝ) / 2 ≤ y ^ 2 / x ^ 2 := by
    simpa [x, y, hr] using hfracLow
  have hratioUp : y ^ 2 / x ^ 2 ≤ (3 : ℝ) / 4 := by
    simpa [x, y, hr] using hfracUp
  have hsqLow : (x / Real.sqrt 2) ^ 2 ≤ y ^ 2 := by
    have hmul := (le_div_iff₀ (sq_pos_of_pos hx)).1 hratioLow
    have hsqrt : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    calc
      (x / Real.sqrt 2) ^ 2 = x ^ 2 / 2 := by rw [div_pow, hsqrt]
      _ ≤ y ^ 2 := by nlinarith [hmul]
  have hsqUp : y ^ 2 ≤ x ^ 2 := by
    have hmul := (div_le_iff₀ (sq_pos_of_pos hx)).1 hratioUp
    nlinarith [hmul, sq_nonneg x]
  have hsqGeom : y ^ 2 ≤ (Real.sqrt ((3 : ℝ) / 4) * x) ^ 2 := by
    have hmul := (div_le_iff₀ (sq_pos_of_pos hx)).1 hratioUp
    have hsqrt : Real.sqrt ((3 : ℝ) / 4) ^ 2 = (3 : ℝ) / 4 :=
      Real.sq_sqrt (by norm_num)
    rw [mul_pow, hsqrt]
    nlinarith [hmul]
  constructor
  · exact (sq_le_sq₀ (by positivity) (by positivity)).1 hsqLow
  constructor
  · exact (sq_le_sq₀ (by positivity) (by positivity)).1 hsqUp
  · exact (sq_le_sq₀ (by positivity) (by positivity)).1 hsqGeom

/-- The actual candidate radii tend to zero, by their exact geometric
contraction after grade `2d`. -/
theorem sharpRadius_vanishes_after {d N : ℕ} (hd : 2 ≤ d) (hN : 2 * d ≤ N)
    {a : ℝ} (ha : 0 < a) :
    ∀ ε : ℝ, 0 < ε → ∃ n, N ≤ n ∧ sharpRadius d a n < ε := by
  let q : ℝ := Real.sqrt ((3 : ℝ) / 4)
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hq2 : q ^ 2 = (3 : ℝ) / 4 := by
    dsimp [q]
    exact Real.sq_sqrt (by norm_num)
  have hq1 : q < 1 := by nlinarith [sq_nonneg (q - 1)]
  have hgeom : ∀ k : ℕ,
      sharpRadius d a (N + k) ≤ q ^ k * sharpRadius d a N := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hn : 0 < N + k := by omega
      have hnd : 2 * d ≤ N + k := by omega
      have hstep := (sharpRadius_adjacent_bounds hd hn hnd ha).2.2
      calc
        sharpRadius d a (N + (k + 1)) = sharpRadius d a ((N + k) + 1) := by
          congr 1
        _ ≤ q * sharpRadius d a (N + k) := by simpa [q] using hstep
        _ ≤ q * (q ^ k * sharpRadius d a N) :=
          mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (k + 1) * sharpRadius d a N := by rw [pow_succ]; ring
  have hpow : Tendsto (fun k : ℕ => q ^ k * sharpRadius d a N) atTop (𝓝 0) := by
    simpa using Tendsto.mul_const (sharpRadius d a N)
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
  intro ε hε
  have hevent : ∀ᶠ k : ℕ in atTop, q ^ k * sharpRadius d a N < ε :=
    hpow.eventually (Iio_mem_nhds hε)
  obtain ⟨K, hK⟩ := eventually_atTop.1 hevent
  refine ⟨N + K, ?_, ?_⟩
  · omega
  · exact lt_of_le_of_lt (hgeom K) (hK K (le_refl K))

end BrownianSharp

namespace BrownianSharp

/-- All-radius sharp-rate extraction for the actual hyperbolic Haar scales.
The only profile-specific input is the discrete estimate at every grade
`n ≥ N`; all scale ratios, dimension growth, reciprocal-log growth, geometric
decay and the adjacent-scale bracket follow from the binomial scale definition.
This deterministic theorem does not assert that a particular small-ball
profile satisfies the discrete estimate. -/
theorem discrete_bound_implies_sharp
    (profile : ℝ → ℝ) {d N : ℕ} (hd : 2 ≤ d) (hN : 2 * d ≤ N)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hscale : ∀ n : ℕ, (N : ℝ) ≤ n →
      b * nativeDimension d n ≤ profile (sharpRadius d a n))
    (hmono : ∀ x y : ℝ, 0 < x → x ≤ y → profile y ≤ profile x)
    {ε : ℝ} (hε : 0 < ε) (hεle1 : ε ≤ 1)
    (hεN : ε ≤ sharpRadius d a N) :
    ((a ^ 2 / (Nat.factorial (d - 1) : ℝ) ^ 2) * b /
      (2 * (1 + |Real.log a|) ^ (2 * (d - 1) + 1))) *
        ε⁻¹ ^ 2 * (Real.log (ε⁻¹)) ^ (2 * (d - 1) + 1) ≤ profile ε := by
  let C : ℝ := 1 + |Real.log a|
  let A : ℝ := a ^ 2 / (Nat.factorial (d - 1) : ℝ) ^ 2
  let k : ℕ := 2 * (d - 1) + 1
  have hNpos : 0 < N := by omega
  have hC : 0 < C := by dsimp [C]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hvanish : ∀ δ : ℝ, 0 < δ →
      ∃ n, N ≤ n ∧ sharpRadius d a n < δ :=
    sharpRadius_vanishes_after hd hN ha
  obtain ⟨n, hnN, hlow, hupp⟩ :=
    exists_adjacent_scale_bracket N hε hεN hvanish
  have hradius : ∀ m : ℕ, (N : ℝ) ≤ m → 0 < sharpRadius d a m := by
    intro m hm
    have hmNat : N ≤ m := by exact_mod_cast hm
    apply sharpRadius_pos hd ha
    exact lt_of_lt_of_le hNpos hmNat
  have hadjacent : ∀ m : ℕ, (N : ℝ) ≤ m →
      sharpRadius d a m / Real.sqrt 2 ≤ sharpRadius d a (m + 1) := by
    intro m hm
    have hmNat : N ≤ m := by exact_mod_cast hm
    have hmn : 2 * d ≤ m := le_trans hN hmNat
    exact (sharpRadius_adjacent_bounds hd (by omega) hmn ha).1
  have hlog : ∀ m : ℕ, (N : ℝ) ≤ m →
      Real.log ((sharpRadius d a (m + 1))⁻¹) ≤ C * m := by
    intro m hm
    have hmNat : N ≤ m := by exact_mod_cast hm
    have hmn : 0 < m := lt_of_lt_of_le (by omega) hmNat
    simpa [C] using sharpRadius_log_inverse_bound hd hmn ha
  have hdimension : ∀ m : ℕ, (N : ℝ) ≤ m →
      A * (sharpRadius d a m)⁻¹ ^ 2 * (m : ℝ) ^ k ≤ nativeDimension d m := by
    intro m hm
    have hmNat : N ≤ m := by exact_mod_cast hm
    have hmn : 0 < m := lt_of_lt_of_le (by omega) hmNat
    simpa [A, k] using nativeDimension_scale_lower hd hmn ha
  have hresult := interpolate_discrete_scales profile
    (fun m => sharpRadius d a m) (fun m => nativeDimension d m)
    k N A b C hA hb hC hradius hadjacent hlog hdimension hscale hmono hNpos
    hε hεle1 ⟨n, by exact_mod_cast hnN, hlow, hupp⟩
  simpa [A, C, k, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hresult

end BrownianSharp
