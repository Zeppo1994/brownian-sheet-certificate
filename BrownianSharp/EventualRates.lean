import BrownianSharp.Interpolation
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-!
Even powers proportional to the grade and the exponential dimension budgets.
These are purely numerical, dimension-dependent eventual estimates. They do
not assume regularity of a small-ball profile.
-/

open Filter
open scoped Topology

namespace BrownianSharp

noncomputable def gradeEvenPower (κ : ℝ) (n : ℕ) : ℕ :=
  2 * Nat.floor (κ * (n + 1) / 2)

theorem gradeEvenPower_even (κ : ℝ) (n : ℕ) : Even (gradeEvenPower κ n) := by
  refine ⟨Nat.floor (κ * (n + 1) / 2), ?_⟩
  simp [gradeEvenPower, two_mul]

theorem gradeEvenPower_bounds {κ : ℝ} (hκ : 0 < κ) (n : ℕ)
    (hlarge : 4 ≤ κ * (n + 1)) :
    (gradeEvenPower κ n : ℝ) ≤ κ * (n + 1) ∧
      κ * (n + 1) / 2 ≤ (gradeEvenPower κ n : ℝ) ∧
      2 ≤ gradeEvenPower κ n := by
  have hf := Nat.floor_le (show 0 ≤ κ * (n + 1) / 2 by positivity)
  have hfl := Nat.lt_floor_add_one (κ * (n + 1) / 2)
  have hcast : (gradeEvenPower κ n : ℝ) =
      2 * (Nat.floor (κ * (n + 1) / 2) : ℝ) := by
    simp [gradeEvenPower]
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [hf]
  · nlinarith [hfl]
  · have hp : (2 : ℝ) ≤ (gradeEvenPower κ n : ℝ) := by nlinarith [hfl]
    exact_mod_cast hp

theorem eventually_gradeEvenPower_bounds {κ : ℝ} (hκ : 0 < κ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (gradeEvenPower κ n : ℝ) ≤ κ * (n + 1) ∧
        κ * (n + 1) / 2 ≤ (gradeEvenPower κ n : ℝ) ∧
        2 ≤ gradeEvenPower κ n := by
  refine ⟨Nat.ceil (4 / κ), ?_⟩
  intro n hn
  have hnreal : (Nat.ceil (4 / κ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hceil := Nat.le_ceil (4 / κ)
  have hlarge : 4 ≤ κ * (n + 1) := by
    have hdiv : 4 / κ ≤ (n : ℝ) := hceil.trans hnreal
    have h := (div_le_iff₀ hκ).mp hdiv
    nlinarith
  exact gradeEvenPower_bounds hκ n hlarge

/-- The elementary exponential-over-polynomial decay controlling the
high-power variance budget. -/
theorem grade_square_over_dyadic_tendsto_zero :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt 2 (by norm_num : (1 : ℝ) < 2)).comp
    (tendsto_add_atTop_nat 1)
  have htwo := h.const_mul (2 : ℝ)
  convert htwo using 1
  · funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, pow_add, pow_one]
    field_simp
  · norm_num

/-- Every fixed polynomial is negligible against the dyadic grade factor. -/
theorem grade_power_over_dyadic_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ k / (2 : ℝ) ^ n) atTop (𝓝 0) := by
  have h := (tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).comp
    (tendsto_add_atTop_nat 1)
  convert h.const_mul (2 : ℝ) using 1
  · funext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, pow_add, pow_one]
    field_simp
  · norm_num

/-- The native layer has at least the dyadic number of coordinates. -/
theorem nativeDimension_ge_dyadic (d n : ℕ) (hd : 0 < d) :
    (2 : ℝ) ^ n ≤ nativeDimension d n := by
  have hchoose : 1 ≤ Nat.choose (n + d - 1) (d - 1) :=
    Nat.succ_le_of_lt (Nat.choose_pos (by omega))
  have hcount : (1 : ℝ) ≤ hyperbolicCount d n := by
    dsimp [hyperbolicCount]
    exact_mod_cast hchoose
  dsimp [nativeDimension]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) n]

/-- The first variance budget holds eventually for the actual even powers
and actual hyperbolic layer dimension. -/
theorem eventually_evenPower_variance_small
    {d : ℕ} (hd : 0 < d) {κ C : ℝ} (hκ : 0 < κ) (hκone : κ ≤ 1) (hC : 0 < C) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      C * (gradeEvenPower κ n : ℝ) ^ 2 / nativeDimension d n ≤ 1 / 16 := by
  obtain ⟨Npower, hpower⟩ := eventually_gradeEvenPower_bounds hκ
  have hlim := (grade_power_over_dyadic_tendsto_zero 2).const_mul C
  have hevent : ∀ᶠ n : ℕ in atTop,
      C * (((n : ℝ) + 1) ^ 2 / (2 : ℝ) ^ n) < 1 / 16 := by
    exact hlim.eventually (show ∀ᶠ x : ℝ in 𝓝 (C * 0), x < (1 / 16 : ℝ) from
      gt_mem_nhds (by norm_num))
  obtain ⟨Nsmall, hsmall⟩ := eventually_atTop.mp hevent
  refine ⟨max Npower Nsmall, ?_⟩
  intro n hn
  have hpn := (hpower n (le_trans (le_max_left _ _) hn)).1
  have hpbound : (gradeEvenPower κ n : ℝ) ≤ (n : ℝ) + 1 := by
    have hκmul := mul_le_mul_of_nonneg_right hκone (show (0 : ℝ) ≤ n + 1 by positivity)
    linarith
  have hsq : (gradeEvenPower κ n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hpbound 2
  have hdim := nativeDimension_ge_dyadic d n hd
  have htwo : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hD : 0 < nativeDimension d n := htwo.trans_le hdim
  calc
    C * (gradeEvenPower κ n : ℝ) ^ 2 / nativeDimension d n ≤
        C * ((n : ℝ) + 1) ^ 2 / nativeDimension d n :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC.le) hD.le
    _ ≤ C * ((n : ℝ) + 1) ^ 2 / (2 : ℝ) ^ n :=
      div_le_div_of_nonneg_left (by positivity) htwo hdim
    _ = C * (((n : ℝ) + 1) ^ 2 / (2 : ℝ) ^ n) := by ring
    _ ≤ 1 / 16 := (hsmall n (le_trans (le_max_right _ _) hn)).le

end BrownianSharp
