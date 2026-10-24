import BrownianSharp.EventualRates
import BrownianSharp.TailBudget

/-! All numerical large-grade conditions in the two-step root repair. -/
open Filter
open scoped Topology
namespace BrownianSharp

theorem nativeDimension_tendsto_atTop {d : ℕ} (hd : 0 < d) :
    Tendsto (nativeDimension d) atTop atTop :=
  tendsto_atTop_mono (fun n => nativeDimension_ge_dyadic d n hd)
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2))

theorem eventually_evenPower_square_le_sqrt_dimension
    {d : ℕ} (hd : 0 < d) {κ : ℝ} (hκ : 0 < κ) (hκone : κ ≤ 1) :
    ∀ᶠ n : ℕ in atTop,
      (gradeEvenPower κ n : ℝ) ^ 2 ≤ Real.sqrt (nativeDimension d n) := by
  obtain ⟨N, hN⟩ := eventually_gradeEvenPower_bounds hκ
  have hp : ∀ᶠ n : ℕ in atTop,
      (gradeEvenPower κ n : ℝ) ≤ κ * (n + 1) :=
    eventually_atTop.mpr ⟨N, fun n hn => (hN n hn).1⟩
  have hpoly : ∀ᶠ n : ℕ in atTop, ((n : ℝ) + 1) ^ 4 / (2 : ℝ) ^ n < 1 :=
    (grade_power_over_dyadic_tendsto_zero 4).eventually
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hp, hpoly] with n hpn hpolyn
  have hpk : (gradeEvenPower κ n : ℝ) ≤ (n : ℝ) + 1 := by
    have hmul := mul_le_mul_of_nonneg_right hκone (by positivity : (0 : ℝ) ≤ n + 1)
    linarith
  have hfour : (gradeEvenPower κ n : ℝ) ^ 4 ≤ ((n : ℝ) + 1) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hpk 4
  have hpolyn' : ((n : ℝ) + 1) ^ 4 < (2 : ℝ) ^ n :=
    (div_lt_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ n)).mp hpolyn
  have hdim := nativeDimension_ge_dyadic d n hd
  have hD : 0 ≤ nativeDimension d n := (by positivity : (0 : ℝ) ≤ 2 ^ n).trans hdim
  have hs := Real.sq_sqrt hD
  have hnonneg := Real.sqrt_nonneg (nativeDimension d n)
  nlinarith

/-- Every informal 'for large n' budget used by the root repair is a proved
eventual consequence of p~n and the actual exponential layer dimension. -/
theorem eventually_root_repair_budgets
    {d : ℕ} (hd : 0 < d) {κ C c : ℝ}
    (hκ : 0 < κ) (hκone : κ ≤ 1) (hC : 0 < C) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      2 ≤ gradeEvenPower κ n ∧
      C * (gradeEvenPower κ n : ℝ) ^ 2 / nativeDimension d n ≤ 1 / 16 ∧
      Real.exp (-c * nativeDimension d n / (C * (gradeEvenPower κ n : ℝ) ^ 2)) ≤
        1 / nativeDimension d n ∧
      (4 * C + 1) / nativeDimension d n ≤ 1 / 4 ∧
      64 * (4 * C + 1) ≤ nativeDimension d n := by
  obtain ⟨Np, hNp⟩ := eventually_gradeEvenPower_bounds hκ
  obtain ⟨Nv, hNv⟩ := eventually_evenPower_variance_small hd hκ hκone hC
  have hp : ∀ᶠ n : ℕ in atTop, 2 ≤ gradeEvenPower κ n :=
    eventually_atTop.mpr ⟨Np, fun n hn => (hNp n hn).2.2⟩
  have hv : ∀ᶠ n : ℕ in atTop,
      C * (gradeEvenPower κ n : ℝ) ^ 2 / nativeDimension d n ≤ 1 / 16 :=
    eventually_atTop.mpr ⟨Nv, hNv⟩
  have hDlim := nativeDimension_tendsto_atTop hd
  have hrootlim := Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hDlim)
  have hlarge : ∀ᶠ n : ℕ in atTop,
      4 * C / c ≤ Real.sqrt (Real.sqrt (nativeDimension d n)) :=
    hrootlim.eventually_ge_atTop _
  have hDlarge : ∀ᶠ n : ℕ in atTop,
      64 * (4 * C + 1) ≤ nativeDimension d n := hDlim.eventually_ge_atTop _
  apply eventually_atTop.mp
  filter_upwards [hp, hv, eventually_evenPower_square_le_sqrt_dimension hd hκ hκone,
    hlarge, hDlarge] with n hpn hvn hsq hlarge_n hDlarge_n
  have hD : 0 < nativeDimension d n :=
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ n).trans_le (nativeDimension_ge_dyadic d n hd)
  have hpR : (0 : ℝ) < (gradeEvenPower κ n : ℝ) := by exact_mod_cast (by omega : 0 < gradeEvenPower κ n)
  have hlarge' : 4 * C ≤ c * Real.sqrt (Real.sqrt (nativeDimension d n)) := by
    have h := (div_le_iff₀ hc).mp hlarge_n
    simpa [mul_comm] using h
  refine ⟨hpn, hvn, exponential_remainder_le_inv_dimension hD hpR hc hC hsq hlarge', ?_, hDlarge_n⟩
  apply (div_le_iff₀ hD).2
  nlinarith

end BrownianSharp
