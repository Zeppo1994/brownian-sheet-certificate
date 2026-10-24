import BrownianSharp.PeriodicRadiusRate

/-! Multiplying an entropy index by a fixed positive integer preserves every
power-log rate, including negative logarithmic powers. -/
noncomputable section
namespace BrownianSharp

theorem exists_log_multiple_power_bound (s : ℕ) (hs : 1 ≤ s) (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
      (Real.log (k:ℝ))^α ≤ C*(Real.log ((s*k:ℕ):ℝ))^α := by
  have hsR : (1:ℝ) ≤ (s:ℝ) := by exact_mod_cast hs
  have hspos : (0:ℝ) < (s:ℝ) := by linarith
  have hlogs : 0 ≤ Real.log (s:ℝ) := Real.log_nonneg hsR
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hα : 0 ≤ α
  · refine ⟨1, by norm_num, ?_⟩
    intro k hk
    have hkR : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hle : Real.log (k:ℝ) ≤ Real.log ((s*k:ℕ):ℝ) := by
      apply Real.log_le_log (by linarith)
      push_cast
      nlinarith
    simpa using Real.rpow_le_rpow (Real.log_nonneg (by linarith)) hle hα
  · let L : ℝ := 1 + Real.log (s:ℝ) / Real.log 2
    have hL : 0 < L := by dsimp [L]; positivity
    refine ⟨L^(-α), by positivity, ?_⟩
    intro k hk
    have hkR : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
    have hkpos : (0:ℝ) < (k:ℝ) := by linarith
    have hlk : 0 < Real.log (k:ℝ) := Real.log_pos (by linarith)
    have hlsk : 0 < Real.log ((s*k:ℕ):ℝ) := by
      apply Real.log_pos
      push_cast
      nlinarith
    have hlogk : Real.log 2 ≤ Real.log (k:ℝ) :=
      Real.log_le_log (by norm_num) hkR
    have hlogmul : Real.log ((s*k:ℕ):ℝ) = Real.log (s:ℝ) + Real.log (k:ℝ) := by
      rw [Nat.cast_mul, Real.log_mul hspos.ne' hkpos.ne']
    have hupper : Real.log ((s*k:ℕ):ℝ) ≤ L*Real.log (k:ℝ) := by
      rw [hlogmul]
      have hprod := mul_le_mul_of_nonneg_left hlogk (div_nonneg hlogs hlog2.le)
      have hcancel : Real.log (s:ℝ)/Real.log 2 * Real.log 2 = Real.log (s:ℝ) :=
        div_mul_cancel₀ _ hlog2.ne'
      dsimp [L]
      nlinarith
    have hdivide : Real.log ((s*k:ℕ):ℝ)/L ≤ Real.log (k:ℝ) :=
      (div_le_iff₀ hL).2 (by nlinarith)
    calc
      _ ≤ (Real.log ((s*k:ℕ):ℝ)/L)^α :=
        Real.rpow_le_rpow_of_nonpos (div_pos hlsk hL) hdivide (le_of_not_ge hα)
      _ = L^(-α)*(Real.log ((s*k:ℕ):ℝ))^α := by
        rw [Real.div_rpow hlsk.le hL.le, Real.rpow_neg hL.le]
        ring

theorem exists_index_multiple_rate_lower (s : ℕ) (hs : 1 ≤ s) (r α : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k →
      c*(k:ℝ)^(-r)*(Real.log (k:ℝ))^α ≤
        ((s*k:ℕ):ℝ)^(-r)*(Real.log ((s*k:ℕ):ℝ))^α := by
  obtain ⟨C,hC,hlog⟩ := exists_log_multiple_power_bound s hs α
  have hspos : (0:ℝ)<(s:ℝ) := by exact_mod_cast (by omega : 0<s)
  refine ⟨(s:ℝ)^(-r)/C, by positivity, ?_⟩
  intro k hk
  have hkpos : (0:ℝ)<(k:ℝ) := by exact_mod_cast (by omega : 0<k)
  have hratio : (Real.log (k:ℝ))^α/C ≤ (Real.log ((s*k:ℕ):ℝ))^α :=
    (div_le_iff₀ hC).2 (by simpa [mul_comm] using hlog k hk)
  rw [Nat.cast_mul, Real.mul_rpow hspos.le hkpos.le]
  calc
    _ = (s:ℝ)^(-r)*(k:ℝ)^(-r)*((Real.log (k:ℝ))^α/C) := by ring
    _ ≤ _ := by
      simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hratio
        (by positivity : 0 ≤ (s:ℝ)^(-r)*(k:ℝ)^(-r))

end BrownianSharp
