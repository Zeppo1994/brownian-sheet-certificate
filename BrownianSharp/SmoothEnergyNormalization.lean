import BrownianSharp.SmoothScaledClassEvents

/-! One fixed coefficient normalization absorbs all moment constants while
preserving the exact native-scale powers. -/
noncomputable section
open scoped ENNReal
namespace BrownianSharp

theorem exists_smooth_energy_normalizer (p C : ℝ) (hp : 0 < p) (hC : 0 < C) :
    ∃ a : ℝ, 0 < a ∧ ∀ L : ℝ, 0 < L →
      ENNReal.ofReal ((a/L)^p) * (2*ENNReal.ofReal (C*L^p)) ≤ 1 := by
  let B : ℝ := 1+2*C
  have hB : 0 < B := by dsimp [B]; linarith
  let a : ℝ := B^(-1/p)
  have ha : 0 < a := by dsimp [a]; positivity
  have hap : a^p = B⁻¹ := by
    dsimp [a]
    rw [← Real.rpow_mul hB.le]
    rw [show (-1/p)*p = (-1:ℝ) by field_simp]
    exact Real.rpow_neg_one B
  refine ⟨a,ha,?_⟩
  intro L hL
  have hreal : (a/L)^p*(2*(C*L^p)) ≤ 1 := by
    rw [Real.div_rpow ha.le hL.le]
    have hLp : L^p ≠ 0 := (Real.rpow_pos_of_pos hL p).ne'
    have heq : (a^p/L^p)*(2*(C*L^p)) = 2*C*a^p := by field_simp
    rw [heq, hap]
    have hfrac : 2*C/B ≤ 1 := (div_le_one hB).2 (by dsimp [B]; linarith)
    simpa [div_eq_mul_inv] using hfrac
  have h := ENNReal.ofReal_le_ofReal hreal
  have heq : ENNReal.ofReal ((a/L)^p*(2*(C*L^p))) =
      ENNReal.ofReal ((a/L)^p)*(2*ENNReal.ofReal (C*L^p)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [heq] at h
  simpa using h

theorem shapeCutoff_le_half {d n : ℕ} (hd : 1 ≤ d) :
    (1/2:ℝ≥0∞)^Nat.choose (n+d-1) (d-1) ≤ (1/2:ℝ≥0∞) := by
  have hS : 1 ≤ Nat.choose (n+d-1) (d-1) := Nat.choose_pos (by omega)
  have hhalf : (1/2:ℝ≥0∞) ≤ 1 := by
    exact ENNReal.div_le_of_le_mul (by norm_num)
  have hpow : (1/2:ℝ≥0∞)^(Nat.choose (n+d-1) (d-1)-1) ≤ 1 :=
    pow_le_one' hhalf _
  have heq : Nat.choose (n+d-1) (d-1) =
      (Nat.choose (n+d-1) (d-1)-1)+1 := by omega
  rw [heq, pow_succ]
  simpa using mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ (1/2:ℝ≥0∞))

end BrownianSharp
