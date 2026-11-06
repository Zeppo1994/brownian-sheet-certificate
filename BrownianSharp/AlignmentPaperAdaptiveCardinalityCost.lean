import BrownianSharp.AlignmentPaperJointStagePieces

/-! Logarithmic costs of the actual adaptive support and volumetric counts.
The zero-support initial stage is included explicitly. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperAdaptiveCardinalityCost
open BrownianSharp.AlignmentPaperJointAdaptiveEntropy
open BrownianSharp.AlignmentPaperJointSupportCount
open BrownianSharp.AlignmentPaperJointStagePieces

def supportCost (D r : ℕ) : ℝ :=
  if r = 0 then 0 else (r : ℝ) * (1 + Real.log ((D : ℝ) / (r : ℝ)))

theorem supportLabel_card_zero (D : ℕ) :
    Fintype.card (SupportLabel (D := D) (r := 0)) = 1 := by
  classical
  letI : Unique (SupportLabel (D := D) (r := 0)) :=
    { default := ⟨∅, by simp⟩
      uniq := fun A => Subtype.ext (Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero A.property)) }
  exact Fintype.card_unique

theorem supportLabel_card_le_exp_cost {D r : ℕ} (hrD : r ≤ D) :
    (Fintype.card (SupportLabel (D := D) (r := r)) : ℝ) ≤
      Real.exp (supportCost D r) := by
  by_cases hr : r = 0
  · subst r
    simp [supportLabel_card_zero, supportCost]
  · have hrpos : 0 < (r : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hr)
    have hDpos : 0 < (D : ℝ) := lt_of_lt_of_le hrpos (by exact_mod_cast hrD)
    have hratio : 0 < (D : ℝ) / (r : ℝ) := div_pos hDpos hrpos
    have heq : Real.exp (supportCost D r) =
        Real.exp (r : ℝ) * ((D : ℝ) / (r : ℝ)) ^ r := by
      unfold supportCost
      rw [if_neg hr, mul_add, mul_one, Real.exp_add, Real.exp_nat_mul,
        Real.exp_log hratio]
    rw [heq]
    exact supportLabel_card_le_exp (Nat.pos_of_ne_zero hr) hrD

theorem supportPairVolumeCount_le_exp {D r₁ r₂ : ℕ} {R ε : ℝ}
    (h₁ : r₁ ≤ D) (h₂ : r₂ ≤ D) (hR : 0 ≤ R) (hε : 0 < ε) :
    ((Fintype.card (SupportLabel (D := D) (r := r₁) ×
      SupportLabel (D := D) (r := r₂)) *
      Nat.ceil ((1 + 2*R/ε) ^ (r₁+r₁+r₂+r₂)) : ℕ) : ℝ) ≤
      2 * Real.exp (supportCost D r₁ + supportCost D r₂ +
        ((r₁+r₁+r₂+r₂ : ℕ) : ℝ) * Real.log (1 + 2*R/ε)) := by
  let b := 1 + 2*R/ε
  let q := r₁+r₁+r₂+r₂
  have hb : 1 ≤ b := by
    have hdv : 0 ≤ 2*R/ε := div_nonneg (by positivity) hε.le
    dsimp [b]
    linarith
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hpow : 1 ≤ b^q := one_le_pow₀ hb
  have hceil : (Nat.ceil (b^q) : ℝ) ≤ 2 * b^q := by
    have ht := Nat.ceil_lt_add_one (le_trans zero_le_one hpow)
    linarith
  have hexp : b^q = Real.exp ((q : ℝ)*Real.log b) := by
    rw [Real.exp_nat_mul, Real.exp_log hbpos]
  have hc₁ := supportLabel_card_le_exp_cost h₁
  have hc₂ := supportLabel_card_le_exp_cost h₂
  rw [Nat.cast_mul, Fintype.card_prod, Nat.cast_mul]
  have hlabels :
      (Fintype.card (SupportLabel (D := D) (r := r₁)) : ℝ) *
      (Fintype.card (SupportLabel (D := D) (r := r₂)) : ℝ) ≤
      Real.exp (supportCost D r₁) * Real.exp (supportCost D r₂) :=
    mul_le_mul hc₁ hc₂ (Nat.cast_nonneg _) (Real.exp_nonneg _)
  calc
    _ ≤ (Real.exp (supportCost D r₁) * Real.exp (supportCost D r₂)) * (2*b^q) :=
      mul_le_mul hlabels hceil (Nat.cast_nonneg _) (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ = _ := by rw [hexp, Real.exp_add, Real.exp_add]; ring

theorem nat_le_two_pow_ceil_of_le_exp {m : ℕ} {A : ℝ}
    (h : (m : ℝ) ≤ Real.exp A) :
    m ≤ 2 ^ Nat.ceil (A / Real.log 2) := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc : A ≤ (Nat.ceil (A / Real.log 2) : ℝ) * Real.log 2 :=
    (div_le_iff₀ hlog).mp (Nat.le_ceil _)
  have he : Real.exp A ≤ (2 : ℝ) ^ Nat.ceil (A / Real.log 2) := by
    calc
      _ ≤ Real.exp ((Nat.ceil (A / Real.log 2) : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hc
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ)<2)]
  exact_mod_cast h.trans he
end BrownianSharp.AlignmentPaperAdaptiveCardinalityCost
