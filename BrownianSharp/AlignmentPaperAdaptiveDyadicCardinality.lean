import BrownianSharp.AlignmentPaperAdaptiveDyadicRadius

noncomputable section
namespace BrownianSharp.AlignmentPaperAdaptiveDyadicCardinality
open BrownianSharp.AlignmentPaperJointAdaptiveEntropy
open BrownianSharp.AlignmentPaperJointStagePieces
open BrownianSharp.AlignmentPaperAdaptiveCardinalityCost

theorem supportLabel_card_mono {D a b : ℕ} (h : a ≤ b) :
    Fintype.card (SupportLabel (D := D) (r := a)) ≤
      Fintype.card (SupportLabel (D := D) (r := b)) := by
  let f : SupportLabel (D := D) (r := a) → SupportLabel (D := D) (r := b) :=
    fun x => ⟨x.val, x.property.trans h⟩
  apply Fintype.card_le_of_injective f
  intro x y he
  apply Subtype.ext
  exact congrArg (fun z : SupportLabel (D := D) (r := b) => z.val) he

theorem supportPairVolumeCount_mono_right {D r a b : ℕ} {R ε : ℝ}
    (hab : a ≤ b) (hR : 0 ≤ R) (hε : 0 < ε) :
    Fintype.card (SupportLabel (D := D) (r := r) × SupportLabel (D := D) (r := a)) *
        Nat.ceil ((1+2*R/ε)^(r+r+a+a)) ≤
      Fintype.card (SupportLabel (D := D) (r := r) × SupportLabel (D := D) (r := b)) *
        Nat.ceil ((1+2*R/ε)^(r+r+b+b)) := by
  have hbase : 1 ≤ 1+2*R/ε := by
    have hdiv : 0 ≤ 2*R/ε := div_nonneg (by positivity) hε.le
    linarith
  rw [Fintype.card_prod, Fintype.card_prod]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (supportLabel_card_mono hab))
    (Nat.ceil_mono (pow_le_pow_right₀ hbase (by omega)))

theorem pairCoverCount_le_exp_of_small_right {d n r₁ r₂ : ℕ} {R ε : ℝ}
    (h₂ : r₂ ≤ r₁)
    (h₁ : r₁ ≤ AlignmentPaperLpJointDvp.JointSampleDimension d n)
    (hR : 0 ≤ R) (hε : 0 < ε) :
    (pairCoverCount d n r₁ r₂ R ε : ℝ) ≤
      2 * Real.exp (2 * supportCost (AlignmentPaperLpJointDvp.JointSampleDimension d n) r₁ +
        (4 * (r₁ : ℝ)) * Real.log (1+2*R/ε)) := by
  have hcount := supportPairVolumeCount_mono_right
    (D := AlignmentPaperLpJointDvp.JointSampleDimension d n) (r := r₁) h₂ hR hε
  have he := supportPairVolumeCount_le_exp h₁ h₁ hR hε
  have hm : (pairCoverCount d n r₁ r₂ R ε : ℝ) ≤
      (pairCoverCount d n r₁ r₁ R ε : ℝ) := by exact_mod_cast hcount
  apply hm.trans
  have hq : ((r₁+r₁+r₁+r₁ : ℕ) : ℝ) = 4*(r₁:ℝ) := by
    push_cast
    ring
  rw [hq] at he
  simpa only [pairCoverCount, ← two_mul] using he
theorem pairCoverCount_le_binary_cost {d n r₁ r₂ gap : ℕ} {R ε : ℝ}
    (h₂ : r₂ ≤ r₁)
    (h₁ : r₁ ≤ AlignmentPaperLpJointDvp.JointSampleDimension d n)
    (hR : 0 ≤ R) (hε : 0 < ε)
    (hratio : R/ε ≤ 3*(2:ℝ)^(2*gap)) :
    pairCoverCount d n r₁ r₂ R ε ≤
      2 ^ Nat.ceil ((Real.log 2 +
        2 * supportCost (AlignmentPaperLpJointDvp.JointSampleDimension d n) r₁ +
        4*(r₁:ℝ)*(Real.log 7 + (2*gap:ℕ)*Real.log 2)) / Real.log 2) := by
  have hbpos : 0 < 1+2*R/ε := by
    have hdiv : 0 ≤ 2*R/ε := div_nonneg (by positivity) hε.le
    linarith
  have hbase : 1+2*R/ε ≤ 7*(2:ℝ)^(2*gap) := by
    have hp : 1 ≤ (2:ℝ)^(2*gap) := one_le_pow₀ (by norm_num)
    have heq : 2*R/ε = 2*(R/ε) := by ring
    rw [heq]
    linarith
  have hlog : Real.log (1+2*R/ε) ≤
      Real.log 7 + (2*gap:ℕ)*Real.log 2 := by
    have hh := Real.log_le_log hbpos hbase
    rwa [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hh
  apply nat_le_two_pow_ceil_of_le_exp
  calc
    _ ≤ 2 * Real.exp (2 * supportCost
        (AlignmentPaperLpJointDvp.JointSampleDimension d n) r₁ +
        4*(r₁:ℝ)*Real.log (1+2*R/ε)) :=
      pairCoverCount_le_exp_of_small_right h₂ h₁ hR hε
    _ ≤ 2 * Real.exp (2 * supportCost
        (AlignmentPaperLpJointDvp.JointSampleDimension d n) r₁ +
        4*(r₁:ℝ)*(Real.log 7 + (2*gap:ℕ)*Real.log 2)) := by
      gcongr
    _ = _ := by
      simp only [Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2)]
      ring

end BrownianSharp.AlignmentPaperAdaptiveDyadicCardinality
