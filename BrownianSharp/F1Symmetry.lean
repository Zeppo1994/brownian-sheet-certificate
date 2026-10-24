import BrownianSharp.F1Stop

/-!
# Two source signs, one F1 stop

Source: unrestricted quarter-gain proof, Section 6.
Negating the source negates every source level and Xi/Gamma matrix. Every
operator/scalar test is unchanged, so the first refusal is shared and the
stopped biases have opposite signs.
-/

open scoped BigOperators

namespace HaarQuarter

theorem criticalFieldLegal_neg {D N : ℕ} (Ω : CoefficientField D N)
    (hΩ : CriticalFieldLegal Ω) : CriticalFieldLegal (-Ω) := by
  intro l v hc x y hxy
  change -Ω l v x = -Ω l v y
  rw [hΩ l v hc x y hxy]

theorem sourceLevel_neg {D N : ℕ} (Ω : CoefficientField D N)
    (l : Fin N) (x : SignCube D N) : sourceLevel (-Ω) l x = -sourceLevel Ω l x := by
  classical
  unfold sourceLevel
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : IsCriticalProfile l v <;> simp [hc]

theorem sourceEntry_neg {D N : ℕ} (Ω : CoefficientField D N)
    (j : Fin D) (mask : BoundedProfile D N → Prop) (u l : Fin N) (x : SignCube D N) :
    sourceEntry (-Ω) j mask u l x = -sourceEntry Ω j mask u l x := by
  classical
  unfold sourceEntry
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : IsCriticalProfile l v ∧ v j = u ∧ mask v <;> simp [hc]

theorem sourcePrefixMatrix_neg {D N : ℕ} (Ω : CoefficientField D N)
    (j : Fin D) (mask : BoundedProfile D N → Prop) (k : ℕ) (x : SignCube D N) :
    sourcePrefixMatrix (-Ω) j mask k x = -sourcePrefixMatrix Ω j mask k x := by
  classical
  ext u l
  by_cases hl : l.val < k <;> simp [sourcePrefixMatrix, hl, sourceEntry_neg]

theorem xiMatrix_neg {D N : ℕ} (Ω : CoefficientField D N)
    (j : Fin D) (k : ℕ) (x : SignCube D N) :
    xiMatrix (-Ω) j k x = -xiMatrix Ω j k x := sourcePrefixMatrix_neg Ω j _ k x

theorem gammaMatrix_neg {D N : ℕ} (Ω : CoefficientField D N)
    (J : Finset (Fin D)) (j : Fin D) (m : BoundedProfile D N) (k : ℕ) (x : SignCube D N) :
    gammaMatrix (-Ω) J j m k x = -gammaMatrix Ω J j m k x := sourcePrefixMatrix_neg Ω j _ k x

theorem matrixOperator_neg {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    matrixOperator (-M) = -matrixOperator M := by
  unfold matrixOperator
  rw [map_neg, map_neg]

theorem F1Test_neg {D N : ℕ} (Ω : CoefficientField D N)
    (ρ B a₀ : ℝ) (l : Fin N) (x : SignCube D N) :
    F1Test (-Ω) ρ B a₀ l x ↔ F1Test Ω ρ B a₀ l x := by
  simp only [F1Test, xiMatrix_neg, gammaMatrix_neg, matrixOperator_neg, norm_neg,
    sourceLevel_neg, mul_neg, abs_neg]

theorem f1Tau_neg {D N : ℕ} (Ω : CoefficientField D N)
    (ρ B a₀ : ℝ) (x : SignCube D N) : f1Tau (-Ω) ρ B a₀ x = f1Tau Ω ρ B a₀ x := by
  have ht : F1Test (-Ω) ρ B a₀ = F1Test Ω ρ B a₀ := by
    funext l x
    exact propext (F1Test_neg Ω ρ B a₀ l x)
  unfold f1Tau
  rw [ht]

theorem f1Bias_neg {D N : ℕ} (Ω : CoefficientField D N)
    (ρ B a₀ : ℝ) (l : Fin N) (x : SignCube D N) :
    f1Bias (-Ω) ρ B a₀ l x = -f1Bias Ω ρ B a₀ l x := by
  classical
  have hplus : f1Bias Ω ρ B a₀ l x =
      if l.val < f1Tau Ω ρ B a₀ x then ρ * sourceLevel Ω l x else 0 :=
    stoppedBias_before_refusal ρ (sourceLevel Ω) (F1Test Ω ρ B a₀) l x
  have hminus : f1Bias (-Ω) ρ B a₀ l x =
      if l.val < f1Tau (-Ω) ρ B a₀ x then ρ * sourceLevel (-Ω) l x else 0 :=
    stoppedBias_before_refusal ρ (sourceLevel (-Ω)) (F1Test (-Ω) ρ B a₀) l x
  rw [hplus, hminus, f1Tau_neg, sourceLevel_neg]
  split_ifs <;> simp

end HaarQuarter
