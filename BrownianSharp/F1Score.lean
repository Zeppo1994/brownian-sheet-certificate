import BrownianSharp.F1Symmetry
import BrownianSharp.ScoreReduction

/-!
# Actual score identities under the two F1 laws

Source: unrestricted quarter-gain proof, Section 6.
The stopped law, opposite source biases and shared refusal time are proved
dependencies. Only row predictability is required of the query. Quantitative
off-diagonal, refusal and aligned-mass bounds remain analytic obligations.
-/

open scoped BigOperators

namespace HaarQuarter

noncomputable def rowPolynomial {D N : ℕ} (c₀ : ℝ)
    (q : Fin N → SignCube D N → ℝ) (x : SignCube D N) : ℝ :=
  c₀ + ∑ l, firstDigit x l * q l x

noncomputable def rawPairScore {D N : ℕ} (ρ : ℝ) (Ω : CoefficientField D N)
    (q : Fin N → SignCube D N → ℝ) (x : SignCube D N) : ℝ :=
  ρ * ∑ l, sourceLevel Ω l x * q l x

noncomputable def refusalMask {D N : ℕ} (Ω : CoefficientField D N)
    (ρ B a₀ : ℝ) (q : Fin N → SignCube D N → ℝ) (x : SignCube D N) : ℝ :=
  ρ * ∑ l, (if l.val < f1Tau Ω ρ B a₀ x then 0 else 1) * sourceLevel Ω l x * q l x

noncomputable def pairOffDiagonal {D N : ℕ} (ρ : ℝ) (Ω : CoefficientField D N)
    (q : Fin N → SignCube D N → ℝ) (diag : SignCube D N → ℝ) (x : SignCube D N) : ℝ :=
  rawPairScore ρ Ω q x - ρ * diag x

theorem stopped_pair_identity {D N : ℕ} (Ω : CoefficientField D N)
    (ρ B a₀ : ℝ) (q : Fin N → SignCube D N → ℝ) (x : SignCube D N) :
    (∑ l, f1Bias Ω ρ B a₀ l x * q l x) = rawPairScore ρ Ω q x - refusalMask Ω ρ B a₀ q x := by
  classical
  unfold rawPairScore refusalMask
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  have hb : f1Bias Ω ρ B a₀ l x =
      if l.val < f1Tau Ω ρ B a₀ x then ρ * sourceLevel Ω l x else 0 :=
    stoppedBias_before_refusal ρ (sourceLevel Ω) (F1Test Ω ρ B a₀) l x
  rw [hb]
  by_cases hbefore : l.val < f1Tau Ω ρ B a₀ x
  · simp only [ite_eq_left hbefore, zero_mul, mul_zero, sub_zero]
    ring
  · simp [hbefore]

theorem f1Law_row_score {D N : ℕ} (Ω : CoefficientField D N)
    (hΩ : CriticalFieldLegal Ω) (h : Fin D) (ρ B a₀ : ℝ)
    (ha₀ : 0 ≤ a₀) (hsmall : a₀ < 1) (c₀ : ℝ)
    (q : Fin N → SignCube D N → ℝ) (hq : ∀ l, ReadsFirstPast l.val (q l)) :
    mean (f1Law Ω hΩ h ρ B a₀ ha₀ hsmall) (rowPolynomial c₀ q) - c₀ =
      mean (f1Law Ω hΩ h ρ B a₀ ha₀ hsmall)
        (fun x => ∑ l, f1Bias Ω ρ B a₀ l x * q l x) := by
  let P := f1Law Ω hΩ h ρ B a₀ ha₀ hsmall
  have hrow : mean P (rowPolynomial c₀ q) = c₀ +
      ∑ l, mean P (fun x => f1Bias Ω ρ B a₀ l x * q l x) := by
    have hm := mean_linear P 1 1 (fun _ => c₀) (fun x => ∑ l, firstDigit x l * q l x)
    have heq : (fun x => 1 * c₀ + 1 * ∑ l, firstDigit x l * q l x) = rowPolynomial c₀ q := by
      funext x
      simp [rowPolynomial]
    rw [heq] at hm
    simp only [one_mul, mean_const, mean_sum] at hm
    rw [hm]
    congr 1
    apply Finset.sum_congr rfl
    intro l hl
    exact f1Law_score Ω hΩ h ρ B a₀ ha₀ hsmall l (q l) (hq l)
  rw [hrow, mean_sum]
  ring

theorem f1Law_plus_score {D N : ℕ} (Ω : CoefficientField D N)
    (hΩ : CriticalFieldLegal Ω) (h : Fin D) (ρ B a₀ : ℝ)
    (ha₀ : 0 ≤ a₀) (hsmall : a₀ < 1) (c₀ : ℝ)
    (q : Fin N → SignCube D N → ℝ) (hq : ∀ l, ReadsFirstPast l.val (q l))
    (diag : SignCube D N → ℝ) :
    mean (f1Law Ω hΩ h ρ B a₀ ha₀ hsmall) (rowPolynomial c₀ q) - c₀ =
      ρ * mean (f1Law Ω hΩ h ρ B a₀ ha₀ hsmall) diag +
      mean (f1Law Ω hΩ h ρ B a₀ ha₀ hsmall) (pairOffDiagonal ρ Ω q diag) -
      mean (f1Law Ω hΩ h ρ B a₀ ha₀ hsmall) (refusalMask Ω ρ B a₀ q) := by
  let P := f1Law Ω hΩ h ρ B a₀ ha₀ hsmall
  rw [f1Law_row_score Ω hΩ h ρ B a₀ ha₀ hsmall c₀ q hq]
  have hfun : (fun x => ∑ l, f1Bias Ω ρ B a₀ l x * q l x) =
      (fun x => rawPairScore ρ Ω q x - refusalMask Ω ρ B a₀ q x) := by
    funext x
    exact stopped_pair_identity Ω ρ B a₀ q x
  rw [hfun]
  have hraw : mean P (rawPairScore ρ Ω q) =
      ρ * mean P diag + mean P (pairOffDiagonal ρ Ω q diag) := by
    have hm := mean_linear P ρ 1 diag (pairOffDiagonal ρ Ω q diag)
    have heq : (fun x => ρ * diag x + 1 * pairOffDiagonal ρ Ω q diag x) = rawPairScore ρ Ω q := by
      funext x
      unfold pairOffDiagonal
      ring
    rw [heq] at hm
    simpa using hm
  have hm := mean_linear P 1 (-1) (rawPairScore ρ Ω q) (refusalMask Ω ρ B a₀ q)
  simpa [hraw, sub_eq_add_neg] using hm

theorem f1Law_minus_score {D N : ℕ} (Ω : CoefficientField D N)
    (hΩ : CriticalFieldLegal Ω) (h : Fin D) (ρ B a₀ : ℝ)
    (ha₀ : 0 ≤ a₀) (hsmall : a₀ < 1) (c₀ : ℝ)
    (q : Fin N → SignCube D N → ℝ) (hq : ∀ l, ReadsFirstPast l.val (q l))
    (diag : SignCube D N → ℝ) :
    mean (f1Law (-Ω) (criticalFieldLegal_neg Ω hΩ) h ρ B a₀ ha₀ hsmall) (rowPolynomial c₀ q) - c₀ =
      -ρ * mean (f1Law (-Ω) (criticalFieldLegal_neg Ω hΩ) h ρ B a₀ ha₀ hsmall) diag -
      mean (f1Law (-Ω) (criticalFieldLegal_neg Ω hΩ) h ρ B a₀ ha₀ hsmall) (pairOffDiagonal ρ Ω q diag) +
      mean (f1Law (-Ω) (criticalFieldLegal_neg Ω hΩ) h ρ B a₀ ha₀ hsmall) (refusalMask Ω ρ B a₀ q) := by
  let P := f1Law (-Ω) (criticalFieldLegal_neg Ω hΩ) h ρ B a₀ ha₀ hsmall
  rw [f1Law_row_score (-Ω) (criticalFieldLegal_neg Ω hΩ) h ρ B a₀ ha₀ hsmall c₀ q hq]
  have hfun : (fun x => ∑ l, f1Bias (-Ω) ρ B a₀ l x * q l x) =
      (fun x => (-ρ) * diag x + (-1) * pairOffDiagonal ρ Ω q diag x + refusalMask Ω ρ B a₀ q x) := by
    funext x
    simp_rw [f1Bias_neg, neg_mul, Finset.sum_neg_distrib]
    rw [stopped_pair_identity]
    unfold pairOffDiagonal
    ring
  rw [hfun]
  have hsplit := mean_linear P 1 1
    (fun x => (-ρ) * diag x + (-1) * pairOffDiagonal ρ Ω q diag x) (refusalMask Ω ρ B a₀ q)
  simp only [one_mul] at hsplit
  rw [hsplit, mean_linear]
  ring

/-- The generic two-law gain reduction instantiated with the actual F1 laws.
Only the quantitative error and aligned-mass transport estimates remain inputs. -/
theorem f1Law_gain_reduction {D N : ℕ} (Ω : CoefficientField D N)
    (hΩ : CriticalFieldLegal Ω) (h : Fin D) (ρ B a₀ : ℝ)
    (ha₀ : 0 ≤ a₀) (hsmall : a₀ < 1) (c₀ : ℝ)
    (q : Fin N → SignCube D N → ℝ) (hq : ∀ l, ReadsFirstPast l.val (q l))
    (diag : SignCube D N → ℝ) (M K m ε r : ℝ)
    (hρ : 0 ≤ ρ) (hK : 0 < K) (hm : 0 ≤ m) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hM : M = K * m)
    (hQ : ∀ x, |rowPolynomial c₀ q x| ≤ 1)
    (herrorPlus : |mean (f1Law Ω hΩ h ρ B a₀ ha₀ hsmall) (pairOffDiagonal ρ Ω q diag)| +
      |mean (f1Law Ω hΩ h ρ B a₀ ha₀ hsmall) (refusalMask Ω ρ B a₀ q)| ≤ r)
    (herrorMinus : |mean (f1Law (-Ω) (criticalFieldLegal_neg Ω hΩ) h ρ B a₀ ha₀ hsmall)
        (pairOffDiagonal ρ Ω q diag)| +
      |mean (f1Law (-Ω) (criticalFieldLegal_neg Ω hΩ) h ρ B a₀ ha₀ hsmall) (refusalMask Ω ρ B a₀ q)| ≤ r)
    (htransportPlus : 1 ≤ ρ * m → (1 - ε) * ρ * m ≤
      ρ * mean (f1Law Ω hΩ h ρ B a₀ ha₀ hsmall) diag)
    (htransportMinus : 1 ≤ ρ * m → (1 - ε) * ρ * m ≤
      ρ * mean (f1Law (-Ω) (criticalFieldLegal_neg Ω hΩ) h ρ B a₀ ha₀ hsmall) diag) :
    ((1 - ε) / (1 + r)) * ρ * M ≤ K :=
  twoLaw_gain_reduction
    (f1Law Ω hΩ h ρ B a₀ ha₀ hsmall)
    (f1Law (-Ω) (criticalFieldLegal_neg Ω hΩ) h ρ B a₀ ha₀ hsmall)
    (rowPolynomial c₀ q) diag (pairOffDiagonal ρ Ω q diag) (refusalMask Ω ρ B a₀ q)
    ρ c₀ M K m ε r hρ hK hm hε hr hM hQ
    (f1Law_plus_score Ω hΩ h ρ B a₀ ha₀ hsmall c₀ q hq diag)
    (f1Law_minus_score Ω hΩ h ρ B a₀ ha₀ hsmall c₀ q hq diag)
    herrorPlus herrorMinus htransportPlus htransportMinus

end HaarQuarter
