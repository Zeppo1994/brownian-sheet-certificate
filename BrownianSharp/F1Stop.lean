import BrownianSharp.Stopping
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The F1 stop: source fields, Xi/Gamma tests and causality

Source: coarse-frame information proof, Definitions and Section 2(a)-(b).
Prefix matrices are represented with zero-padded columns in an `N × N`
Euclidean operator. Gamma tests include every permitted frozen set, free axis
and depth box. No cap-survival or refusal-probability estimate is asserted.
-/

open scoped BigOperators

namespace HaarQuarter

theorem firstPastAgreement_prefix {D N : ℕ} {k : ℕ} {x y : SignCube D N}
    (hxy : FirstPastAgreement k x y) (v : Profile D) : PrefixAgreement k v x y := by
  refine ⟨hxy.2, ?_⟩
  intro a u hu
  exact congrFun (congrFun hxy.1 a) u

theorem profileWord_transverse_eq {D N : ℕ} {x y : SignCube D N}
    (hxy : x.transverse = y.transverse) (v : BoundedProfile D N) :
    profileWord x v = profileWord y v := by
  simp only [profileWord, digit, hxy]

theorem erasedWord_transverse_eq {D N : ℕ} {x y : SignCube D N}
    (hxy : x.transverse = y.transverse) (v : BoundedProfile D N) (j : Fin D) :
    erasedWord x v j = erasedWord y v j := by
  simp only [erasedWord, digit, hxy]

noncomputable def sourceLevel {D N : ℕ} (Ω : CoefficientField D N)
    (l : Fin N) (x : SignCube D N) : ℝ := by
  classical
  exact ∑ v, if IsCriticalProfile l v then Ω l v x * profileWord x v else 0

theorem sourceLevel_firstPast {D N : ℕ} (Ω : CoefficientField D N)
    (hΩ : CriticalFieldLegal Ω) (l : Fin N) : ReadsFirstPast l.val (sourceLevel Ω l) := by
  classical
  intro x y hxy
  unfold sourceLevel
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : IsCriticalProfile l v
  · simp only [ite_eq_left hc]
    rw [hΩ l v hc x y (firstPastAgreement_prefix hxy _), profileWord_transverse_eq hxy.1]
  · simp [hc]

noncomputable def sourceEntry {D N : ℕ} (Ω : CoefficientField D N)
    (j : Fin D) (mask : BoundedProfile D N → Prop)
    (u l : Fin N) (x : SignCube D N) : ℝ := by
  classical
  exact ∑ v, if IsCriticalProfile l v ∧ v j = u ∧ mask v then
    Ω l v x * erasedWord x v j else 0

noncomputable def sourcePrefixMatrix {D N : ℕ} (Ω : CoefficientField D N)
    (j : Fin D) (mask : BoundedProfile D N → Prop)
    (k : ℕ) (x : SignCube D N) : Matrix (Fin N) (Fin N) ℝ := by
  classical
  exact fun u l => if l.val < k then sourceEntry Ω j mask u l x else 0

noncomputable def xiMatrix {D N : ℕ} (Ω : CoefficientField D N)
    (j : Fin D) (k : ℕ) (x : SignCube D N) : Matrix (Fin N) (Fin N) ℝ :=
  sourcePrefixMatrix Ω j (fun _ => True) k x

def GammaMask {D N : ℕ} (J : Finset (Fin D)) (j : Fin D)
    (m v : BoundedProfile D N) : Prop :=
  (∀ a ∈ J, v a = m a) ∧ m j < v j ∧
    ∀ a : Fin D, a < j → a ∉ J → v a ≤ m a

noncomputable def gammaMatrix {D N : ℕ} (Ω : CoefficientField D N)
    (J : Finset (Fin D)) (j : Fin D) (m : BoundedProfile D N)
    (k : ℕ) (x : SignCube D N) : Matrix (Fin N) (Fin N) ℝ :=
  sourcePrefixMatrix Ω j (GammaMask J j m) k x

noncomputable def matrixOperator {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  M.toEuclideanLin.toContinuousLinearMap

/-- Every column visible to the label-l test reads only first signs before l. -/
theorem sourcePrefixMatrix_firstPast {D N : ℕ} (Ω : CoefficientField D N)
    (hΩ : CriticalFieldLegal Ω) (j : Fin D) (mask : BoundedProfile D N → Prop)
    (t : Fin N) {x y : SignCube D N} (hxy : FirstPastAgreement t.val x y) :
    sourcePrefixMatrix Ω j mask (t.val + 1) x = sourcePrefixMatrix Ω j mask (t.val + 1) y := by
  classical
  ext u l
  by_cases hl : l.val < t.val + 1
  · simp only [sourcePrefixMatrix, ite_eq_left hl]
    have hlt : l.val ≤ t.val := Nat.le_of_lt_succ hl
    have hxy_l := firstPastAgreement_mono hxy hlt
    unfold sourceEntry
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hc : IsCriticalProfile l v ∧ v j = u ∧ mask v
    · simp only [ite_eq_left hc]
      rw [hΩ l v hc.1 x y (firstPastAgreement_prefix hxy_l _), erasedWord_transverse_eq hxy.1]
    · simp [hc]
  · simp [sourcePrefixMatrix, hl]

def F1Test {D N : ℕ} (Ω : CoefficientField D N) (ρ B a₀ : ℝ)
    (l : Fin N) (x : SignCube D N) : Prop :=
  (∀ j : Fin D, ‖matrixOperator (xiMatrix Ω j (l.val + 1) x)‖ ^ 2 ≤ B) ∧
    (∀ (J : Finset (Fin D)) (j : Fin D), j ∉ J →
      ∀ m : BoundedProfile D N, grade (naturalProfile m) ≤ N - 1 →
        ‖matrixOperator (gammaMatrix Ω J j m (l.val + 1) x)‖ ^ 2 ≤ B / (N : ℝ) ^ J.card) ∧
    |ρ * sourceLevel Ω l x| ≤ a₀

theorem F1Test_firstPast {D N : ℕ} (Ω : CoefficientField D N)
    (hΩ : CriticalFieldLegal Ω) (ρ B a₀ : ℝ) (l : Fin N) :
    FirstPastEvent l.val (F1Test Ω ρ B a₀ l) := by
  intro x y hxy
  have hxi : ∀ j, xiMatrix Ω j (l.val + 1) x = xiMatrix Ω j (l.val + 1) y :=
    fun j => sourcePrefixMatrix_firstPast Ω hΩ j _ l hxy
  have hgamma : ∀ J j m, gammaMatrix Ω J j m (l.val + 1) x =
      gammaMatrix Ω J j m (l.val + 1) y :=
    fun J j m => sourcePrefixMatrix_firstPast Ω hΩ j _ l hxy
  have hA := sourceLevel_firstPast Ω hΩ l x y hxy
  simp only [F1Test, hxi, hgamma, hA]

noncomputable def f1Tau {D N : ℕ} (Ω : CoefficientField D N) (ρ B a₀ : ℝ)
    (x : SignCube D N) : ℕ := firstRefusal (F1Test Ω ρ B a₀) x

noncomputable def f1Bias {D N : ℕ} (Ω : CoefficientField D N) (ρ B a₀ : ℝ) :
    Fin N → SignCube D N → ℝ := stoppedBias ρ (sourceLevel Ω) (F1Test Ω ρ B a₀)

theorem f1Bias_firstPast {D N : ℕ} (Ω : CoefficientField D N)
    (hΩ : CriticalFieldLegal Ω) (ρ B a₀ : ℝ) (l : Fin N) :
    ReadsFirstPast l.val (f1Bias Ω ρ B a₀ l) :=
  stoppedBias_firstPast ρ _ _ (sourceLevel_firstPast Ω hΩ) (F1Test_firstPast Ω hΩ ρ B a₀) l

theorem f1Bias_abs_cap {D N : ℕ} (Ω : CoefficientField D N)
    (ρ B a₀ : ℝ) (ha₀ : 0 ≤ a₀) (l : Fin N) (x : SignCube D N) :
    |f1Bias Ω ρ B a₀ l x| ≤ a₀ :=
  stoppedBias_abs_cap ρ a₀ ha₀ _ _ (fun _ _ ht => ht.2.2) l x

noncomputable def f1Law {D N : ℕ} (Ω : CoefficientField D N)
    (hΩ : CriticalFieldLegal Ω) (h : Fin D) (ρ B a₀ : ℝ)
    (ha₀ : 0 ≤ a₀) (hsmall : a₀ < 1) : PositiveLaw (SignCube D N) :=
  stoppedFirstLaw h ρ a₀ ha₀ hsmall (sourceLevel Ω) (F1Test Ω ρ B a₀)
    (sourceLevel_firstPast Ω hΩ) (F1Test_firstPast Ω hΩ ρ B a₀)
    (fun _ _ ht => ht.2.2)

theorem f1Law_score {D N : ℕ} (Ω : CoefficientField D N)
    (hΩ : CriticalFieldLegal Ω) (h : Fin D) (ρ B a₀ : ℝ)
    (ha₀ : 0 ≤ a₀) (hsmall : a₀ < 1) (l : Fin N)
    (G : SignCube D N → ℝ) (hG : ReadsFirstPast l.val G) :
    mean (f1Law Ω hΩ h ρ B a₀ ha₀ hsmall) (fun x => firstDigit x l * G x) =
      mean (f1Law Ω hΩ h ρ B a₀ ha₀ hsmall) (fun x => f1Bias Ω ρ B a₀ l x * G x) :=
  stoppedFirstLaw_score h ρ a₀ ha₀ hsmall _ _ _ _ _ l G hG

end HaarQuarter
