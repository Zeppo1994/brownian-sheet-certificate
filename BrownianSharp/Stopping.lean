import BrownianSharp.FirstCoordinate

/-!
# Exact absorbing first-refusal stop

Source: coarse-frame information proof, Definitions and Section 2.
Tests for label `l` read first signs strictly before `l`, and may read every
transverse sign. Admission includes the test at `l`; a refusal is permanent.
The actual F1 scalar and operator tests are instantiated in a separate module.
-/

namespace HaarQuarter

noncomputable def failedLabels {D N : ℕ}
    (test : Fin N → SignCube D N → Prop) (x : SignCube D N) : Finset (Fin N) := by
  classical
  exact Finset.univ.filter (fun u => ¬ test u x)

noncomputable def firstRefusal {D N : ℕ}
    (test : Fin N → SignCube D N → Prop) (x : SignCube D N) : ℕ := by
  classical
  exact if h : (failedLabels test x).Nonempty then ((failedLabels test x).min' h).val else N

def Admitted {D N : ℕ} (test : Fin N → SignCube D N → Prop)
    (l : Fin N) (x : SignCube D N) : Prop :=
  ∀ u : Fin N, u.val ≤ l.val → test u x

theorem firstRefusal_le {D N : ℕ} (test : Fin N → SignCube D N → Prop)
    (x : SignCube D N) : firstRefusal test x ≤ N := by
  classical
  unfold firstRefusal
  split_ifs with h
  · exact le_of_lt ((failedLabels test x).min' h).isLt
  · exact le_refl N

/-- The refused label is excluded, and every earlier label is admitted. -/
theorem admitted_iff_before_refusal {D N : ℕ}
    (test : Fin N → SignCube D N → Prop) (l : Fin N) (x : SignCube D N) :
    Admitted test l x ↔ l.val < firstRefusal test x := by
  classical
  by_cases hb : (failedLabels test x).Nonempty
  · simp only [firstRefusal, dite_eq_left hb]
    constructor
    · intro hadmit
      by_contra hn
      have hm : ((failedLabels test x).min' hb).val ≤ l.val := Nat.le_of_not_gt hn
      have hpass := hadmit ((failedLabels test x).min' hb) hm
      have hfail := (Finset.mem_filter.mp (Finset.min'_mem (failedLabels test x) hb)).2
      exact hfail hpass
    · intro hl u hu
      by_contra hfail
      have hbad : u ∈ failedLabels test x :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ u, hfail⟩
      have hmin : (failedLabels test x).min' hb ≤ u := Finset.min'_le _ _ hbad
      have hminval : ((failedLabels test x).min' hb).val ≤ u.val := hmin
      exact (not_lt_of_ge (hminval.trans hu)) hl
  · simp only [firstRefusal, dite_eq_right hb]
    constructor
    · intro _
      exact l.isLt
    · intro _ u hu
      by_contra hfail
      apply hb
      exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ u, hfail⟩⟩

theorem admitted_test {D N : ℕ} {test : Fin N → SignCube D N → Prop}
    {l : Fin N} {x : SignCube D N} (hl : Admitted test l x) : test l x :=
  hl l (le_refl _)

theorem admitted_firstPast {D N : ℕ} (test : Fin N → SignCube D N → Prop)
    (htest : ∀ u, FirstPastEvent u.val (test u)) (l : Fin N) :
    FirstPastEvent l.val (Admitted test l) := by
  intro x y hxy
  constructor
  · intro hadmit u hu
    exact (htest u x y (firstPastAgreement_mono hxy hu)).mp (hadmit u hu)
  · intro hadmit u hu
    exact (htest u x y (firstPastAgreement_mono hxy hu)).mpr (hadmit u hu)

noncomputable def stoppedBias {D N : ℕ} (ρ : ℝ)
    (A : Fin N → SignCube D N → ℝ) (test : Fin N → SignCube D N → Prop)
    (l : Fin N) (x : SignCube D N) : ℝ := by
  classical
  exact if Admitted test l x then ρ * A l x else 0

theorem stoppedBias_before_refusal {D N : ℕ} (ρ : ℝ)
    (A : Fin N → SignCube D N → ℝ) (test : Fin N → SignCube D N → Prop)
    (l : Fin N) (x : SignCube D N) :
    stoppedBias ρ A test l x = if l.val < firstRefusal test x then ρ * A l x else 0 := by
  classical
  simp only [stoppedBias, admitted_iff_before_refusal]

theorem stoppedBias_firstPast {D N : ℕ} (ρ : ℝ)
    (A : Fin N → SignCube D N → ℝ) (test : Fin N → SignCube D N → Prop)
    (hA : ∀ l, ReadsFirstPast l.val (A l))
    (htest : ∀ l, FirstPastEvent l.val (test l)) (l : Fin N) :
    ReadsFirstPast l.val (stoppedBias ρ A test l) := by
  classical
  intro x y hxy
  have hadmit := admitted_firstPast test htest l x y hxy
  have hvalue := hA l x y hxy
  by_cases hx : Admitted test l x
  · have hy := hadmit.mp hx
    simp [stoppedBias, hx, hy, hvalue]
  · have hy : ¬ Admitted test l y := fun hy => hx (hadmit.mpr hy)
    simp [stoppedBias, hx, hy]

theorem stoppedBias_abs_cap {D N : ℕ} (ρ a₀ : ℝ) (ha₀ : 0 ≤ a₀)
    (A : Fin N → SignCube D N → ℝ) (test : Fin N → SignCube D N → Prop)
    (hcap : ∀ l x, test l x → |ρ * A l x| ≤ a₀) (l : Fin N) (x : SignCube D N) :
    |stoppedBias ρ A test l x| ≤ a₀ := by
  classical
  by_cases hl : Admitted test l x
  · simpa [stoppedBias, hl] using hcap l x (admitted_test hl)
  · simpa [stoppedBias, hl] using ha₀

noncomputable def stoppedFirstLaw {D N : ℕ} (h : Fin D) (ρ a₀ : ℝ)
    (ha₀ : 0 ≤ a₀) (hsmall : a₀ < 1)
    (A : Fin N → SignCube D N → ℝ) (test : Fin N → SignCube D N → Prop)
    (hA : ∀ l, ReadsFirstPast l.val (A l))
    (htest : ∀ l, FirstPastEvent l.val (test l))
    (hcap : ∀ l x, test l x → |ρ * A l x| ≤ a₀) : PositiveLaw (SignCube D N) :=
  firstTiltedLaw h (stoppedBias ρ A test)
    (stoppedBias_firstPast ρ A test hA htest)
    (fun l x => (stoppedBias_abs_cap ρ a₀ ha₀ A test hcap l x).trans_lt hsmall)

theorem stoppedFirstLaw_score {D N : ℕ} (h : Fin D) (ρ a₀ : ℝ)
    (ha₀ : 0 ≤ a₀) (hsmall : a₀ < 1)
    (A : Fin N → SignCube D N → ℝ) (test : Fin N → SignCube D N → Prop)
    (hA : ∀ l, ReadsFirstPast l.val (A l))
    (htest : ∀ l, FirstPastEvent l.val (test l))
    (hcap : ∀ l x, test l x → |ρ * A l x| ≤ a₀)
    (l : Fin N) (G : SignCube D N → ℝ) (hG : ReadsFirstPast l.val G) :
    mean (stoppedFirstLaw h ρ a₀ ha₀ hsmall A test hA htest hcap)
      (fun x => firstDigit x l * G x) =
    mean (stoppedFirstLaw h ρ a₀ ha₀ hsmall A test hA htest hcap)
      (fun x => stoppedBias ρ A test l x * G x) :=
  first_score_identity h _ _ _ l G hG

theorem firstRefusal_failed_at_stop {D N : ℕ}
    (test : Fin N → SignCube D N → Prop) (x : SignCube D N)
    (hbad : firstRefusal test x < N) :
    ¬ test ⟨firstRefusal test x, hbad⟩ x := by
  intro hpass
  let l : Fin N := ⟨firstRefusal test x, hbad⟩
  have hadmit : Admitted test l x := by
    intro u hu
    by_cases heq : u = l
    · simpa only [heq] using hpass
    · have hlt : u.val < firstRefusal test x := by
        have hne : u.val ≠ l.val := fun h => heq (Fin.ext h)
        dsimp [l] at hu hne
        omega
      exact admitted_test ((admitted_iff_before_refusal test u x).2 hlt)
  have hh := (admitted_iff_before_refusal test l x).1 hadmit
  exact (Nat.lt_irrefl (firstRefusal test x)) hh

theorem firstRefusal_mono_tests {D N : ℕ}
    (small large : Fin N → SignCube D N → Prop)
    (himp : ∀ l x, small l x → large l x) (x : SignCube D N) :
    firstRefusal small x ≤ firstRefusal large x := by
  by_contra hn
  have hlt : firstRefusal large x < firstRefusal small x := Nat.lt_of_not_ge hn
  have hN : firstRefusal large x < N := hlt.trans_le (firstRefusal_le small x)
  let l : Fin N := ⟨firstRefusal large x, hN⟩
  have hs := (admitted_iff_before_refusal small l x).2 hlt
  have hl : Admitted large l x := fun u hu => himp u x (hs u hu)
  have hh := (admitted_iff_before_refusal large l x).1 hl
  exact (Nat.lt_irrefl (firstRefusal large x)) hh

end HaarQuarter
