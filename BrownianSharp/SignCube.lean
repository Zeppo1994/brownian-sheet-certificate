import BrownianSharp.FirstEscape
import Mathlib.Tactic.NormNum

/-!
# Legal prefixes and the fresh sign

Source: unrestricted quarter-gain proof, Section 5, Lemma A1.
Flipping the escaping sign fixes every factor of its coefficient and negates
the complete interaction. This is the finite combinatorial predictability
obligation, before changing probability laws.
-/

open scoped BigOperators

namespace HaarQuarter

structure SignCube (D N : ℕ) where
  first : Fin N → Bool
  transverse : Fin D → Fin N → Bool

def flip {D N : ℕ} (x : SignCube D N) (h : Fin D) (u : Fin N) : SignCube D N :=
  { first := x.first
    transverse := fun a k =>
      if a = h ∧ k = u then !(x.transverse a k) else x.transverse a k }

def PrefixAgreement {D N : ℕ} (l : ℕ) (v : Profile D)
    (x y : SignCube D N) : Prop :=
  (∀ k : Fin N, k.val < l → x.first k = y.first k) ∧
    ∀ (a : Fin D) (k : Fin N), k.val < v a → x.transverse a k = y.transverse a k

def LegalCoefficient {D N : ℕ} (l : ℕ) (v : Profile D)
    (F : SignCube D N → ℝ) : Prop :=
  ∀ x y, PrefixAgreement l v x y → F x = F y

/-- The finite version of the one-axis filtration: all first/other-axis bits,
and only depths strictly below `u` on axis `h`. -/
def AxisPastAgreement {D N : ℕ} (h : Fin D) (u : Fin N)
    (x y : SignCube D N) : Prop :=
  x.first = y.first ∧
    (∀ (a : Fin D) (k : Fin N), a ≠ h → x.transverse a k = y.transverse a k) ∧
    ∀ k : Fin N, k.val < u.val → x.transverse h k = y.transverse h k

def ReadsAxisPast {D N : ℕ} (h : Fin D) (u : Fin N)
    (F : SignCube D N → ℝ) : Prop :=
  ∀ x y, AxisPastAgreement h u x y → F x = F y

theorem axisPastAgreement_prefix {D N : ℕ} (l : ℕ) (v : Profile D)
    (h : Fin D) (u : Fin N) (hbound : v h ≤ u.val)
    {x y : SignCube D N} (hxy : AxisPastAgreement h u x y) :
    PrefixAgreement l v x y := by
  constructor
  · intro k hk
    exact congrFun hxy.1 k
  · intro a k hk
    by_cases ha : a = h
    · subst a
      exact hxy.2.2 k (lt_of_lt_of_le hk hbound)
    · exact hxy.2.1 a k ha

/-- A coefficient reading strictly earlier bits cannot read the flipped bit. -/
theorem prefixAgreement_flip {D N : ℕ} (l : ℕ) (v : Profile D)
    (x : SignCube D N) (h : Fin D) (u : Fin N) (hbound : v h ≤ u.val) :
    PrefixAgreement l v x (flip x h u) := by
  constructor
  · intro k hk
    rfl
  · intro a k hk
    by_cases ha : a = h
    · subst a
      have hklt : k.val < u.val := lt_of_lt_of_le hk hbound
      have hne : k ≠ u := by
        intro heq
        subst k
        exact (Nat.lt_irrefl u.val) hklt
      simp [flip, hne]
    · simp [flip, ha]

theorem legalCoefficient_flip {D N : ℕ} {l : ℕ} {v : Profile D}
    {F : SignCube D N → ℝ} (hlegal : LegalCoefficient l v F)
    (x : SignCube D N) (h : Fin D) (u : Fin N) (hbound : v h ≤ u.val) :
    F (flip x h u) = F x :=
  (hlegal x (flip x h u) (prefixAgreement_flip l v x h u hbound)).symm

def sign (b : Bool) : ℝ := if b then 1 else -1

def digit {D N : ℕ} (x : SignCube D N) (h : Fin D) (u : Fin N) : ℝ :=
  sign (x.transverse h u)

theorem digit_sq {D N : ℕ} (x : SignCube D N) (h : Fin D) (u : Fin N) :
    digit x h u * digit x h u = 1 := by
  cases hb : x.transverse h u <;> norm_num [digit, sign, hb]

theorem digit_flip_self {D N : ℕ} (x : SignCube D N) (h : Fin D) (u : Fin N) :
    digit (flip x h u) h u = -digit x h u := by
  cases hb : x.transverse h u <;> norm_num [digit, sign, flip, hb]

theorem digit_flip_of_axis_ne {D N : ℕ} (x : SignCube D N)
    (h a : Fin D) (u k : Fin N) (ha : a ≠ h) :
    digit (flip x h u) a k = digit x a k := by
  simp [digit, flip, ha]

theorem digit_flip_of_depth_ne {D N : ℕ} (x : SignCube D N)
    (h a : Fin D) (u k : Fin N) (hk : k ≠ u) :
    digit (flip x h u) a k = digit x a k := by
  simp [digit, flip, hk]

abbrev BoundedProfile (D N : ℕ) := Fin D → Fin N

def naturalProfile {D N : ℕ} (v : BoundedProfile D N) : Profile D :=
  fun a => (v a).val

theorem naturalProfile_injective {D N : ℕ} :
    Function.Injective (@naturalProfile D N) := by
  intro v t heq
  funext a
  apply Fin.ext
  exact congrFun heq a

def profileWord {D N : ℕ} (x : SignCube D N) (v : BoundedProfile D N) : ℝ :=
  ∏ a, digit x a (v a)

def erasedWord {D N : ℕ} (x : SignCube D N) (v : BoundedProfile D N)
    (h : Fin D) : ℝ := ∏ a ∈ Finset.univ.erase h, digit x a (v a)

theorem profileWord_sq {D N : ℕ} (x : SignCube D N) (v : BoundedProfile D N) :
    profileWord x v * profileWord x v = 1 := by
  unfold profileWord
  rw [← Finset.prod_mul_distrib]
  simp [digit_sq]

theorem profileWord_factor {D N : ℕ} (x : SignCube D N)
    (v : BoundedProfile D N) (h : Fin D) :
    profileWord x v = digit x h (v h) * erasedWord x v h :=
  (Finset.mul_prod_erase Finset.univ (fun a => digit x a (v a))
    (Finset.mem_univ h)).symm

theorem erasedWord_flip {D N : ℕ} (x : SignCube D N)
    (v : BoundedProfile D N) (h : Fin D) (u : Fin N) :
    erasedWord (flip x h u) v h = erasedWord x v h := by
  apply Finset.prod_congr rfl
  intro a ha
  exact digit_flip_of_axis_ne x h a u (v a) (Finset.mem_erase.mp ha).1

theorem profileWord_flip_below {D N : ℕ} (x : SignCube D N)
    (v t : BoundedProfile D N) (h : Fin D)
    (hbelow : (t h).val < (v h).val) :
    profileWord (flip x h (v h)) t = profileWord x t := by
  apply Finset.prod_congr rfl
  intro a ha
  by_cases heq : a = h
  · subst a
    have hne : t h ≠ v h := by
      intro heq
      rw [heq] at hbelow
      exact (Nat.lt_irrefl (v h).val) hbelow
    exact digit_flip_of_depth_ne x h h (v h) (t h) hne
  · exact digit_flip_of_axis_ne x h a (v h) (t a) heq

def escapingCoefficient {D N : ℕ} (Ω β : SignCube D N → ℝ)
    (v t : BoundedProfile D N) (h : Fin D) (x : SignCube D N) : ℝ :=
  Ω x * β x * erasedWord x v h * profileWord x t

/-- Full one-axis predictability, including independence of all later bits. -/
theorem escapingCoefficient_readsAxisPast {D N : ℕ} (l : ℕ)
    (Ω β : SignCube D N → ℝ) (v t : BoundedProfile D N) (h : Fin D)
    (hΩ : LegalCoefficient l (naturalProfile v) Ω)
    (hβ : LegalCoefficient l (naturalProfile t) β)
    (hfirst : IsFirstEscape (naturalProfile v) (naturalProfile t) h) :
    ReadsAxisPast h (v h) (escapingCoefficient Ω β v t h) := by
  intro x y hxy
  have hsource := hΩ x y (axisPastAgreement_prefix l (naturalProfile v)
    h (v h) (le_refl _) hxy)
  have htarget := hβ x y (axisPastAgreement_prefix l (naturalProfile t)
    h (v h) (Nat.le_of_lt hfirst.1) hxy)
  have herased : erasedWord x v h = erasedWord y v h := by
    apply Finset.prod_congr rfl
    intro a ha
    exact congrArg sign (hxy.2.1 a (v a) (Finset.mem_erase.mp ha).1)
  have hword : profileWord x t = profileWord y t := by
    apply Finset.prod_congr rfl
    intro a ha
    by_cases heq : a = h
    · subst a
      exact congrArg sign (hxy.2.2 (t h) hfirst.1)
    · exact congrArg sign (hxy.2.1 a (t a) heq)
  simp only [escapingCoefficient, hsource, htarget, herased, hword]

/-- The coefficient of the fresh digit is invariant under flipping that digit. -/
theorem escapingCoefficient_flip {D N : ℕ} (l : ℕ)
    (Ω β : SignCube D N → ℝ) (v t : BoundedProfile D N) (h : Fin D)
    (hΩ : LegalCoefficient l (naturalProfile v) Ω)
    (hβ : LegalCoefficient l (naturalProfile t) β)
    (hfirst : IsFirstEscape (naturalProfile v) (naturalProfile t) h)
    (x : SignCube D N) :
    escapingCoefficient Ω β v t h (flip x h (v h)) =
      escapingCoefficient Ω β v t h x := by
  unfold escapingCoefficient
  rw [legalCoefficient_flip hΩ x h (v h) (le_refl _)]
  rw [legalCoefficient_flip hβ x h (v h) (Nat.le_of_lt hfirst.1)]
  rw [erasedWord_flip, profileWord_flip_below x v t h hfirst.1]

/-- The complete escaping interaction is odd in a sign its coefficient cannot read. -/
theorem escapingInteraction_flip {D N : ℕ} (l : ℕ)
    (Ω β : SignCube D N → ℝ) (v t : BoundedProfile D N) (h : Fin D)
    (hΩ : LegalCoefficient l (naturalProfile v) Ω)
    (hβ : LegalCoefficient l (naturalProfile t) β)
    (hfirst : IsFirstEscape (naturalProfile v) (naturalProfile t) h)
    (x : SignCube D N) :
    digit (flip x h (v h)) h (v h) *
        escapingCoefficient Ω β v t h (flip x h (v h)) =
      -(digit x h (v h) * escapingCoefficient Ω β v t h x) := by
  rw [digit_flip_self, escapingCoefficient_flip l Ω β v t h hΩ hβ hfirst x]
  exact neg_mul _ _

end HaarQuarter
