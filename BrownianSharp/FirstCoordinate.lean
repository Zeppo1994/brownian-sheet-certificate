import BrownianSharp.TiltedSigns
import BrownianSharp.Target

/-!
# The biased law in the original first-coordinate convention

The coordinate swap is an exact finite equivalence. It transfers the proved
generic biased-axis law to first-coordinate signs while allowing every
transverse bit to be read. No independence of the adaptive biases is assumed.
-/

open scoped BigOperators

namespace HaarQuarter

def FirstPastAgreement {D N : ℕ} (k : ℕ) (x y : SignCube D N) : Prop :=
  x.transverse = y.transverse ∧ ∀ u : Fin N, u.val < k → x.first u = y.first u

def ReadsFirstPast {D N : ℕ} (k : ℕ) (F : SignCube D N → ℝ) : Prop :=
  ∀ x y, FirstPastAgreement k x y → F x = F y

def FirstPastEvent {D N : ℕ} (k : ℕ) (E : SignCube D N → Prop) : Prop :=
  ∀ x y, FirstPastAgreement k x y → (E x ↔ E y)

theorem firstPastAgreement_mono {D N : ℕ} {k l : ℕ} {x y : SignCube D N}
    (hxy : FirstPastAgreement l x y) (hkl : k ≤ l) : FirstPastAgreement k x y := by
  refine ⟨hxy.1, ?_⟩
  intro u hu
  exact hxy.2 u (lt_of_lt_of_le hu hkl)

def swapFirst {D N : ℕ} (h : Fin D) (x : SignCube D N) : SignCube D N :=
  { first := x.transverse h
    transverse := fun a u => if a = h then x.first u else x.transverse a u }

theorem swapFirst_involutive {D N : ℕ} (h : Fin D) :
    Function.Involutive (swapFirst h : SignCube D N → SignCube D N) := by
  intro x
  cases x with
  | mk first transverse =>
    dsimp [swapFirst]
    simp only [ite_true]
    congr 1
    funext a u
    by_cases ha : a = h <;> simp [ha]

def swapFirstEquiv {D N : ℕ} (h : Fin D) : SignCube D N ≃ SignCube D N where
  toFun := swapFirst h
  invFun := swapFirst h
  left_inv := swapFirst_involutive h
  right_inv := swapFirst_involutive h

theorem swap_axisPast_to_firstPast {D N : ℕ} (h : Fin D) (u : Fin N)
    {x y : SignCube D N} (hxy : AxisPastAgreement h u x y) :
    FirstPastAgreement u.val (swapFirst h x) (swapFirst h y) := by
  constructor
  · funext a k
    by_cases ha : a = h
    · simpa [swapFirst, ha] using congrFun hxy.1 k
    · simpa [swapFirst, ha] using hxy.2.1 a k ha
  · intro k hk
    exact hxy.2.2 k hk

theorem firstPredictable_after_swap {D N : ℕ} (h : Fin D) (u : Fin N)
    (F : SignCube D N → ℝ) (hF : ReadsFirstPast u.val F) :
    ReadsAxisPast h u (fun x => F (swapFirst h x)) := by
  intro x y hxy
  exact hF _ _ (swap_axisPast_to_firstPast h u hxy)

noncomputable def pullbackLaw {ι : Type*} [Fintype ι]
    (e : ι ≃ ι) (P : PositiveLaw ι) : PositiveLaw ι where
  mass x := P.mass (e x)
  positive x := P.positive (e x)
  total := (e.sum_comp P.mass).trans P.total

theorem pullback_mean {ι : Type*} [Fintype ι] (e : ι ≃ ι)
    (P : PositiveLaw ι) (G : ι → ℝ) :
    mean (pullbackLaw e P) G = mean P (fun y => G (e.symm y)) := by
  have h := e.sum_comp (fun y => P.mass y * G (e.symm y))
  simpa only [Equiv.symm_apply_apply, mean, pullbackLaw] using h

noncomputable def firstDensityPrefix {D N : ℕ}
    (f : Fin N → SignCube D N → ℝ) (k : ℕ) (x : SignCube D N) : ℝ :=
  ∏ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k), (1 + firstDigit x u * f u x)

noncomputable def firstTiltedLaw {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hf : ∀ u, ReadsFirstPast u.val (f u))
    (hsmall : ∀ u x, |f u x| < 1) : PositiveLaw (SignCube D N) :=
  pullbackLaw (swapFirstEquiv h)
    (tiltedLaw h (fun u x => f u (swapFirst h x))
      (fun u => firstPredictable_after_swap h u (f u) (hf u))
      (fun u x => hsmall u (swapFirst h x)))

/-- The transferred law has the exact original first-sign density. -/
theorem firstTilted_mass_density {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hf : ∀ u, ReadsFirstPast u.val (f u))
    (hsmall : ∀ u x, |f u x| < 1) (x : SignCube D N) :
    (firstTiltedLaw h f hf hsmall).mass x =
      (fairCubeLaw D N).mass x * firstDensityPrefix f N x := by
  change (fairCubeLaw D N).mass (swapFirst h x) *
      densityPrefix h (fun u y => f u (swapFirst h y)) N (swapFirst h x) = _
  have hfair : (fairCubeLaw D N).mass (swapFirst h x) = (fairCubeLaw D N).mass x := rfl
  rw [hfair]
  congr 1
  unfold densityPrefix firstDensityPrefix
  apply Finset.prod_congr rfl
  intro u hu
  dsimp only
  rw [swapFirst_involutive h x]
  simp [digit, firstDigit, swapFirst]

theorem first_score_identity {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hf : ∀ u, ReadsFirstPast u.val (f u))
    (hsmall : ∀ u x, |f u x| < 1) (u : Fin N)
    (G : SignCube D N → ℝ) (hG : ReadsFirstPast u.val G) :
    mean (firstTiltedLaw h f hf hsmall) (fun x => firstDigit x u * G x) =
      mean (firstTiltedLaw h f hf hsmall) (fun x => f u x * G x) := by
  unfold firstTiltedLaw
  rw [pullback_mean, pullback_mean]
  have hs := tilted_score_identity h (fun k x => f k (swapFirst h x))
    (fun k => firstPredictable_after_swap h k (f k) (hf k))
    (fun k x => hsmall k (swapFirst h x)) u (fun x => G (swapFirst h x))
    (firstPredictable_after_swap h u G hG)
  have hinv (y : SignCube D N) : (swapFirstEquiv h).symm y = swapFirst h y := rfl
  simp_rw [hinv]
  simpa only [firstDigit, digit, swapFirst] using hs

theorem firstBiasFactor_positive {D N : ℕ}
    (f : Fin N → SignCube D N → ℝ) (hsmall : ∀ u x, |f u x| < 1)
    (u : Fin N) (x : SignCube D N) : 0 < 1 + firstDigit x u * f u x := by
  have hlo := (abs_lt.mp (hsmall u x)).1
  have hhi := (abs_lt.mp (hsmall u x)).2
  cases hb : x.first u <;> norm_num [firstDigit, sign, hb] <;> linarith

theorem first_log_likelihood {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hf : ∀ u, ReadsFirstPast u.val (f u))
    (hsmall : ∀ u x, |f u x| < 1) (x : SignCube D N) :
    Real.log ((firstTiltedLaw h f hf hsmall).mass x / (fairCubeLaw D N).mass x) =
      ∑ u, Real.log (1 + firstDigit x u * f u x) := by
  have hmass : (fairCubeLaw D N).mass x ≠ 0 := ((fairCubeLaw D N).positive x).ne'
  rw [firstTilted_mass_density, mul_div_cancel_left₀ _ hmass]
  unfold firstDensityPrefix
  have hset : Finset.univ.filter (fun u : Fin N => u.val < N) = Finset.univ := by ext u; simp
  rw [hset, Real.log_prod]
  intro u hu
  exact (firstBiasFactor_positive f hsmall u x).ne'

theorem first_information_budget {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hf : ∀ u, ReadsFirstPast u.val (f u))
    (hsmall : ∀ u x, |f u x| < 1) (V : ℝ)
    (henergy : ∀ x, ∑ u, (f u x) ^ 2 ≤ V) :
    relativeEntropy (firstTiltedLaw h f hf hsmall) (fairCubeLaw D N) ≤ V := by
  apply information_budget_from_score (firstTiltedLaw h f hf hsmall) (fairCubeLaw D N)
    (fun u x => firstDigit x u) f V
  · exact firstBiasFactor_positive f hsmall
  · exact first_log_likelihood h f hf hsmall
  · intro u
    simpa only [sq] using first_score_identity h f hf hsmall u (f u) (hf u)
  · exact henergy

end HaarQuarter
