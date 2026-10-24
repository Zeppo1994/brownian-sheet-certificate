import BrownianSharp.FiniteEntropy
import BrownianSharp.SignCube
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Lean.Elab.Tactic.Omega

/-!
# The exponential budget for predictable fair signs

Source: unrestricted quarter-gain proof, Section 4, Lemma T2.
The reference law is the uniform law on the finite first/transverse sign cube.
All first signs and other-axis signs may be read by a coefficient. On the
selected axis, it may read only signs of strictly smaller depth.
-/

open scoped BigOperators

namespace HaarQuarter

def signCubeEquiv (D N : ℕ) :
    SignCube D N ≃ ((Fin N → Bool) × (Fin D → Fin N → Bool)) where
  toFun x := (x.first, x.transverse)
  invFun x := ⟨x.1, x.2⟩
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

noncomputable instance signCubeFintype (D N : ℕ) : Fintype (SignCube D N) :=
  Fintype.ofEquiv _ (signCubeEquiv D N).symm

instance signCubeNonempty (D N : ℕ) : Nonempty (SignCube D N) :=
  ⟨⟨fun _ => false, fun _ _ => false⟩⟩

noncomputable def uniformLaw (ι : Type*) [Fintype ι] [Nonempty ι] : PositiveLaw ι where
  mass _ := (Fintype.card ι : ℝ)⁻¹
  positive _ := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  total := by
    have hn : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    simp [hn]

noncomputable def fairCubeLaw (D N : ℕ) : PositiveLaw (SignCube D N) :=
  uniformLaw (SignCube D N)

theorem mean_const {ι : Type*} [Fintype ι] (P : PositiveLaw ι) (a : ℝ) :
    mean P (fun _ => a) = a := by
  unfold mean
  rw [← Finset.sum_mul, P.total, one_mul]

theorem mean_mono {ι : Type*} [Fintype ι] (P : PositiveLaw ι)
    {F G : ι → ℝ} (h : ∀ x, F x ≤ G x) : mean P F ≤ mean P G := by
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (h i) (le_of_lt (P.positive i)))

theorem flip_involutive {D N : ℕ} (h : Fin D) (u : Fin N) :
    Function.Involutive (fun x : SignCube D N => flip x h u) := by
  intro x
  cases x with
  | mk first transverse =>
    dsimp [flip]
    congr 1
    funext a k
    by_cases hk : a = h ∧ k = u <;> simp [hk]

def flipEquiv {D N : ℕ} (h : Fin D) (u : Fin N) : SignCube D N ≃ SignCube D N where
  toFun x := flip x h u
  invFun x := flip x h u
  left_inv := flip_involutive h u
  right_inv := flip_involutive h u

theorem fair_mean_flip {D N : ℕ} (F : SignCube D N → ℝ) (h : Fin D) (u : Fin N) :
    mean (fairCubeLaw D N) (fun x => F (flip x h u)) = mean (fairCubeLaw D N) F := by
  unfold mean fairCubeLaw uniformLaw
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  exact (flipEquiv h u).sum_comp F

theorem axisPastAgreement_flip_later {D N : ℕ} (x : SignCube D N)
    (h : Fin D) (u k : Fin N) (huk : u.val ≤ k.val) :
    AxisPastAgreement h u x (flip x h k) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro a j ha
    simp [flip, ha]
  · intro j hj
    have hne : j ≠ k := by
      intro heq
      subst j
      omega
    simp [flip, hne]

theorem readsAxisPast_flip_later {D N : ℕ} {F : SignCube D N → ℝ}
    (h : Fin D) (u k : Fin N) (hF : ReadsAxisPast h u F) (huk : u.val ≤ k.val)
    (x : SignCube D N) : F (flip x h k) = F x :=
  (hF x (flip x h k) (axisPastAgreement_flip_later x h u k huk)).symm

noncomputable def exponentialFactor {D N : ℕ} (c : Fin N → SignCube D N → ℝ)
    (s : ℝ) (h : Fin D) (u : Fin N) (x : SignCube D N) : ℝ :=
  Real.exp (s * digit x h u * c u x + (-(s ^ 2) / 2) * (c u x) ^ 2)

theorem symmetric_exponentialFactor_le_one (s a : ℝ) (b : Bool) :
    (Real.exp (s * sign b * a + (-(s ^ 2) / 2) * a ^ 2) +
      Real.exp (s * (-sign b) * a + (-(s ^ 2) / 2) * a ^ 2)) / 2 ≤ 1 := by
  have hid : (-(s ^ 2) / 2) * a ^ 2 = -((s * a) ^ 2 / 2) := by ring
  have hcosh : Real.cosh (s * a) * Real.exp (-((s * a) ^ 2 / 2)) ≤ 1 := by
    calc
      _ ≤ Real.exp ((s * a) ^ 2 / 2) * Real.exp (-((s * a) ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_right (Real.cosh_le_exp_half_sq _) (le_of_lt (Real.exp_pos _))
      _ = 1 := by rw [← Real.exp_add]; simp
  calc
    _ = Real.cosh (s * a) * Real.exp (-((s * a) ^ 2 / 2)) := by
      rw [hid]
      cases b <;>
        simp only [sign, Bool.false_eq_true, ite_false, ite_true, neg_neg,
          mul_one, mul_neg_one, neg_mul, Real.exp_add, Real.cosh_eq] <;> ring
    _ ≤ 1 := hcosh

theorem fair_exponential_step {D N : ℕ} (h : Fin D) (u : Fin N)
    (F c : SignCube D N → ℝ) (s : ℝ) (hFnonneg : ∀ x, 0 ≤ F x)
    (hF : ∀ x, F (flip x h u) = F x) (hc : ReadsAxisPast h u c) :
    mean (fairCubeLaw D N) (fun x => F x *
      Real.exp (s * digit x h u * c x + (-(s ^ 2) / 2) * (c x) ^ 2)) ≤
      mean (fairCubeLaw D N) F := by
  let T := fun x => F x * Real.exp (s * digit x h u * c x + (-(s ^ 2) / 2) * (c x) ^ 2)
  have hpair : mean (fairCubeLaw D N) T =
      mean (fairCubeLaw D N) (fun x => (T x + T (flip x h u)) / 2) := by
    have hm := mean_linear (fairCubeLaw D N) (1 / 2) (1 / 2)
      T (fun x => T (flip x h u))
    rw [fair_mean_flip] at hm
    have hfun : (fun x => (1 / 2) * T x + (1 / 2) * T (flip x h u)) =
        (fun x => (T x + T (flip x h u)) / 2) := by funext x; ring
    rw [hfun] at hm
    linarith
  rw [hpair]
  apply mean_mono
  intro x
  have hcflip := readsAxisPast_flip_later h u u hc (le_refl _) x
  dsimp [T]
  rw [hF, hcflip, digit_flip_self]
  have h := mul_le_mul_of_nonneg_left
    (symmetric_exponentialFactor_le_one s (c x) (x.transverse h u)) (hFnonneg x)
  unfold digit at *
  nlinarith

noncomputable def exponentialPrefix {D N : ℕ} (c : Fin N → SignCube D N → ℝ)
    (s : ℝ) (h : Fin D) (k : ℕ) (x : SignCube D N) : ℝ :=
  ∏ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k), exponentialFactor c s h u x

theorem exponentialPrefix_nonneg {D N : ℕ} (c : Fin N → SignCube D N → ℝ)
    (s : ℝ) (h : Fin D) (k : ℕ) (x : SignCube D N) :
    0 ≤ exponentialPrefix c s h k x :=
  Finset.prod_nonneg (fun _ _ => le_of_lt (Real.exp_pos _))

theorem exponentialPrefix_flip {D N : ℕ} (c : Fin N → SignCube D N → ℝ)
    (s : ℝ) (h : Fin D) (k : Fin N)
    (hc : ∀ u, ReadsAxisPast h u (c u)) (x : SignCube D N) :
    exponentialPrefix c s h k.val (flip x h k) = exponentialPrefix c s h k.val x := by
  apply Finset.prod_congr rfl
  intro u hu
  have huk : u.val < k.val := (Finset.mem_filter.mp hu).2
  have hne : u ≠ k := by intro heq; subst u; exact (Nat.lt_irrefl k.val) huk
  unfold exponentialFactor
  rw [digit_flip_of_depth_ne x h h k u hne,
    readsAxisPast_flip_later h u k (hc u) (le_of_lt huk) x]

theorem exponentialPrefix_succ {D N : ℕ} (c : Fin N → SignCube D N → ℝ)
    (s : ℝ) (h : Fin D) (k : ℕ) (hk : k < N) (x : SignCube D N) :
    exponentialPrefix c s h (k + 1) x =
      exponentialPrefix c s h k x * exponentialFactor c s h ⟨k, hk⟩ x := by
  have hset : Finset.univ.filter (fun u : Fin N => u.val < k + 1) =
      insert ⟨k, hk⟩ (Finset.univ.filter (fun u : Fin N => u.val < k)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hu
      by_cases huk : u.val < k
      · exact Or.inr huk
      · left
        apply Fin.ext
        change u.val = k
        omega
    · rintro (hu | hu)
      · subst u
        exact Nat.lt_succ_self k
      · omega
  have hnot : (⟨k, hk⟩ : Fin N) ∉ Finset.univ.filter (fun u : Fin N => u.val < k) := by simp
  unfold exponentialPrefix
  rw [hset, Finset.prod_insert hnot, mul_comm]

theorem fair_exponentialPrefix_le_one {D N : ℕ} (c : Fin N → SignCube D N → ℝ)
    (s : ℝ) (h : Fin D) (hc : ∀ u, ReadsAxisPast h u (c u)) :
    ∀ k : ℕ, k ≤ N → mean (fairCubeLaw D N) (exponentialPrefix c s h k) ≤ 1 := by
  intro k
  induction k with
  | zero =>
    intro hk
    simpa [mean, exponentialPrefix] using le_of_eq (fairCubeLaw D N).total
  | succ k ih =>
    intro hk
    have hklt : k < N := Nat.lt_of_succ_le hk
    have hstep := fair_exponential_step h ⟨k, hklt⟩
      (exponentialPrefix c s h k) (c ⟨k, hklt⟩) s
      (exponentialPrefix_nonneg c s h k)
      (exponentialPrefix_flip c s h ⟨k, hklt⟩ hc) (hc ⟨k, hklt⟩)
    have heq : exponentialPrefix c s h (k + 1) =
        (fun x => exponentialPrefix c s h k x *
          Real.exp (s * digit x h ⟨k, hklt⟩ * c ⟨k, hklt⟩ x +
            (-(s ^ 2) / 2) * (c ⟨k, hklt⟩ x) ^ 2)) := by
      funext x
      exact exponentialPrefix_succ c s h k hklt x
    rw [heq]
    exact hstep.trans (ih (Nat.le_of_lt hklt))

def axisMartingale {D N : ℕ} (h : Fin D) (c : Fin N → SignCube D N → ℝ)
    (x : SignCube D N) : ℝ := ∑ u, digit x h u * c u x

def axisVariance {D N : ℕ} (c : Fin N → SignCube D N → ℝ)
    (x : SignCube D N) : ℝ := ∑ u, (c u x) ^ 2

theorem fair_exponential_budget {D N : ℕ} (h : Fin D)
    (c : Fin N → SignCube D N → ℝ) (hc : ∀ u, ReadsAxisPast h u (c u)) (s : ℝ) :
    mean (fairCubeLaw D N) (fun x => Real.exp (s * axisMartingale h c x +
      (-(s ^ 2) / 2) * axisVariance c x)) ≤ 1 := by
  have heq : (fun x => Real.exp (s * axisMartingale h c x +
        (-(s ^ 2) / 2) * axisVariance c x)) = exponentialPrefix c s h N := by
    funext x
    unfold exponentialPrefix exponentialFactor axisMartingale axisVariance
    have hset : Finset.univ.filter (fun u : Fin N => u.val < N) = Finset.univ := by
      ext u
      simp
    rw [hset, ← Real.exp_sum]
    congr 1
    simp only [Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  rw [heq]
  exact fair_exponentialPrefix_le_one c s h hc N (le_refl N)

/-- Lemma T2: no exponential-budget assumption remains. -/
theorem oneAxis_gibbs {D N : ℕ} (P : PositiveLaw (SignCube D N)) (h : Fin D)
    (c : Fin N → SignCube D N → ℝ) (hc : ∀ u, ReadsAxisPast h u (c u)) :
    |mean P (axisMartingale h c)| ≤
      Real.sqrt (2 * relativeEntropy P (fairCubeLaw D N) * mean P (axisVariance c)) := by
  apply mean_abs_le_sqrt_entropy_variance P (fairCubeLaw D N)
  · intro x
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  · exact fair_exponential_budget h c hc

end HaarQuarter
