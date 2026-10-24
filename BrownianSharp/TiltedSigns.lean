import BrownianSharp.InformationBudget

/-!
# An exact predictable biased-sign law

The selected-axis product `∏ (1 + εᵤ fᵤ)` is a positive mean-one density.
Its law satisfies the score identity and the sufficient information budget
`KL ≤ ∑ E fᵤ²`. The actual Haar stop and its original first-axis coordinate
representation have not yet been instantiated in this generic finite model.
-/

open scoped BigOperators

namespace HaarQuarter

noncomputable def densityPrefix {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (k : ℕ) (x : SignCube D N) : ℝ :=
  ∏ u ∈ Finset.univ.filter (fun u : Fin N => u.val < k), (1 + digit x h u * f u x)

theorem fair_linear_step {D N : ℕ} (h : Fin D) (u : Fin N)
    (F f : SignCube D N → ℝ) (hF : ∀ x, F (flip x h u) = F x)
    (hf : ReadsAxisPast h u f) :
    mean (fairCubeLaw D N) (fun x => F x * (1 + digit x h u * f x)) =
      mean (fairCubeLaw D N) F := by
  let T := fun x => F x * (1 + digit x h u * f x)
  have hm := mean_linear (fairCubeLaw D N) (1 / 2) (1 / 2)
    T (fun x => T (flip x h u))
  rw [fair_mean_flip] at hm
  have hfun : (fun x => (1 / 2) * T x + (1 / 2) * T (flip x h u)) = F := by
    funext x
    dsimp [T]
    rw [hF, readsAxisPast_flip_later h u u hf (le_refl _) x, digit_flip_self]
    ring
  rw [hfun] at hm
  linarith

theorem densityPrefix_flip {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (k : Fin N)
    (hf : ∀ u, ReadsAxisPast h u (f u)) (x : SignCube D N) :
    densityPrefix h f k.val (flip x h k) = densityPrefix h f k.val x := by
  apply Finset.prod_congr rfl
  intro u hu
  have huk : u.val < k.val := (Finset.mem_filter.mp hu).2
  have hne : u ≠ k := by intro heq; subst u; exact (Nat.lt_irrefl k.val) huk
  rw [digit_flip_of_depth_ne x h h k u hne,
    readsAxisPast_flip_later h u k (hf u) (le_of_lt huk) x]

theorem densityPrefix_succ {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (k : ℕ) (hk : k < N) (x : SignCube D N) :
    densityPrefix h f (k + 1) x =
      densityPrefix h f k x * (1 + digit x h ⟨k, hk⟩ * f ⟨k, hk⟩ x) := by
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
  unfold densityPrefix
  rw [hset, Finset.prod_insert hnot, mul_comm]

/-- Integrating future signs removes the future density factors exactly. -/
theorem density_test_restriction {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hf : ∀ u, ReadsAxisPast h u (f u))
    (G : SignCube D N → ℝ) (t : ℕ)
    (hG : ∀ k : Fin N, t ≤ k.val → ∀ x, G (flip x h k) = G x) :
    ∀ k : ℕ, t ≤ k → k ≤ N →
      mean (fairCubeLaw D N) (fun x => densityPrefix h f k x * G x) =
        mean (fairCubeLaw D N) (fun x => densityPrefix h f t x * G x) := by
  intro k
  induction k with
  | zero =>
    intro ht hk
    have htzero : t = 0 := Nat.eq_zero_of_le_zero ht
    subst t
    rfl
  | succ k ih =>
    intro ht hk
    by_cases htk : t ≤ k
    · have hklt : k < N := Nat.lt_of_succ_le hk
      have hstep := fair_linear_step h ⟨k, hklt⟩
        (fun x => densityPrefix h f k x * G x) (f ⟨k, hklt⟩)
        (fun x => by
          rw [densityPrefix_flip h f ⟨k, hklt⟩ hf, hG ⟨k, hklt⟩ htk x])
        (hf ⟨k, hklt⟩)
      have heq : (fun x => densityPrefix h f (k + 1) x * G x) =
          (fun x => (densityPrefix h f k x * G x) *
            (1 + digit x h ⟨k, hklt⟩ * f ⟨k, hklt⟩ x)) := by
        funext x
        rw [densityPrefix_succ h f k hklt]
        ring
      rw [heq, hstep]
      exact ih htk (Nat.le_of_lt hklt)
    · have hteq : t = k + 1 := by omega
      rw [hteq]

theorem densityPrefix_mean_one {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hf : ∀ u, ReadsAxisPast h u (f u)) :
    mean (fairCubeLaw D N) (densityPrefix h f N) = 1 := by
  have h := density_test_restriction h f hf (fun _ => 1) 0
    (fun _ _ _ => rfl) N (Nat.zero_le _) (le_refl _)
  simpa [densityPrefix, mean, (fairCubeLaw D N).total] using h

theorem biasFactor_positive {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hsmall : ∀ u x, |f u x| < 1)
    (u : Fin N) (x : SignCube D N) : 0 < 1 + digit x h u * f u x := by
  have hlo := (abs_lt.mp (hsmall u x)).1
  have hhi := (abs_lt.mp (hsmall u x)).2
  cases hb : x.transverse h u <;> norm_num [digit, sign, hb] <;> linarith

theorem densityPrefix_positive {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hsmall : ∀ u x, |f u x| < 1)
    (k : ℕ) (x : SignCube D N) : 0 < densityPrefix h f k x :=
  Finset.prod_pos (fun u _ => biasFactor_positive h f hsmall u x)

noncomputable def tiltedLaw {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hf : ∀ u, ReadsAxisPast h u (f u))
    (hsmall : ∀ u x, |f u x| < 1) : PositiveLaw (SignCube D N) where
  mass x := (fairCubeLaw D N).mass x * densityPrefix h f N x
  positive x := mul_pos ((fairCubeLaw D N).positive x) (densityPrefix_positive h f hsmall N x)
  total := densityPrefix_mean_one h f hf

theorem tilted_mean_density {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hf : ∀ u, ReadsAxisPast h u (f u))
    (hsmall : ∀ u x, |f u x| < 1) (G : SignCube D N → ℝ) :
    mean (tiltedLaw h f hf hsmall) G =
      mean (fairCubeLaw D N) (fun x => densityPrefix h f N x * G x) := by
  unfold mean tiltedLaw
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem fair_mean_digit_zero {D N : ℕ} (h : Fin D) (u : Fin N)
    (G : SignCube D N → ℝ) (hG : ∀ x, G (flip x h u) = G x) :
    mean (fairCubeLaw D N) (fun x => digit x h u * G x) = 0 := by
  let T := fun x => digit x h u * G x
  have hflip := fair_mean_flip T h u
  have heq : (fun x => T (flip x h u)) = (fun x => (-1) * T x + 0 * T x) := by
    funext x
    dsimp [T]
    rw [digit_flip_self, hG]
    ring
  rw [heq, mean_linear] at hflip
  linarith

/-- The exact conditional-mean/score identity, expressed with finite test functions. -/
theorem tilted_score_identity {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hf : ∀ u, ReadsAxisPast h u (f u))
    (hsmall : ∀ u x, |f u x| < 1) (u : Fin N)
    (G : SignCube D N → ℝ) (hG : ReadsAxisPast h u G) :
    mean (tiltedLaw h f hf hsmall) (fun x => digit x h u * G x) =
      mean (tiltedLaw h f hf hsmall) (fun x => f u x * G x) := by
  have hleft := density_test_restriction h f hf (fun x => digit x h u * G x) (u.val + 1)
    (fun k hk x => by
      have huk : u.val < k.val := by omega
      have hne : u ≠ k := by intro heq; subst u; exact (Nat.lt_irrefl k.val) huk
      rw [digit_flip_of_depth_ne x h h k u hne,
        readsAxisPast_flip_later h u k hG (le_of_lt huk) x])
    N (Nat.succ_le_of_lt u.isLt) (le_refl N)
  have hright := density_test_restriction h f hf (fun x => f u x * G x) u.val
    (fun k hk x => by
      rw [readsAxisPast_flip_later h u k (hf u) hk x,
        readsAxisPast_flip_later h u k hG hk x]) N (Nat.le_of_lt u.isLt) (le_refl N)
  have hzero := fair_mean_digit_zero h u (fun x => densityPrefix h f u.val x * G x)
    (fun x => by
      rw [densityPrefix_flip h f u hf,
        readsAxisPast_flip_later h u u hG (le_refl _) x])
  rw [tilted_mean_density, tilted_mean_density, hleft, hright]
  have hfun : (fun x => densityPrefix h f (u.val + 1) x * (digit x h u * G x)) =
      (fun x => digit x h u * (densityPrefix h f u.val x * G x) +
        densityPrefix h f u.val x * (f u x * G x)) := by
    funext x
    rw [densityPrefix_succ h f u.val u.isLt]
    have heq : (⟨u.val, u.isLt⟩ : Fin N) = u := Fin.ext rfl
    rw [heq]
    calc
      _ = digit x h u * (densityPrefix h f u.val x * G x) +
          (digit x h u * digit x h u) * (densityPrefix h f u.val x * (f u x * G x)) := by ring
      _ = _ := by rw [digit_sq, one_mul]
  rw [hfun]
  have hm := mean_linear (fairCubeLaw D N) 1 1
    (fun x => digit x h u * (densityPrefix h f u.val x * G x))
    (fun x => densityPrefix h f u.val x * (f u x * G x))
  simpa [hzero] using hm

theorem tilted_log_likelihood {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hf : ∀ u, ReadsAxisPast h u (f u))
    (hsmall : ∀ u x, |f u x| < 1) (x : SignCube D N) :
    Real.log ((tiltedLaw h f hf hsmall).mass x / (fairCubeLaw D N).mass x) =
      ∑ u, Real.log (1 + digit x h u * f u x) := by
  have hmass : (fairCubeLaw D N).mass x ≠ 0 := ((fairCubeLaw D N).positive x).ne'
  change Real.log ((fairCubeLaw D N).mass x * densityPrefix h f N x /
    (fairCubeLaw D N).mass x) = _
  rw [mul_div_cancel_left₀ _ hmass]
  unfold densityPrefix
  have hset : Finset.univ.filter (fun u : Fin N => u.val < N) = Finset.univ := by ext u; simp
  rw [hset, Real.log_prod]
  intro u hu
  exact (biasFactor_positive h f hsmall u x).ne'

theorem tilted_information_budget {D N : ℕ} (h : Fin D)
    (f : Fin N → SignCube D N → ℝ) (hf : ∀ u, ReadsAxisPast h u (f u))
    (hsmall : ∀ u x, |f u x| < 1) (V : ℝ)
    (henergy : ∀ x, ∑ u, (f u x) ^ 2 ≤ V) :
    relativeEntropy (tiltedLaw h f hf hsmall) (fairCubeLaw D N) ≤ V := by
  apply information_budget_from_score (tiltedLaw h f hf hsmall) (fairCubeLaw D N)
    (fun u x => digit x h u) f V
  · exact biasFactor_positive h f hsmall
  · exact tilted_log_likelihood h f hf hsmall
  · intro u
    simpa only [sq] using tilted_score_identity h f hf hsmall u (f u) (hf u)
  · exact henergy

end HaarQuarter
