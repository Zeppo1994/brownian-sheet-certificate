import BrownianSharp.Alignment

/-!
# Local recovery and orthogonality of legal tensor Haar coefficients

Coefficients may depend on all strictly earlier digits in their own profile.
A positive-probability prefix cell recovers each coefficient without any
assumption on its size. Distinct profiles are orthogonal by first escape.
-/

open scoped BigOperators

namespace HaarQuarter

theorem prefixAgreement_refl {D N : ℕ} (l : ℕ) (v : Profile D)
    (x : SignCube D N) : PrefixAgreement l v x x :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem prefixAgreement_symm {D N : ℕ} {l : ℕ} {v : Profile D}
    {x y : SignCube D N} (hxy : PrefixAgreement l v x y) :
    PrefixAgreement l v y x :=
  ⟨fun k hk => (hxy.1 k hk).symm, fun a k hk => (hxy.2 a k hk).symm⟩

theorem prefixAgreement_trans {D N : ℕ} {l : ℕ} {v : Profile D}
    {x y z : SignCube D N} (hxy : PrefixAgreement l v x y)
    (hyz : PrefixAgreement l v y z) : PrefixAgreement l v x z :=
  ⟨fun k hk => (hxy.1 k hk).trans (hyz.1 k hk),
    fun a k hk => (hxy.2 a k hk).trans (hyz.2 a k hk)⟩

theorem fair_mean_eq_zero_of_flip {D N : ℕ} (F : SignCube D N → ℝ)
    (h : Fin D) (u : Fin N) (hodd : ∀ x, F (flip x h u) = -F x) :
    mean (fairCubeLaw D N) F = 0 := by
  have hm := fair_mean_flip F h u
  have hf : (fun x => F (flip x h u)) = (fun x => -F x) := funext hodd
  rw [hf] at hm
  have hn : mean (fairCubeLaw D N) (fun x => -F x) = -mean (fairCubeLaw D N) F := by
    unfold mean
    simp_rw [mul_neg]
    rw [Finset.sum_neg_distrib]
  rw [hn] at hm
  linarith

theorem fair_interaction_orthogonal {D N : ℕ} (F G : SignCube D N → ℝ)
    (v t : BoundedProfile D N)
    (hF : LegalCoefficient 0 (naturalProfile v) F)
    (hG : LegalCoefficient 0 (naturalProfile t) G) (hne : v ≠ t) :
    mean (fairCubeLaw D N) (interaction F G v t) = 0 := by
  have hn : naturalProfile v ≠ naturalProfile t :=
    fun heq => hne (naturalProfile_injective heq)
  by_cases hgrade : grade (naturalProfile t) ≤ grade (naturalProfile v)
  · obtain ⟨h, hh⟩ := exists_firstEscape hgrade hn
    apply fair_mean_eq_zero_of_flip _ h (v h)
    intro x
    rw [interaction_factor, interaction_factor]
    exact escapingInteraction_flip 0 F G v t h hF hG hh x
  · obtain ⟨h, hh⟩ := exists_firstEscape
      (le_of_lt (lt_of_not_ge hgrade)) hn.symm
    have hswap : interaction F G v t = interaction G F t v := by
      funext x
      unfold interaction
      ring
    rw [hswap]
    apply fair_mean_eq_zero_of_flip _ h (t h)
    intro x
    rw [interaction_factor, interaction_factor]
    exact escapingInteraction_flip 0 G F t v h hG hF hh x

theorem profileWord_abs {D N : ℕ} (x : SignCube D N) (v : BoundedProfile D N) :
    |profileWord x v| = 1 := by
  have hs := profileWord_sq x v
  have ha : |profileWord x v| * |profileWord x v| = 1 := by
    rw [← abs_mul, hs, abs_one]
  nlinarith [abs_nonneg (profileWord x v)]

theorem fair_tensorTerm_mean_zero {D N : ℕ} (hD : 0 < D)
    (F : SignCube D N → ℝ) (v : BoundedProfile D N)
    (hF : LegalCoefficient 0 (naturalProfile v) F) :
    mean (fairCubeLaw D N) (fun x => F x * profileWord x v) = 0 := by
  let h : Fin D := ⟨0, hD⟩
  apply fair_mean_eq_zero_of_flip _ h (v h)
  intro x
  rw [legalCoefficient_flip hF x h (v h) (le_refl _),
    profileWord_factor (flip x h (v h)) v h, digit_flip_self, erasedWord_flip,
    profileWord_factor x v h]
  ring

noncomputable def prefixCell {D N : ℕ} (v : BoundedProfile D N)
    (x y : SignCube D N) : ℝ := by
  classical
  exact if PrefixAgreement 0 (naturalProfile v) x y then 1 else 0

theorem prefixCell_nonneg {D N : ℕ} (v : BoundedProfile D N)
    (x y : SignCube D N) : 0 ≤ prefixCell v x y := by
  classical
  unfold prefixCell
  split_ifs <;> norm_num

theorem prefixCell_legal {D N : ℕ} (v : BoundedProfile D N)
    (x : SignCube D N) : LegalCoefficient 0 (naturalProfile v) (prefixCell v x) := by
  classical
  intro y z hyz
  have heq : PrefixAgreement 0 (naturalProfile v) x y ↔
      PrefixAgreement 0 (naturalProfile v) x z :=
    ⟨fun hxy => prefixAgreement_trans hxy hyz,
      fun hxz => prefixAgreement_trans hxz (prefixAgreement_symm hyz)⟩
  simp only [prefixCell, heq]

theorem prefixCell_mean_pos {D N : ℕ} (v : BoundedProfile D N)
    (x : SignCube D N) : 0 < mean (fairCubeLaw D N) (prefixCell v x) := by
  classical
  apply Finset.sum_pos'
  · intro y hy
    exact mul_nonneg (le_of_lt ((fairCubeLaw D N).positive y)) (prefixCell_nonneg v x y)
  · refine ⟨x, Finset.mem_univ x, ?_⟩
    simpa [prefixCell, prefixAgreement_refl] using (fairCubeLaw D N).positive x

noncomputable def tensorPolynomial {D N : ℕ} (c₀ : ℝ)
    (F : BoundedProfile D N → SignCube D N → ℝ) (x : SignCube D N) : ℝ :=
  c₀ + ∑ v, F v x * profileWord x v

theorem tensor_coefficient_recovery {D N : ℕ} (hD : 0 < D) (c₀ : ℝ)
    (F : BoundedProfile D N → SignCube D N → ℝ)
    (hF : ∀ v, LegalCoefficient 0 (naturalProfile v) (F v))
    (t : BoundedProfile D N) (x : SignCube D N) :
    mean (fairCubeLaw D N)
        (fun y => tensorPolynomial c₀ F y * profileWord y t * prefixCell t x y) =
      F t x * mean (fairCubeLaw D N) (prefixCell t x) := by
  classical
  have hsplit : (fun y => tensorPolynomial c₀ F y * profileWord y t * prefixCell t x y) =
      (fun y => c₀ * (prefixCell t x y * profileWord y t) +
        1 * ∑ v, interaction (F v) (prefixCell t x) v t y) := by
    funext y
    unfold tensorPolynomial interaction
    simp only [add_mul, Finset.sum_mul, Finset.mul_sum, one_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro v hv
      ring
  rw [hsplit, mean_linear, fair_tensorTerm_mean_zero hD _ t (prefixCell_legal t x),
    mul_zero, zero_add, one_mul, mean_sum]
  rw [Finset.sum_eq_single t]
  · have hdiag : interaction (F t) (prefixCell t x) t t =
        (fun y => F t x * prefixCell t x y) := by
      funext y
      rw [interaction_self]
      by_cases hxy : PrefixAgreement 0 (naturalProfile t) x y
      · rw [← hF t x y hxy]
      · simp [prefixCell, hxy]
    rw [hdiag]
    unfold mean
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  · intro v hv hvt
    exact fair_interaction_orthogonal _ _ v t (hF v) (prefixCell_legal t x) hvt
  · simp

theorem tensor_coefficient_bound {D N : ℕ} (hD : 0 < D) (c₀ K : ℝ)
    (F : BoundedProfile D N → SignCube D N → ℝ)
    (hF : ∀ v, LegalCoefficient 0 (naturalProfile v) (F v))
    (hbound : ∀ y, |tensorPolynomial c₀ F y| ≤ K)
    (t : BoundedProfile D N) (x : SignCube D N) : |F t x| ≤ K := by
  have hp := prefixCell_mean_pos t x
  have hrecovery := tensor_coefficient_recovery hD c₀ F hF t x
  have hest : |F t x| * mean (fairCubeLaw D N) (prefixCell t x) ≤
      K * mean (fairCubeLaw D N) (prefixCell t x) := by
    calc
      _ = |mean (fairCubeLaw D N)
          (fun y => tensorPolynomial c₀ F y * profileWord y t * prefixCell t x y)| := by
        rw [hrecovery, abs_mul, abs_of_pos hp]
      _ ≤ mean (fairCubeLaw D N)
          (fun y => |tensorPolynomial c₀ F y * profileWord y t * prefixCell t x y|) :=
        abs_mean_le_mean_abs _ _
      _ ≤ mean (fairCubeLaw D N) (fun y => K * prefixCell t x y) := by
        apply mean_mono
        intro y
        rw [abs_mul, abs_mul, profileWord_abs, mul_one,
          abs_of_nonneg (prefixCell_nonneg t x y)]
        exact mul_le_mul_of_nonneg_right (hbound y) (prefixCell_nonneg t x y)
      _ = _ := by
        unfold mean
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y hy
        ring
  exact (mul_le_mul_iff_left₀ hp).mp hest

theorem fair_tensorPolynomial_mean {D N : ℕ} (hD : 0 < D) (c₀ : ℝ)
    (F : BoundedProfile D N → SignCube D N → ℝ)
    (hF : ∀ v, LegalCoefficient 0 (naturalProfile v) (F v)) :
    mean (fairCubeLaw D N) (tensorPolynomial c₀ F) = c₀ := by
  have h := mean_linear (fairCubeLaw D N) 1 1 (fun _ => c₀)
    (fun x => ∑ v, F v x * profileWord x v)
  simp only [one_mul, mean_const, mean_sum,
    fair_tensorTerm_mean_zero hD _ _ (hF _), Finset.sum_const_zero, add_zero] at h
  exact h

theorem fair_tensorPolynomial_pairing {D N : ℕ} (hD : 0 < D) (c₀ : ℝ)
    (F : BoundedProfile D N → SignCube D N → ℝ)
    (hF : ∀ v, LegalCoefficient 0 (naturalProfile v) (F v))
    (t : BoundedProfile D N) :
    mean (fairCubeLaw D N) (fun x => tensorPolynomial c₀ F x * F t x * profileWord x t) =
      mean (fairCubeLaw D N) (fun x => (F t x) ^ 2) := by
  classical
  have hsplit : (fun x => tensorPolynomial c₀ F x * F t x * profileWord x t) =
      (fun x => c₀ * (F t x * profileWord x t) +
        1 * ∑ v, interaction (F v) (F t) v t x) := by
    funext x
    unfold tensorPolynomial interaction
    simp only [add_mul, Finset.sum_mul, one_mul]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro v hv
      ring
  rw [hsplit, mean_linear, fair_tensorTerm_mean_zero hD _ t (hF t),
    mul_zero, zero_add, one_mul, mean_sum, Finset.sum_eq_single t]
  · congr 1
    funext x
    rw [interaction_self, sq]
  · intro v hv hvt
    exact fair_interaction_orthogonal _ _ v t (hF v) (hF t) hvt
  · simp

theorem fair_tensor_parseval {D N : ℕ} (hD : 0 < D) (c₀ : ℝ)
    (F : BoundedProfile D N → SignCube D N → ℝ)
    (hF : ∀ v, LegalCoefficient 0 (naturalProfile v) (F v)) :
    mean (fairCubeLaw D N) (fun x => (tensorPolynomial c₀ F x) ^ 2) =
      c₀ ^ 2 + ∑ v, mean (fairCubeLaw D N) (fun x => (F v x) ^ 2) := by
  have hsplit : (fun x => (tensorPolynomial c₀ F x) ^ 2) =
      (fun x => c₀ * tensorPolynomial c₀ F x +
        1 * ∑ v, tensorPolynomial c₀ F x * F v x * profileWord x v) := by
    funext x
    simp only [one_mul, ← Finset.mul_sum, mul_assoc]
    change (tensorPolynomial c₀ F x) ^ 2 =
      c₀ * tensorPolynomial c₀ F x + tensorPolynomial c₀ F x *
        (∑ v, F v x * profileWord x v)
    have hp : tensorPolynomial c₀ F x = c₀ + ∑ v, F v x * profileWord x v := rfl
    rw [hp]
    ring
  rw [hsplit, mean_linear, fair_tensorPolynomial_mean hD c₀ F hF, one_mul, mean_sum]
  simp only [fair_tensorPolynomial_pairing hD c₀ F hF, sq]

end HaarQuarter
