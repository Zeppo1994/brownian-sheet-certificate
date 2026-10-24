import BrownianSharp.FiniteHaarGradeEnergy

/-! Cardinal bounds for the actual finite mixed-Haar index sets, including the
low-grade dictionary component used in the width assembly. -/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace BrownianSharp
open HaarQuarter

private def finiteHaarProfileAddress {d N : ℕ} (a : FiniteHaarIndex d N)
    (i : Fin d) : ℕ :=
  match a i with
  | none => 0
  | some ax => ax.2.val

private def finiteHaarProfileCode {d N : ℕ} (r : Fin d → ℕ)
    (a : FiniteHaarProfileFiber (N := N) r) : ∀ i, Fin (2 ^ r i) := fun i =>
  ⟨finiteHaarProfileAddress a.1 i, by
    cases ha : a.1 i with
    | none =>
        have hr : r i = 0 := by
          simpa [ha, finiteHaarAxisGrade] using (a.2 i).symm
        simp [finiteHaarProfileAddress, ha, hr]
    | some ax =>
        rcases ax with ⟨s, j⟩
        have hr : s.val + 1 = r i := by
          simpa [ha, finiteHaarAxisGrade] using a.2 i
        simp [finiteHaarProfileAddress, ha]
        rw [← hr, Nat.pow_succ]
        have hp : 1 ≤ 2 ^ s.val := Nat.one_le_two_pow
        omega⟩

private theorem finiteHaarProfileCode_injective {d N : ℕ} (r : Fin d → ℕ) :
    Function.Injective (finiteHaarProfileCode (N := N) r) := by
  intro a b h
  apply Subtype.ext
  funext i
  have haGrade := a.2 i
  have hbGrade := b.2 i
  cases ha : a.1 i with
  | none =>
    cases hb : b.1 i with
    | none => rfl
    | some bx =>
        rcases bx with ⟨t, k⟩
        simp [ha, hb, finiteHaarAxisGrade] at haGrade hbGrade
        omega
  | some ax =>
    rcases ax with ⟨s, j⟩
    cases hb : b.1 i with
    | none =>
        simp [ha, hb, finiteHaarAxisGrade] at haGrade hbGrade
        omega
    | some bx =>
        rcases bx with ⟨t, k⟩
        have hs : s.val + 1 = r i := by
          simpa [ha, finiteHaarAxisGrade] using haGrade
        have ht : t.val + 1 = r i := by
          simpa [hb, finiteHaarAxisGrade] using hbGrade
        have hjval : j.val = k.val := by
          have hcode := congrFun h i
          have hh := congrArg Fin.val hcode
          simpa [finiteHaarProfileCode, finiteHaarProfileAddress, ha, hb] using hh
        have hst : s.val = t.val := by omega
        have hse : s = t := Fin.ext hst
        cases hse
        have hje : j = k := Fin.ext hjval
        simp [ha, hb, hje]

theorem finiteHaarProfileFiber_card_le_pow {d N : ℕ}
    (r : Fin d → ℕ) :
    Fintype.card (FiniteHaarProfileFiber (N := N) r) ≤
      2 ^ (∑ i : Fin d, r i) := by
  classical
  have hinj := Fintype.card_le_of_injective
    (finiteHaarProfileCode (N := N) r) (finiteHaarProfileCode_injective r)
  calc
    Fintype.card (FiniteHaarProfileFiber (N := N) r) ≤
        Fintype.card (∀ i, Fin (2 ^ r i)) := hinj
    _ = ∏ i : Fin d, 2 ^ r i := by simp [Fintype.card_pi]
    _ = 2 ^ (∑ i : Fin d, r i) := by
      rw [Finset.prod_pow_eq_pow_sum]

private def finiteHaarGradeProfileOf {d N n : ℕ}
    (a : FiniteHaarGradeLayer d N n) : FiniteHaarGradeProfile d n :=
  ⟨fun i => finiteHaarAxisGrade (a.1 i), by
    simpa [finiteHaarGrade] using a.2⟩

private def finiteHaarGradeProfileEquiv {d N n : ℕ} :
    FiniteHaarGradeLayer d N n ≃
      Σ r : FiniteHaarGradeProfile d n, FiniteHaarProfileFiber (N := N) r.1 where
  toFun a := ⟨finiteHaarGradeProfileOf a, ⟨a.1, fun _ => rfl⟩⟩
  invFun p := ⟨p.2.1, by
    calc
      finiteHaarGrade p.2.1 = ∑ i : Fin d, finiteHaarAxisGrade (p.2.1 i) := by
        simp [finiteHaarGrade]
      _ = ∑ i : Fin d, p.1.1 i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact p.2.2 i
      _ = n := p.1.2⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨r, a⟩
    have hsum : finiteHaarGrade a.1 = n := by
      calc
        finiteHaarGrade a.1 = ∑ i : Fin d, finiteHaarAxisGrade (a.1 i) := by
          simp [finiteHaarGrade]
        _ = ∑ i : Fin d, r.1 i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact a.2 i
        _ = n := r.2
    let x : FiniteHaarGradeLayer d N n := ⟨a.1, hsum⟩
    have hr : finiteHaarGradeProfileOf x = r := by
      apply Subtype.ext
      funext i
      exact a.2 i
    apply Sigma.ext
    · change finiteHaarGradeProfileOf x = r
      exact hr
    · have hshape : ∀ i, (finiteHaarGradeProfileOf x).1 i = r.1 i := by
        intro i
        exact congrArg (fun z : FiniteHaarGradeProfile d n => z.1 i) hr
      have hnew : ∀ i, finiteHaarAxisGrade (x.1 i) =
          (finiteHaarGradeProfileOf x).1 i := by intro i; rfl
      change HEq (⟨x.1, hnew⟩ : FiniteHaarProfileFiber (N := N)
        (finiteHaarGradeProfileOf x).1) a
      apply (Subtype.heq_iff_coe_eq (fun b => by
        constructor
        · intro hb i
          change finiteHaarAxisGrade (b i) = r.1 i
          rw [← hshape i]
          exact hb i
        · intro hb i
          change finiteHaarAxisGrade (b i) = (finiteHaarGradeProfileOf x).1 i
          rw [hshape i]
          exact hb i)).2
      rfl

private def finiteHaarProfileShapeEquiv {d n : ℕ} :
    FiniteHaarGradeProfile d n ≃ Shape d n where
  toFun r := by
    refine ⟨Finsupp.equivFunOnFinite.symm r.1, ?_⟩
    apply Finset.mem_finsuppAntidiag'.2
    constructor
    · simpa [Finsupp.sum_fintype] using r.2
    · simp
  invFun r := ⟨fun i => r.1 i, by
    have h := (Finset.mem_finsuppAntidiag'.mp r.2).1
    simpa [Finsupp.sum_fintype] using h⟩
  left_inv r := by
    apply Subtype.ext
    rfl
  right_inv r := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    rfl

theorem finiteHaarGradeLayer_card_le {d N n : ℕ} (hd : 0 < d) :
    Fintype.card (FiniteHaarGradeLayer d N n) ≤
      2 ^ n * Nat.choose (n + d - 1) (d - 1) := by
  classical
  rw [Fintype.card_congr (finiteHaarGradeProfileEquiv (d := d) (N := N) (n := n)),
    Fintype.card_sigma]
  calc
    (∑ r : FiniteHaarGradeProfile d n,
      Fintype.card (FiniteHaarProfileFiber (N := N) r.1)) ≤
      ∑ _r : FiniteHaarGradeProfile d n, 2 ^ n := by
        apply Finset.sum_le_sum
        intro r hr
        exact finiteHaarProfileFiber_card_le_pow (N := N) r.1 |>.trans_eq
          (congrArg (fun k => 2 ^ k) r.2)
    _ = 2 ^ n * Nat.choose (n + d - 1) (d - 1) := by
      rw [Finset.sum_const, Finset.card_univ]
      have hcard := Fintype.card_congr (finiteHaarProfileShapeEquiv (d := d) (n := n))
      rw [hcard, shape_card d n hd]
      simp [Nat.mul_comm]

private theorem sum_two_pow_fin_eq (n : ℕ) :
    (∑ k : Fin n, 2 ^ k.val) = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero]
      simp only [Fin.val_succ]
      have hs : (∑ k : Fin n, 2 ^ (k.val + 1)) =
          (∑ k : Fin n, 2 ^ k.val) * 2 := by
        simp_rw [pow_succ]
        rw [Finset.sum_mul]
      rw [hs, ih]
      have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
      rw [hpow]
      let x : ℕ := 2 ^ n
      have hx : 1 ≤ x := by dsimp [x]; exact Nat.one_le_two_pow
      change 1 + (x - 1) * 2 = x * 2 - 1
      omega

private noncomputable def finiteHaarLowGradeEquiv {d N n₀ : ℕ} :
    {a : FiniteHaarIndex d N // finiteHaarGrade a < n₀} ≃
      Σ k : Fin n₀, FiniteHaarGradeLayer d N k.val where
  toFun a := ⟨⟨finiteHaarGrade a.1, a.2⟩, ⟨a.1, rfl⟩⟩
  invFun p := ⟨p.2.1, p.2.2.trans_lt p.1.isLt⟩
  left_inv a := by cases a; rfl
  right_inv p := by
    rcases p with ⟨k, a⟩
    apply Sigma.ext
    · change (⟨finiteHaarGrade a.1, a.2.trans_lt k.isLt⟩ : Fin n₀) = k
      apply Fin.ext
      exact a.2
    · change HEq
        (⟨a.1, rfl⟩ : {b : FiniteHaarIndex d N // finiteHaarGrade b =
          finiteHaarGrade a.1}) a
      apply (Subtype.heq_iff_coe_eq (fun b => by
        constructor
        · intro hb
          rw [← a.2]
          exact hb
        · intro hb
          rw [a.2]
          exact hb)).2
      rfl

theorem finiteHaarLowIndex_card_le {d N n₀ : ℕ} (hd : 0 < d) :
    Fintype.card {a : FiniteHaarIndex d N // finiteHaarGrade a < n₀} ≤
      2 ^ n₀ * Nat.choose (n₀ + d - 1) (d - 1) := by
  classical
  rw [Fintype.card_congr (finiteHaarLowGradeEquiv (d := d) (N := N) (n₀ := n₀)),
    Fintype.card_sigma]
  let S : ℕ := Nat.choose (n₀ + d - 1) (d - 1)
  have hchoose : ∀ k : Fin n₀,
      Nat.choose (k.val + d - 1) (d - 1) ≤ S := by
    intro k
    apply Nat.choose_le_choose
    have hk : k.val + d ≤ n₀ + d := Nat.add_le_add_right k.isLt.le d
    exact Nat.sub_le_sub_right hk 1
  calc
    (∑ k : Fin n₀, Fintype.card (FiniteHaarGradeLayer d N k.val)) ≤
        ∑ k : Fin n₀, 2 ^ k.val * S := by
      apply Finset.sum_le_sum
      intro k hk
      have hkcard := finiteHaarGradeLayer_card_le (d := d) (N := N) (n := k.val) hd
      have hpow : 2 ^ k.val ≤ 2 ^ k.val := le_rfl
      calc
        Fintype.card (FiniteHaarGradeLayer d N k.val) ≤
            2 ^ k.val * Nat.choose (k.val + d - 1) (d - 1) := hkcard
        _ ≤ 2 ^ k.val * S := Nat.mul_le_mul_left _ (hchoose k)
    _ = (∑ k : Fin n₀, 2 ^ k.val) * S := by rw [Finset.sum_mul]
    _ ≤ 2 ^ n₀ * S := Nat.mul_le_mul_right S (by
      rw [sum_two_pow_fin_eq]
      exact Nat.sub_le _ _)
    _ = 2 ^ n₀ * Nat.choose (n₀ + d - 1) (d - 1) := by rfl

end BrownianSharp
