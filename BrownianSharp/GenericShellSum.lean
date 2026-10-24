import BrownianSharp.NativeShellSum

open scoped BigOperators

namespace BrownianSharp

/-- A covariance kernel restricted to a deterministic good-row predicate,
extended by zero to the complete midpoint pair grid. -/
noncomputable def genericGoodPairKernelGrid {d n : ℕ} (p : ℕ)
    (good : MidpointGridIndex d n → Prop)
    (rho : MidpointGridIndex d n → MidpointGridIndex d n → ℝ)
    (x : MidpointPairGrid d n) : ℝ := by
  classical
  exact if good (fun i => (x i).1) ∧ good (fun i => (x i).2) then
    highPowerPairKernel p (rho (fun i => (x i).1) (fun i => (x i).2)) else 0

/-- The high-power kernel is monotone with respect to an absolute-value
correlation cap; this form does not assume covariance nonnegativity. -/
theorem highPowerPairKernel_le_of_abs_le {p : ℕ} {rho R : ℝ}
    (hab : |rho| ≤ R) (hR : 0 ≤ R) :
    highPowerPairKernel p rho ≤
      4 * (p : ℝ) ^ 2 * R ^ 2 * Real.exp (2 * (p : ℝ) * R) := by
  have hsq : rho ^ 2 ≤ R ^ 2 := by
    have hgap : 0 ≤ R - |rho| := sub_nonneg.mpr hab
    have hsum : 0 ≤ R + |rho| := by positivity
    have hmul := mul_nonneg hgap hsum
    have hsquare : |rho| ^ 2 = rho ^ 2 := sq_abs rho
    nlinarith
  have hexp : Real.exp (2 * (p : ℝ) * |rho|) ≤
      Real.exp (2 * (p : ℝ) * R) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hab (by positivity)
  unfold highPowerPairKernel
  calc
    4 * (p : ℝ) ^ 2 * rho ^ 2 * Real.exp (2 * (p : ℝ) * |rho|) ≤
        4 * (p : ℝ) ^ 2 * rho ^ 2 * Real.exp (2 * (p : ℝ) * R) := by
          exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ ≤ 4 * (p : ℝ) ^ 2 * R ^ 2 * Real.exp (2 * (p : ℝ) * R) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left hsq (by positivity)

/-- On an exact shell with total common-prefix grade `n+h`, the good-pair
high-power kernel inherits the same weak-composition count and geometric
decay as the native covariance. The only analytic input is the explicit
absolute-correlation cap on good rows. -/
theorem genericGoodPairKernelGrid_shell_sum_mul_pow_le {d n h p : ℕ}
    (hd : 0 < d) (hD : 2 ≤ d) (hn : 0 < n) {L κ : ℝ}
    (hL : 0 < L)
    (hκ : κ ≤ Real.log 2 / (4 * L * (Nat.factorial (d - 1) : ℝ)))
    (hp : (p : ℝ) ≤ κ * ((n : ℝ) + 1))
    (good : MidpointGridIndex d n → Prop)
    (rho : MidpointGridIndex d n → MidpointGridIndex d n → ℝ)
    (hcap : ∀ q q', good q → good q' →
      midpointCommonPrefixGrade (fun i => (q i, q' i)) = n + h →
      |rho q q'| ≤ shapeOverlapCap d n h L) :
    (∑ x : midpointPairShell (d := d) (n := n) (n + h),
      genericGoodPairKernelGrid p good rho x.1) * (2 ^ (n + h) : ℝ) ≤
      (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) *
        (4 * (p : ℝ) ^ 2 *
          (L * (Nat.factorial (d - 1) : ℝ) *
            (((h : ℝ) + 1) / ((n : ℝ) + 1)) ^ (d - 1)) ^ 2 *
          Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ))) := by
  let Pcap : ℝ := L * (Nat.factorial (d - 1) : ℝ) *
    (((h : ℝ) + 1) / ((n : ℝ) + 1)) ^ (d - 1)
  have hPcap : shapeOverlapCap d n h L ≤ Pcap := by
    dsimp [Pcap]
    exact shapeOverlapCap_le_polynomial (by omega) n h hL.le
  have hPcap0 : 0 ≤ Pcap := by positivity
  have hdecay := shapeOverlapCap_shell_decay_condition
    (d := d) (n := n) (h := h) (p := p) hD hn hL hκ hp
  have hExp : Real.exp (2 * (p : ℝ) * shapeOverlapCap d n h L) ≤
      Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ)) :=
    Real.exp_le_exp.mpr hdecay
  apply midpointPairShell_sum_mul_pow_le hd _
    (4 * (p : ℝ) ^ 2 * Pcap ^ 2 *
      Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ))) (by positivity)
  intro x
  let q : MidpointGridIndex d n := fun i => (x.1 i).1
  let q' : MidpointGridIndex d n := fun i => (x.1 i).2
  have hgrade : midpointCommonPrefixGrade (fun i => (q i, q' i)) = n + h := by
    simpa [q, q', midpointCommonPrefixGrade] using x.2
  by_cases hg : good q ∧ good q'
  · simp [genericGoodPairKernelGrid, q, q', hg]
    have hab := hcap q q' hg.1 hg.2 hgrade
    have hR0 : 0 ≤ shapeOverlapCap d n h L :=
      shapeOverlapCap_nonneg (by omega) n h hL.le
    have hkernel := highPowerPairKernel_le_of_abs_le (p := p) hab hR0
    have hkernel' : highPowerPairKernel p
        (rho (fun i => (x.1 i).1) (fun i => (x.1 i).2)) ≤
        4 * (p : ℝ) ^ 2 * (shapeOverlapCap d n h L) ^ 2 *
          Real.exp (2 * (p : ℝ) * shapeOverlapCap d n h L) := by
      simpa [q, q'] using hkernel
    have hRsq : (shapeOverlapCap d n h L) ^ 2 ≤ Pcap ^ 2 := by nlinarith
    calc
      _ ≤ 4 * (p : ℝ) ^ 2 * Pcap ^ 2 *
          Real.exp (2 * (p : ℝ) * shapeOverlapCap d n h L) := by
        calc
          _ ≤ 4 * (p : ℝ) ^ 2 * (shapeOverlapCap d n h L) ^ 2 *
              Real.exp (2 * (p : ℝ) * shapeOverlapCap d n h L) := hkernel'
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
            exact mul_le_mul_of_nonneg_left hRsq (by positivity)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hExp
        positivity
  · simp [genericGoodPairKernelGrid, q, q', hg]
    positivity

/-- Exact finite-shell decomposition for an arbitrary good-pair covariance
kernel extended by zero. -/
theorem genericGoodPairKernelGrid_sum_eq_shells {d n p : ℕ}
    (good : MidpointGridIndex d n → Prop)
    (rho : MidpointGridIndex d n → MidpointGridIndex d n → ℝ) :
    (∑ x : MidpointPairGrid d n, genericGoodPairKernelGrid p good rho x) =
      ∑ u : Fin (d * (n + 1) + 1),
        ∑ x : midpointPairShell (d := d) (n := n) u.val,
          genericGoodPairKernelGrid p good rho x.1 := by
  classical
  exact midpointPairGrid_sum_eq_shell_sums
    (fun x => genericGoodPairKernelGrid p good rho x)

/-- Below layer grade, the generic restricted kernel vanishes whenever the
correlation has the common-prefix support property. -/
theorem genericGoodPairKernelGrid_shell_eq_zero_of_grade_lt {d n u p : ℕ}
    (good : MidpointGridIndex d n → Prop)
    (rho : MidpointGridIndex d n → MidpointGridIndex d n → ℝ)
    (hbelow : ∀ q q', good q → good q' →
      midpointCommonPrefixGrade (fun i => (q i, q' i)) < n → rho q q' = 0)
    (x : midpointPairShell (d := d) (n := n) u) (hu : u < n) :
    genericGoodPairKernelGrid p good rho x.1 = 0 := by
  let q : MidpointGridIndex d n := fun i => (x.1 i).1
  let q' : MidpointGridIndex d n := fun i => (x.1 i).2
  have hgrade : midpointCommonPrefixGrade (fun i => (q i, q' i)) = u := by
    simpa [q, q', midpointCommonPrefixGrade] using x.2
  by_cases hg : good q ∧ good q'
  · have hzero := hbelow q q' hg.1 hg.2 (by rw [hgrade]; exact hu)
    simp [genericGoodPairKernelGrid, q, q', hg, hzero, highPowerPairKernel]
  · simp [genericGoodPairKernelGrid, q, q', hg]

/-- Summed generic good-pair kernel bound. The lower shells vanish by the
support premise and the upper shells are controlled by the same explicit
polynomial-geometric budget as the native case. -/
theorem genericGoodPairKernelGrid_sum_le_budget {d n p : ℕ} {L κ : ℝ}
    (hd : 0 < d) (hD : 2 ≤ d) (hn : 0 < n) (hL : 0 < L)
    (hκ : κ ≤ Real.log 2 / (4 * L * (Nat.factorial (d - 1) : ℝ)))
    (hp : (p : ℝ) ≤ κ * ((n : ℝ) + 1))
    (good : MidpointGridIndex d n → Prop)
    (rho : MidpointGridIndex d n → MidpointGridIndex d n → ℝ)
    (hbelow : ∀ q q', good q → good q' →
      midpointCommonPrefixGrade (fun i => (q i, q' i)) < n → rho q q' = 0)
    (hcap : ∀ h q q', good q → good q' →
      midpointCommonPrefixGrade (fun i => (q i, q' i)) = n + h →
      |rho q q'| ≤ shapeOverlapCap d n h L) :
    (∑ x : MidpointPairGrid d n, genericGoodPairKernelGrid p good rho x) ≤
      nativeGoodPairKernelBudgetConstant d n p L * shellPolynomialBudget (d - 1) := by
  classical
  let f : Fin (d * (n + 1) + 1) → ℝ := fun u =>
    ∑ x : midpointPairShell (d := d) (n := n) u.val,
      genericGoodPairKernelGrid p good rho x.1
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun u : Fin (d * (n + 1) + 1) => n ≤ u.val) f
  have hlow :
      (∑ u : {u : Fin (d * (n + 1) + 1) // ¬ n ≤ u.val}, f u.1) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    dsimp [f]
    apply Finset.sum_eq_zero
    intro x hx
    exact genericGoodPairKernelGrid_shell_eq_zero_of_grade_lt
      good rho hbelow x (by omega)
  have hhigh :
      (∑ u : nativeHighGoodShellIndex d n, f u.1) ≤
        ∑ u : nativeHighGoodShellIndex d n,
          nativeGoodPairShellBudgetTerm d n (u.1.val - n) p L := by
    apply Finset.sum_le_sum
    intro u hu
    let h := u.1.val - n
    have hgrade : n + h = u.1.val := Nat.add_sub_of_le u.2
    have hshell := genericGoodPairKernelGrid_shell_sum_mul_pow_le
      (d := d) (n := n) (h := h) (p := p) hd hD hn hL hκ hp good rho (hcap h)
    have hden : 0 < (2 : ℝ) ^ (n + h) := by positivity
    change (∑ x : midpointPairShell (d := d) (n := n) u.1.val,
      genericGoodPairKernelGrid p good rho x.1) ≤ _
    have hsumEq :
        (∑ x : midpointPairShell (d := d) (n := n) u.1.val,
          genericGoodPairKernelGrid p good rho x.1) =
        ∑ x : midpointPairShell (d := d) (n := n) (n + h),
          genericGoodPairKernelGrid p good rho x.1 := by
      let e : midpointPairShell (d := d) (n := n) (n + h) ≃
          midpointPairShell (d := d) (n := n) u.1.val :=
        Equiv.subtypeEquivRight (fun x => by rw [hgrade])
      symm
      exact Fintype.sum_equiv e
        (fun x => genericGoodPairKernelGrid p good rho x.1)
        (fun x => genericGoodPairKernelGrid p good rho x.1)
        (by intro x; dsimp [e, Equiv.subtypeEquivRight, Equiv.subtypeEquiv]; rfl)
    have henv :
        (∑ x : midpointPairShell (d := d) (n := n) u.1.val,
          genericGoodPairKernelGrid p good rho x.1) ≤
          nativeGoodPairShellEnvelope d n h p L := by
      rw [hsumEq]
      rw [nativeGoodPairShellEnvelope]
      apply (le_div_iff₀ hden).2
      simpa [nativeGoodPairShellEnvelope] using hshell
    exact henv.trans (nativeGoodPairShellEnvelope_le_budgetTerm (by omega) L)
  let N := d * (n + 1) - n
  let H := d * (n + 1) - n + 1
  let q := d - 1
  let e := nativeHighGoodShellIndexEquiv d n hd hn
  have hreindex :
      (∑ u : nativeHighGoodShellIndex d n,
        nativeGoodPairShellBudgetTerm d n (u.1.val - n) p L) =
      ∑ h : Fin H, nativeGoodPairShellBudgetTerm d n h.val p L := by
    unfold H
    exact Fintype.sum_equiv e
      (fun u : nativeHighGoodShellIndex d n =>
        nativeGoodPairShellBudgetTerm d n (u.1.val - n) p L)
      (fun h : Fin (d * (n + 1) - n + 1) =>
        nativeGoodPairShellBudgetTerm d n h.val p L)
      (by intro u; rfl)
  have hfin :
      (∑ h : Fin H, nativeGoodPairShellBudgetTerm d n h.val p L) =
      ∑ h ∈ Finset.range (N + 1),
        nativeGoodPairKernelBudgetConstant d n p L *
          ((h + 1 : ℝ) ^ (3 * q) * (Real.sqrt (1 / 2 : ℝ)) ^ h) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro h hh
    simp [nativeGoodPairShellBudgetTerm, nativeGoodPairKernelBudgetConstant,
      N, H, q]
    ring
  have hpartial :
      (∑ h ∈ Finset.range (N + 1),
        ((h + 1 : ℝ) ^ (3 * q)) *
          (Real.sqrt (1 / 2 : ℝ)) ^ h) ≤ shellPolynomialBudget q :=
    shellPolynomial_partial_le_budget q N
  have hseries :
      (∑ h ∈ Finset.range (N + 1),
        nativeGoodPairKernelBudgetConstant d n p L *
          ((h + 1 : ℝ) ^ (3 * q) * (Real.sqrt (1 / 2 : ℝ)) ^ h)) ≤
      nativeGoodPairKernelBudgetConstant d n p L * shellPolynomialBudget q := by
    calc
      _ = nativeGoodPairKernelBudgetConstant d n p L *
          (∑ h ∈ Finset.range (N + 1),
            ((h + 1 : ℝ) ^ (3 * q)) *
              (Real.sqrt (1 / 2 : ℝ)) ^ h) := by rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpartial (by
        dsimp [nativeGoodPairKernelBudgetConstant]
        positivity)
  rw [genericGoodPairKernelGrid_sum_eq_shells]
  calc
    _ = (∑ u : {u : Fin (d * (n + 1) + 1) // n ≤ u.val}, f u.1) +
        ∑ u : {u : Fin (d * (n + 1) + 1) // ¬ n ≤ u.val}, f u.1 := hsplit.symm
    _ = ∑ u : nativeHighGoodShellIndex d n, f u.1 := by
      rw [hlow, add_zero]
      rfl
    _ ≤ _ := hhigh
    _ = ∑ h : Fin H, nativeGoodPairShellBudgetTerm d n h.val p L := hreindex
    _ = _ := hfin
    _ ≤ _ := hseries

/-- A generic good-row set, requiring no particular variance definition. -/
noncomputable def GenericGoodRows {d n : ℕ}
    (good : MidpointGridIndex d n → Prop) :=
  {q : MidpointGridIndex d n // good q}

noncomputable instance genericGoodRowsFintype {d n : ℕ}
    (good : MidpointGridIndex d n → Prop) : Fintype (GenericGoodRows good) := by
  letI : Finite (GenericGoodRows good) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  exact Fintype.ofFinite _

/-- Ordered pairs drawn from a generic good-row set. -/
abbrev GenericGoodPair {d n : ℕ} (good : MidpointGridIndex d n → Prop) :=
  GenericGoodRows good × GenericGoodRows good

noncomputable def genericGoodPairAsGrid {d n : ℕ}
    {good : MidpointGridIndex d n → Prop} (x : GenericGoodPair good) :
    MidpointPairGrid d n := fun i => (x.1.1 i, x.2.1 i)

noncomputable def genericGoodPairGridEquiv {d n : ℕ}
    (good : MidpointGridIndex d n → Prop) :
    GenericGoodPair good ≃ {x : MidpointPairGrid d n //
      good (fun i => (x i).1) ∧ good (fun i => (x i).2)} where
  toFun x := ⟨genericGoodPairAsGrid x, x.1.2, x.2.2⟩
  invFun x :=
    (⟨fun i => (x.1 i).1, x.2.1⟩, ⟨fun i => (x.1 i).2, x.2.2⟩)
  left_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      funext i
      rfl
    · apply Subtype.ext
      funext i
      rfl
  right_inv x := by
    apply Subtype.ext
    funext i
    exact Prod.ext rfl rfl

/-- The pair sum over actual good rows is exactly the full midpoint-grid sum
of the kernel extended by zero outside the good-pair set. -/
theorem genericGoodPairKernel_sum_eq_grid {d n p : ℕ}
    (good : MidpointGridIndex d n → Prop)
    (rho : MidpointGridIndex d n → MidpointGridIndex d n → ℝ) :
    (∑ x : GenericGoodPair good, highPowerPairKernel p (rho x.1.1 x.2.1)) =
      ∑ x : MidpointPairGrid d n, genericGoodPairKernelGrid p good rho x := by
  classical
  letI := genericGoodRowsFintype good
  let f : MidpointPairGrid d n → ℝ := genericGoodPairKernelGrid p good rho
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun x : MidpointPairGrid d n =>
      good (fun i => (x i).1) ∧ good (fun i => (x i).2)) f
  have hout :
      (∑ x : {x : MidpointPairGrid d n //
        ¬ (good (fun i => (x i).1) ∧ good (fun i => (x i).2))}, f x.1) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    dsimp [f, genericGoodPairKernelGrid]
    simp [x.2]
  have hequiv :
      (∑ x : GenericGoodPair good,
        highPowerPairKernel p (rho x.1.1 x.2.1)) =
        ∑ x : {x : MidpointPairGrid d n //
          good (fun i => (x i).1) ∧ good (fun i => (x i).2)}, f x.1 := by
    exact Fintype.sum_equiv (genericGoodPairGridEquiv good)
      (fun x => highPowerPairKernel p (rho x.1.1 x.2.1))
      (fun x => f x.1) (by
        intro x
        have hfirst : good x.1.1 := x.1.2
        have hsecond : good x.2.1 := x.2.2
        change highPowerPairKernel p (rho x.1.1 x.2.1) =
          genericGoodPairKernelGrid p good rho (genericGoodPairAsGrid x)
        simp [genericGoodPairKernelGrid, genericGoodPairAsGrid, hfirst, hsecond])
  calc
    _ = ∑ x : {x : MidpointPairGrid d n //
        good (fun i => (x i).1) ∧ good (fun i => (x i).2)}, f x.1 := hequiv
    _ = ∑ x : MidpointPairGrid d n, f x := by
      rw [← hsplit, hout, add_zero]

end BrownianSharp
