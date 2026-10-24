import BrownianSharp.ShellDecay
import BrownianSharp.Moments

open scoped BigOperators

namespace BrownianSharp

/-- The variance scale naturally paired with the native row-covariance
coefficient bound. -/
noncomputable def nativeShellVarianceFloor (d n : ℕ) (L : ℝ) : ℝ :=
  (1 / (2 : ℝ) ^ (n + 2 * d)) * hyperbolicCount d n / L

/-- The rows on which the variance has the deterministic floor used to
normalize the Gaussian polynomial. -/
noncomputable def NativeGoodRows (d n : ℕ) (v₀ : ℝ) :=
  {q : MidpointGridIndex d n // v₀ ≤ nativeLayerRowVariance q}

noncomputable instance nativeGoodRowsFintype (d n : ℕ) (v₀ : ℝ) :
    Fintype (NativeGoodRows d n v₀) := by
  letI : Finite (NativeGoodRows d n v₀) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  exact Fintype.ofFinite _

/-- A good pair is an ordered pair of rows satisfying the same variance floor.
Its coordinates give an element of the midpoint pair grid. -/
abbrev NativeGoodPair (d n : ℕ) (v₀ : ℝ) :=
  NativeGoodRows d n v₀ × NativeGoodRows d n v₀

noncomputable def nativeGoodPairAsGrid {d n : ℕ} {v₀ : ℝ}
    (x : NativeGoodPair d n v₀) : MidpointPairGrid d n :=
  fun i => (x.1.1 i, x.2.1 i)

theorem nativeGoodPairAsGrid_injective {d n : ℕ} {v₀ : ℝ} :
    Function.Injective (nativeGoodPairAsGrid (d := d) (n := n) (v₀ := v₀)) := by
  intro x y h
  apply Prod.ext
  · apply Subtype.ext
    funext i
    exact congrArg Prod.fst (congrFun h i)
  · apply Subtype.ext
    funext i
    exact congrArg Prod.snd (congrFun h i)

/-- Good row pairs in a fixed exact common-prefix grade. -/
noncomputable def nativeGoodPairShell {d n u : ℕ} {v₀ : ℝ}
    : NativeGoodPair d n v₀ → Prop := fun x =>
    midpointCommonPrefixGrade (nativeGoodPairAsGrid x) = u

noncomputable instance nativeGoodPairShellFintype {d n u : ℕ} {v₀ : ℝ} :
    Fintype (Subtype (nativeGoodPairShell (d := d) (n := n) (u := u) (v₀ := v₀))) := by
  letI : Finite (Subtype (nativeGoodPairShell
      (d := d) (n := n) (u := u) (v₀ := v₀))) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  exact Fintype.ofFinite _

/-- Injecting a good shell into the full midpoint shell gives the same exact
weak-composition cardinal bound, independent of how the good set is chosen. -/
theorem nativeGoodPairShell_card_mul_pow_le {d n u : ℕ} {v₀ : ℝ}
    (hd : 0 < d) :
    Fintype.card (Subtype (nativeGoodPairShell
      (d := d) (n := n) (u := u) (v₀ := v₀))) * 2 ^ u ≤
      Nat.choose (u + d - 1) (d - 1) * Fintype.card (MidpointPairGrid d n) := by
  let e : Subtype (nativeGoodPairShell (d := d) (n := n) (u := u) (v₀ := v₀)) →
      midpointPairShell (d := d) (n := n) u := fun x =>
    ⟨nativeGoodPairAsGrid x.1, x.2⟩
  have hinj : Function.Injective e := by
    intro x y h
    apply Subtype.ext
    apply nativeGoodPairAsGrid_injective
    have hxy := congrArg Subtype.val h
    change nativeGoodPairAsGrid x.1 = nativeGoodPairAsGrid y.1 at hxy
    exact hxy
  have hcard : Fintype.card (Subtype (nativeGoodPairShell
      (d := d) (n := n) (u := u) (v₀ := v₀))) ≤
      Fintype.card (midpointPairShell (d := d) (n := n) u) :=
    Fintype.card_le_of_injective e hinj
  calc
    Fintype.card (Subtype (nativeGoodPairShell
        (d := d) (n := n) (u := u) (v₀ := v₀))) * 2 ^ u ≤
        Fintype.card (midpointPairShell (d := d) (n := n) u) * 2 ^ u :=
      Nat.mul_le_mul_right _ hcard
    _ ≤ Nat.choose (u + d - 1) (d - 1) * Fintype.card (MidpointPairGrid d n) :=
      midpointPairShell_card_mul_pow_le hd

/-- A bounded nonnegative observable on a good shell inherits the full-grid
shell-count estimate. -/
theorem nativeGoodPairShell_sum_mul_pow_le {d n u : ℕ} {v₀ : ℝ}
    (hd : 0 < d)
    (f : Subtype (nativeGoodPairShell (d := d) (n := n) (u := u) (v₀ := v₀)) → ℝ)
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ x, f x ≤ B) :
    (∑ x : Subtype (nativeGoodPairShell
      (d := d) (n := n) (u := u) (v₀ := v₀)), f x) * (2 ^ u : ℝ) ≤
      (Nat.choose (u + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) * B := by
  have hsum : (∑ x : Subtype
      (nativeGoodPairShell (d := d) (n := n) (u := u) (v₀ := v₀)), f x) ≤
      ((Fintype.card (Subtype (nativeGoodPairShell
        (d := d) (n := n) (u := u) (v₀ := v₀))) : ℝ) * B) := by
    calc
      _ ≤ ∑ _x : Subtype
          (nativeGoodPairShell (d := d) (n := n) (u := u) (v₀ := v₀)), B :=
        Finset.sum_le_sum (fun x _ => hf x)
      _ = _ := by simp
  have hcard := nativeGoodPairShell_card_mul_pow_le
    (d := d) (n := n) (u := u) (v₀ := v₀) hd
  have hcardR : (Fintype.card (Subtype (nativeGoodPairShell
      (d := d) (n := n) (u := u) (v₀ := v₀))) : ℝ) * (2 ^ u : ℝ) ≤
      (Nat.choose (u + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) := by
    exact_mod_cast hcard
  calc
    (∑ x : Subtype (nativeGoodPairShell
      (d := d) (n := n) (u := u) (v₀ := v₀)), f x) * (2 ^ u : ℝ) ≤
      ((Fintype.card (Subtype (nativeGoodPairShell
        (d := d) (n := n) (u := u) (v₀ := v₀))) : ℝ) * B) * (2 ^ u : ℝ) :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = ((Fintype.card (Subtype (nativeGoodPairShell
        (d := d) (n := n) (u := u) (v₀ := v₀))) : ℝ) * (2 ^ u : ℝ)) * B := by ring
    _ ≤ ((Nat.choose (u + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ)) * B :=
      mul_le_mul_of_nonneg_right hcardR hB
    _ = _ := by ring

/-- Exact-prefix shell decomposition of the good row-pair space. -/
private def nativeGoodPairShellSigma {d n : ℕ} {v₀ : ℝ} :=
  Σ u : Fin (d * (n + 1) + 1),
    Subtype (nativeGoodPairShell (d := d) (n := n) (u := u.val) (v₀ := v₀))

noncomputable def nativeGoodPairShellDecompositionEquiv {d n : ℕ} {v₀ : ℝ} :
    NativeGoodPair d n v₀ ≃ nativeGoodPairShellSigma (d := d) (n := n) (v₀ := v₀) where
  toFun x :=
    ⟨⟨midpointCommonPrefixGrade (nativeGoodPairAsGrid x),
      Nat.lt_succ_of_le (midpointCommonPrefixGrade_le (nativeGoodPairAsGrid x))⟩,
      ⟨x, rfl⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨u, ⟨x, hx⟩⟩
    have hidx : (⟨midpointCommonPrefixGrade (nativeGoodPairAsGrid x),
        Nat.lt_succ_of_le (midpointCommonPrefixGrade_le (nativeGoodPairAsGrid x))⟩ :
        Fin (d * (n + 1) + 1)) = u := Fin.ext hx
    subst u
    rfl

theorem nativeGoodPair_sum_eq_shell_sums {d n : ℕ} {v₀ : ℝ}
    (f : NativeGoodPair d n v₀ → ℝ) :
    (∑ x : NativeGoodPair d n v₀, f x) =
      ∑ u : Fin (d * (n + 1) + 1),
        ∑ x : Subtype
          (nativeGoodPairShell (d := d) (n := n) (u := u.val) (v₀ := v₀)),
          f x.1 := by
  classical
  letI : ∀ u : Fin (d * (n + 1) + 1),
      Fintype (Subtype (nativeGoodPairShell
        (d := d) (n := n) (u := u.val) (v₀ := v₀))) :=
    fun _ => nativeGoodPairShellFintype
  letI : Fintype (nativeGoodPairShellSigma (d := d) (n := n) (v₀ := v₀)) := by
    unfold nativeGoodPairShellSigma
    infer_instance
  rw [Fintype.sum_equiv nativeGoodPairShellDecompositionEquiv f
    (fun x => f x.2.1) (by intro x; rfl)]
  unfold nativeGoodPairShellSigma
  rw [Fintype.sum_sigma]

/-- A good-shell pair's native row correlation is bounded by the exact
weak-composition overlap cap, when the row variance floor is the native
coefficient scale divided by `L`. -/
theorem nativeGoodPairCorrelation_le_shapeCap {d n h : ℕ}
    (hd : 0 < d) (hn : 0 < n) {L : ℝ} (hL : 0 < L)
    (x : Subtype (nativeGoodPairShell (d := d) (n := n) (u := n + h)
      (v₀ := nativeShellVarianceFloor d n L))) :
    nativeRowCorrelation (x.1.1.1) (x.1.2.1) ≤ shapeOverlapCap d n h L := by
  let q : MidpointGridIndex d n := x.1.1.1
  let q' : MidpointGridIndex d n := x.1.2.1
  let v₀ := nativeShellVarianceFloor d n L
  let c := midpointCommonPrefixCaps q q'
  have hv₀ : 0 < v₀ := by
    dsimp [v₀, nativeShellVarianceFloor]
    have hSn : 0 < hyperbolicCount d n := hyperbolicCount_pos (by omega)
    positivity
  have hgrade : c.sum (fun _ z => z) = n + h := by
    have hxgrade := x.2
    change midpointCommonPrefixGrade (nativeGoodPairAsGrid x.1) = n + h at hxgrade
    simpa [c, q, q', midpointCommonPrefixGrade, nativeGoodPairAsGrid] using hxgrade
  have hp : MidpointCommonPrefixProfile q q' c := by
    simpa [c, q, q'] using midpointCommonPrefixCaps_profile q q'
  have hcorr := nativeRowCorrelation_le_prefix hd q q' c hgrade hp hv₀
    x.1.1.2 x.1.2.2
  have hcap :
      (1 / (2 : ℝ) ^ (n + 2 * d)) *
        min (Nat.choose (n + d - 1) (d - 1))
          (Nat.choose (h + d - 1) (d - 1)) / v₀ = shapeOverlapCap d n h L := by
    rw [show v₀ = nativeShellVarianceFloor d n L by rfl]
    unfold nativeShellVarianceFloor shapeOverlapCap hyperbolicCount
    have hQ : (2 : ℝ) ^ (n + 2 * d) ≠ 0 := by positivity
    have hS : (Nat.choose (n + d - 1) (d - 1) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : d - 1 ≤ n + d - 1)).ne'
    field_simp
    simp only [Nat.cast_min]
  rw [hcap] at hcorr
  exact hcorr

/-- Polynomial shape bound for the good-shell native high-power kernel.  The
shell exponential has already been converted to the geometric factor, while
the quadratic cap is kept at its sharper degree-`d-1` form. -/
theorem nativeGoodPairKernel_shell_sum_mul_pow_le {d n h p : ℕ}
    (hd : 0 < d) (hD : 2 ≤ d) (hn : 0 < n) {L κ : ℝ} (hL : 0 < L)
    (hκ : κ ≤ Real.log 2 /
      (4 * L * (Nat.factorial (d - 1) : ℝ)))
    (hp : (p : ℝ) ≤ κ * ((n : ℝ) + 1)) :
    (∑ x : Subtype (nativeGoodPairShell (d := d) (n := n) (u := n + h)
      (v₀ := nativeShellVarianceFloor d n L)),
      highPowerPairKernel p
        (nativeRowCorrelation (x.1.1.1) (x.1.2.1))) * (2 ^ (n + h) : ℝ) ≤
      (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) *
          (4 * (p : ℝ) ^ 2 *
            (L * (Nat.factorial (d - 1) : ℝ) *
              (((h : ℝ) + 1) / ((n : ℝ) + 1)) ^ (d - 1)) ^ 2 *
            Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ))) := by
  let v₀ := nativeShellVarianceFloor d n L
  let R := shapeOverlapCap d n h L
  let Pcap : ℝ := L * (Nat.factorial (d - 1) : ℝ) *
    (((h : ℝ) + 1) / ((n : ℝ) + 1)) ^ (d - 1)
  have hv₀ : 0 < v₀ := by
    dsimp [v₀, nativeShellVarianceFloor]
    have hSn : 0 < hyperbolicCount d n := hyperbolicCount_pos (by omega)
    positivity
  have hR : 0 ≤ R := shapeOverlapCap_nonneg (by omega) n h hL.le
  have hdecay := shapeOverlapCap_shell_decay_condition
    (d := d) (n := n) (h := h) (p := p) hD hn hL hκ hp
  have hPcap : R ≤ Pcap := by
    dsimp [R, Pcap]
    exact shapeOverlapCap_le_polynomial (by omega) n h hL.le
  have hPcap0 : 0 ≤ Pcap := by positivity
  have hPcapSq : R ^ 2 ≤ Pcap ^ 2 := by nlinarith
  have hExp : Real.exp (2 * (p : ℝ) * R) ≤
      Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ)) :=
    Real.exp_le_exp.mpr hdecay
  have hB : ∀ x : Subtype (nativeGoodPairShell (d := d) (n := n)
      (u := n + h) (v₀ := v₀)),
      highPowerPairKernel p
        (nativeRowCorrelation (x.1.1.1) (x.1.2.1)) ≤
      4 * (p : ℝ) ^ 2 * Pcap ^ 2 *
        Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ)) := by
    intro x
    have hcorr : nativeRowCorrelation (x.1.1.1) (x.1.2.1) ≤ R := by
      simpa [R] using nativeGoodPairCorrelation_le_shapeCap hd hn hL x
    have hkernel := highPowerPairKernel_le_of_le (p := p)
      (nativeRowCorrelation_nonneg _ _) hcorr hR
    calc
      _ ≤ 4 * (p : ℝ) ^ 2 * R ^ 2 * Real.exp (2 * (p : ℝ) * R) := hkernel
      _ ≤ 4 * (p : ℝ) ^ 2 * Pcap ^ 2 *
          Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ)) := by
            have hfac : 0 ≤ 4 * (p : ℝ) ^ 2 := by positivity
            calc
              _ ≤ 4 * (p : ℝ) ^ 2 * Pcap ^ 2 * Real.exp (2 * (p : ℝ) * R) := by
                exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hPcapSq hfac) (Real.exp_nonneg _)
              _ ≤ _ := by
                apply mul_le_mul_of_nonneg_left hExp
                positivity
  have hsum := nativeGoodPairShell_sum_mul_pow_le hd
    (fun x => highPowerPairKernel p
      (nativeRowCorrelation (x.1.1.1) (x.1.2.1)))
    (4 * (p : ℝ) ^ 2 * Pcap ^ 2 *
      Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ))) (by positivity) hB
  simpa [Pcap, mul_assoc, mul_left_comm, mul_comm] using hsum

/-- High-grade shell index, obtained by subtracting the layer grade from the
exact prefix grade. -/
def nativeHighGoodShellIndex (d n : ℕ) :=
  {u : Fin (d * (n + 1) + 1) // n ≤ u.val}

private theorem nativeLayerGrade_le_total (d n : ℕ) (hd : 0 < d) :
    n ≤ d * (n + 1) := by
  calc
    n ≤ n + 1 := Nat.le_succ _
    _ = 1 * (n + 1) := by omega
    _ ≤ d * (n + 1) := Nat.mul_le_mul_right _ (by omega)

noncomputable instance nativeHighGoodShellIndexFintype (d n : ℕ) :
    Fintype (nativeHighGoodShellIndex d n) := by
  unfold nativeHighGoodShellIndex
  infer_instance

noncomputable def nativeHighGoodShellIndexEquiv (d n : ℕ)
    (hd : 0 < d) (hn : 0 < n) :
    nativeHighGoodShellIndex d n ≃ Fin (d * (n + 1) - n + 1) where
  toFun u := ⟨u.1.val - n, by
    have htop : u.1.val ≤ d * (n + 1) := Nat.le_of_lt_succ u.1.isLt
    have hsub := Nat.sub_le_sub_right htop n
    exact Nat.lt_succ_of_le hsub⟩
  invFun h := ⟨⟨n + h.val, by
    have hbase := nativeLayerGrade_le_total d n hd
    have htop : h.val ≤ d * (n + 1) - n := Nat.le_of_lt_succ h.isLt
    have hadd := Nat.add_le_add_left htop n
    have hsum : n + (d * (n + 1) - n) = d * (n + 1) := by
      rw [Nat.add_comm]
      exact Nat.sub_add_cancel hbase
    rw [hsum] at hadd
    exact Nat.lt_succ_of_le hadd⟩, by exact Nat.le_add_right _ _⟩
  left_inv u := by
    apply Subtype.ext
    apply Fin.ext
    exact Nat.add_sub_of_le u.2
  right_inv h := by
    apply Fin.ext
    exact Nat.add_sub_cancel_left n h.val

theorem nativeGoodPairKernelShellSum_eq_zero_of_grade_lt {d n u p : ℕ}
    {L : ℝ} (x : Subtype (nativeGoodPairShell (d := d) (n := n) (u := u)
      (v₀ := nativeShellVarianceFloor d n L))) (hu : u < n) :
    highPowerPairKernel p
      (nativeRowCorrelation (x.1.1.1) (x.1.2.1)) = 0 := by
  let q : MidpointGridIndex d n := x.1.1.1
  let q' : MidpointGridIndex d n := x.1.2.1
  let c := midpointCommonPrefixCaps q q'
  have hxgrade := x.2
  change midpointCommonPrefixGrade (nativeGoodPairAsGrid x.1) = u at hxgrade
  have hgrade : c.sum (fun _ z => z) = u := by
    simpa [c, q, q', midpointCommonPrefixGrade, nativeGoodPairAsGrid] using hxgrade
  have hp : MidpointCommonPrefixProfile q q' c := by
    simpa [c, q, q'] using midpointCommonPrefixCaps_profile q q'
  exact highPowerPairKernel_eq_zero_of_prefix_grade_lt q q' c hp hgrade hu

/-- The total high-power covariance over the good rows decomposes into its
exact common-prefix shells; all shells below grade `n` vanish. -/
theorem nativeGoodPairKernel_sum_eq_high_shells {d n p : ℕ} {L : ℝ}
    (hd : 0 < d) (hn : 0 < n) :
    (∑ x : NativeGoodPair d n (nativeShellVarianceFloor d n L),
      highPowerPairKernel p (nativeRowCorrelation (x.1.1) (x.2.1))) =
      ∑ u : nativeHighGoodShellIndex d n,
        ∑ x : Subtype (nativeGoodPairShell (d := d) (n := n) (u := u.1.val)
          (v₀ := nativeShellVarianceFloor d n L)),
          highPowerPairKernel p (nativeRowCorrelation (x.1.1.1) (x.1.2.1)) := by
  classical
  let f : Fin (d * (n + 1) + 1) → ℝ := fun u =>
    ∑ x : Subtype (nativeGoodPairShell (d := d) (n := n) (u := u.val)
      (v₀ := nativeShellVarianceFloor d n L)),
      highPowerPairKernel p (nativeRowCorrelation (x.1.1.1) (x.1.2.1))
  rw [nativeGoodPair_sum_eq_shell_sums (f := fun x =>
    highPowerPairKernel p (nativeRowCorrelation (x.1.1) (x.2.1)))]
  have hsplit := Fintype.sum_subtype_add_sum_subtype
    (fun u : Fin (d * (n + 1) + 1) => n ≤ u.val) f
  have hlow : (∑ u : {u : Fin (d * (n + 1) + 1) // ¬ n ≤ u.val}, f u.1) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    have hzero : f u.1 = 0 := by
      dsimp [f]
      apply Finset.sum_eq_zero
      intro x hx
      exact nativeGoodPairKernelShellSum_eq_zero_of_grade_lt x (by omega)
    exact hzero
  calc
    _ = (∑ u : {u : Fin (d * (n + 1) + 1) // n ≤ u.val}, f u.1) +
        ∑ u : {u : Fin (d * (n + 1) + 1) // ¬ n ≤ u.val}, f u.1 := hsplit.symm
    _ = ∑ u : {u : Fin (d * (n + 1) + 1) // n ≤ u.val}, f u.1 := by rw [hlow, add_zero]
    _ = _ := by rfl

/-- The shell exponential exactly cancels all but the geometric half-grade
factor after division by the common-prefix weight. -/
theorem expLogHalf_shell_identity (h : ℕ) :
    Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ)) / (2 : ℝ) ^ h =
      Real.sqrt 2 * (Real.sqrt (1 / 2 : ℝ)) ^ h := by
  have hexp : Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ)) =
      (Real.sqrt 2) ^ (h + 1) := by
    rw [show (Real.log 2 / 2) * (h + 1 : ℝ) =
      (h + 1 : ℕ) * (Real.log 2 / 2) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_half, Real.exp_log (by positivity : (0 : ℝ) < 2)]
  have hsqrt : Real.sqrt (1 / 2 : ℝ) = (Real.sqrt 2)⁻¹ := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by positivity)).2
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hexp, hsqrt]
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [pow_succ]
  have hden : (2 : ℝ) ^ h = (Real.sqrt 2 ^ h) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm h 2, pow_mul, h2]
  rw [hden]
  field_simp
  have hcancel : Real.sqrt 2 * (1 / Real.sqrt 2) = 1 := by field_simp
  rw [← mul_pow, hcancel, one_pow]

/-- Closed envelope for a single exact common-prefix grade after the kernel
bound and the weak-composition shell count have both been applied. -/
noncomputable def nativeGoodPairShellEnvelope (d n h p : ℕ) (L : ℝ) : ℝ :=
  (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
    (Fintype.card (MidpointPairGrid d n) : ℝ) *
      (4 * (p : ℝ) ^ 2 *
        (L * (Nat.factorial (d - 1) : ℝ) *
          (((h : ℝ) + 1) / ((n : ℝ) + 1)) ^ (d - 1)) ^ 2 *
        Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ))) /
    (2 : ℝ) ^ (n + h)

private theorem choose_ratio_power_le {d n h : ℕ} (hd : 1 ≤ d) :
    (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
        (((h : ℝ) + 1) / ((n : ℝ) + 1)) ^ (2 * (d - 1)) ≤
      ((h : ℝ) + 1) ^ (3 * (d - 1)) / ((n : ℝ) + 1) ^ (d - 1) := by
  let q := d - 1
  have hchoose : (Nat.choose (n + h + d - 1) (d - 1) : ℝ) ≤
      ((n : ℝ) + 1) ^ q * ((h : ℝ) + 1) ^ q := by
    have h := hyperbolicCount_add_upper_product hd n h
    simpa [hyperbolicCount, q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
  have hx : 0 ≤ (((h : ℝ) + 1) / ((n : ℝ) + 1)) ^ (2 * q) := by positivity
  calc
    _ ≤ (((n : ℝ) + 1) ^ q * ((h : ℝ) + 1) ^ q) *
        (((h : ℝ) + 1) / ((n : ℝ) + 1)) ^ (2 * q) :=
      mul_le_mul_of_nonneg_right hchoose hx
    _ = ((h : ℝ) + 1) ^ (3 * q) / ((n : ℝ) + 1) ^ q := by
      rw [show 2 * q = q + q by omega, pow_add, div_pow]
      field_simp
      ring

noncomputable def nativeGoodPairShellBudgetTerm (d n h p : ℕ) (L : ℝ) : ℝ :=
  ((Fintype.card (MidpointPairGrid d n) : ℝ) * 4 * (p : ℝ) ^ 2 *
    (L * (Nat.factorial (d - 1) : ℝ)) ^ 2 * Real.sqrt 2 *
    ((h : ℝ) + 1) ^ (3 * (d - 1)) *
    (Real.sqrt (1 / 2 : ℝ)) ^ h) /
    ((2 : ℝ) ^ n * ((n : ℝ) + 1) ^ (d - 1))

theorem nativeGoodPairShellEnvelope_le_budgetTerm {d n h p : ℕ}
    (hd : 1 ≤ d) (L : ℝ) :
    nativeGoodPairShellEnvelope d n h p L ≤
      nativeGoodPairShellBudgetTerm d n h p L := by
  let q := d - 1
  let x : ℝ := ((h : ℝ) + 1) / ((n : ℝ) + 1)
  let A : ℝ := ((Fintype.card (MidpointPairGrid d n) : ℝ) * 4 * (p : ℝ) ^ 2 *
    (L * (Nat.factorial q : ℝ)) ^ 2 * Real.sqrt 2 *
    (Real.sqrt (1 / 2 : ℝ)) ^ h) / ((2 : ℝ) ^ n)
  have hExp : Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ)) =
      Real.sqrt 2 * (Real.sqrt (1 / 2 : ℝ)) ^ h * (2 : ℝ) ^ h := by
    calc
      _ = (Real.exp ((Real.log 2 / 2) * (h + 1 : ℝ)) / (2 : ℝ) ^ h) *
          (2 : ℝ) ^ h := by field_simp
      _ = _ := by rw [expLogHalf_shell_identity]
  have hrewrite : nativeGoodPairShellEnvelope d n h p L =
      A * ((Nat.choose (n + h + d - 1) (d - 1) : ℝ) * x ^ (2 * q)) := by
    dsimp [nativeGoodPairShellEnvelope, A, x, q]
    rw [hExp]
    rw [show (2 : ℝ) ^ (n + h) = (2 : ℝ) ^ n * (2 : ℝ) ^ h by rw [pow_add]]
    field_simp
    ring
  have hshape := choose_ratio_power_le (d := d) (n := n) (h := h) hd
  have hA : 0 ≤ A := by dsimp [A]; positivity
  calc
    _ = A * ((Nat.choose (n + h + d - 1) (d - 1) : ℝ) * x ^ (2 * q)) := hrewrite
    _ ≤ A * (((h : ℝ) + 1) ^ (3 * q) / ((n : ℝ) + 1) ^ q) :=
      mul_le_mul_of_nonneg_left (by simpa [q, x] using hshape) hA
    _ = nativeGoodPairShellBudgetTerm d n h p L := by
      dsimp [nativeGoodPairShellBudgetTerm, A, q]
      ring

/-- Summing the proved shell estimate over the exact finite prefix
decomposition bounds the full covariance-kernel sum on any variance-good
subset. No assumption about the geometry of that subset is used beyond its
rowwise variance floor. -/
theorem nativeGoodPairKernel_sum_le_shell_envelopes {d n p : ℕ} {L κ : ℝ}
    (hd : 0 < d) (hD : 2 ≤ d) (hn : 0 < n) (hL : 0 < L)
    (hκ : κ ≤ Real.log 2 / (4 * L * (Nat.factorial (d - 1) : ℝ)))
    (hp : (p : ℝ) ≤ κ * ((n : ℝ) + 1)) :
    (∑ x : NativeGoodPair d n (nativeShellVarianceFloor d n L),
      highPowerPairKernel p (nativeRowCorrelation (x.1.1) (x.2.1))) ≤
      ∑ u : nativeHighGoodShellIndex d n,
        nativeGoodPairShellEnvelope d n (u.1.val - n) p L := by
  classical
  rw [nativeGoodPairKernel_sum_eq_high_shells hd hn]
  apply Finset.sum_le_sum
  intro u hu
  let h := u.1.val - n
  have hgrade : n + h = u.1.val := Nat.add_sub_of_le u.2
  have hshell := nativeGoodPairKernel_shell_sum_mul_pow_le
    (d := d) (n := n) (h := h) (p := p) hd hD hn hL hκ hp
  have hden : 0 < (2 : ℝ) ^ (n + h) := by positivity
  rw [← hgrade]
  rw [nativeGoodPairShellEnvelope]
  simp only [Nat.add_sub_cancel_left]
  apply (le_div_iff₀ hden).2
  simpa [nativeGoodPairShellEnvelope, h, hgrade, mul_assoc, mul_left_comm,
    mul_comm] using hshell

noncomputable def nativeGoodPairKernelBudgetConstant (d n p : ℕ) (L : ℝ) : ℝ :=
  ((Fintype.card (MidpointPairGrid d n) : ℝ) * 4 * (p : ℝ) ^ 2 *
    (L * (Nat.factorial (d - 1) : ℝ)) ^ 2 * Real.sqrt 2) /
    ((2 : ℝ) ^ n * ((n : ℝ) + 1) ^ (d - 1))

theorem midpointPairGrid_card_eq_midpointGrid_card_sq {d n : ℕ} :
    (Fintype.card (MidpointPairGrid d n) : ℝ) =
      (Fintype.card (MidpointGridIndex d n) : ℝ) ^ 2 := by
  have hpair : Fintype.card (MidpointPairGrid d n) =
      (2 ^ (n + 1) * 2 ^ (n + 1)) ^ d := by
    simp [MidpointPairGrid, MidpointGridCoordinate, Fintype.card_pi,
      Fintype.card_prod]
  have hrow : Fintype.card (MidpointGridIndex d n) =
      (2 ^ (n + 1)) ^ d := by
    simp [MidpointGridIndex, MidpointGridCoordinate, Fintype.card_pi]
  rw [show (Fintype.card (MidpointPairGrid d n) : ℝ) =
    ((2 : ℝ) ^ (n + 1) * 2 ^ (n + 1)) ^ d by exact_mod_cast hpair]
  rw [show (Fintype.card (MidpointGridIndex d n) : ℝ) =
    ((2 : ℝ) ^ (n + 1)) ^ d by exact_mod_cast hrow]
  rw [mul_pow, pow_two]

/-- The finite geometric shell sum is bounded by the convergent moment
budget. This retains the full pair-grid cardinal, so it can be normalized by
the square of any positive-density good set without losing a grid factor. -/
theorem nativeGoodPairKernel_sum_le_budget {d n p : ℕ} {L κ : ℝ}
    (hd : 0 < d) (hD : 2 ≤ d) (hn : 0 < n) (hL : 0 < L)
    (hκ : κ ≤ Real.log 2 / (4 * L * (Nat.factorial (d - 1) : ℝ)))
    (hp : (p : ℝ) ≤ κ * ((n : ℝ) + 1)) :
    (∑ x : NativeGoodPair d n (nativeShellVarianceFloor d n L),
      highPowerPairKernel p (nativeRowCorrelation (x.1.1) (x.2.1))) ≤
      nativeGoodPairKernelBudgetConstant d n p L *
        shellPolynomialBudget (d - 1) := by
  classical
  have henvelopes := nativeGoodPairKernel_sum_le_shell_envelopes
    (d := d) (n := n) (p := p) hd hD hn hL hκ hp
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
          (Real.sqrt (1 / 2 : ℝ)) ^ h) ≤ shellPolynomialBudget q := by
    exact shellPolynomial_partial_le_budget q N
  have hsum :
      (∑ h ∈ Finset.range (N + 1),
        nativeGoodPairKernelBudgetConstant d n p L *
          ((h + 1 : ℝ) ^ (3 * q) * (Real.sqrt (1 / 2 : ℝ)) ^ h)) ≤
      nativeGoodPairKernelBudgetConstant d n p L *
        shellPolynomialBudget q := by
    calc
      _ = nativeGoodPairKernelBudgetConstant d n p L *
          (∑ h ∈ Finset.range (N + 1),
            ((h + 1 : ℝ) ^ (3 * q)) *
              (Real.sqrt (1 / 2 : ℝ)) ^ h) := by rw [← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpartial (by
        dsimp [nativeGoodPairKernelBudgetConstant]
        positivity)
  calc
    _ ≤ ∑ u : nativeHighGoodShellIndex d n,
        nativeGoodPairShellEnvelope d n (u.1.val - n) p L := henvelopes
    _ ≤ ∑ u : nativeHighGoodShellIndex d n,
        nativeGoodPairShellBudgetTerm d n (u.1.val - n) p L :=
      Finset.sum_le_sum (fun u _ => nativeGoodPairShellEnvelope_le_budgetTerm
        (d := d) (n := n) (h := u.1.val - n) (p := p) (by omega) L)
    _ = ∑ h : Fin H, nativeGoodPairShellBudgetTerm d n h.val p L := hreindex
    _ = ∑ h ∈ Finset.range (N + 1),
        nativeGoodPairKernelBudgetConstant d n p L *
          ((h + 1 : ℝ) ^ (3 * q) * (Real.sqrt (1 / 2 : ℝ)) ^ h) := hfin
    _ ≤ _ := hsum

/-- Density converts the raw full-grid shell estimate into the exact
good-pair average. The denominator is the square of the actual good-row
cardinality, with no replacement by the ambient grid size. -/
theorem nativeGoodPairKernel_average_le_of_density {d n p : ℕ} {L κ δ : ℝ}
    (hd : 0 < d) (hD : 2 ≤ d) (hn : 0 < n) (hL : 0 < L)
    (hκ : κ ≤ Real.log 2 / (4 * L * (Nat.factorial (d - 1) : ℝ)))
    (hp : (p : ℝ) ≤ κ * ((n : ℝ) + 1)) (hδ : 0 < δ)
    (hdensity : δ * (Fintype.card (MidpointGridIndex d n) : ℝ) ≤
      (Fintype.card (NativeGoodRows d n (nativeShellVarianceFloor d n L)) : ℝ)) :
    (∑ x : NativeGoodPair d n (nativeShellVarianceFloor d n L),
      highPowerPairKernel p (nativeRowCorrelation (x.1.1) (x.2.1))) /
        (Fintype.card (NativeGoodPair d n (nativeShellVarianceFloor d n L)) : ℝ) ≤
      (4 * (p : ℝ) ^ 2 *
        (L * (Nat.factorial (d - 1) : ℝ)) ^ 2 * Real.sqrt 2 *
        shellPolynomialBudget (d - 1)) /
        (δ ^ 2 * (2 : ℝ) ^ n * ((n : ℝ) + 1) ^ (d - 1)) := by
  have hraw := nativeGoodPairKernel_sum_le_budget
    (d := d) (n := n) (p := p) hd hD hn hL hκ hp
  have hcardpair := midpointPairGrid_card_eq_midpointGrid_card_sq (d := d) (n := n)
  let R : ℝ := Fintype.card (MidpointGridIndex d n)
  let G : ℝ := Fintype.card (NativeGoodRows d n
    (nativeShellVarianceFloor d n L))
  have hR : 0 < R := by
    dsimp [R, MidpointGridIndex, MidpointGridCoordinate]
    simp [Fintype.card_pi]
  have hG : 0 < G := lt_of_lt_of_le (mul_pos hδ hR) (by simpa [R, G] using hdensity)
  have hpairCard :
      (Fintype.card (NativeGoodPair d n (nativeShellVarianceFloor d n L)) : ℝ) = G ^ 2 := by
    simp [NativeGoodPair, G, Fintype.card_prod]
    ring
  have hden : 0 < (Fintype.card (NativeGoodPair d n
      (nativeShellVarianceFloor d n L)) : ℝ) := by
    rw [hpairCard]
    positivity
  let C : ℝ := (4 * (p : ℝ) ^ 2 *
    (L * (Nat.factorial (d - 1) : ℝ)) ^ 2 * Real.sqrt 2 *
    shellPolynomialBudget (d - 1)) /
    ((2 : ℝ) ^ n * ((n : ℝ) + 1) ^ (d - 1))
  have hraw' :
      (∑ x : NativeGoodPair d n (nativeShellVarianceFloor d n L),
        highPowerPairKernel p (nativeRowCorrelation (x.1.1) (x.2.1))) ≤ R ^ 2 * C := by
    have hrewrite : nativeGoodPairKernelBudgetConstant d n p L *
        shellPolynomialBudget (d - 1) = R ^ 2 * C := by
      dsimp [C, nativeGoodPairKernelBudgetConstant, R]
      rw [hcardpair]
      ring
    exact hraw.trans hrewrite.le
  have hratio : R ^ 2 / G ^ 2 ≤ 1 / δ ^ 2 := by
    apply (div_le_iff₀ (sq_pos_of_pos hG)).2
    have hsq : (δ * R) ^ 2 ≤ G ^ 2 := by
      have hgap : 0 ≤ G - δ * R := sub_nonneg.mpr (by simpa [R, G] using hdensity)
      have hsum : 0 ≤ G + δ * R := by positivity
      nlinarith
    field_simp
    nlinarith [hsq]
  have hbudget : 0 ≤ shellPolynomialBudget (d - 1) := by
    unfold shellPolynomialBudget
    exact tsum_nonneg (fun h => by positivity)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ (R ^ 2 * C) / G ^ 2 := by
      rw [hpairCard]
      exact div_le_div_of_nonneg_right hraw' (sq_nonneg G)
    _ = (R ^ 2 / G ^ 2) * C := by ring
    _ ≤ (1 / δ ^ 2) * C := mul_le_mul_of_nonneg_right hratio hC
    _ = _ := by dsimp [C]; field_simp

end BrownianSharp
