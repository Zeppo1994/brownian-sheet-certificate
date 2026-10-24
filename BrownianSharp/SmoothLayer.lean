import BrownianSharp.CovarianceBound

/-!
Deterministic support and counting for smooth tensor atoms on the midpoint
lattice.  The only assumptions on the one-dimensional atom are its unit
supremum bound and support in the open unit interval; no stochastic or
concentration statement is imported.
-/

open scoped BigOperators

namespace BrownianSharp

private theorem smoothDyadicCellIndex_coarsen {N : ℕ} (r s : Fin N)
    (hrs : r.val ≤ s.val) (k : ℕ) :
    HaarQuarter.dyadicCellIndex N r k =
      HaarQuarter.dyadicCellIndex N s k / 2 ^ (s.val - r.val) := by
  unfold HaarQuarter.dyadicCellIndex
  have hexp : N - r.val = (N - s.val) + (s.val - r.val) := by omega
  rw [hexp, Nat.pow_add, ← Nat.div_div_eq_div_mul]

private theorem smoothMidpointPrefix_eq_of_fine_eq {n r s : ℕ}
    (q q' : MidpointGridCoordinate n) (hsr : s ≤ r) (hr : r ≤ n)
    (heq : HaarQuarter.dyadicCellIndex (n + 1) ⟨r, by omega⟩ q.val =
      HaarQuarter.dyadicCellIndex (n + 1) ⟨r, by omega⟩ q'.val) :
    midpointPrefixCell s q = midpointPrefixCell s q' := by
  have hsc : s ≤ n := by omega
  let ls : Fin (n + 1) := ⟨s, by omega⟩
  let lr : Fin (n + 1) := ⟨r, by omega⟩
  simp only [midpointPrefixCell, dif_pos hsc]
  calc
    HaarQuarter.dyadicCellIndex (n + 1) ls q.val =
        HaarQuarter.dyadicCellIndex (n + 1) lr q.val /
          2 ^ (r - s) := by rw [smoothDyadicCellIndex_coarsen ls lr hsr]
    _ = HaarQuarter.dyadicCellIndex (n + 1) lr q'.val /
          2 ^ (r - s) := by rw [heq]
    _ = HaarQuarter.dyadicCellIndex (n + 1) ls q'.val := by
      rw [smoothDyadicCellIndex_coarsen ls lr hsr]

/-- Tensor smooth atom sampled at a product midpoint. The atom is scaled by
its shape depth and translated by its dyadic cell address. -/
noncomputable def smoothLayerAtom {d n : ℕ} (ψ : ℝ → ℝ)
    (q : MidpointGridIndex d n) (a : LayerIndex d n) : ℝ :=
  ∏ i : Fin d,
    ψ ((2 : ℝ) ^ layerIndexDepth a i * midpointGridCoordinate n (q i) -
      (layerIndexCell a i : ℝ))

/-- Unit-bounded one-dimensional atoms give unit-bounded tensor samples. -/
theorem smoothLayerAtom_abs_le_one {d n : ℕ} (ψ : ℝ → ℝ)
    (hψ : ∀ x, |ψ x| ≤ 1) (q : MidpointGridIndex d n) (a : LayerIndex d n) :
    |smoothLayerAtom ψ q a| ≤ 1 := by
  rw [smoothLayerAtom, Finset.abs_prod]
  calc
    (∏ i : Fin d,
        |ψ ((2 : ℝ) ^ layerIndexDepth a i * midpointGridCoordinate n (q i) -
          (layerIndexCell a i : ℝ))|) ≤ ∏ _i : Fin d, (1 : ℝ) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact abs_nonneg _
      · intro i hi
        exact hψ _
    _ = 1 := by simp

/-- Nonvanishing of a compactly supported smooth atom places the midpoint
strictly inside the addressed dyadic interval. -/
theorem smoothLayerAtom_nonzero_address {d n : ℕ}
    (ψ : ℝ → ℝ)
    (hψsupport : ∀ x, (x ≤ 0 ∨ 1 ≤ x) → ψ x = 0)
    (q : MidpointGridIndex d n) (a : LayerIndex d n)
    (hneq : smoothLayerAtom ψ q a ≠ 0) (i : Fin d) :
    HaarQuarter.dyadicCellIndex (n + 1)
      ⟨layerIndexDepth a i, by
        have hgrade := layerIndexDepth_grade a
        have hsum : (∑ j : Fin d, layerIndexDepth a j) = n := by
          simpa [Finsupp.sum_fintype, layerIndexDepth] using hgrade
        have hle := Finset.single_le_sum
          (fun j _ => Nat.zero_le (layerIndexDepth a j)) (Finset.mem_univ i)
        omega⟩ (q i).val = layerIndexCell a i := by
  have hgrade := layerIndexDepth_grade a
  have hsum : (∑ j : Fin d, layerIndexDepth a j) = n := by
    simpa [Finsupp.sum_fintype, layerIndexDepth] using hgrade
  have hle := Finset.single_le_sum
    (fun j _ => Nat.zero_le (layerIndexDepth a j)) (Finset.mem_univ i)
  have hr : layerIndexDepth a i ≤ n := by omega
  have hfactor : ψ ((2 : ℝ) ^ layerIndexDepth a i *
      midpointGridCoordinate n (q i) - (layerIndexCell a i : ℝ)) ≠ 0 := by
    intro hz
    apply hneq
    unfold smoothLayerAtom
    exact Finset.prod_eq_zero (Finset.mem_univ i) hz
  let x := (2 : ℝ) ^ layerIndexDepth a i *
      midpointGridCoordinate n (q i) - (layerIndexCell a i : ℝ)
  have hx0 : 0 < x := by
    by_contra hn
    have hle0 : x ≤ 0 := le_of_not_gt hn
    exact hfactor (by simpa [x] using hψsupport x (Or.inl hle0))
  have hx1 : x < 1 := by
    by_contra hn
    have hge1 : 1 ≤ x := le_of_not_gt hn
    exact hfactor (by simpa [x] using hψsupport x (Or.inr hge1))
  have hden : 0 < (2 : ℝ) ^ layerIndexDepth a i := by positivity
  have hleft : dyadicHaarLeft (layerIndexDepth a i) (layerIndexCell a i) <
      midpointGridCoordinate n (q i) := by
    dsimp [dyadicHaarLeft]
    apply (div_lt_iff₀ hden).2
    dsimp [x] at hx0
    push_cast at hx0
    nlinarith
  have hright : midpointGridCoordinate n (q i) <
      dyadicHaarRight (layerIndexDepth a i) (layerIndexCell a i) := by
    dsimp [dyadicHaarRight]
    apply (lt_div_iff₀ hden).2
    dsimp [x] at hx1
    have hcast : (2 : ℝ) ^ layerIndexDepth a i *
        midpointGridCoordinate n (q i) - (layerIndexCell a i : ℝ) < 1 := hx1
    have htarget : midpointGridCoordinate n (q i) *
        (2 : ℝ) ^ layerIndexDepth a i < (layerIndexCell a i : ℝ) + 1 := by
      linarith
    simpa only [Nat.cast_add, Nat.cast_one] using htarget
  exact midpointAddress_eq_dyadicCellIndex (q i) (layerIndexCell a i) hr
    hleft hright

/-- If the two midpoint addresses separate just after the prefix cap, then
any nonzero product of smooth atoms has its shape below that cap. -/
theorem smoothLayerPair_support {d n h : ℕ}
    (ψ : ℝ → ℝ) (hψsupport : ∀ x, (x ≤ 0 ∨ 1 ≤ x) → ψ x = 0)
    (q q' : MidpointGridIndex d n) (c : Fin d →₀ ℕ)
    (hp : MidpointCommonPrefixProfile q q' c)
    (a : LayerIndex d n)
    (hpos : 0 < |smoothLayerAtom ψ q a * smoothLayerAtom ψ q' a|) :
    ∀ i, layerIndexDepth a i ≤ c i := by
  have hprod : smoothLayerAtom ψ q a * smoothLayerAtom ψ q' a ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at hpos
    exact (lt_irrefl _ hpos)
  have hq : smoothLayerAtom ψ q a ≠ 0 := by
    intro hz
    exact hprod (by simp [hz])
  have hq' : smoothLayerAtom ψ q' a ≠ 0 := by
    intro hz
    exact hprod (by simp [hz])
  intro i
  by_contra hnot
  have hrc : c i < layerIndexDepth a i := by omega
  have hdepth : layerIndexDepth a i ≤ n := by
    have hgrade := layerIndexDepth_grade a
    have hsum : (∑ j : Fin d, layerIndexDepth a j) = n := by
      simpa [Finsupp.sum_fintype, layerIndexDepth] using hgrade
    have hle := Finset.single_le_sum
      (fun j _ => Nat.zero_le (layerIndexDepth a j)) (Finset.mem_univ i)
    omega
  have haddr := smoothLayerAtom_nonzero_address ψ hψsupport q a hq i
  have haddr' := smoothLayerAtom_nonzero_address ψ hψsupport q' a hq' i
  have hsame : HaarQuarter.dyadicCellIndex (n + 1)
      ⟨layerIndexDepth a i, by omega⟩ (q i).val =
      HaarQuarter.dyadicCellIndex (n + 1)
      ⟨layerIndexDepth a i, by omega⟩ (q' i).val := by omega
  have hprefix := smoothMidpointPrefix_eq_of_fine_eq (q i) (q' i)
    (by omega : c i + 1 ≤ layerIndexDepth a i) hdepth hsame
  have hnext : c i < n + 1 := by omega
  exact (hp.diverge i hnext) hprefix

/-- At any fixed shape, a nonzero smooth atom has at most one address tuple,
since its support interval at each coordinate is fixed by the midpoint. -/
theorem smoothLayerPair_unique_addresses {d n : ℕ}
    (ψ : ℝ → ℝ) (hψsupport : ∀ x, (x ≤ 0 ∨ 1 ≤ x) → ψ x = 0)
    (q q' : MidpointGridIndex d n) (a b : LayerIndex d n)
    (ha : smoothLayerAtom ψ q a * smoothLayerAtom ψ q' a ≠ 0)
    (hb : smoothLayerAtom ψ q b * smoothLayerAtom ψ q' b ≠ 0)
    (hdepth : layerIndexDepth a = layerIndexDepth b) : a = b := by
  have hqa : smoothLayerAtom ψ q a ≠ 0 := by
    intro hz
    exact ha (by simp [hz])
  have hqb : smoothLayerAtom ψ q b ≠ 0 := by
    intro hz
    exact hb (by simp [hz])
  have hshape : a.1.1 = b.1.1 := by
    apply Finsupp.ext
    intro i
    exact congrArg (fun r : Fin d → ℕ => r i) hdepth
  have hcell : layerIndexCell a = layerIndexCell b := by
    funext i
    have haddrA := smoothLayerAtom_nonzero_address ψ hψsupport q a hqa i
    have haddrB := smoothLayerAtom_nonzero_address ψ hψsupport q b hqb i
    have hsameDepth := congrArg (fun r : Fin d → ℕ => r i) hdepth
    have haddrB' : HaarQuarter.dyadicCellIndex (n + 1)
        ⟨layerIndexDepth a i, by
          have hgrade := layerIndexDepth_grade a
          have hsum : (∑ j : Fin d, layerIndexDepth a j) = n := by
            simpa [Finsupp.sum_fintype, layerIndexDepth] using hgrade
          have hle := Finset.single_le_sum
            (fun j _ => Nat.zero_le (layerIndexDepth a j)) (Finset.mem_univ i)
          omega⟩ (q i).val = layerIndexCell b i := by
      simpa [hsameDepth] using haddrB
    calc
      layerIndexCell a i = HaarQuarter.dyadicCellIndex (n + 1)
          ⟨layerIndexDepth a i, by
            have hgrade := layerIndexDepth_grade a
            have hsum : (∑ j : Fin d, layerIndexDepth a j) = n := by
              simpa [Finsupp.sum_fintype, layerIndexDepth] using hgrade
            have hle := Finset.single_le_sum
              (fun j _ => Nat.zero_le (layerIndexDepth a j)) (Finset.mem_univ i)
            omega⟩ (q i).val := haddrA.symm
      _ = layerIndexCell b i := haddrB'
  cases a with
  | mk ra ja =>
    cases b with
    | mk rb jb =>
      have hrs : ra = rb := Subtype.ext hshape
      cases hrs
      have htuple : ja = jb := by
        funext i
        apply Fin.ext
        exact congrArg (fun f : Fin d → ℕ => f i) hcell
      subst jb
      rfl

/-- Sum of absolute smooth-layer coefficient products is bounded by the
smaller of the layer shape count and the complementary-prefix shape count. -/
theorem smoothLayerPair_abs_sum_le {d n h : ℕ} (hd : 0 < d)
    (ψ : ℝ → ℝ) (hψsupport : ∀ x, (x ≤ 0 ∨ 1 ≤ x) → ψ x = 0)
    (hψ : ∀ x, |ψ x| ≤ 1)
    (q q' : MidpointGridIndex d n) (c : Fin d →₀ ℕ)
    (hc : c.sum (fun _ x => x) = n + h)
    (hp : MidpointCommonPrefixProfile q q' c) :
    (∑ a : LayerIndex d n,
        |smoothLayerAtom ψ q a * smoothLayerAtom ψ q' a|) ≤
      min (Nat.choose (n + d - 1) (d - 1))
        (Nat.choose (h + d - 1) (d - 1)) := by
  let f : LayerIndex d n → ℝ := fun a =>
    |smoothLayerAtom ψ q a * smoothLayerAtom ψ q' a|
  have hnonneg : ∀ a, 0 ≤ f a := by intro a; exact abs_nonneg _
  have hbound : ∀ a, f a ≤ 1 := by
    intro a
    dsimp [f]
    rw [abs_mul]
    have ha := smoothLayerAtom_abs_le_one ψ hψ q a
    have hb := smoothLayerAtom_abs_le_one ψ hψ q' a
    calc
      |smoothLayerAtom ψ q a| * |smoothLayerAtom ψ q' a| ≤
          1 * |smoothLayerAtom ψ q' a| :=
        mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = 1 := by norm_num
  have hsupport : ∀ a, 0 < f a → ∀ i, layerIndexDepth a i ≤ c i := by
    intro a ha
    exact smoothLayerPair_support (h := h) ψ hψsupport q q' c hp a
      (by simpa [f] using ha)
  have hunique : ∀ a b, 0 < f a → 0 < f b →
      layerIndexDepth a = layerIndexDepth b → a = b := by
    intro a b ha hb hdepth
    apply smoothLayerPair_unique_addresses ψ hψsupport q q' a b
    · exact abs_pos.mp (by simpa [f] using ha)
    · exact abs_pos.mp (by simpa [f] using hb)
    · exact hdepth
  have hsum := layerRowProduct_sum_le_of_support hd c hc f 1
    (by norm_num) hnonneg hbound hsupport hunique
  simpa [f] using hsum

/-- If the common-prefix grade is below the layer grade, no nonzero smooth
atom product can occur. -/
theorem smoothLayerPair_zero_of_prefix_lt {d n h : ℕ}
    (ψ : ℝ → ℝ)
    (hψsupport : ∀ x, (x ≤ 0 ∨ 1 ≤ x) → ψ x = 0)
    (q q' : MidpointGridIndex d n) (c : Fin d →₀ ℕ)
    (hc : c.sum (fun _ x => x) < n)
    (hp : MidpointCommonPrefixProfile q q' c) :
    ∀ a : LayerIndex d n,
      smoothLayerAtom ψ q a * smoothLayerAtom ψ q' a = 0 := by
  intro a
  by_contra hne
  have hpos : 0 < |smoothLayerAtom ψ q a * smoothLayerAtom ψ q' a| :=
    abs_pos.mpr hne
  have hs := smoothLayerPair_support (h := h) ψ hψsupport q q' c hp a hpos
  have hgrade := layerIndexDepth_grade a
  have hsum : (∑ i : Fin d, layerIndexDepth a i) = n := by
    simpa [Finsupp.sum_fintype, layerIndexDepth] using hgrade
  have hle : (∑ i : Fin d, layerIndexDepth a i) ≤ ∑ i : Fin d, c i :=
    Finset.sum_le_sum (fun i hi => hs i)
  have hc' : (∑ i : Fin d, c i) < n := by
    simpa [Finsupp.sum_fintype] using hc
  omega

end BrownianSharp
