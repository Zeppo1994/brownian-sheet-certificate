import BrownianSharp.LayerIndex
import BrownianSharp.Prefix
import BrownianSharp.NativeRow

/-!
Finite covariance counting for a fixed native tensor-Haar layer.  The main
lemma isolates the support/multiplicity input from tent geometry: once a
nonzero row product is supported on shape profiles below the common-prefix
vector and at most one address tuple per shape contributes, the exact
weak-composition bounds follow by subtraction of shapes.
-/

open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp

/-- The dyadic prefix label of a depth-`n+1` midpoint at requested depth `r`.
The final branch only makes the definition total; all actual layer depths are
at most `n`. -/
def midpointPrefixCell {n : ℕ} (r : ℕ) (q : MidpointGridCoordinate n) : ℕ :=
  if hr : r ≤ n then
    HaarQuarter.dyadicCellIndex (n + 1) ⟨r, by omega⟩ q.val
  else q.val

/-- A coordinatewise common-prefix profile for two midpoint-grid points.
At depth `c i` the addresses agree, while at the next depth they separate
unless the cap has reached the end of the grid. -/
structure MidpointCommonPrefixProfile {d n : ℕ}
    (q q' : MidpointGridIndex d n) (c : Fin d →₀ ℕ) : Prop where
  depth_le_grid : ∀ i, c i ≤ n + 1
  agree : ∀ i, midpointPrefixCell (c i) (q i) = midpointPrefixCell (c i) (q' i)
  diverge : ∀ i, c i < n + 1 →
    midpointPrefixCell (c i + 1) (q i) ≠ midpointPrefixCell (c i + 1) (q' i)

/-- A deeper dyadic prefix determines every shallower one. -/
private theorem dyadicCellIndex_coarsen {N : ℕ} (r s : Fin N)
    (hrs : r.val ≤ s.val) (k : ℕ) :
    HaarQuarter.dyadicCellIndex N r k =
      HaarQuarter.dyadicCellIndex N s k / 2 ^ (s.val - r.val) := by
  unfold HaarQuarter.dyadicCellIndex
  have hexp : N - r.val = (N - s.val) + (s.val - r.val) := by omega
  rw [hexp, Nat.pow_add, ← Nat.div_div_eq_div_mul]

/-- Equality of the fine dyadic address implies equality of the coarser
prefix address. -/
private theorem midpointPrefix_eq_of_fine_eq {n r s : ℕ}
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
          2 ^ (r - s) := by
      rw [dyadicCellIndex_coarsen ls lr hsr]
    _ = HaarQuarter.dyadicCellIndex (n + 1) lr q'.val /
          2 ^ (r - s) := by rw [heq]
    _ = HaarQuarter.dyadicCellIndex (n + 1) ls q'.val := by
      rw [dyadicCellIndex_coarsen ls lr hsr]

/-- A strict geometric containment of a fine midpoint in a Haar interval
identifies the addressed interval with the corresponding dyadic prefix cell.
This is the floor bridge from the real tent support to the integer address
used in the common-prefix count. -/
theorem midpointAddress_eq_dyadicCellIndex {n r : ℕ}
    (q : MidpointGridCoordinate n) (j : ℕ) (hr : r ≤ n)
    (hleft : dyadicHaarLeft r j < midpointGridCoordinate n q)
    (hright : midpointGridCoordinate n q < dyadicHaarRight r j) :
    HaarQuarter.dyadicCellIndex (n + 1) ⟨r, by omega⟩ q.val = j := by
  have hr' : r ≤ n + 1 := by omega
  have hpowNat : 2 ^ (n + 1) = 2 ^ r * 2 ^ (n + 1 - r) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hr']
  have hpow : (2 : ℝ) ^ (n + 1) =
      (2 : ℝ) ^ r * (2 : ℝ) ^ (n + 1 - r) := by
    exact_mod_cast hpowNat
  have hleftMul :
      (j : ℝ) * (2 : ℝ) ^ (n + 1 - r) < (q.val : ℝ) + (1 / 2 : ℝ) := by
    have h := mul_lt_mul_of_pos_right hleft (by positivity : 0 < (2 : ℝ) ^ (n + 1))
    dsimp [dyadicHaarLeft, midpointGridCoordinate] at h
    rw [hpow] at h
    field_simp at h
    nlinarith [h]
  have hrightMul :
      (q.val : ℝ) + (1 / 2 : ℝ) <
        ((j + 1 : ℕ) : ℝ) * (2 : ℝ) ^ (n + 1 - r) := by
    have h := mul_lt_mul_of_pos_right hright (by positivity : 0 < (2 : ℝ) ^ (n + 1))
    dsimp [dyadicHaarRight, midpointGridCoordinate] at h
    rw [hpow] at h
    field_simp at h
    nlinarith [h]
  have hlow : j * 2 ^ (n + 1 - r) < q.val + 1 := by
    have hcast : ((j * 2 ^ (n + 1 - r) : ℕ) : ℝ) <
        (q.val : ℝ) + (1 / 2 : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hleftMul
    have hreal : ((j * 2 ^ (n + 1 - r) : ℕ) : ℝ) < (q.val : ℝ) + 1 := by
      linarith
    exact_mod_cast hreal
  have hhigh : q.val < (j + 1) * 2 ^ (n + 1 - r) := by
    have hcast : (q.val : ℝ) + (1 / 2 : ℝ) <
        (((j + 1) * 2 ^ (n + 1 - r) : ℕ) : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow,
        Nat.cast_ofNat] using hrightMul
    have hreal : (q.val : ℝ) < (((j + 1) * 2 ^ (n + 1 - r) : ℕ) : ℝ) := by
      linarith
    exact_mod_cast hreal
  apply (HaarQuarter.dyadicCellIndex_eq_iff_contains (n + 1)
    ⟨r, by omega⟩ j q.val).2
  exact ⟨Nat.lt_succ_iff.mp hlow, hhigh⟩

/-- A positive native row coefficient identifies the exact dyadic prefix
cell containing each coordinate midpoint. -/
theorem nativeLayerRow_address_of_pos {d n : ℕ}
    (q : MidpointGridIndex d n) (a : LayerIndex d n)
    (hpos : 0 < nativeLayerRowCoefficient q a) (i : Fin d) :
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
  have hinterior := (nativeLayerRowCoefficient_pos_iff_interior q a).1 hpos
  exact (midpointAddress_eq_dyadicCellIndex (q i) (layerIndexCell a i) hr
    (hinterior i).1 (hinterior i).2)

/-- The geometric support of a positive row product is contained in the
coordinatewise common-prefix cap. -/
theorem nativeLayerRowProduct_support {d n h : ℕ}
    (q q' : MidpointGridIndex d n) (c : Fin d →₀ ℕ)
    (hp : MidpointCommonPrefixProfile q q' c)
    (a : LayerIndex d n)
    (hpos : 0 < nativeLayerRowCoefficient q a * nativeLayerRowCoefficient q' a) :
    ∀ i, layerIndexDepth a i ≤ c i := by
  have hq : 0 < nativeLayerRowCoefficient q a := by
    have hn := nativeLayerRowCoefficient_nonneg q' a
    by_contra hnot
    have hz : nativeLayerRowCoefficient q a = 0 := by
      have := nativeLayerRowCoefficient_nonneg q a
      linarith
    rw [hz, zero_mul] at hpos
    exact (lt_irrefl _ hpos)
  have hq' : 0 < nativeLayerRowCoefficient q' a := by
    have hn := nativeLayerRowCoefficient_nonneg q a
    by_contra hnot
    have hz : nativeLayerRowCoefficient q' a = 0 := by
      have := nativeLayerRowCoefficient_nonneg q' a
      linarith
    rw [hz, mul_zero] at hpos
    exact (lt_irrefl _ hpos)
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
  have hfine := nativeLayerRow_address_of_pos q a hq i
  have hfine' := nativeLayerRow_address_of_pos q' a hq' i
  have hsame : HaarQuarter.dyadicCellIndex (n + 1)
      ⟨layerIndexDepth a i, by omega⟩ (q i).val =
      HaarQuarter.dyadicCellIndex (n + 1)
      ⟨layerIndexDepth a i, by omega⟩ (q' i).val := by omega
  have hnext_lt : c i < n + 1 := by omega
  have hnext : c i + 1 ≤ n := by omega
  have hcoarse := midpointPrefix_eq_of_fine_eq (q i) (q' i)
    (by omega : c i + 1 ≤ layerIndexDepth a i) hdepth hsame
  have hprefix : midpointPrefixCell (c i + 1) (q i) =
      midpointPrefixCell (c i + 1) (q' i) := hcoarse
  exact (hp.diverge i hnext_lt) hprefix

/-- For a fixed shape, at most one row address can be active: its cell in
each coordinate is uniquely determined by the left midpoint. -/
theorem nativeLayerRowProduct_unique_addresses {d n : ℕ}
    (q q' : MidpointGridIndex d n) (a b : LayerIndex d n)
    (ha : 0 < nativeLayerRowCoefficient q a * nativeLayerRowCoefficient q' a)
    (hb : 0 < nativeLayerRowCoefficient q b * nativeLayerRowCoefficient q' b)
    (hdepth : layerIndexDepth a = layerIndexDepth b) : a = b := by
  have hqa : 0 < nativeLayerRowCoefficient q a := by
    have hn := nativeLayerRowCoefficient_nonneg q' a
    have hnn := nativeLayerRowCoefficient_nonneg q a
    by_contra hnot
    have hz : nativeLayerRowCoefficient q a = 0 := by linarith
    rw [hz, zero_mul] at ha
    exact (lt_irrefl _ ha)
  have hqb : 0 < nativeLayerRowCoefficient q b := by
    have hn := nativeLayerRowCoefficient_nonneg q' b
    have hnn := nativeLayerRowCoefficient_nonneg q b
    by_contra hnot
    have hz : nativeLayerRowCoefficient q b = 0 := by linarith
    rw [hz, zero_mul] at hb
    exact (lt_irrefl _ hb)
  have hshape : a.1.1 = b.1.1 := by
    apply Finsupp.ext
    intro i
    exact congrArg (fun r : Fin d → ℕ => r i) hdepth
  have hsigma : a.1 = b.1 := by
    apply Subtype.ext
    exact hshape
  have hcell : layerIndexCell a = layerIndexCell b := by
    funext i
    have haddrA := nativeLayerRow_address_of_pos q a hqa i
    have haddrB := nativeLayerRow_address_of_pos q b hqb i
    have hsameDepth := congrArg (fun r : Fin d → ℕ => r i) hdepth
    have hgradeA := layerIndexDepth_grade a
    have hsumA : (∑ j : Fin d, layerIndexDepth a j) = n := by
      simpa [Finsupp.sum_fintype, layerIndexDepth] using hgradeA
    have hleA := Finset.single_le_sum
      (fun j _ => Nat.zero_le (layerIndexDepth a j)) (Finset.mem_univ i)
    have hdepthA : layerIndexDepth a i ≤ n := by omega
    have hgradeB := layerIndexDepth_grade b
    have hsumB : (∑ j : Fin d, layerIndexDepth b j) = n := by
      simpa [Finsupp.sum_fintype, layerIndexDepth] using hgradeB
    have hleB := Finset.single_le_sum
      (fun j _ => Nat.zero_le (layerIndexDepth b j)) (Finset.mem_univ i)
    have hdepthB : layerIndexDepth b i ≤ n := by omega
    have haddrB' : HaarQuarter.dyadicCellIndex (n + 1)
        ⟨layerIndexDepth a i, by omega⟩ (q i).val = layerIndexCell b i := by
      simpa [hsameDepth] using haddrB
    calc
      layerIndexCell a i = HaarQuarter.dyadicCellIndex (n + 1)
          ⟨layerIndexDepth a i, by omega⟩ (q i).val := haddrA.symm
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

/-- A pair of midpoint rows, multiplied coordinatewise in the coefficient
space of the grade-`n` native layer. -/
noncomputable def layerRowProduct {d n : ℕ}
    (left right : LayerIndex d n → ℝ) (a : LayerIndex d n) : ℝ :=
  left a * right a

/-- The active indices of a nonnegative row product. -/
noncomputable def activeLayerIndices {d n : ℕ} (f : LayerIndex d n → ℝ) : Finset (LayerIndex d n) :=
  Finset.univ.filter (fun a => 0 < f a)

/-- If a nonnegative layer weight is supported on profiles `r ≤ c`, and at
most one active address tuple occurs at each profile, then its active-index
count is bounded both by the layer size and by the complementary-grade
weak-composition count. -/
theorem activeLayerIndices_card_le_min {d n h : ℕ} (hd : 0 < d)
    (c : Fin d →₀ ℕ) (hc : c.sum (fun _ x => x) = n + h)
    (f : LayerIndex d n → ℝ)
    (hsupport : ∀ a, 0 < f a → ∀ i, layerIndexDepth a i ≤ c i)
    (hunique : ∀ a b, 0 < f a → 0 < f b →
      layerIndexDepth a = layerIndexDepth b → a = b) :
    (activeLayerIndices f).card ≤
      min (Nat.choose (n + d - 1) (d - 1))
        (Nat.choose (h + d - 1) (d - 1)) := by
  classical
  let A := activeLayerIndices f
  let ShapesN : Finset (Fin d →₀ ℕ) :=
    (Finset.univ : Finset (Fin d)).finsuppAntidiag n
  let ShapesH : Finset (Fin d →₀ ℕ) :=
    (Finset.univ : Finset (Fin d)).finsuppAntidiag h
  have hshapeN : ShapesN.card = Nat.choose (n + d - 1) (d - 1) := by
    have hc := Prefix.weak_composition_count d n
    have htop : d + n - 1 = n + d - 1 := by omega
    have hle : d - 1 ≤ n + d - 1 := by omega
    calc
      ShapesN.card = Nat.choose (d + n - 1) n := by simpa [ShapesN] using hc
      _ = Nat.choose (n + d - 1) n := by rw [htop]
      _ = Nat.choose (n + d - 1) (d - 1) := by
        calc
          Nat.choose (n + d - 1) n =
              Nat.choose (n + d - 1) (n + d - 1 - (d - 1)) := by
            congr 1
            omega
          _ = Nat.choose (n + d - 1) (d - 1) := Nat.choose_symm hle
  have hshapeH : ShapesH.card = Nat.choose (h + d - 1) (d - 1) := by
    have hc := Prefix.weak_composition_count d h
    have htop : d + h - 1 = h + d - 1 := by omega
    have hle : d - 1 ≤ h + d - 1 := by omega
    calc
      ShapesH.card = Nat.choose (d + h - 1) h := by simpa [ShapesH] using hc
      _ = Nat.choose (h + d - 1) h := by rw [htop]
      _ = Nat.choose (h + d - 1) (d - 1) := by
        calc
          Nat.choose (h + d - 1) h =
              Nat.choose (h + d - 1) (h + d - 1 - (d - 1)) := by
            congr 1
            omega
          _ = Nat.choose (h + d - 1) (d - 1) := Nat.choose_symm hle
  have hA_n : A.card ≤ ShapesN.card := by
    apply Finset.card_le_card_of_injOn (fun a => (a.1).1)
    · intro a ha
      change (a.1).1 ∈ ShapesN
      rw [Finset.mem_finsuppAntidiag']
      exact ⟨(Finset.mem_finsuppAntidiag'.mp a.1.2).1,
        Finsupp.support_subset_iff.mpr (by simp)⟩
    · intro a ha b hb heq
      exact hunique a b (Finset.mem_filter.mp ha).2
        (Finset.mem_filter.mp hb).2 (by simpa [layerIndexDepth] using heq)
  have hA_h : A.card ≤ ShapesH.card := by
    apply Finset.card_le_card_of_injOn (fun a => c - (a.1).1)
    · intro a ha
      have hactive := (Finset.mem_filter.mp ha).2
      have hb := hsupport a hactive
      have hshape := (Finset.mem_finsuppAntidiag'.mp a.1.2).1
      have hsumadd :
          ((a.1).1.sum fun _ x => x) +
            ((c - (a.1).1).sum fun _ x => x) = c.sum (fun _ x => x) := by
        have heq : (a.1).1 + (c - (a.1).1) = c := by
          ext i
          exact Nat.add_sub_of_le (hb i)
        have hadd := Finsupp.sum_hom_add_index
          (h := fun _ : Fin d => AddMonoidHom.id ℕ)
          (f := (a.1).1) (g := c - (a.1).1)
        calc
          _ = ((a.1).1 + (c - (a.1).1)).sum fun _ x => x := hadd.symm
          _ = c.sum (fun _ x => x) := by rw [heq]
      have hrem : ((c - (a.1).1).sum fun _ x => x) = h := by omega
      change c - (a.1).1 ∈ ShapesH
      rw [Finset.mem_finsuppAntidiag']
      exact ⟨hrem, Finsupp.support_subset_iff.mpr (by simp)⟩
    · intro a ha b hb heq
      have ha' := hsupport a (Finset.mem_filter.mp ha).2
      have hb' := hsupport b (Finset.mem_filter.mp hb).2
      have hshapeEq : (a.1).1 = (b.1).1 := by
        apply Finsupp.ext
        intro i
        have hi : c i - (a.1).1 i = c i - (b.1).1 i :=
          congrArg (fun r : Fin d →₀ ℕ => r i) heq
        have hia := ha' i
        have hib := hb' i
        change (a.1).1 i ≤ c i at hia
        change (b.1).1 i ≤ c i at hib
        omega
      exact hunique a b (Finset.mem_filter.mp ha).2
        (Finset.mem_filter.mp hb).2 (by
          funext i
          exact congrArg (fun r : Fin d →₀ ℕ => r i) hshapeEq)
  have hmin : A.card ≤ min ShapesN.card ShapesH.card :=
    (Nat.le_min).2 ⟨hA_n, hA_h⟩
  rw [hshapeN, hshapeH] at hmin
  simpa [A, activeLayerIndices] using hmin

/-- A finite nonnegative covariance sum is bounded by the maximum active
entry times the active-index count. -/
theorem layerRowProduct_sum_le_of_support {d n h : ℕ} (hd : 0 < d)
    (c : Fin d →₀ ℕ) (hc : c.sum (fun _ x => x) = n + h)
    (f : LayerIndex d n → ℝ) (Q : ℝ) (hQ : 0 ≤ Q)
    (hnonneg : ∀ a, 0 ≤ f a)
    (hbound : ∀ a, f a ≤ Q)
    (hsupport : ∀ a, 0 < f a → ∀ i, layerIndexDepth a i ≤ c i)
    (hunique : ∀ a b, 0 < f a → 0 < f b →
      layerIndexDepth a = layerIndexDepth b → a = b) :
    (∑ a : LayerIndex d n, f a) ≤
      Q * min (Nat.choose (n + d - 1) (d - 1))
        (Nat.choose (h + d - 1) (d - 1)) := by
  classical
  let A := activeLayerIndices f
  have hsum : (∑ a : LayerIndex d n, f a) = ∑ a ∈ A, f a := by
    calc
      (∑ a : LayerIndex d n, f a) =
          ∑ a : LayerIndex d n, if 0 < f a then f a else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        by_cases hp : 0 < f a
        · simp [hp]
        · have hz : f a = 0 := by linarith [hnonneg a]
          simp [hz]
      _ = ∑ a ∈ A, f a := by
        symm
        change (∑ a ∈ Finset.univ.filter (fun a : LayerIndex d n => 0 < f a),
            f a) = ∑ a : LayerIndex d n, if 0 < f a then f a else 0
        rw [Finset.sum_filter]
  have hentry : (∑ a ∈ A, f a) ≤ ∑ a ∈ A, Q := by
    apply Finset.sum_le_sum
    intro a ha
    exact hbound a
  have hcard := activeLayerIndices_card_le_min hd c hc f hsupport hunique
  rw [hsum]
  calc
    (∑ a ∈ A, f a) ≤ ∑ a ∈ A, Q := hentry
    _ = (A.card : ℝ) * Q := by simp [mul_comm]
    _ ≤ (min (Nat.choose (n + d - 1) (d - 1))
          (Nat.choose (h + d - 1) (d - 1)) : ℝ) * Q := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hQ
    _ = Q * min (Nat.choose (n + d - 1) (d - 1))
          (Nat.choose (h + d - 1) (d - 1)) := by
      simp only [Nat.cast_min]
      ring

/-- Actual native-layer row covariance bound. Tent positivity forces the
shape below the common-prefix cap, and the midpoint address is unique at each
shape. Each row product is bounded by the native coefficient square scale,
so the finite sum has the stated weak-composition multiplicity bound. -/
theorem nativeMidpointRowCovariance_le {d n h : ℕ} (hd : 0 < d)
    (q q' : MidpointGridIndex d n) (c : Fin d →₀ ℕ)
    (hc : c.sum (fun _ x => x) = n + h)
    (hp : MidpointCommonPrefixProfile q q' c) :
    (∑ a : LayerIndex d n,
        nativeLayerRowCoefficient q a * nativeLayerRowCoefficient q' a) ≤
      (1 / (2 : ℝ) ^ (n + 2 * d)) *
        min (Nat.choose (n + d - 1) (d - 1))
          (Nat.choose (h + d - 1) (d - 1)) := by
  let f : LayerIndex d n → ℝ := fun a =>
    nativeLayerRowCoefficient q a * nativeLayerRowCoefficient q' a
  let Q : ℝ := 1 / (2 : ℝ) ^ (n + 2 * d)
  have hQ : 0 ≤ Q := by positivity
  have hnonneg : ∀ a, 0 ≤ f a := by
    intro a
    dsimp [f]
    exact mul_nonneg (nativeLayerRowCoefficient_nonneg q a)
      (nativeLayerRowCoefficient_nonneg q' a)
  have hbound : ∀ a, f a ≤ Q := by
    intro a
    have hleft := nativeLayerRowCoefficient_sq_le q a
    have hright := nativeLayerRowCoefficient_sq_le q' a
    have hsq := sq_nonneg
      (nativeLayerRowCoefficient q a - nativeLayerRowCoefficient q' a)
    dsimp [f, Q]
    nlinarith
  have hsupport : ∀ a, 0 < f a → ∀ i, layerIndexDepth a i ≤ c i := by
    intro a ha
    exact nativeLayerRowProduct_support (h := h) q q' c hp a
      (by simpa [f] using ha)
  have hunique : ∀ a b, 0 < f a → 0 < f b →
      layerIndexDepth a = layerIndexDepth b → a = b := by
    intro a b ha hb hdepth
    exact nativeLayerRowProduct_unique_addresses q q' a b
      (by simpa [f] using ha) (by simpa [f] using hb) hdepth
  have hsum := layerRowProduct_sum_le_of_support hd c hc f Q hQ
    hnonneg hbound hsupport hunique
  simpa [f, Q] using hsum

end BrownianSharp
