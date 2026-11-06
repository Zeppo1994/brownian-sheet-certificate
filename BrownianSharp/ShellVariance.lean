import BrownianSharp.SmoothLayer
import BrownianSharp.NativeGaussian

/-!
Finite common-prefix shells on the actual midpoint product grid.  A pair of
midpoint addresses is assigned its exact longest common dyadic prefix in each
coordinate.  The resulting profile is the native profile consumed by the
covariance and moment modules.
-/

open scoped BigOperators

namespace BrownianSharp

/-- Prefix depths at which two one-dimensional midpoint addresses still
belong to the same dyadic cell. -/
def midpointCommonPrefixCandidates {n : ℕ}
    (q q' : MidpointGridCoordinate n) : Finset ℕ :=
  (Finset.range (n + 2)).filter
    (fun r => midpointPrefixCell r q = midpointPrefixCell r q')

private theorem midpointPrefixCell_zero {n : ℕ}
    (q : MidpointGridCoordinate n) : midpointPrefixCell 0 q = 0 := by
  have hdiv : q.val / 2 ^ (n + 1) = 0 := Nat.div_eq_of_lt q.isLt
  simpa [midpointPrefixCell, HaarQuarter.dyadicCellIndex] using hdiv

private theorem midpointCommonPrefixCandidates_nonempty {n : ℕ}
    (q q' : MidpointGridCoordinate n) :
    (midpointCommonPrefixCandidates q q').Nonempty := by
  refine ⟨0, ?_⟩
  simp [midpointCommonPrefixCandidates, midpointPrefixCell_zero]

/-- The exact number of initial address bits shared by a pair of grid points.
It ranges from zero through the full grid depth `n+1`. -/
noncomputable def midpointCommonPrefixDepth {n : ℕ}
    (q q' : MidpointGridCoordinate n) : ℕ := by
  exact (midpointCommonPrefixCandidates q q').max'
    (midpointCommonPrefixCandidates_nonempty q q')

/-- The coordinatewise exact common-prefix cap, stored as a Finsupp profile. -/
noncomputable def midpointCommonPrefixCaps {d n : ℕ}
    (q q' : MidpointGridIndex d n) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    (fun i => midpointCommonPrefixDepth (q i) (q' i))

@[simp] theorem midpointCommonPrefixCaps_apply {d n : ℕ}
    (q q' : MidpointGridIndex d n) (i : Fin d) :
    midpointCommonPrefixCaps q q' i = midpointCommonPrefixDepth (q i) (q' i) := by
  simp [midpointCommonPrefixCaps]

/-- The maximum prefix candidate is within the full grid depth. -/
theorem midpointCommonPrefixDepth_le {n : ℕ}
    (q q' : MidpointGridCoordinate n) :
    midpointCommonPrefixDepth q q' ≤ n + 1 := by
  classical
  unfold midpointCommonPrefixDepth
  have hmem := (midpointCommonPrefixCandidates q q').max'_mem
    (midpointCommonPrefixCandidates_nonempty q q')
  have hrange := (Finset.mem_filter.mp hmem).1
  change (midpointCommonPrefixCandidates q q').max' _ ∈
    Finset.range (n + 2) at hrange
  have hrange' : (midpointCommonPrefixCandidates q q').max'
      (midpointCommonPrefixCandidates_nonempty q q') < n + 2 :=
    Finset.mem_range.mp hrange
  omega

/-- The exact maximal prefix profile satisfies the common-prefix hypotheses
used by both the native Haar and smooth-atom covariance support theorems. -/
theorem midpointCommonPrefixCaps_profile {d n : ℕ}
    (q q' : MidpointGridIndex d n) :
    MidpointCommonPrefixProfile q q' (midpointCommonPrefixCaps q q') := by
  classical
  constructor
  · intro i
    simp only [midpointCommonPrefixCaps_apply]
    exact midpointCommonPrefixDepth_le (q i) (q' i)
  · intro i
    simp only [midpointCommonPrefixCaps_apply]
    unfold midpointCommonPrefixDepth
    exact (Finset.mem_filter.mp
      ((midpointCommonPrefixCandidates (q i) (q' i)).max'_mem
        (midpointCommonPrefixCandidates_nonempty (q i) (q' i)))).2
  · intro i hi hEq
    simp only [midpointCommonPrefixCaps_apply] at hi ⊢
    have hEq' : midpointPrefixCell
        (midpointCommonPrefixDepth (q i) (q' i) + 1) (q i) =
          midpointPrefixCell (midpointCommonPrefixDepth (q i) (q' i) + 1) (q' i) := by
      simpa only [midpointCommonPrefixCaps_apply] using hEq
    unfold midpointCommonPrefixDepth at hi
    unfold midpointCommonPrefixDepth at hEq'
    have hnonempty := midpointCommonPrefixCandidates_nonempty (q i) (q' i)
    have hmem : (midpointCommonPrefixCandidates (q i) (q' i)).max'
        hnonempty + 1 ∈ midpointCommonPrefixCandidates (q i) (q' i) := by
      change (midpointCommonPrefixCandidates (q i) (q' i)).max'
          hnonempty + 1 ∈
        (Finset.range (n + 2)).filter
          (fun r => midpointPrefixCell r (q i) = midpointPrefixCell r (q' i))
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (by omega), hEq'⟩
    have hle := (midpointCommonPrefixCandidates (q i) (q' i)).le_max'
      _ hmem
    omega

/-- One-coordinate midpoint addresses sharing a prefix of length `r`. -/
def midpointCoordinatePrefixFiber {n : ℕ} (r : ℕ)
    (q : MidpointGridCoordinate n) :=
  {k : MidpointGridCoordinate n // midpointPrefixCell r k = midpointPrefixCell r q}

noncomputable instance midpointCoordinatePrefixFiberFintype {n r : ℕ}
    (q : MidpointGridCoordinate n) : Fintype (midpointCoordinatePrefixFiber r q) := by
  letI : Finite (midpointCoordinatePrefixFiber r q) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  exact Fintype.ofFinite _

/-- The cardinality of one fixed midpoint prefix fiber is at most the number
of descendants of a cell at depth `r`, including the full-depth endpoint. -/
theorem midpointCoordinatePrefixFiber_card_le {n r : ℕ}
    (hr : r ≤ n + 1) (q : MidpointGridCoordinate n) :
    Fintype.card (midpointCoordinatePrefixFiber r q) ≤ 2 ^ (n + 1 - r) := by
  classical
  by_cases hlt : r ≤ n
  · let l : Fin (n + 1) := ⟨r, by omega⟩
    let cell : Fin (2 ^ r) := ⟨
      HaarQuarter.dyadicCellIndex (n + 1) l q.val,
      HaarQuarter.dyadicCellIndex_lt (n + 1) l q.isLt⟩
    have hcard := Prefix.common_prefix_fiber_card l cell
    let e : midpointCoordinatePrefixFiber r q ≃
        {k : MidpointGridCoordinate n //
          HaarQuarter.dyadicCellIndex (n + 1) l k.val = cell.val} := {
      toFun := fun k => ⟨k.val, by
        simpa [midpointPrefixCell, hlt, l, cell] using k.property⟩
      invFun := fun k => ⟨k.val, by
        simpa [midpointPrefixCell, hlt, l, cell] using k.property⟩
      left_inv := by intro k; apply Subtype.ext; rfl
      right_inv := by intro k; apply Subtype.ext; rfl }
    have hEq : Fintype.card (midpointCoordinatePrefixFiber r q) =
        2 ^ (n + 1 - r) := by
      rw [Fintype.card_congr e]
      simpa [l, cell] using hcard
    exact hEq.le
  · have heq : r = n + 1 := by omega
    subst r
    haveI : Subsingleton (midpointCoordinatePrefixFiber (n + 1) q) := by
      refine ⟨?_⟩
      intro a b
      apply Subtype.ext
      apply Fin.ext
      have ha := a.property
      have hb := b.property
      simpa [midpointCoordinatePrefixFiber, midpointPrefixCell] using
        ha.trans hb.symm
    have hcard : Fintype.card (midpointCoordinatePrefixFiber (n + 1) q) ≤ 1 :=
      Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    simpa using hcard

/-- Grid pairs represented coordinatewise, which exposes the product fiber
structure for a fixed common-prefix cap. -/
abbrev MidpointPairGrid (d n : ℕ) :=
  Fin d → MidpointGridCoordinate n × MidpointGridCoordinate n

/-- Pair-grid points whose two coordinates agree in every prefix cell named
by `c`. -/
def midpointPairPrefixFiber {d n : ℕ} (c : Fin d →₀ ℕ) :=
  {p : MidpointPairGrid d n //
    ∀ i, midpointPrefixCell (c i) (p i).1 = midpointPrefixCell (c i) (p i).2}

noncomputable instance midpointPairPrefixFiberFintype {d n : ℕ}
    (c : Fin d →₀ ℕ) : Fintype (midpointPairPrefixFiber (d := d) (n := n) c) := by
  letI : Finite (midpointPairPrefixFiber (d := d) (n := n) c) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  exact Fintype.ofFinite _

def midpointCoordinatePairPrefixFiber {n : ℕ} (r : ℕ) :=
  {p : MidpointGridCoordinate n × MidpointGridCoordinate n //
    midpointPrefixCell r p.1 = midpointPrefixCell r p.2}

noncomputable instance midpointCoordinatePairPrefixFiberFintype {n : ℕ} (r : ℕ) :
    Fintype (midpointCoordinatePairPrefixFiber (n := n) r) := by
  letI : Finite (midpointCoordinatePairPrefixFiber (n := n) r) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  exact Fintype.ofFinite _

/-- A prefix-pair fiber is the product of its one-coordinate fibers. -/
noncomputable def midpointPairPrefixFiberEquiv {d n : ℕ}
    (c : Fin d →₀ ℕ) : midpointPairPrefixFiber (d := d) (n := n) c ≃
      ((i : Fin d) →
        midpointCoordinatePairPrefixFiber (n := n) (c i)) where
  toFun p := fun i =>
    (⟨p.val i, p.property i⟩ :
      midpointCoordinatePairPrefixFiber (n := n) (c i))
  invFun p :=
    (⟨fun i => (p i).val, fun i => (p i).property⟩ :
      midpointPairPrefixFiber (d := d) (n := n) c)
  left_inv p := by
    apply Subtype.ext
    funext i
    rfl
  right_inv p := by
    funext i
    apply Subtype.ext
    rfl

/-- In one coordinate, the number of address pairs sharing an `r`-bit
prefix is at most `2^(n+1) 2^(n+1-r)`. -/
theorem midpointCoordinatePairPrefixFiber_card_le {n r : ℕ}
    (hr : r ≤ n + 1) :
    Fintype.card (midpointCoordinatePairPrefixFiber (n := n) r) ≤
      2 ^ (n + 1) * 2 ^ (n + 1 - r) := by
  classical
  let e : midpointCoordinatePairPrefixFiber (n := n) r ≃
      Σ q : MidpointGridCoordinate n, midpointCoordinatePrefixFiber r q := {
    toFun := fun p => ⟨p.val.1, ⟨p.val.2, p.property.symm⟩⟩
    invFun := fun p => ⟨(p.1, p.2.val), p.2.property.symm⟩
    left_inv := by intro p; apply Subtype.ext; rfl
    right_inv := by intro p; cases p with | mk q k => cases k; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  calc
    (∑ q : MidpointGridCoordinate n,
        Fintype.card (midpointCoordinatePrefixFiber r q)) ≤
      ∑ _q : MidpointGridCoordinate n, 2 ^ (n + 1 - r) := by
        apply Finset.sum_le_sum
        intro q hq
        exact midpointCoordinatePrefixFiber_card_le hr q
    _ = 2 ^ (n + 1) * 2 ^ (n + 1 - r) := by
      simp [MidpointGridCoordinate, Finset.sum_const]

/-- Pair-grid prefix fibers factor by coordinate and are bounded by the
product of the one-coordinate pair-fiber bounds. -/
theorem midpointPairPrefixFiber_card_le {d n : ℕ}
    (c : Fin d →₀ ℕ) (hc : ∀ i, c i ≤ n + 1) :
    Fintype.card (midpointPairPrefixFiber (d := d) (n := n) c) ≤
      ∏ i : Fin d, (2 ^ (n + 1) * 2 ^ (n + 1 - c i)) := by
  classical
  rw [Fintype.card_congr (midpointPairPrefixFiberEquiv c), Fintype.card_pi]
  apply Finset.prod_le_prod
  intro i hi
  exact midpointCoordinatePairPrefixFiber_card_le (hc i)

/-- Clearing the prefix probability denominator shows that a fixed-profile
pair fiber occupies at most the `2^(-sum c)` fraction of the full pair grid. -/
theorem midpointPairPrefixFiber_card_mul_pow_le {d n : ℕ}
    (c : Fin d →₀ ℕ) (hc : ∀ i, c i ≤ n + 1) :
    Fintype.card (midpointPairPrefixFiber (d := d) (n := n) c) *
        2 ^ (c.sum fun _ x => x) ≤ Fintype.card (MidpointPairGrid d n) := by
  classical
  let L := n + 1
  have hfiber := midpointPairPrefixFiber_card_le c hc
  have hshapeSum : (∑ i : Fin d, c i) = c.sum (fun _ x => x) := by
    simp [Finsupp.sum_fintype]
  have hfactor :
      (∏ i : Fin d, (2 ^ L * 2 ^ (L - c i))) * 2 ^ (c.sum fun _ x => x) =
        ∏ i : Fin d, 2 ^ (2 * L) := by
    rw [← hshapeSum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    calc
      (2 ^ L * 2 ^ (L - c i)) * 2 ^ (c i) =
          2 ^ (L + (L - c i) + c i) := by
            rw [← Nat.pow_add, ← Nat.pow_add]
      _ = 2 ^ (2 * L) := by
            congr 1
            have hcL : c i ≤ L := by simpa [L] using hc i
            have hsub : L - c i + c i = L := Nat.sub_add_cancel hcL
            rw [Nat.add_assoc]
            rw [hsub]
            omega
  have hgrid' : Fintype.card (MidpointPairGrid d n) =
      (2 ^ (n + 1) * 2 ^ (n + 1)) ^ d := by
    simp [MidpointPairGrid, MidpointGridCoordinate, Fintype.card_pi,
      Fintype.card_prod]
  have hbase : 2 ^ L * 2 ^ L = 2 ^ (2 * L) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hgrid : Fintype.card (MidpointPairGrid d n) =
      ∏ i : Fin d, 2 ^ (2 * L) := by
    rw [hgrid']
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← hbase]
  calc
    Fintype.card (midpointPairPrefixFiber (d := d) (n := n) c) *
        2 ^ (c.sum fun _ x => x) ≤
        (∏ i : Fin d, (2 ^ L * 2 ^ (L - c i))) *
          2 ^ (c.sum fun _ x => x) :=
      Nat.mul_le_mul_right _ hfiber
    _ = ∏ i : Fin d, 2 ^ (2 * L) := hfactor
    _ = Fintype.card (MidpointPairGrid d n) := hgrid.symm

/-- Grade-`u` prefix profiles whose coordinates fit the grid depth. -/
def midpointPairPrefixShape (d n u : ℕ) :=
  {c : Shape d u // ∀ i : Fin d, c.1 i ≤ n + 1}

noncomputable instance midpointPairPrefixShapeFintype (d n u : ℕ) :
    Fintype (midpointPairPrefixShape d n u) := by
  letI : Finite (midpointPairPrefixShape d n u) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  exact Fintype.ofFinite _

/-- Exact common-prefix grade of a pair of midpoint grid points. -/
noncomputable def midpointCommonPrefixGrade {d n : ℕ} (p : MidpointPairGrid d n) : ℕ :=
  (midpointCommonPrefixCaps (fun i => (p i).1) (fun i => (p i).2)).sum
    (fun _ x => x)

/-- The set of pairs whose exact prefix profile has total grade `u`. -/
def midpointPairShell {d n : ℕ} (u : ℕ) :=
  {p : MidpointPairGrid d n // midpointCommonPrefixGrade p = u}

noncomputable instance midpointPairShellFintype {d n u : ℕ} :
    Fintype (midpointPairShell (d := d) (n := n) u) := by
  letI : Finite (midpointPairShell (d := d) (n := n) u) :=
    Finite.of_injective Subtype.val Subtype.coe_injective
  exact Fintype.ofFinite _

/-- Exact prefix grade never exceeds the total number of coordinate bits in
the midpoint grid. -/
theorem midpointCommonPrefixGrade_le {d n : ℕ} (p : MidpointPairGrid d n) :
    midpointCommonPrefixGrade p ≤ d * (n + 1) := by
  let c := midpointCommonPrefixCaps (fun i => (p i).1) (fun i => (p i).2)
  have hgrade : midpointCommonPrefixGrade p = ∑ i : Fin d, c i := by
    simp [midpointCommonPrefixGrade, c, Finsupp.sum_fintype]
  calc
    midpointCommonPrefixGrade p = ∑ i : Fin d, c i := hgrade
    _ ≤ ∑ _i : Fin d, (n + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      exact midpointCommonPrefixDepth_le ((p i).1) ((p i).2)
    _ = d * (n + 1) := by simp

private def midpointPairShellProfileSigma {d n : ℕ} (u : ℕ) :=
  Σ c : midpointPairPrefixShape d n u,
    midpointPairPrefixFiber (d := d) (n := n) c.1.1

noncomputable instance midpointPairShellProfileSigmaFintype {d n u : ℕ} :
    Fintype (midpointPairShellProfileSigma (d := d) (n := n) u) := by
  classical
  letI : Fintype (midpointPairPrefixShape d n u) :=
    midpointPairPrefixShapeFintype d n u
  letI : ∀ c : midpointPairPrefixShape d n u,
      Fintype (midpointPairPrefixFiber (d := d) (n := n) c.1.1) :=
    fun c => midpointPairPrefixFiberFintype c.1.1
  change Fintype (Σ c : midpointPairPrefixShape d n u,
    midpointPairPrefixFiber (d := d) (n := n) c.1.1)
  infer_instance

/-- Each shell pair maps injectively to its exact profile and fiber. -/
private noncomputable def midpointPairShellProfileMap {d n u : ℕ}
    (p : midpointPairShell (d := d) (n := n) u) :
    midpointPairShellProfileSigma (d := d) (n := n) u := by
  classical
  let c := midpointCommonPrefixCaps (fun i => (p.1 i).1) (fun i => (p.1 i).2)
  have hgrade : (c.sum fun _ x => x) = u := by
    simpa [c, midpointCommonPrefixGrade] using p.2
  have hmem : c ∈ (Finset.univ : Finset (Fin d)).finsuppAntidiag u := by
    rw [Finset.mem_finsuppAntidiag']
    refine ⟨hgrade, ?_⟩
    simp
  have hcap : ∀ i, c i ≤ n + 1 := by
    intro i
    exact midpointCommonPrefixDepth_le ((p.1 i).1) ((p.1 i).2)
  refine ⟨⟨⟨c, hmem⟩, hcap⟩, ⟨p.1, ?_⟩⟩
  intro i
  exact (midpointCommonPrefixCaps_profile
    (fun i => (p.1 i).1) (fun i => (p.1 i).2)).agree i

private theorem midpointPairShellProfileMap_injective {d n u : ℕ} :
    Function.Injective (midpointPairShellProfileMap (d := d) (n := n) (u := u)) := by
  intro p q h
  apply Subtype.ext
  have hval := congrArg
    (fun z : midpointPairShellProfileSigma (d := d) (n := n) u => z.2.1) h
  exact hval

/-- Exact prefix-grade shell cardinality bound, with the profile count given
by the weak-composition number. -/
theorem midpointPairShell_card_mul_pow_le {d n u : ℕ} (hd : 0 < d) :
    Fintype.card (midpointPairShell (d := d) (n := n) u) * 2 ^ u ≤
      Nat.choose (u + d - 1) (d - 1) * Fintype.card (MidpointPairGrid d n) := by
  classical
  letI := midpointPairPrefixShapeFintype d n u
  have hinj := Fintype.card_le_of_injective
    (midpointPairShellProfileMap (d := d) (n := n) (u := u))
    (midpointPairShellProfileMap_injective (d := d) (n := n) (u := u))
  have hsum :
      (∑ c : midpointPairPrefixShape d n u,
        Fintype.card (midpointPairPrefixFiber (d := d) (n := n) c.1.1)) * 2 ^ u ≤
        Fintype.card (midpointPairPrefixShape d n u) *
          Fintype.card (MidpointPairGrid d n) := by
    rw [Finset.sum_mul]
    calc
      (∑ c : midpointPairPrefixShape d n u,
          Fintype.card (midpointPairPrefixFiber (d := d) (n := n) c.1.1) * 2 ^ u) ≤
        ∑ _c : midpointPairPrefixShape d n u, Fintype.card (MidpointPairGrid d n) := by
          apply Finset.sum_le_sum
          intro c hc
          have hgrade : (c.1.1.sum fun _ x => x) = u :=
            (Finset.mem_finsuppAntidiag'.mp c.1.2).1
          simpa [hgrade] using midpointPairPrefixFiber_card_mul_pow_le c.1.1 c.2
      _ = Fintype.card (midpointPairPrefixShape d n u) *
          Fintype.card (MidpointPairGrid d n) := by simp
  have hshape : Fintype.card (midpointPairPrefixShape d n u) ≤
      Nat.choose (u + d - 1) (d - 1) := by
    calc
      Fintype.card (midpointPairPrefixShape d n u) ≤ Fintype.card (Shape d u) :=
        Fintype.card_le_of_injective Subtype.val Subtype.coe_injective
      _ = Nat.choose (u + d - 1) (d - 1) := shape_card d u hd
  calc
    Fintype.card (midpointPairShell (d := d) (n := n) u) * 2 ^ u ≤
        Fintype.card (midpointPairPrefixShape d n u) *
          Fintype.card (MidpointPairGrid d n) := by
            calc
              Fintype.card (midpointPairShell (d := d) (n := n) u) * 2 ^ u ≤
                  Fintype.card (midpointPairShellProfileSigma (d := d) (n := n) u) * 2 ^ u :=
                Nat.mul_le_mul_right _ hinj
              _ = (∑ c : midpointPairPrefixShape d n u,
                  Fintype.card (midpointPairPrefixFiber (d := d) (n := n) c.1.1)) * 2 ^ u := by
                    change Fintype.card (Σ c : midpointPairPrefixShape d n u,
                      midpointPairPrefixFiber (d := d) (n := n) c.1.1) * 2 ^ u = _
                    rw [Fintype.card_sigma]
              _ ≤ Fintype.card (midpointPairPrefixShape d n u) *
                  Fintype.card (MidpointPairGrid d n) := hsum
    _ ≤ Nat.choose (u + d - 1) (d - 1) * Fintype.card (MidpointPairGrid d n) :=
      Nat.mul_le_mul_right _ hshape

/-- If the total exact-prefix grade is below the layer grade, every native
row-product term vanishes. Consequently the normalized row correlation is
zero whenever the two row variances are positive. -/
/- High-power covariance kernel used in the all-order Gaussian moment estimate. -/
noncomputable def highPowerPairKernel (p : ℕ) (rho : ℝ) : ℝ :=
  4 * (p : ℝ) ^ 2 * rho ^ 2 * Real.exp (2 * (p : ℝ) * |rho|)

theorem nativeRowCorrelation_eq_zero_of_prefix_grade_lt {d n u : ℕ}
    (q q' : MidpointGridIndex d n) (c : Fin d →₀ ℕ)
    (hp : MidpointCommonPrefixProfile q q' c)
    (hc : c.sum (fun _ x => x) = u) (hu : u < n) :
    nativeRowCorrelation q q' = 0 := by
  have hnum : (∑ a : LayerIndex d n,
      nativeLayerRowCoefficient q a * nativeLayerRowCoefficient q' a) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    by_contra hne
    have hnonneg : 0 ≤ nativeLayerRowCoefficient q a * nativeLayerRowCoefficient q' a :=
      mul_nonneg (nativeLayerRowCoefficient_nonneg q a)
        (nativeLayerRowCoefficient_nonneg q' a)
    have hpos : 0 < nativeLayerRowCoefficient q a * nativeLayerRowCoefficient q' a :=
      lt_of_le_of_ne hnonneg (Ne.symm hne)
    have hsupport := nativeLayerRowProduct_support (h := 0) q q' c hp a hpos
    have hgradeR : (∑ i : Fin d, layerIndexDepth a i) = n := by
      simpa [layerIndexDepth, Finsupp.sum_fintype] using layerIndexDepth_grade a
    have hgradeC : (∑ i : Fin d, c i) = u := by
      simpa [Finsupp.sum_fintype] using hc
    have hfalse := Prefix.no_shape_below_prefix_when_grade_exceeds
      (layerIndexDepth a) (fun i => c i) hsupport hgradeR (by omega)
    exact hfalse
  unfold nativeRowCorrelation
  rw [hnum]
  simp

/-- Below the layer grade the high-power covariance kernel also vanishes,
since its correlation argument is exactly zero. -/
theorem highPowerPairKernel_eq_zero_of_prefix_grade_lt {d n u p : ℕ}
    (q q' : MidpointGridIndex d n) (c : Fin d →₀ ℕ)
    (hp : MidpointCommonPrefixProfile q q' c)
    (hc : c.sum (fun _ x => x) = u) (hu : u < n) :
    highPowerPairKernel p (nativeRowCorrelation q q') = 0 := by
  rw [nativeRowCorrelation_eq_zero_of_prefix_grade_lt q q' c hp hc hu]
  simp [highPowerPairKernel]

/-- A shell-specific rho cap retains the quadratic rho decay while bounding
the exponential by its value at the cap. -/
theorem highPowerPairKernel_le_of_le {p : ℕ} {rho R : ℝ}
    (hrho0 : 0 ≤ rho) (hrhoR : rho ≤ R) (hR : 0 ≤ R) :
    highPowerPairKernel p rho ≤
      4 * (p : ℝ) ^ 2 * R ^ 2 * Real.exp (2 * (p : ℝ) * R) := by
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hExp : Real.exp (2 * (p : ℝ) * |rho|) ≤
      Real.exp (2 * (p : ℝ) * R) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hrho0]
    exact mul_le_mul_of_nonneg_left hrhoR (by positivity)
  have hSq : rho ^ 2 ≤ R ^ 2 := by nlinarith
  unfold highPowerPairKernel
  calc
    4 * (p : ℝ) ^ 2 * rho ^ 2 * Real.exp (2 * (p : ℝ) * |rho|) ≤
        4 * (p : ℝ) ^ 2 * rho ^ 2 * Real.exp (2 * (p : ℝ) * R) := by
          apply mul_le_mul_of_nonneg_left hExp
          positivity
    _ ≤ 4 * (p : ℝ) ^ 2 * R ^ 2 * Real.exp (2 * (p : ℝ) * R) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left hSq (by positivity)

end BrownianSharp
