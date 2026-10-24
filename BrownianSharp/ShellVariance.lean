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

private def midpointPairShellSigma {d n : ℕ} :=
  Σ u : Fin (d * (n + 1) + 1), midpointPairShell (d := d) (n := n) u.val

/-- A grid pair belongs to exactly one exact-prefix shell, so the whole pair
grid is equivalent to the finite sigma of its shells. -/
noncomputable def midpointPairShellDecompositionEquiv (d n : ℕ) :
    MidpointPairGrid d n ≃ midpointPairShellSigma (d := d) (n := n) where
  toFun p :=
    ⟨⟨midpointCommonPrefixGrade p,
      Nat.lt_succ_of_le (midpointCommonPrefixGrade_le p)⟩, ⟨p, rfl⟩⟩
  invFun x := x.2.1
  left_inv p := rfl
  right_inv x := by
    rcases x with ⟨u, p⟩
    rcases p with ⟨p, hp⟩
    have hidx : (⟨midpointCommonPrefixGrade p,
        Nat.lt_succ_of_le (midpointCommonPrefixGrade_le p)⟩ :
        Fin (d * (n + 1) + 1)) = u := Fin.ext hp
    subst u
    rfl

/-- Summing over the full pair grid is the finite sum of the exact-shell
sums. This is the partition identity needed to aggregate covariance bounds. -/
theorem midpointPairGrid_sum_eq_shell_sums {d n : ℕ} (f : MidpointPairGrid d n → ℝ) :
    (∑ p : MidpointPairGrid d n, f p) =
      ∑ u : Fin (d * (n + 1) + 1),
        ∑ p : midpointPairShell (d := d) (n := n) u.val, f p.1 := by
  classical
  letI : ∀ u : Fin (d * (n + 1) + 1),
      Fintype (midpointPairShell (d := d) (n := n) u.val) :=
    fun _ => midpointPairShellFintype
  letI : Fintype (midpointPairShellSigma (d := d) (n := n)) := by
    unfold midpointPairShellSigma
    infer_instance
  rw [Fintype.sum_equiv (midpointPairShellDecompositionEquiv d n) f
    (fun x => f x.2.1) (by intro p; rfl)]
  unfold midpointPairShellSigma
  rw [Fintype.sum_sigma]

/-- Product-grid pair sums decompose by the same exact common-prefix shells.
This is the interface matching the usual second-moment double sum over two
independent uniform grid points. -/
theorem midpointGridPair_sum_eq_shell_sums {d n : ℕ}
    (f : MidpointGridIndex d n → MidpointGridIndex d n → ℝ) :
    (∑ q : MidpointGridIndex d n, ∑ q' : MidpointGridIndex d n, f q q') =
      ∑ u : Fin (d * (n + 1) + 1),
        ∑ p : midpointPairShell (d := d) (n := n) u.val,
          f (fun i => (p.1 i).1) (fun i => (p.1 i).2) := by
  classical
  let e : (MidpointGridIndex d n × MidpointGridIndex d n) ≃ MidpointPairGrid d n := {
    toFun := fun q => fun i => (q.1 i, q.2 i)
    invFun := fun p => (fun i => (p i).1, fun i => (p i).2)
    left_inv := by intro q; cases q; rfl
    right_inv := by
      intro p
      funext i
      exact Prod.ext rfl rfl }
  calc
    (∑ q : MidpointGridIndex d n, ∑ q' : MidpointGridIndex d n, f q q') =
        ∑ z : MidpointGridIndex d n × MidpointGridIndex d n, f z.1 z.2 := by
          rw [← Fintype.sum_prod_type']
    _ = ∑ p : MidpointPairGrid d n,
        f (fun i => (p i).1) (fun i => (p i).2) :=
          Fintype.sum_equiv e (fun q => f q.1 q.2)
            (fun p => f (fun i => (p i).1) (fun i => (p i).2)) (by
              intro q
              rfl)
    _ = ∑ u : Fin (d * (n + 1) + 1),
        ∑ p : midpointPairShell (d := d) (n := n) u.val,
          f (fun i => (p.1 i).1) (fun i => (p.1 i).2) :=
            midpointPairGrid_sum_eq_shell_sums _

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

/-- A uniformly bounded observable on one exact-prefix shell contributes at
most the weak-composition shell weight times its bound to the pair-grid
average. The denominator is kept cleared, avoiding any hidden probability
normalization. -/
theorem midpointPairShell_sum_mul_pow_le {d n u : ℕ} (hd : 0 < d)
    (f : midpointPairShell (d := d) (n := n) u → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hf : ∀ p, f p ≤ B) :
    (∑ p : midpointPairShell (d := d) (n := n) u, f p) * (2 ^ u : ℝ) ≤
      (Nat.choose (u + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) * B := by
  have hsum : (∑ p : midpointPairShell (d := d) (n := n) u, f p) ≤
      (Fintype.card (midpointPairShell (d := d) (n := n) u) : ℝ) * B := by
    calc
      (∑ p : midpointPairShell (d := d) (n := n) u, f p) ≤
          ∑ _p : midpointPairShell (d := d) (n := n) u, B := by
            apply Finset.sum_le_sum
            intro p hp
            exact hf p
      _ = (Fintype.card (midpointPairShell (d := d) (n := n) u) : ℝ) * B := by
            simp
  have hcard := midpointPairShell_card_mul_pow_le (d := d) (n := n) (u := u) hd
  have hcardR :
      (Fintype.card (midpointPairShell (d := d) (n := n) u) : ℝ) *
          (2 ^ u : ℝ) ≤
        (Nat.choose (u + d - 1) (d - 1) : ℝ) *
          (Fintype.card (MidpointPairGrid d n) : ℝ) := by
    exact_mod_cast hcard
  calc
    (∑ p : midpointPairShell (d := d) (n := n) u, f p) * (2 ^ u : ℝ) ≤
        ((Fintype.card (midpointPairShell (d := d) (n := n) u) : ℝ) * B) *
          (2 ^ u : ℝ) := mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = ((Fintype.card (midpointPairShell (d := d) (n := n) u) : ℝ) *
          (2 ^ u : ℝ)) * B := by ring
    _ ≤ ((Nat.choose (u + d - 1) (d - 1) : ℝ) *
          (Fintype.card (MidpointPairGrid d n) : ℝ)) * B :=
        mul_le_mul_of_nonneg_right hcardR hB
    _ = _ := by ring

/-- The actual native normalized Gaussian row correlations obey a shellwise
average bound. The row variance floor is an explicit hypothesis; the theorem
does not assume every midpoint row is nondegenerate without proof. -/
theorem nativeRowCorrelation_shell_sum_mul_pow_le {d n h : ℕ} (hd : 0 < d)
    {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hvar : ∀ q : MidpointGridIndex d n, v₀ ≤ nativeLayerRowVariance q) :
    (∑ p : midpointPairShell (d := d) (n := n) (n + h),
      nativeRowCorrelation (fun i => (p.1 i).1) (fun i => (p.1 i).2)) *
        (2 ^ (n + h) : ℝ) ≤
      (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) *
          ((1 / (2 : ℝ) ^ (n + 2 * d)) *
            (Nat.min (Nat.choose (n + d - 1) (d - 1))
              (Nat.choose (h + d - 1) (d - 1)) : ℝ) / v₀) := by
  let B : ℝ := (1 / (2 : ℝ) ^ (n + 2 * d)) *
    (Nat.min (Nat.choose (n + d - 1) (d - 1))
      (Nat.choose (h + d - 1) (d - 1)) : ℝ) / v₀
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  apply midpointPairShell_sum_mul_pow_le (d := d) (n := n) (u := n + h)
    hd (fun p => nativeRowCorrelation (fun i => (p.1 i).1) (fun i => (p.1 i).2)) B hB
  intro p
  let q : MidpointGridIndex d n := fun i => (p.1 i).1
  let q' : MidpointGridIndex d n := fun i => (p.1 i).2
  let c := midpointCommonPrefixCaps q q'
  have hgrade : (c.sum fun _ x => x) = n + h := by
    simpa [c, q, q', midpointCommonPrefixGrade] using p.2
  have hp : MidpointCommonPrefixProfile q q' c := by
    simpa [c, q, q'] using midpointCommonPrefixCaps_profile q q'
  have hq : v₀ ≤ nativeLayerRowVariance q := hvar q
  have hq' : v₀ ≤ nativeLayerRowVariance q' := hvar q'
  have hcorr := nativeRowCorrelation_le_prefix hd q q' c hgrade hp hv₀ hq hq'
  simpa [B] using hcorr

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

/-- The full native high-power covariance sum is the sum of the exact prefix
shells at or above the layer grade. Every lower shell contributes zero by
support, so this is the finite deterministic shell decomposition used in the
variance aggregation. -/
theorem nativeHighPowerKernel_grid_sum_eq_shells {d n p : ℕ} :
    (∑ x : MidpointPairGrid d n,
      highPowerPairKernel p (nativeRowCorrelation (fun i => (x i).1)
        (fun i => (x i).2))) =
      ∑ u : Fin (d * (n + 1) + 1),
        if n ≤ u.val then
          ∑ x : midpointPairShell (d := d) (n := n) u.val,
            highPowerPairKernel p (nativeRowCorrelation (fun i => (x.1 i).1)
              (fun i => (x.1 i).2))
        else 0 := by
  classical
  rw [midpointPairGrid_sum_eq_shell_sums]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hun : n ≤ u.val
  · simp [hun]
  · simp only [hun, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro x hx
    let q : MidpointGridIndex d n := fun i => (x.1 i).1
    let q' : MidpointGridIndex d n := fun i => (x.1 i).2
    let c := midpointCommonPrefixCaps q q'
    have hgrade : c.sum (fun _ y => y) = u.val := by
      simpa [c, q, q', midpointCommonPrefixGrade] using x.2
    have hp : MidpointCommonPrefixProfile q q' c := by
      simpa [c, q, q'] using midpointCommonPrefixCaps_profile q q'
    have hu_lt : u.val < n := by omega
    have hz := highPowerPairKernel_eq_zero_of_prefix_grade_lt
      (u := u.val) (p := p) q q' c hp hgrade hu_lt
    simpa [q, q'] using hz

/-- High-power covariance kernel used in the all-order Gaussian moment
estimate. The universal correlation cap `rho≤1` reduces its shell sum to a
constant depending on `p` times the first correlation shell sum. -/
theorem highPowerPairKernel_le_exp_times_correlation {p : ℕ} {rho : ℝ}
    (hrho0 : 0 ≤ rho) (hrho1 : rho ≤ 1) :
    highPowerPairKernel p rho ≤
      (4 * (p : ℝ) ^ 2 * Real.exp (2 * (p : ℝ))) * rho := by
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  have hexp : Real.exp (2 * (p : ℝ) * |rho|) ≤ Real.exp (2 * (p : ℝ)) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hrho0]
    nlinarith
  have hrhoSq : rho ^ 2 ≤ rho := by nlinarith
  unfold highPowerPairKernel
  calc
    4 * (p : ℝ) ^ 2 * rho ^ 2 * Real.exp (2 * (p : ℝ) * |rho|) ≤
        4 * (p : ℝ) ^ 2 * rho ^ 2 * Real.exp (2 * (p : ℝ)) := by
          apply mul_le_mul_of_nonneg_left hexp
          positivity
    _ ≤ 4 * (p : ℝ) ^ 2 * rho * Real.exp (2 * (p : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
          exact mul_le_mul_of_nonneg_left hrhoSq (by positivity)
    _ = (4 * (p : ℝ) ^ 2 * Real.exp (2 * (p : ℝ))) * rho := by ring

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

/-- Per-shell high-power pair sum with the exact shell-specific correlation
cap. The quadratic factor is preserved, allowing the later `p=O(n)` argument
to control the exponential by the shell grade rather than by `exp(2p)`. -/
theorem highPowerPairKernel_shell_sum_mul_pow_le_of_cap {d n h : ℕ}
    (hd : 0 < d) (p : ℕ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hvar : ∀ q : MidpointGridIndex d n, v₀ ≤ nativeLayerRowVariance q) :
    (∑ x : midpointPairShell (d := d) (n := n) (n + h),
      highPowerPairKernel p
        (nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2))) *
        (2 ^ (n + h) : ℝ) ≤
      (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) *
          (4 * (p : ℝ) ^ 2 *
            ((1 / (2 : ℝ) ^ (n + 2 * d)) *
              (Nat.min (Nat.choose (n + d - 1) (d - 1))
                (Nat.choose (h + d - 1) (d - 1)) : ℝ) / v₀) ^ 2 *
            Real.exp (2 * (p : ℝ) *
              ((1 / (2 : ℝ) ^ (n + 2 * d)) *
                (Nat.min (Nat.choose (n + d - 1) (d - 1))
                  (Nat.choose (h + d - 1) (d - 1)) : ℝ) / v₀))) := by
  let R : ℝ := (1 / (2 : ℝ) ^ (n + 2 * d)) *
    (Nat.min (Nat.choose (n + d - 1) (d - 1))
      (Nat.choose (h + d - 1) (d - 1)) : ℝ) / v₀
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hcorr := nativeRowCorrelation_shell_sum_mul_pow_le
    (d := d) (n := n) (h := h) hd hv₀ hvar
  have hpoint : ∀ x : midpointPairShell (d := d) (n := n) (n + h),
      highPowerPairKernel p
        (nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2)) ≤
      4 * (p : ℝ) ^ 2 * R ^ 2 * Real.exp (2 * (p : ℝ) * R) := by
    intro x
    apply highPowerPairKernel_le_of_le
    · exact nativeRowCorrelation_nonneg _ _
    · have hq : v₀ ≤ nativeLayerRowVariance (fun i => (x.1 i).1) :=
        hvar (fun i => (x.1 i).1)
      have hq' : v₀ ≤ nativeLayerRowVariance (fun i => (x.1 i).2) :=
        hvar (fun i => (x.1 i).2)
      let c := midpointCommonPrefixCaps (fun i => (x.1 i).1) (fun i => (x.1 i).2)
      have hgrade : (c.sum fun _ y => y) = n + h := by
        simpa [c, midpointCommonPrefixGrade] using x.2
      have hp : MidpointCommonPrefixProfile (fun i => (x.1 i).1)
          (fun i => (x.1 i).2) c := by
        simpa [c] using midpointCommonPrefixCaps_profile
          (fun i => (x.1 i).1) (fun i => (x.1 i).2)
      have hcap := nativeRowCorrelation_le_prefix hd
        (fun i => (x.1 i).1) (fun i => (x.1 i).2) c hgrade hp hv₀ hq hq'
      simpa [R] using hcap
    · exact hR
  simpa [R, mul_assoc, mul_left_comm, mul_comm] using
    (midpointPairShell_sum_mul_pow_le (d := d) (n := n) (u := n + h) hd
      (fun x => highPowerPairKernel p
        (nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2)))
      (4 * (p : ℝ) ^ 2 * R ^ 2 * Real.exp (2 * (p : ℝ) * R)) (by positivity) hpoint)

/-- Shell sum for the high-power covariance envelope `4 p² rho² exp(2p|rho|)`.
The variance floor remains explicit. This theorem combines the genuine row
correlation bound with the exact midpoint shell count. -/
theorem highPowerPairKernel_shell_sum_mul_pow_le {d n h : ℕ} (hd : 0 < d)
    (p : ℕ) {v₀ : ℝ} (hv₀ : 0 < v₀)
    (hvar : ∀ q : MidpointGridIndex d n, v₀ ≤ nativeLayerRowVariance q) :
    (∑ x : midpointPairShell (d := d) (n := n) (n + h),
      highPowerPairKernel p
        (nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2))) *
        (2 ^ (n + h) : ℝ) ≤
      (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
        (Fintype.card (MidpointPairGrid d n) : ℝ) *
          ((4 * (p : ℝ) ^ 2 * Real.exp (2 * (p : ℝ))) *
            ((1 / (2 : ℝ) ^ (n + 2 * d)) *
              (Nat.min (Nat.choose (n + d - 1) (d - 1))
                (Nat.choose (h + d - 1) (d - 1)) : ℝ) / v₀)) := by
  let R : ℝ := (1 / (2 : ℝ) ^ (n + 2 * d)) *
    (Nat.min (Nat.choose (n + d - 1) (d - 1))
      (Nat.choose (h + d - 1) (d - 1) : ℕ) : ℝ) / v₀
  let C : ℝ := 4 * (p : ℝ) ^ 2 * Real.exp (2 * (p : ℝ))
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcorr := nativeRowCorrelation_shell_sum_mul_pow_le
    (d := d) (n := n) (h := h) hd hv₀ hvar
  have hsum :
      (∑ x : midpointPairShell (d := d) (n := n) (n + h),
        nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2)) *
          (2 ^ (n + h) : ℝ) ≤
        (Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
          (Fintype.card (MidpointPairGrid d n) : ℝ) * R := by
    simpa [R] using hcorr
  have hpoint : ∀ x : midpointPairShell (d := d) (n := n) (n + h),
      highPowerPairKernel p
        (nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2)) ≤
      C * nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2) := by
    intro x
    apply highPowerPairKernel_le_exp_times_correlation
    · exact nativeRowCorrelation_nonneg _ _
    · exact nativeRowCorrelation_le_one _ _
  have hsumKernel :
      (∑ x : midpointPairShell (d := d) (n := n) (n + h),
        highPowerPairKernel p
          (nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2))) *
          (2 ^ (n + h) : ℝ) ≤ C *
        ((Nat.choose (n + h + d - 1) (d - 1) : ℝ) *
          (Fintype.card (MidpointPairGrid d n) : ℝ) * R) := by
    have hsumPoint :
        (∑ x : midpointPairShell (d := d) (n := n) (n + h),
          highPowerPairKernel p
            (nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2))) ≤
          C * ∑ x : midpointPairShell (d := d) (n := n) (n + h),
            nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2) := by
      calc
        _ ≤ ∑ x : midpointPairShell (d := d) (n := n) (n + h),
            C * nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2) :=
          Finset.sum_le_sum fun x _ => hpoint x
        _ = _ := by rw [Finset.mul_sum]
    calc
      _ ≤ (C * ∑ x : midpointPairShell (d := d) (n := n) (n + h),
          nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2)) *
            (2 ^ (n + h) : ℝ) := mul_le_mul_of_nonneg_right hsumPoint (by positivity)
      _ = C * ((∑ x : midpointPairShell (d := d) (n := n) (n + h),
          nativeRowCorrelation (fun i => (x.1 i).1) (fun i => (x.1 i).2)) *
            (2 ^ (n + h) : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsum hC
  simpa [R, C, mul_assoc, mul_left_comm, mul_comm] using hsumKernel


end BrownianSharp
