import BrownianSharp.SmoothLayer
import BrownianSharp.SmoothAtomMass
import BrownianSharp.NativeVarianceMean
import BrownianSharp.Prefix

set_option maxHeartbeats 800000

/-! Midpoint-grid variance bounds for the concrete smooth plateau atom.

The lower estimate uses only the literal plateau `[1/4,3/4]`: inside every
dyadic cell, half of its finer midpoint samples lie on that plateau. -/

open scoped BigOperators

namespace BrownianSharp

private noncomputable def smoothScalarSample {n r : ℕ}
    (j : Fin (2 ^ r)) (q : Fin (2 ^ (n + 1))) : ℝ :=
  smoothAtom ((2 : ℝ) ^ r * midpointGridCoordinate n q - (j.val : ℝ))

private noncomputable def smoothScalarEnergy {n r : ℕ}
    (q : Fin (2 ^ (n + 1))) : ℝ :=
  ∑ j : Fin (2 ^ r), (smoothScalarSample j q) ^ 2

private noncomputable def smoothSplitCellEnergy {n r : ℕ} (hr : r ≤ n)
    (c : Fin (2 ^ r)) (k : Fin (2 ^ (n + 1 - r))) : ℝ :=
  ∑ j : Fin (2 ^ r), (smoothScalarSample j
    ((HaarQuarter.dyadicGridSplitEquiv (n + 1)
      ⟨r, Nat.lt_succ_of_le hr⟩).symm (c, k))) ^ 2

private theorem smoothSplit_symm_val {N : ℕ} (l : Fin N)
    (j : Fin (2 ^ l.val)) (k : Fin (2 ^ (N - l.val))) :
    ((HaarQuarter.dyadicGridSplitEquiv N l).symm (j, k)).val =
      j.val * 2 ^ (N - l.val) + k.val := by
  simp [HaarQuarter.dyadicGridSplitEquiv]
  ac_rfl

private theorem smoothMidpoint_split {n r : ℕ} (hr : r ≤ n)
    (j : Fin (2 ^ r)) (k : Fin (2 ^ (n + 1 - r))) :
    midpointGridCoordinate n
        ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (j, k)) =
      ((j.val : ℝ) + ((k.val : ℝ) + 1 / 2) /
        (2 : ℝ) ^ (n + 1 - r)) / (2 : ℝ) ^ r := by
  let l : Fin (n + 1) := ⟨r, by omega⟩
  change ((((HaarQuarter.dyadicGridSplitEquiv (n + 1) l).symm (j, k)).val : ℝ) +
      1 / 2) / (2 : ℝ) ^ (n + 1) = _
  calc
    _ = ((((j.val * 2 ^ (n + 1 - r) + k.val : ℕ) : ℝ) + 1 / 2) /
        (2 : ℝ) ^ (n + 1)) := by rw [smoothSplit_symm_val]
    _ = ((j.val : ℝ) + ((k.val : ℝ) + 1 / 2) /
        (2 : ℝ) ^ (n + 1 - r)) / (2 : ℝ) ^ r := by
          have hexp : n + 1 = r + (n + 1 - r) := by omega
          have hpow : (2 : ℝ) ^ (n + 1) =
              (2 : ℝ) ^ r * (2 : ℝ) ^ (n + 1 - r) := by
            rw [hexp, pow_add]
            congr 1
            simp [Nat.add_sub_cancel_left]
          rw [hpow]
          push_cast
          field_simp
          <;> ring

/-- A convenient injection into the central half of the fine midpoint grid.
The two-point grid (`a=1`) is handled separately. -/
private def smoothCentralIndex (a : ℕ) (ha1 : 1 ≤ a)
    (m : Fin (2 ^ (a - 1))) : Fin (2 ^ a) := by
  by_cases ha : a = 1
  · subst a
    exact ⟨0, by norm_num⟩
  · have ha2 : 2 ≤ a := by omega
    refine ⟨2 ^ (a - 2) + m.val, ?_⟩
    have hhalf : 2 ^ (a - 1) = 2 * 2 ^ (a - 2) := by
      calc
        2 ^ (a - 1) = 2 ^ ((a - 2) + 1) := by congr 1; omega
        _ = 2 ^ (a - 2) * 2 := by rw [Nat.pow_succ]
        _ = 2 * 2 ^ (a - 2) := by ring
    have hwhole : 2 ^ a = 4 * 2 ^ (a - 2) := by
      calc
        2 ^ a = 2 ^ ((a - 2) + 2) := by congr 1; omega
        _ = 2 ^ (a - 2) * 2 ^ 2 := by rw [Nat.pow_add]
        _ = 4 * 2 ^ (a - 2) := by norm_num; ring
    omega

private theorem smoothCentralIndex_injective (a : ℕ) (ha1 : 1 ≤ a) :
    Function.Injective (smoothCentralIndex a ha1) := by
  intro x y h
  by_cases ha : a = 1
  · subst a
    have hdom : 2 ^ (1 - 1) = 1 := by norm_num
    rw [hdom] at x y
    apply Fin.ext
    have hx := x.isLt
    have hy := y.isLt
    norm_num at hx hy ⊢
  · apply Fin.ext
    have hv := congrArg Fin.val h
    simpa [smoothCentralIndex, ha] using hv

private theorem smoothCentralIndex_local_mem (a : ℕ) (ha1 : 1 ≤ a)
    (m : Fin (2 ^ (a - 1))) :
    (((smoothCentralIndex a ha1 m).val : ℝ) + 1 / 2) / (2 : ℝ) ^ a ∈
      Set.Icc (1 / 4 : ℝ) (3 / 4) := by
  by_cases ha : a = 1
  · subst a
    norm_num [smoothCentralIndex]
  · have ha2 : 2 ≤ a := by omega
    have hhalf : 2 ^ (a - 1) = 2 * 2 ^ (a - 2) := by
      calc
        2 ^ (a - 1) = 2 ^ ((a - 2) + 1) := by congr 1; omega
        _ = 2 ^ (a - 2) * 2 := by rw [Nat.pow_succ]
        _ = 2 * 2 ^ (a - 2) := by ring
    have hwhole : 2 ^ a = 4 * 2 ^ (a - 2) := by
      calc
        2 ^ a = 2 ^ ((a - 2) + 2) := by congr 1; omega
        _ = 2 ^ (a - 2) * 2 ^ 2 := by rw [Nat.pow_add]
        _ = 4 * 2 ^ (a - 2) := by norm_num; ring
    have hval : (smoothCentralIndex a ha1 m).val = 2 ^ (a - 2) + m.val := by
      simp [smoothCentralIndex, ha]
    have hm : m.val < 2 * 2 ^ (a - 2) := by omega
    have hwholeR : (2 : ℝ) ^ a = 4 * (2 : ℝ) ^ (a - 2) := by
      exact_mod_cast hwhole
    rw [hval, hwholeR]
    constructor
    · have hp : (0 : ℝ) < (2 : ℝ) ^ (a - 2) := by positivity
      have hmcast : (m.val : ℝ) ≥ 0 := by positivity
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * 2 ^ (a - 2))).2
      push_cast
      nlinarith
    · have hmupper : (m.val : ℝ) < 2 * (2 ^ (a - 2) : ℝ) := by
        exact_mod_cast hm
      have hmupper' : (m.val : ℝ) + 1 ≤ 2 * (2 ^ (a - 2) : ℝ) := by
        have hnat : m.val + 1 ≤ 2 * 2 ^ (a - 2) := by omega
        exact_mod_cast hnat
      have hpowcast : (2 : ℝ) ^ a = 4 * (2 ^ (a - 2) : ℝ) := by
        exact_mod_cast hwhole
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (2 ^ (a - 2) : ℝ))).2
      push_cast
      nlinarith

private theorem smoothScalarSample_split_plateau {n r : ℕ} (hr : r ≤ n)
    (c : Fin (2 ^ r)) (m : Fin (2 ^ ((n + 1 - r) - 1))) :
    smoothScalarSample c
      ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm
        (c, smoothCentralIndex (n + 1 - r) (by omega) m)) = 1 := by
  have ha : 1 ≤ n + 1 - r := by omega
  let k := smoothCentralIndex (n + 1 - r) ha m
  have hlocal := smoothCentralIndex_local_mem (n + 1 - r) ha m
  have hcoord := smoothMidpoint_split hr c k
  have hexp : n + 1 = r + (n + 1 - r) := by omega
  have hpow : (2 : ℝ) ^ (n + 1) =
      (2 : ℝ) ^ r * (2 : ℝ) ^ (n + 1 - r) := by
    rw [hexp, pow_add]
    congr 1
    simp [Nat.add_sub_cancel_left]
  have harg : (2 : ℝ) ^ r * midpointGridCoordinate n
        ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k)) -
        (c.val : ℝ) = (((k.val : ℝ) + 1 / 2) / (2 : ℝ) ^ (n + 1 - r)) := by
    rw [hcoord]
    field_simp
    <;> ring
  rw [smoothScalarSample, harg]
  exact smoothAtom_plateau _ hlocal

private theorem smoothSplitCellEnergy_center_lower {n r : ℕ} (hr : r ≤ n)
    (c : Fin (2 ^ r)) (m : Fin (2 ^ ((n + 1 - r) - 1))) :
    1 ≤ smoothSplitCellEnergy hr c
      (smoothCentralIndex (n + 1 - r) (by omega) m) := by
  have hplateau := smoothScalarSample_split_plateau hr c m
  change 1 ≤ ∑ j : Fin (2 ^ r),
    (smoothScalarSample j
      ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm
        (c, smoothCentralIndex (n + 1 - r) (by omega) m))) ^ 2
  calc
    1 = (smoothScalarSample c
        ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm
          (c, smoothCentralIndex (n + 1 - r) (by omega) m))) ^ 2 := by
            rw [hplateau]
            norm_num
    _ ≤ _ := by
      apply Finset.single_le_sum (s := Finset.univ)
        (f := fun j => (smoothScalarSample j
          ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm
            (c, smoothCentralIndex (n + 1 - r) (by omega) m))) ^ 2)
      · intro j hj
        exact sq_nonneg _
      · exact Finset.mem_univ c

private theorem smoothScalarSample_sq_sum_lower {n r : ℕ} (hr : r ≤ n) :
    (1 / 2 : ℝ) ≤
      (∑ q : Fin (2 ^ (n + 1)), ∑ j : Fin (2 ^ r),
        (smoothScalarSample j q) ^ 2) / (2 : ℝ) ^ (n + 1) := by
  classical
  let a := n + 1 - r
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hsplit :
      (∑ q : Fin (2 ^ (n + 1)), smoothScalarEnergy (r := r) q) =
      ∑ c : Fin (2 ^ r), ∑ k : Fin (2 ^ a), smoothSplitCellEnergy hr c k := by
    calc
      _ = ∑ p : Fin (2 ^ r) × Fin (2 ^ a), smoothSplitCellEnergy hr p.1 p.2 := by
              apply Fintype.sum_equiv (HaarQuarter.dyadicGridSplitEquiv (n + 1)
                ⟨r, by omega⟩)
              intro q
              simp [smoothScalarEnergy, smoothSplitCellEnergy, a]
      _ = _ := Fintype.sum_prod_type _
  have hcell (c : Fin (2 ^ r)) :
      (2 ^ (a - 1) : ℝ) ≤
        ∑ k : Fin (2 ^ a), smoothSplitCellEnergy hr c k := by
    let e := smoothCentralIndex a ha
    let s : Finset (Fin (2 ^ a)) := Finset.univ.image e
    have hsub : s ⊆ Finset.univ := Finset.subset_univ _
    have hsum : (∑ k ∈ s, (1 : ℝ)) = (2 ^ (a - 1) : ℝ) := by
      calc
        _ = (s.card : ℝ) := by simp
        _ = (Finset.univ.card : ℝ) := by
          change ((Finset.univ.image e).card : ℝ) = _
          rw [Finset.card_image_of_injective Finset.univ
            (smoothCentralIndex_injective a ha)]
        _ = _ := by simp
    have hlower : (∑ k ∈ s, (1 : ℝ)) ≤
        ∑ k : Fin (2 ^ a), smoothSplitCellEnergy hr c k := by
      calc
        _ ≤ ∑ k ∈ s, smoothSplitCellEnergy hr c k := by
              apply Finset.sum_le_sum
              intro k hk
              rcases Finset.mem_image.mp hk with ⟨m, hm, rfl⟩
              have hmeq : a - 1 = n - r := by dsimp [a]; omega
              have hmeq' : a - 1 = (n + 1 - r) - 1 := by omega
              have hpowEq : 2 ^ (a - 1) = 2 ^ ((n + 1 - r) - 1) :=
                congrArg (fun t : ℕ => 2 ^ t) hmeq'
              let m' : Fin (2 ^ ((n + 1 - r) - 1)) := Fin.cast hpowEq m
              have ha' : 1 ≤ n + 1 - r := by omega
              have hidx : smoothCentralIndex (n + 1 - r) ha' m' =
                  smoothCentralIndex a ha m := by
                apply Fin.ext
                simp [a, m', Fin.cast, smoothCentralIndex, hmeq']
              change 1 ≤ smoothSplitCellEnergy hr c (smoothCentralIndex a ha m)
              rw [← hidx]
              exact smoothSplitCellEnergy_center_lower hr c m'
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
              intro k hk hknot
              change 0 ≤ smoothSplitCellEnergy hr c k
              simp only [smoothSplitCellEnergy]
              exact Finset.sum_nonneg fun j hj => sq_nonneg _)
    simpa [hsum] using hlower
  have htotal :
      (2 ^ (r + a - 1) : ℝ) ≤
        ∑ c : Fin (2 ^ r), ∑ k : Fin (2 ^ a), smoothSplitCellEnergy hr c k := by
    calc
      _ = ∑ c : Fin (2 ^ r), (2 ^ (a - 1) : ℝ) := by
        simp [Fintype.card_fin]
        rw [← pow_add]
        congr 1
        omega
      _ ≤ _ := Finset.sum_le_sum (fun c hc => hcell c)
  have hpow : r + a - 1 = n := by dsimp [a]; omega
  have hgrid : (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n := by rw [pow_succ]; ring
  have hpos : 0 < (2 : ℝ) ^ n := by positivity
  have hcardcast : (2 ^ n : ℕ) = (2 : ℝ) ^ n := by norm_cast
  have htotal' : (2 : ℝ) ^ n ≤
      ∑ c : Fin (2 ^ r), ∑ k : Fin (2 ^ a), smoothSplitCellEnergy hr c k := by
    have heq : (2 : ℝ) ^ (r + a - 1) = (2 : ℝ) ^ n := by rw [hpow]
    rw [← heq]
    exact htotal
  have hmeanE : (1 / 2 : ℝ) ≤
      (∑ q : Fin (2 ^ (n + 1)), smoothScalarEnergy (r := r) q) /
        (2 : ℝ) ^ (n + 1) := by
    rw [hsplit, hgrid]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (2 : ℝ) ^ n)]
    nlinarith [htotal']
  simpa [smoothScalarEnergy] using hmeanE

private theorem sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (f : ∀ i, α i → ℝ) :
    (∑ x : (∀ i, α i), ∏ i, f i (x i)) =
      ∏ i, ∑ a : α i, f i a := by
  classical
  simpa using (Finset.prod_univ_sum
    (fun i => (Finset.univ : Finset (α i))) f).symm

/-- Sum of squared smooth atom samples in one fixed tensor shape. -/
noncomputable def smoothLayerVariance {d n : ℕ}
    (q : MidpointGridIndex d n) : ℝ :=
  ∑ a : LayerIndex d n, (smoothLayerAtom smoothAtom q a) ^ 2

private theorem smoothLayerAtom_eq_scalarProduct {d n : ℕ}
    (q : MidpointGridIndex d n) (a : LayerIndex d n) :
    smoothLayerAtom smoothAtom q a =
      ∏ i : Fin d, smoothScalarSample (a.2 i) (q i) := by
  unfold smoothLayerAtom smoothScalarSample
  rfl

private theorem smoothShapeSquare_sum_eq_product {d n : ℕ}
    (r : Shape d n) :
    (∑ q : MidpointGridIndex d n,
      ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
        (smoothLayerAtom smoothAtom q ⟨r, j⟩) ^ 2) =
      ∏ i : Fin d, ∑ q : Fin (2 ^ (n + 1)),
        ∑ j : Fin (2 ^ r.1 i),
          (smoothScalarSample j q) ^ 2 := by
  classical
  calc
    _ = ∑ q : MidpointGridIndex d n,
        ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
          ∏ i : Fin d, (smoothScalarSample (j i) (q i)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro q hq
            apply Finset.sum_congr rfl
            intro j hj
            rw [smoothLayerAtom_eq_scalarProduct]
            rw [Finset.prod_pow]
    _ = ∑ q : MidpointGridIndex d n,
        ∏ i : Fin d, ∑ j : Fin (2 ^ r.1 i),
          (smoothScalarSample j (q i)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro q hq
            exact sum_pi_prod (fun i j =>
              (smoothScalarSample j (q i)) ^ 2)
    _ = ∏ i : Fin d, ∑ q : Fin (2 ^ (n + 1)),
        ∑ j : Fin (2 ^ r.1 i), (smoothScalarSample j q) ^ 2 := by
            exact sum_pi_prod (fun i q =>
              ∑ j : Fin (2 ^ r.1 i), (smoothScalarSample j q) ^ 2)

private theorem smoothShapeSquare_mean_lower {d n : ℕ}
    (r : Shape d n) :
    (1 / 2 : ℝ) ^ d ≤
      (∑ q : MidpointGridIndex d n,
        ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
          (smoothLayerAtom smoothAtom q ⟨r, j⟩) ^ 2) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
  classical
  let K := 2 ^ (n + 1)
  have hcoord (i : Fin d) :
      (1 / 2 : ℝ) ≤
        (∑ q : Fin K, ∑ j : Fin (2 ^ r.1 i),
          (smoothScalarSample j q) ^ 2) / (Fintype.card (Fin K) : ℝ) := by
    simpa [K, Fintype.card_fin] using
      smoothScalarSample_sq_sum_lower (n := n) (r := r.1 i)
        (by
          have hgrade := (Finset.mem_finsuppAntidiag'.mp r.2).1
          have hsum : (∑ j : Fin d, r.1 j) = n := by
            simpa [Finsupp.sum_fintype] using hgrade
          have hle := Finset.single_le_sum
            (fun j hj => Nat.zero_le (r.1 j)) (Finset.mem_univ i)
          omega)
  have hprod := Finset.prod_le_prod₀
    (s := (Finset.univ : Finset (Fin d)))
    (fun i hi => by positivity)
    (fun i hi => hcoord i)
  have hcard : (Fintype.card (MidpointGridIndex d n) : ℝ) =
      ∏ i : Fin d, (Fintype.card (Fin K) : ℝ) := by
    simp [MidpointGridIndex, K, Fintype.card_pi]
  rw [smoothShapeSquare_sum_eq_product, hcard, ← Finset.prod_div_distrib]
  have hconstant : (∏ i : Fin d, (1 / 2 : ℝ)) = (1 / 2 : ℝ) ^ d := by
    simp [Fintype.card_fin]
  calc
    _ = ∏ i : Fin d, (1 / 2 : ℝ) := hconstant.symm
    _ ≤ ∏ i : Fin d,
        (∑ q : Fin K, ∑ j : Fin (2 ^ r.1 i),
          (smoothScalarSample j q) ^ 2) / (Fintype.card (Fin K) : ℝ) := hprod

/-- The actual smooth-layer variance on the midpoint grid has a mean bounded
below by `2^-d` times the weak-composition count. -/
theorem smoothLayerVariance_mean_lower {d n : ℕ} (hd : 0 < d) :
    (1 / 2 : ℝ) ^ d * Nat.choose (n + d - 1) (d - 1) ≤
      (∑ q : MidpointGridIndex d n, smoothLayerVariance q) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
  classical
  let M : ℝ := (1 / 2 : ℝ) ^ d
  have hshape : ∀ r : Shape d n,
      M ≤ (∑ q : MidpointGridIndex d n,
        ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
          (smoothLayerAtom smoothAtom q ⟨r, j⟩) ^ 2) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    intro r
    simpa [M] using smoothShapeSquare_mean_lower r
  have htotal :
      (∑ q : MidpointGridIndex d n, smoothLayerVariance q) =
        ∑ r : Shape d n,
          ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
            ∑ q : MidpointGridIndex d n,
              (smoothLayerAtom smoothAtom q ⟨r, j⟩) ^ 2 := by
    unfold smoothLayerVariance
    rw [Finset.sum_comm, Fintype.sum_sigma]
  have hdiv :
      (∑ q : MidpointGridIndex d n, smoothLayerVariance q) /
          (Fintype.card (MidpointGridIndex d n) : ℝ) =
        ∑ r : Shape d n,
          (∑ q : MidpointGridIndex d n,
            ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
              (smoothLayerAtom smoothAtom q ⟨r, j⟩) ^ 2) /
            (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    rw [htotal, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_comm]
  have hsum : M * (Fintype.card (Shape d n) : ℝ) ≤
      ∑ r : Shape d n,
        (∑ q : MidpointGridIndex d n,
          ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
            (smoothLayerAtom smoothAtom q ⟨r, j⟩) ^ 2) /
          (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    calc
      _ = ∑ r : Shape d n, M := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
      _ ≤ _ := Finset.sum_le_sum (fun r hr => hshape r)
  rw [← hdiv] at hsum
  rw [show (Fintype.card (Shape d n) : ℝ) =
    Nat.choose (n + d - 1) (d - 1) by exact_mod_cast shape_card d n hd] at hsum
  simpa [M] using hsum

/-- Pointwise smooth-layer variance upper bound from one active address per
shape. -/
theorem smoothLayerVariance_le {d n : ℕ} (hd : 0 < d)
    (q : MidpointGridIndex d n) :
    smoothLayerVariance q ≤ (Nat.choose (n + d - 1) (d - 1) : ℝ) := by
  classical
  let c := nativeFullDepthProfile d n
  let h := d * (n + 1) - n
  have hsumc : c.sum (fun _ x => x) = d * (n + 1) := by
    simp [c, nativeFullDepthProfile, Finsupp.sum_fintype]
  have hc : c.sum (fun _ x => x) = n + h := by
    have hd' : 1 ≤ d := hd
    have hnle : n ≤ d * (n + 1) := by
      calc
        n ≤ n + 1 := Nat.le_succ _
        _ = 1 * (n + 1) := by omega
        _ ≤ d * (n + 1) := Nat.mul_le_mul_right _ hd'
    dsimp [h]
    rw [hsumc]
    omega
  have hp : MidpointCommonPrefixProfile q q c := by
    refine ⟨?_, ?_, ?_⟩
    · intro i
      simp [c, nativeFullDepthProfile]
    · intro i
      rfl
    · intro i hi
      have : n + 1 < n + 1 := by simpa [c, nativeFullDepthProfile] using hi
      omega
  have hsum := smoothLayerPair_abs_sum_le hd smoothAtom
    (fun x hx => smoothAtom_support x hx) smoothAtom_abs_le_one q q c hc hp
  have hnonneg (a : LayerIndex d n) :
      0 ≤ smoothLayerAtom smoothAtom q a := by
    unfold smoothLayerAtom
    apply Finset.prod_nonneg
    intro i hi
    exact (smoothAtom_bounds _).1
  have hconvert :
      smoothLayerVariance q =
        ∑ a : LayerIndex d n,
          |smoothLayerAtom smoothAtom q a * smoothLayerAtom smoothAtom q a| := by
    unfold smoothLayerVariance
    apply Finset.sum_congr rfl
    intro a ha
    rw [abs_of_nonneg (mul_nonneg (hnonneg a) (hnonneg a))]
    ring
  rw [hconvert]
  calc
    _ ≤ ((Nat.min (Nat.choose (n + d - 1) (d - 1))
        (Nat.choose (h + d - 1) (d - 1)) : ℕ) : ℝ) := hsum
    _ ≤ (Nat.choose (n + d - 1) (d - 1) : ℝ) := by
      exact_mod_cast Nat.min_le_left _ _

/-- The proved mean floor for the sampled variance of the concrete smooth
plateau layer. -/
noncomputable def smoothVarianceMeanLowerBound (d n : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ d * Nat.choose (n + d - 1) (d - 1)

/-- Midpoint rows where the concrete smooth layer has at least half its mean
lower bound. -/
noncomputable def SmoothGoodGrid (d n : ℕ) :=
  {q : MidpointGridIndex d n //
    smoothVarianceMeanLowerBound d n / 2 ≤ smoothLayerVariance q}

noncomputable instance smoothGoodGridFintype (d n : ℕ) :
    Fintype (SmoothGoodGrid d n) := by
  classical
  letI : Finite (SmoothGoodGrid d n) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

theorem smoothVarianceMeanLowerBound_pos {d n : ℕ} (hd : 0 < d) :
    0 < smoothVarianceMeanLowerBound d n := by
  unfold smoothVarianceMeanLowerBound
  have hc : 0 < Nat.choose (n + d - 1) (d - 1) := by
    apply Nat.choose_pos
    omega
  positivity

private theorem smoothGoodGrid_card_eq_filter {d n : ℕ} :
    Fintype.card (SmoothGoodGrid d n) =
      (Finset.univ.filter (fun q : MidpointGridIndex d n =>
        smoothVarianceMeanLowerBound d n / 2 ≤ smoothLayerVariance q)).card := by
  classical
  let s : Finset (MidpointGridIndex d n) := Finset.univ.filter fun q =>
    smoothVarianceMeanLowerBound d n / 2 ≤ smoothLayerVariance q
  let e : SmoothGoodGrid d n ≃ {q // q ∈ s} := {
    toFun := fun q => ⟨q.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, q.2⟩⟩
    invFun := fun q => ⟨q.1, (Finset.mem_filter.mp q.2).2⟩
    left_inv q := by apply Subtype.ext; rfl
    right_inv q := by apply Subtype.ext; rfl
  }
  calc
    Fintype.card (SmoothGoodGrid d n) = Fintype.card {q // q ∈ s} :=
      Fintype.card_congr e
    _ = s.card := Fintype.card_coe s
    _ = _ := rfl

/-- At least `2^(-(d+1))` of the midpoint grid has smooth-layer variance at
least half the proved mean lower bound. -/
theorem smoothGoodGrid_fraction_lower {d n : ℕ} (hd : 0 < d) :
    1 / (2 : ℝ) ^ (d + 1) ≤
      (Fintype.card (SmoothGoodGrid d n) : ℝ) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
  classical
  let m := smoothVarianceMeanLowerBound d n
  let M := (Nat.choose (n + d - 1) (d - 1) : ℝ)
  have hm : 0 < m := by simpa [m] using smoothVarianceMeanLowerBound_pos hd
  have hM : 0 < M := by
    dsimp [M]
    apply Nat.cast_pos.mpr
    apply Nat.choose_pos
    omega
  have hmean : m ≤
      (∑ q : MidpointGridIndex d n, smoothLayerVariance q) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    simpa [m, smoothVarianceMeanLowerBound] using
      (smoothLayerVariance_mean_lower (d := d) (n := n) hd)
  have hfrac := Prefix.finite_good_fraction_lower smoothLayerVariance hm hM
    (fun q => by simpa [M] using smoothLayerVariance_le hd q) hmean
  have hcardEq : Fintype.card (SmoothGoodGrid d n) =
      (Finset.univ.filter (fun q : MidpointGridIndex d n =>
        m / 2 ≤ smoothLayerVariance q)).card := by
    simpa [m] using smoothGoodGrid_card_eq_filter (d := d) (n := n)
  rw [← hcardEq] at hfrac
  have hratio : m / (2 * M) = 1 / (2 : ℝ) ^ (d + 1) := by
    dsimp [m, M, smoothVarianceMeanLowerBound]
    have hc : (Nat.choose (n + d - 1) (d - 1) : ℝ) ≠ 0 := ne_of_gt hM
    rw [show (2 : ℝ) ^ (d + 1) = 2 * 2 ^ d by
      rw [pow_succ]; ring]
    field_simp
    rw [one_div, inv_pow]
    field_simp
    <;> ring
  rw [hratio] at hfrac
  simpa using hfrac

/-- The smooth good set is nonempty. -/
theorem smoothGoodGrid_nonempty {d n : ℕ} (hd : 0 < d) :
    Nonempty (SmoothGoodGrid d n) := by
  classical
  have hgrid : 0 < (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    simp [MidpointGridIndex, Fintype.card_pi]
  have hfrac := smoothGoodGrid_fraction_lower (d := d) (n := n) hd
  have hcard : 0 < (Fintype.card (SmoothGoodGrid d n) : ℝ) := by
    have hpositive : 0 < 1 / (2 : ℝ) ^ (d + 1) := by positivity
    have hratio : 0 <
        (Fintype.card (SmoothGoodGrid d n) : ℝ) /
          (Fintype.card (MidpointGridIndex d n) : ℝ) :=
      lt_of_lt_of_le hpositive hfrac
    have hnonneg : 0 ≤ (Fintype.card (SmoothGoodGrid d n) : ℝ) := by positivity
    by_contra hnot
    have hz : (Fintype.card (SmoothGoodGrid d n) : ℝ) = 0 :=
      le_antisymm (le_of_not_gt hnot) hnonneg
    rw [hz] at hratio
    simp at hratio
  exact Fintype.card_pos_iff.mp (by exact_mod_cast hcard)

/-- Every member of the good set satisfies its advertised variance floor. -/
theorem smoothGoodGrid_variance_floor {d n : ℕ} (q : SmoothGoodGrid d n) :
    smoothVarianceMeanLowerBound d n / 2 ≤ smoothLayerVariance q.1 :=
  q.2

end BrownianSharp

