import BrownianSharp.NativeRow
import BrownianSharp.CovarianceBound
import BrownianSharp.Prefix

/-!
Finite-row variance of the actual Brownian-sheet projection.  All row entries
are inner products against the original anchored-box evaluation vectors.
-/

open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp

/-- Squared Euclidean norm of the native layer's coefficient row at a midpoint
anchor. -/
noncomputable def nativeLayerRowVariance {d n : ℕ}
    (q : MidpointGridIndex d n) : ℝ :=
  ∑ a : LayerIndex d n, (nativeLayerRowCoefficient q a) ^ 2

/-- The full grid depth profile, viewed as a finitely supported function. -/
noncomputable def nativeFullDepthProfile (d n : ℕ) : Fin d →₀ ℕ :=
  Finsupp.onFinset Finset.univ (fun _ => n + 1) (by simp)

/-- Every depth in a grade-`n` layer is at most `n`. -/
theorem layerIndexDepth_le_grade {d n : ℕ} (a : LayerIndex d n) (i : Fin d) :
    layerIndexDepth a i ≤ n := by
  have hgrade := layerIndexDepth_grade a
  have hsum : (∑ j : Fin d, layerIndexDepth a j) = n := by
    simpa [layerIndexDepth, Finsupp.sum_fintype] using hgrade
  have hle : layerIndexDepth a i ≤ ∑ j : Fin d, layerIndexDepth a j := by
    apply Finset.single_le_sum (s := Finset.univ)
    · intro j hj
      exact Nat.zero_le _
    · simp
  omega

/-- A positive row square identifies its dyadic address from the midpoint
location. -/
theorem nativeLayerRowCoefficient_sq_pos_address {d n : ℕ}
    (q : MidpointGridIndex d n) (a : LayerIndex d n) (i : Fin d)
    (hpos : 0 < (nativeLayerRowCoefficient q a) ^ 2) :
    HaarQuarter.dyadicCellIndex (n + 1)
      ⟨layerIndexDepth a i, by
        exact Nat.lt_succ_of_le (layerIndexDepth_le_grade a i)⟩
      (q i).val = layerIndexCell a i := by
  have hcoeff : 0 < nativeLayerRowCoefficient q a := by
    have hn := nativeLayerRowCoefficient_nonneg q a
    have hne : nativeLayerRowCoefficient q a ≠ 0 := by
      intro hz
      rw [hz] at hpos
      norm_num at hpos
    exact lt_of_le_of_ne hn (Ne.symm hne)
  have hi := (nativeLayerRowCoefficient_pos_iff_interior q a).1 hcoeff i
  exact midpointAddress_eq_dyadicCellIndex (q i) (layerIndexCell a i)
    (layerIndexDepth_le_grade a i) hi.1 hi.2

/-- For a fixed midpoint and a fixed depth profile, at most one cell-address
choice can have a nonzero row coefficient. -/
theorem nativeLayerRowCoefficient_sq_pos_unique {d n : ℕ}
    (q : MidpointGridIndex d n) (a b : LayerIndex d n)
    (ha : 0 < (nativeLayerRowCoefficient q a) ^ 2)
    (hb : 0 < (nativeLayerRowCoefficient q b) ^ 2)
    (hdepth : layerIndexDepth a = layerIndexDepth b) : a = b := by
  exact nativeLayerRowProduct_unique_addresses q q a b
    (by simpa [pow_two] using ha)
    (by simpa [pow_two] using hb) hdepth

/-- The sum of squared native row coefficients has the elementary sharp
upper bound obtained by counting one active address per depth profile. -/
theorem nativeLayerRowVariance_le {d n : ℕ} (hd : 0 < d)
    (q : MidpointGridIndex d n) :
    nativeLayerRowVariance q ≤
      (1 / (2 : ℝ) ^ (n + 2 * d)) * Nat.choose (n + d - 1) (d - 1) := by
  classical
  let f : LayerIndex d n → ℝ := fun a =>
    (nativeLayerRowCoefficient q a) ^ 2
  let c := nativeFullDepthProfile d n
  let h := d * (n + 1) - n
  have hc : c.sum (fun _ x => x) = n + h := by
    have hsum : c.sum (fun _ x => x) = d * (n + 1) := by
      simp [c, nativeFullDepthProfile, Finsupp.sum_fintype]
    dsimp [h]
    have hd' : 1 ≤ d := hd
    have hnle : n ≤ d * (n + 1) := by
      calc
        n ≤ n + 1 := Nat.le_succ _
        _ = 1 * (n + 1) := by omega
        _ ≤ d * (n + 1) := Nat.mul_le_mul_right _ hd'
    omega
  have hnonneg : ∀ a, 0 ≤ f a := by
    intro a
    dsimp [f]
    positivity
  have hbound : ∀ a, f a ≤ 1 / (2 : ℝ) ^ (n + 2 * d) := by
    intro a
    dsimp [f]
    exact nativeLayerRowCoefficient_sq_le q a
  have hsupport : ∀ a, 0 < f a → ∀ i, layerIndexDepth a i ≤ c i := by
    intro a ha i
    simp [c, nativeFullDepthProfile]
    have hle := layerIndexDepth_le_grade a i
    omega
  have hunique : ∀ a b, 0 < f a → 0 < f b →
      layerIndexDepth a = layerIndexDepth b → a = b := by
    intro a b ha hb hdepth
    exact nativeLayerRowCoefficient_sq_pos_unique q a b (by simpa [f] using ha)
      (by simpa [f] using hb) hdepth
  have hsum := layerRowProduct_sum_le_of_support hd c hc f
      (1 / (2 : ℝ) ^ (n + 2 * d)) (by positivity) hnonneg hbound hsupport hunique
  calc
    nativeLayerRowVariance q ≤
        (1 / (2 : ℝ) ^ (n + 2 * d)) *
          min (Nat.choose (n + d - 1) (d - 1))
            (Nat.choose (h + d - 1) (d - 1)) := by
      simpa [nativeLayerRowVariance, f] using hsum
    _ ≤ (1 / (2 : ℝ) ^ (n + 2 * d)) *
          Nat.choose (n + d - 1) (d - 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast Nat.min_le_left _ _

/-- The explicit integer address of a point reconstructed from its dyadic
cell and its within-cell midpoint index. -/
private theorem dyadicGridSplit_symm_val {N : ℕ} (l : Fin N)
    (j : Fin (2 ^ l.val)) (k : Fin (2 ^ (N - l.val))) :
    ((HaarQuarter.dyadicGridSplitEquiv N l).symm (j, k)).val =
      j.val * 2 ^ (N - l.val) + k.val := by
  simp [HaarQuarter.dyadicGridSplitEquiv]
  ac_rfl

/-- Midpoint coordinates split affinely into a dyadic cell and its local
midpoint coordinate. -/
private theorem midpointGridCoordinate_split {n r : ℕ} (hr : r ≤ n)
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
        (2 : ℝ) ^ (n + 1)) := by
          rw [dyadicGridSplit_symm_val]
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

/-- On a fixed dyadic cell, the tent at a fine midpoint is the cell width
times the ordinary unit tent at its within-cell midpoint. -/
private theorem dyadicHaarTentAt_split {n r : ℕ} (hr : r ≤ n)
    (j : Fin (2 ^ r)) (k : Fin (2 ^ (n + 1 - r))) :
    dyadicHaarTentAt r j.val
        (midpointGridCoordinate n
          ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (j, k))) =
      (min (((k.val : ℝ) + 1 / 2) / (2 : ℝ) ^ (n + 1 - r))
        (1 - (((k.val : ℝ) + 1 / 2) / (2 : ℝ) ^ (n + 1 - r)))) /
        (2 : ℝ) ^ r := by
  let u : ℝ := ((k.val : ℝ) + 1 / 2) / (2 : ℝ) ^ (n + 1 - r)
  let t := midpointGridCoordinate n
    ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (j, k))
  have hu0 : 0 < u := by
    dsimp [u]
    positivity
  have hu1 : u < 1 := by
    dsimp [u]
    have hk : (k.val : ℝ) + 1 ≤ (2 : ℝ) ^ (n + 1 - r) := by
      exact_mod_cast Nat.succ_le_of_lt k.isLt
    have hden : 0 < (2 : ℝ) ^ (n + 1 - r) := by positivity
    apply (div_lt_one hden).2
    linarith
  have hleft_t : t - dyadicHaarLeft r j.val = u / (2 : ℝ) ^ r := by
    dsimp [t, u, dyadicHaarLeft]
    rw [midpointGridCoordinate_split hr]
    field_simp
    <;> ring_nf
  have hwidth : dyadicHaarRight r j.val - dyadicHaarLeft r j.val =
      1 / (2 : ℝ) ^ r := by
    dsimp [dyadicHaarRight, dyadicHaarLeft]
    field_simp
    push_cast
    ring
  have ht_right : dyadicHaarRight r j.val - t = (1 - u) / (2 : ℝ) ^ r := by
    calc
      dyadicHaarRight r j.val - t =
          (dyadicHaarRight r j.val - dyadicHaarLeft r j.val) -
            (t - dyadicHaarLeft r j.val) := by ring
      _ = (1 - u) / (2 : ℝ) ^ r := by rw [hwidth, hleft_t]; ring
  have hleft : dyadicHaarLeft r j.val < t := by
    rw [← sub_pos, hleft_t]
    positivity
  have hright : t < dyadicHaarRight r j.val := by
    rw [← sub_pos, ht_right]
    exact div_pos (by linarith) (by positivity)
  have hmid : t ≤ dyadicHaarMid r j.val ↔ u ≤ 1 / 2 := by
    have hmid' : t ≤ dyadicHaarMid r j.val ↔
        t - dyadicHaarLeft r j.val ≤
          (dyadicHaarRight r j.val - dyadicHaarLeft r j.val) / 2 := by
      rw [dyadicHaarMid]
      constructor <;> intro h <;> linarith
    rw [hmid', hleft_t, hwidth]
    have hden : 0 < (2 : ℝ) ^ r := by positivity
    constructor <;> intro h
    · field_simp at h
      nlinarith
    · have h' : u * 2 ≤ 1 := by nlinarith
      field_simp
      nlinarith
  unfold dyadicHaarTentAt
  change (if t ≤ dyadicHaarLeft r j.val then 0 else
      if t ≤ dyadicHaarMid r j.val then t - dyadicHaarLeft r j.val else
      if t ≤ dyadicHaarRight r j.val then dyadicHaarRight r j.val - t else 0) = _
  rw [if_neg (not_le_of_gt hleft)]
  by_cases hu : u ≤ 1 / 2
  · simp only [if_pos (hmid.mpr hu), if_pos (le_of_lt hright)]
    rw [min_eq_left (by linarith : u ≤ 1 - u)]
    rw [hleft_t]
  · simp only [if_neg (mt hmid.mp hu), if_pos (le_of_lt hright)]
    rw [min_eq_right (by linarith : 1 - u ≤ u)]
    rw [ht_right]

/-- Scalar normalized Haar coefficient on the depth-`n+1` midpoint grid. -/
private noncomputable def nativeTentCoefficient {n r : ℕ}
    (j : Fin (2 ^ r)) (q : Fin (2 ^ (n + 1))) : ℝ :=
  Real.sqrt (2 : ℝ) ^ r *
    dyadicHaarTentAt r j.val (midpointGridCoordinate n q)

/-- A scalar Haar tent vanishes on a grid point reconstructed from a
different dyadic cell. -/
private theorem nativeTentCoefficient_zero_of_cell_ne {n r : ℕ} (hr : r ≤ n)
    (j c : Fin (2 ^ r)) (k : Fin (2 ^ (n + 1 - r))) (hjc : j ≠ c) :
    nativeTentCoefficient j
      ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k)) = 0 := by
  have hcell : HaarQuarter.dyadicCellIndex (n + 1) ⟨r, by omega⟩
      ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k)).val =
        c.val := by
    calc
      _ = ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩)
          ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k))).1.val :=
        (HaarQuarter.dyadicGridSplitEquiv_fst _ _ _).symm
      _ = c.val := congrArg (fun p : Fin (2 ^ r) × Fin (2 ^ (n + 1 - r)) => p.1.val)
        ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).apply_symm_apply (c, k))
  have hnonneg := dyadicHaarTentAt_bounds
    (midpointGridCoordinate n
      ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k)))
      j.isLt
  have hzero : dyadicHaarTentAt r j.val
      (midpointGridCoordinate n
        ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k))) = 0 := by
    by_contra hnz
    have hpos : 0 < dyadicHaarTentAt r j.val
        (midpointGridCoordinate n
          ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k))) :=
      lt_of_le_of_ne hnonneg.1 (Ne.symm hnz)
    have hinterior := (dyadicHaarTentAt_pos_iff _ j.isLt).1 hpos
    have haddr := midpointAddress_eq_dyadicCellIndex
      ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k))
      j.val hr hinterior.1 hinterior.2
    have : j.val = c.val := by omega
    exact hjc (Fin.ext this)
  simp [nativeTentCoefficient, hzero]

/-- The unit tent at a dyadic midpoint, in the integer numerator convention
used by `Prefix.midpoint_tent_square_mean`. -/
private noncomputable def midpointPeakValue (a : ℕ)
    (k : Fin (2 ^ a)) : ℝ :=
  ((min (2 * k.val + 1) (2 ^ (a + 1) - (2 * k.val + 1)) : ℕ) : ℝ) /
    (2 : ℝ) ^ a

private theorem twice_local_min_eq_midpointPeakValue {a : ℕ}
    (k : Fin (2 ^ a)) :
    2 * min (((k.val : ℝ) + 1 / 2) / (2 : ℝ) ^ a)
        (1 - (((k.val : ℝ) + 1 / 2) / (2 : ℝ) ^ a)) =
      midpointPeakValue a k := by
  let D : ℝ := (2 : ℝ) ^ a
  let A : ℕ := 2 * k.val + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : A ≤ 2 ^ (a + 1) := by
    dsimp [A]
    have hk := k.isLt
    omega
  have hAcast : (A : ℝ) ≤ (2 : ℝ) ^ (a + 1) := by exact_mod_cast hA
  have hpow : (2 : ℝ) ^ (a + 1) = 2 * D := by
    dsimp [D]
    rw [pow_succ]
    ring
  have hu : ((k.val : ℝ) + 1 / 2) / D = (A : ℝ) / (2 * D) := by
    dsimp [D, A]
    push_cast
    field_simp
    <;> ring
  have hv : 1 - ((k.val : ℝ) + 1 / 2) / D =
      ((2 ^ (a + 1) - A : ℕ) : ℝ) / (2 * D) := by
    rw [hu]
    have hcast : ((2 ^ (a + 1) - A : ℕ) : ℝ) =
        (2 : ℝ) ^ (a + 1) - A := by
      rw [Nat.cast_sub hA]
      simp
    rw [hcast, hpow]
    field_simp
  have hv' : 1 - (A : ℝ) / (2 * D) =
      ((2 ^ (a + 1) - A : ℕ) : ℝ) / (2 * D) := by
    calc
      _ = 1 - ((k.val : ℝ) + 1 / 2) / D := by rw [hu]
      _ = _ := hv
  rw [hu, hv', min_div_div_right (by positivity : 0 ≤ (2 * D : ℝ))]
  rw [midpointPeakValue]
  simp only [Nat.cast_min]
  rw [Nat.cast_sub hA]
  have hpowCast : ((2 ^ (a + 1) : ℕ) : ℝ) = 2 * D := by
    change ((2 ^ (a + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ a
    exact_mod_cast (show 2 ^ (a + 1) = 2 * 2 ^ a by
      rw [Nat.pow_succ]
      omega)
  rw [hpowCast]
  dsimp [D]
  field_simp
  <;> ring

/-- Squared normalized coefficient at the cell's own midpoint fiber. -/
private theorem nativeTentCoefficient_split_sq {n r : ℕ} (hr : r ≤ n)
    (j : Fin (2 ^ r)) (k : Fin (2 ^ (n + 1 - r))) :
    (nativeTentCoefficient j
      ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (j, k))) ^ 2 =
      (1 / (2 : ℝ) ^ r) * (midpointPeakValue (n + 1 - r) k / 2) ^ 2 := by
  rw [nativeTentCoefficient, dyadicHaarTentAt_split hr]
  have hmin := twice_local_min_eq_midpointPeakValue (a := n + 1 - r) k
  have hmin' : min (((k.val : ℝ) + 1 / 2) / (2 : ℝ) ^ (n + 1 - r))
      (1 - (((k.val : ℝ) + 1 / 2) / (2 : ℝ) ^ (n + 1 - r))) =
        midpointPeakValue (n + 1 - r) k / 2 := by linarith
  rw [hmin']
  have hsqrt : (Real.sqrt (2 : ℝ) ^ r) ^ 2 = (2 : ℝ) ^ r := by
    calc
      (Real.sqrt (2 : ℝ) ^ r) ^ 2 =
          (Real.sqrt (2 : ℝ)) ^ (r * 2) := by rw [pow_mul]
      _ = (Real.sqrt (2 : ℝ)) ^ (2 * r) := by congr 1 <;> omega
      _ = (Real.sqrt (2 : ℝ) ^ 2) ^ r := by rw [← pow_mul]
      _ = (2 : ℝ) ^ r := by rw [Real.sq_sqrt (by norm_num)]
  field_simp
  rw [hsqrt]
  <;> ring

private theorem nativeTentCoefficient_sq_fiber_sum {n r : ℕ} (hr : r ≤ n)
    (c : Fin (2 ^ r)) (k : Fin (2 ^ (n + 1 - r))) :
    (∑ j : Fin (2 ^ r),
      (nativeTentCoefficient j
        ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k))) ^ 2) =
      (nativeTentCoefficient c
        ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k))) ^ 2 := by
  classical
  rw [Finset.sum_eq_single c]
  · intro j hj hjc
    have hz := nativeTentCoefficient_zero_of_cell_ne hr j c k hjc
    simp [hz]
  · intro hc
    exact False.elim (hc (Finset.mem_univ c))

/-- Reindex the double sum over grid points and Haar addresses by the dyadic
cell and the within-cell midpoint address. -/
private theorem nativeTentCoefficient_sq_sum_reindex {n r : ℕ} (hr : r ≤ n) :
    (∑ q : Fin (2 ^ (n + 1)), ∑ j : Fin (2 ^ r),
      (nativeTentCoefficient j q) ^ 2) =
      ∑ c : Fin (2 ^ r), ∑ k : Fin (2 ^ (n + 1 - r)),
        ∑ j : Fin (2 ^ r),
          (nativeTentCoefficient j
            ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k))) ^ 2 := by
  classical
  calc
    _ = ∑ p : Fin (2 ^ r) × Fin (2 ^ (n + 1 - r)),
        ∑ j : Fin (2 ^ r),
          (nativeTentCoefficient j
            ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm p)) ^ 2 := by
          apply Fintype.sum_equiv (HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩)
          intro q
          simp
    _ = ∑ c : Fin (2 ^ r), ∑ k : Fin (2 ^ (n + 1 - r)),
        ∑ j : Fin (2 ^ r),
          (nativeTentCoefficient j
            ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k))) ^ 2 :=
          Fintype.sum_prod_type _

/-- Once a midpoint-grid mean lower bound is available, the actual native row
variance has a positive-density set of grid points above half that mean.
The pointwise upper bound is the sharp layer-count bound proved above. -/
theorem nativeLayerRowVariance_good_fraction {d n : ℕ} (hd : 0 < d)
    (m : ℝ) (hm : 0 < m)
    (hmean : m ≤
      (∑ q : MidpointGridIndex d n, nativeLayerRowVariance q) /
        (Fintype.card (MidpointGridIndex d n) : ℝ)) :
    m / (2 * ((1 / (2 : ℝ) ^ (n + 2 * d)) *
        Nat.choose (n + d - 1) (d - 1))) ≤
      ((Finset.univ.filter (fun q : MidpointGridIndex d n =>
          m / 2 ≤ nativeLayerRowVariance q)).card : ℝ) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
  classical
  have hchoose : 0 < Nat.choose (n + d - 1) (d - 1) := by
    apply Nat.choose_pos
    omega
  have hM : 0 < (1 / (2 : ℝ) ^ (n + 2 * d)) *
      Nat.choose (n + d - 1) (d - 1) := by
    apply mul_pos
    · positivity
    · exact_mod_cast hchoose
  apply Prefix.finite_good_fraction_lower (fun q : MidpointGridIndex d n =>
      nativeLayerRowVariance q) hm
  · exact hM
  · intro q
    exact nativeLayerRowVariance_le hd q
  · exact hmean

end BrownianSharp
