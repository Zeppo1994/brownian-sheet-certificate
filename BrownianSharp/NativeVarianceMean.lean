import BrownianSharp.NativeVariance

/-! Midpoint-grid mean identities for the actual native Brownian row. -/

open scoped BigOperators

namespace BrownianSharp

private noncomputable def peakTentValue (a : ℕ) (k : Fin (2 ^ a)) : ℝ :=
  ((min (2 * k.val + 1) (2 ^ (a + 1) - (2 * k.val + 1)) : ℕ) : ℝ) /
    (2 : ℝ) ^ a

private theorem fin_sum_to_range {N : ℕ} (f : Fin N → ℝ) :
    (∑ i : Fin N, f i) =
      ∑ i ∈ Finset.range N, if h : i < N then f ⟨i, h⟩ else 0 := by
  rw [Finset.sum_fin_eq_sum_range]

private theorem peakTentValue_square_sum {a : ℕ} (ha : 1 ≤ a) :
    (∑ k : Fin (2 ^ a), (peakTentValue a k) ^ 2) =
      (2 ^ a : ℝ) * Prefix.midpoint_tent_square_mean (2 ^ (a - 1)) := by
  have h2m : 2 * 2 ^ (a - 1) = 2 ^ a := by
    calc
      2 * 2 ^ (a - 1) = 2 ^ (a - 1) * 2 := by ring
      _ = 2 ^ ((a - 1) + 1) := (Nat.pow_succ 2 (a - 1)).symm
      _ = 2 ^ a := by congr 1; omega
  have h4m : 4 * 2 ^ (a - 1) = 2 ^ (a + 1) := by
    calc
      4 * 2 ^ (a - 1) = 2 * (2 * 2 ^ (a - 1)) := by omega
      _ = 2 * 2 ^ a := by rw [h2m]
      _ = 2 ^ (a + 1) := by rw [Nat.pow_succ]; ring
  have hL :
      (∑ k : Fin (2 ^ a), (peakTentValue a k) ^ 2) =
        ∑ j ∈ Finset.range (2 ^ a),
          (((min (2 * j + 1) (2 ^ (a + 1) - (2 * j + 1)) : ℕ) : ℝ) /
            (2 : ℝ) ^ a) ^ 2 := by
    rw [fin_sum_to_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hlt := Finset.mem_range.mp hj
    simp [peakTentValue, hlt]
  rw [hL, Prefix.midpoint_tent_square_mean]
  rw [h4m]
  have hden : (2 * (2 ^ (a - 1) : ℕ) : ℝ) = (2 : ℝ) ^ a := by
    exact_mod_cast h2m
  rw [hden]
  rw [h2m]
  simp_rw [div_pow]
  rw [← Finset.sum_div]
  field_simp
  <;> ring

private theorem meanSplit_symm_val {N : ℕ} (l : Fin N)
    (j : Fin (2 ^ l.val)) (k : Fin (2 ^ (N - l.val))) :
    ((HaarQuarter.dyadicGridSplitEquiv N l).symm (j, k)).val =
      j.val * 2 ^ (N - l.val) + k.val := by
  simp [HaarQuarter.dyadicGridSplitEquiv]
  ac_rfl

private theorem meanMidpointCoordinate_split {n r : ℕ} (hr : r ≤ n)
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
        (2 : ℝ) ^ (n + 1)) := by rw [meanSplit_symm_val]
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

private theorem meanHaarTentAt_split {n r : ℕ} (hr : r ≤ n)
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
  have hu0 : 0 < u := by dsimp [u]; positivity
  have hu1 : u < 1 := by
    dsimp [u]
    have hk : (k.val : ℝ) + 1 ≤ (2 : ℝ) ^ (n + 1 - r) := by
      exact_mod_cast Nat.succ_le_of_lt k.isLt
    have hden : 0 < (2 : ℝ) ^ (n + 1 - r) := by positivity
    apply (div_lt_one hden).2
    linarith
  have hleft_t : t - dyadicHaarLeft r j.val = u / (2 : ℝ) ^ r := by
    dsimp [t, u, dyadicHaarLeft]
    rw [meanMidpointCoordinate_split hr]
    field_simp
    <;> ring_nf
  have hwidth : dyadicHaarRight r j.val - dyadicHaarLeft r j.val =
      1 / (2 : ℝ) ^ r := by
    dsimp [dyadicHaarRight, dyadicHaarLeft]
    field_simp
    push_cast
    ring
  have hright_t : dyadicHaarRight r j.val - t = (1 - u) / (2 : ℝ) ^ r := by
    calc
      dyadicHaarRight r j.val - t =
          (dyadicHaarRight r j.val - dyadicHaarLeft r j.val) -
            (t - dyadicHaarLeft r j.val) := by ring
      _ = (1 - u) / (2 : ℝ) ^ r := by rw [hwidth, hleft_t]; ring
  have hleft : dyadicHaarLeft r j.val < t := by
    rw [← sub_pos, hleft_t]
    positivity
  have hright : t < dyadicHaarRight r j.val := by
    rw [← sub_pos, hright_t]
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
    rw [min_eq_left (by linarith : u ≤ 1 - u), hleft_t]
  · simp only [if_neg (mt hmid.mp hu), if_pos (le_of_lt hright)]
    rw [min_eq_right (by linarith : 1 - u ≤ u), hright_t]

noncomputable def midpointScalarTentCoefficient {n r : ℕ}
    (j : Fin (2 ^ r)) (q : Fin (2 ^ (n + 1))) : ℝ :=
  Real.sqrt (2 : ℝ) ^ r * dyadicHaarTentAt r j.val (midpointGridCoordinate n q)

private theorem twiceLocalMin_eq_peakTentValue {a : ℕ}
    (k : Fin (2 ^ a)) :
    2 * min (((k.val : ℝ) + 1 / 2) / (2 : ℝ) ^ a)
        (1 - (((k.val : ℝ) + 1 / 2) / (2 : ℝ) ^ a)) = peakTentValue a k := by
  let D : ℝ := (2 : ℝ) ^ a
  let A : ℕ := 2 * k.val + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hA : A ≤ 2 ^ (a + 1) := by
    dsimp [A]
    have hk := k.isLt
    omega
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
  have hmin : min (((k.val : ℝ) + 1 / 2) / D)
      (1 - (((k.val : ℝ) + 1 / 2) / D)) =
        min (A : ℝ) ((2 ^ (a + 1) - A : ℕ) : ℝ) / (2 * D) := by
    rw [hu, hv', min_div_div_right (by positivity : 0 ≤ (2 * D : ℝ))]
  rw [hmin, peakTentValue]
  simp only [Nat.cast_min]
  rw [Nat.cast_sub hA]
  have hpowCast : ((2 ^ (a + 1) : ℕ) : ℝ) = 2 * D := by
    change ((2 ^ (a + 1) : ℕ) : ℝ) = 2 * (2 : ℝ) ^ a
    exact_mod_cast (show 2 ^ (a + 1) = 2 * 2 ^ a by
      rw [Nat.pow_succ]
      omega)
  rw [hpowCast]
  dsimp [D, A]
  field_simp
  <;> ring

private theorem midpointScalarTentCoefficient_split_sq {n r : ℕ} (hr : r ≤ n)
    (j : Fin (2 ^ r)) (k : Fin (2 ^ (n + 1 - r))) :
    (midpointScalarTentCoefficient j
      ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (j, k))) ^ 2 =
      (1 / (2 : ℝ) ^ r) *
        (peakTentValue (n + 1 - r) k / 2) ^ 2 := by
  rw [midpointScalarTentCoefficient, meanHaarTentAt_split hr]
  have hmin := twiceLocalMin_eq_peakTentValue (a := n + 1 - r) k
  have hmin' : min (((k.val : ℝ) + 1 / 2) / (2 : ℝ) ^ (n + 1 - r))
      (1 - (((k.val : ℝ) + 1 / 2) / (2 : ℝ) ^ (n + 1 - r))) =
        peakTentValue (n + 1 - r) k / 2 := by linarith
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

private theorem midpointScalarTentCoefficient_zero_of_cell_ne {n r : ℕ} (hr : r ≤ n)
    (j c : Fin (2 ^ r)) (k : Fin (2 ^ (n + 1 - r))) (hjc : j ≠ c) :
    midpointScalarTentCoefficient j
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
  simp [midpointScalarTentCoefficient, hzero]

private theorem midpointScalarTentCoefficient_sq_fiber_sum {n r : ℕ}
    (hr : r ≤ n) (c : Fin (2 ^ r)) (k : Fin (2 ^ (n + 1 - r))) :
    (∑ j : Fin (2 ^ r),
      (midpointScalarTentCoefficient j
        ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k))) ^ 2) =
      (midpointScalarTentCoefficient c
        ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k))) ^ 2 := by
  classical
  rw [Finset.sum_eq_single c]
  · intro j hj hjc
    have hz := midpointScalarTentCoefficient_zero_of_cell_ne hr j c k hjc
    simp [hz]
  · intro hc
    exact False.elim (hc (Finset.mem_univ c))

private theorem midpointScalarTentCoefficient_sq_sum_reindex {n r : ℕ}
    (hr : r ≤ n) :
    (∑ q : Fin (2 ^ (n + 1)), ∑ j : Fin (2 ^ r),
      (midpointScalarTentCoefficient j q) ^ 2) =
      ∑ c : Fin (2 ^ r), ∑ k : Fin (2 ^ (n + 1 - r)),
        ∑ j : Fin (2 ^ r),
          (midpointScalarTentCoefficient j
            ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k))) ^ 2 := by
  classical
  calc
    _ = ∑ p : Fin (2 ^ r) × Fin (2 ^ (n + 1 - r)),
        ∑ j : Fin (2 ^ r),
          (midpointScalarTentCoefficient j
            ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm p)) ^ 2 := by
          apply Fintype.sum_equiv (HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩)
          intro q
          simp
    _ = ∑ c : Fin (2 ^ r), ∑ k : Fin (2 ^ (n + 1 - r)),
        ∑ j : Fin (2 ^ r),
          (midpointScalarTentCoefficient j
            ((HaarQuarter.dyadicGridSplitEquiv (n + 1) ⟨r, by omega⟩).symm (c, k))) ^ 2 :=
          Fintype.sum_prod_type _

private theorem midpointScalarTentCoefficient_sq_total {n r : ℕ} (hr : r ≤ n) :
    (∑ q : Fin (2 ^ (n + 1)), ∑ j : Fin (2 ^ r),
      (midpointScalarTentCoefficient j q) ^ 2) =
      (2 ^ (n + 1 - r) : ℝ) / 4 *
        Prefix.midpoint_tent_square_mean (2 ^ (n - r)) := by
  let a : ℕ := n + 1 - r
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hshape : n + 1 - r = a := rfl
  have htail : n - r = a - 1 := by dsimp [a]; omega
  have hsumPeak : (∑ k : Fin (2 ^ a), (peakTentValue a k / 2) ^ 2) =
      ((2 ^ a : ℝ) * Prefix.midpoint_tent_square_mean (2 ^ (a - 1))) / 4 := by
    simp_rw [div_pow]
    rw [← Finset.sum_div, peakTentValue_square_sum ha]
    ring
  rw [midpointScalarTentCoefficient_sq_sum_reindex hr]
  simp_rw [midpointScalarTentCoefficient_sq_fiber_sum hr]
  simp_rw [midpointScalarTentCoefficient_split_sq hr]
  calc
    _ = ∑ c : Fin (2 ^ r),
        (1 / (2 : ℝ) ^ r) *
          (∑ k : Fin (2 ^ a), (peakTentValue a k / 2) ^ 2) := by
          apply Finset.sum_congr rfl
          intro c hc
          rw [← Finset.mul_sum]
    _ = ∑ c : Fin (2 ^ r),
        (1 / (2 : ℝ) ^ r) *
          (((2 ^ a : ℝ) * Prefix.midpoint_tent_square_mean (2 ^ (a - 1))) / 4) := by
          simp_rw [hsumPeak]
    _ = (2 ^ a : ℝ) / 4 * Prefix.midpoint_tent_square_mean (2 ^ (a - 1)) := by
          simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
          push_cast
          field_simp
          <;> ring
    _ = (2 ^ (n + 1 - r) : ℝ) / 4 *
        Prefix.midpoint_tent_square_mean (2 ^ (n - r)) := by
          rw [← hshape, ← htail]

/-- Mean square of all one-dimensional depth-r Haar coefficients on the
depth-(n+1) midpoint grid is at least `2^(-r)/16`. -/
theorem midpointScalarTentCoefficient_mean_lower {n r : ℕ} (hr : r ≤ n) :
    (1 / (2 : ℝ) ^ r) / 16 ≤
      (∑ q : Fin (2 ^ (n + 1)), ∑ j : Fin (2 ^ r),
        (midpointScalarTentCoefficient j q) ^ 2) /
        (Fintype.card (Fin (2 ^ (n + 1))) : ℝ) := by
  have ha : 1 ≤ n + 1 - r := by omega
  have hmean : (1 : ℝ) / 4 ≤ Prefix.midpoint_tent_square_mean (2 ^ (n - r)) := by
    have htail : n - r = n + 1 - r - 1 := by omega
    rw [htail, Prefix.midpoint_tent_square_mean_dyadic ha]
    exact Prefix.midpoint_tent_square_mean_lower ha
  have htotal := midpointScalarTentCoefficient_sq_total hr
  have hcard : (Fintype.card (Fin (2 ^ (n + 1))) : ℝ) = (2 : ℝ) ^ (n + 1) := by simp
  rw [htotal, hcard]
  have hpow : (2 : ℝ) ^ (n + 1 - r) * (2 : ℝ) ^ r = (2 : ℝ) ^ (n + 1) := by
    rw [← pow_add, Nat.sub_add_cancel (by omega : r ≤ n + 1)]
  have hratio : (2 : ℝ) ^ (n + 1 - r) / (2 : ℝ) ^ (n + 1) =
      1 / (2 : ℝ) ^ r := by
    rw [← hpow]
    field_simp
  rw [show (2 ^ (n + 1 - r) : ℝ) / 4 *
      Prefix.midpoint_tent_square_mean (2 ^ (n - r)) /
        (2 : ℝ) ^ (n + 1) =
      ((2 : ℝ) ^ (n + 1 - r) / (2 : ℝ) ^ (n + 1)) / 4 *
        Prefix.midpoint_tent_square_mean (2 ^ (n - r)) by ring, hratio]
  have hscale : 0 ≤ (1 / (2 : ℝ) ^ r) / 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hmean hscale]

private theorem sum_pi_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)]
    (f : ∀ i, α i → ℝ) :
    (∑ x : (∀ i, α i), ∏ i, f i (x i)) =
      ∏ i, ∑ a : α i, f i a := by
  classical
  simpa using (Finset.prod_univ_sum
    (fun i => (Finset.univ : Finset (α i))) f).symm

private theorem nativeLayerRowCoefficient_eq_scalarProduct {d n : ℕ}
    (q : MidpointGridIndex d n) (a : LayerIndex d n) :
    nativeLayerRowCoefficient q a =
      ∏ i : Fin d, midpointScalarTentCoefficient (a.2 i) (q i) := by
  rw [rowCoefficient_eq_normalized_tent_product]
  rfl

private theorem nativeShapeRowSquare_sum_eq_product {d n : ℕ}
    (r : Shape d n) :
    (∑ q : MidpointGridIndex d n,
      ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
        (nativeLayerRowCoefficient q ⟨r, j⟩) ^ 2) =
      ∏ i : Fin d, ∑ q : Fin (2 ^ (n + 1)),
        ∑ j : Fin (2 ^ r.1 i),
          (midpointScalarTentCoefficient j q) ^ 2 := by
  classical
  calc
    _ = ∑ q : MidpointGridIndex d n,
        ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
          ∏ i : Fin d, (midpointScalarTentCoefficient (j i) (q i)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro q hq
            apply Finset.sum_congr rfl
            intro j hj
            rw [nativeLayerRowCoefficient_eq_scalarProduct]
            rw [Finset.prod_pow]
    _ = ∑ q : MidpointGridIndex d n,
        ∏ i : Fin d, ∑ j : Fin (2 ^ r.1 i),
          (midpointScalarTentCoefficient j (q i)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro q hq
            exact sum_pi_prod (fun i j =>
              (midpointScalarTentCoefficient j (q i)) ^ 2)
    _ = ∏ i : Fin d, ∑ q : Fin (2 ^ (n + 1)),
        ∑ j : Fin (2 ^ r.1 i),
          (midpointScalarTentCoefficient j q) ^ 2 := by
            exact sum_pi_prod (fun i q =>
              ∑ j : Fin (2 ^ r.1 i),
                (midpointScalarTentCoefficient j q) ^ 2)

private theorem shape_depth_le_grade {d n : ℕ} (r : Shape d n) (i : Fin d) :
    r.1 i ≤ n := by
  let a : LayerIndex d n := ⟨r, fun j => ⟨0, Nat.pow_pos (by decide)⟩⟩
  have h := layerIndexDepth_le_grade a i
  simpa [a, layerIndexDepth] using h

private theorem nativeShapeRowSquare_mean_lower {d n : ℕ}
    (r : Shape d n) :
    (1 / (2 : ℝ) ^ (n + 4 * d)) ≤
      (∑ q : MidpointGridIndex d n,
        ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
          (nativeLayerRowCoefficient q ⟨r, j⟩) ^ 2) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
  classical
  let K := 2 ^ (n + 1)
  have hcoord (i : Fin d) :
      (1 / (2 : ℝ) ^ (r.1 i)) / 16 ≤
        (∑ q : Fin K, ∑ j : Fin (2 ^ r.1 i),
          (midpointScalarTentCoefficient j q) ^ 2) /
          (Fintype.card (Fin K) : ℝ) := by
    simpa [K] using midpointScalarTentCoefficient_mean_lower
      (n := n) (r := r.1 i) (shape_depth_le_grade r i)
  have hprod := Finset.prod_le_prod₀
    (s := (Finset.univ : Finset (Fin d)))
    (fun i hi => by positivity)
    (fun i hi => hcoord i)
  have hcard : (Fintype.card (MidpointGridIndex d n) : ℝ) =
      ∏ i : Fin d, (Fintype.card (Fin K) : ℝ) := by
    simp [MidpointGridIndex, K, Fintype.card_pi]
  rw [nativeShapeRowSquare_sum_eq_product, hcard, ← Finset.prod_div_distrib]
  have hgradeNat : (∑ i : Fin d, r.1 i) = n := by
    have h := (Finset.mem_finsuppAntidiag'.mp r.2).1
    simpa [Finsupp.sum_fintype] using h
  have hconst :
      (∏ i : Fin d, (1 / (2 : ℝ) ^ (r.1 i)) / 16) =
        1 / (2 : ℝ) ^ (n + 4 * d) := by
    have h16 : (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
    have hfactor (i : Fin d) :
        (1 / (2 : ℝ) ^ (r.1 i)) / 16 =
          1 / (2 : ℝ) ^ (r.1 i + 4) := by
      rw [h16, div_div, ← pow_add]
    simp_rw [hfactor]
    simp_rw [one_div]
    rw [Finset.prod_inv_distrib]
    rw [Finset.prod_pow_eq_pow_sum]
    rw [Finset.sum_add_distrib, hgradeNat]
    simp [Fintype.card_fin]
    ring
  calc
    _ = ∏ i : Fin d, (1 / (2 : ℝ) ^ (r.1 i)) / 16 := hconst.symm
    _ ≤ ∏ i : Fin d,
        (∑ q : Fin K, ∑ j : Fin (2 ^ r.1 i),
          (midpointScalarTentCoefficient j q) ^ 2) /
          (Fintype.card (Fin K) : ℝ) := hprod

/-- The actual native Brownian row variance has the claimed finite midpoint
mean lower bound. This is the tensorized dyadic tent identity, summed over all
weak-composition shapes. -/
theorem nativeLayerRowVariance_mean_lower {d n : ℕ} (hd : 0 < d) :
    (1 / (2 : ℝ) ^ (n + 4 * d)) * Nat.choose (n + d - 1) (d - 1) ≤
      (∑ q : MidpointGridIndex d n, nativeLayerRowVariance q) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
  classical
  let M : ℝ := 1 / (2 : ℝ) ^ (n + 4 * d)
  have hshapeMean : ∀ r : Shape d n,
      M ≤ (∑ q : MidpointGridIndex d n,
        ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
          (nativeLayerRowCoefficient q ⟨r, j⟩) ^ 2) /
        (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    intro r
    exact nativeShapeRowSquare_mean_lower r
  have htotal :
      (∑ q : MidpointGridIndex d n, nativeLayerRowVariance q) =
        ∑ r : Shape d n,
          ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
            ∑ q : MidpointGridIndex d n,
              (nativeLayerRowCoefficient q ⟨r, j⟩) ^ 2 := by
    unfold nativeLayerRowVariance
    rw [Finset.sum_comm, Fintype.sum_sigma]
  have hdiv :
      (∑ q : MidpointGridIndex d n, nativeLayerRowVariance q) /
          (Fintype.card (MidpointGridIndex d n) : ℝ) =
        ∑ r : Shape d n,
          (∑ q : MidpointGridIndex d n,
            ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
              (nativeLayerRowCoefficient q ⟨r, j⟩) ^ 2) /
            (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    rw [htotal, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_comm]
  have hsumLower :
      M * (Fintype.card (Shape d n) : ℝ) ≤
        ∑ r : Shape d n,
          (∑ q : MidpointGridIndex d n,
            ∑ j : (∀ i : Fin d, Fin (2 ^ r.1 i)),
              (nativeLayerRowCoefficient q ⟨r, j⟩) ^ 2) /
            (Fintype.card (MidpointGridIndex d n) : ℝ) := by
    calc
      _ = ∑ r : Shape d n, M := by simp [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ _ := Finset.sum_le_sum (fun r hr => hshapeMean r)
  have hshapeCard : (Fintype.card (Shape d n) : ℝ) =
      Nat.choose (n + d - 1) (d - 1) := by
    exact_mod_cast shape_card d n hd
  rw [← hdiv] at hsumLower
  rw [hshapeCard] at hsumLower
  simpa [M] using hsumLower

end BrownianSharp
