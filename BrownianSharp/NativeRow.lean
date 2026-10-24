import BrownianSharp.Projection

/-!
Exact coefficients of the native layer against the finite midpoint grid.
The row entries are actual inner products in the Brownian sheet's anchored
box span; their tent factorization gives support and magnitude bounds without
introducing a surrogate Gaussian field.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace BrownianSharp
open HaarQuarter

/-- The univariate tent factor obtained by integrating a Haar step against an
anchored interval indicator. -/
noncomputable def dyadicHaarTentAt (r j : ℕ) (t : ℝ) : ℝ :=
  if t ≤ dyadicHaarLeft r j then 0
  else if t ≤ dyadicHaarMid r j then t - dyadicHaarLeft r j
  else if t ≤ dyadicHaarRight r j then dyadicHaarRight r j - t
  else 0

/-- The Brownian cube anchor represented by a midpoint-grid index. -/
noncomputable def nativeMidpointBrownianAnchor {d n : ℕ}
    (q : MidpointGridIndex d n) : BrownianCubeAnchor d := by
  refine ⟨fun i => midpointGridCoordinate n (q i), ?_⟩
  intro i
  have h := midpointGridCoordinate_mem_Ioo n (q i)
  simpa [Set.mem_Icc] using And.intro (le_of_lt h.1) (le_of_lt h.2)

/-- A finite native-layer coefficient in the evaluation row at grid point q. -/
noncomputable def nativeLayerRowCoefficient {d n : ℕ}
    (q : MidpointGridIndex d n) (a : LayerIndex d n) : ℝ :=
  ⟪nativeLayerVector a,
    (⟨brownianSheetBoxIndicatorLp (nativeMidpointBrownianAnchor q).val,
      brownianCubeBoxIndicator_mem (nativeMidpointBrownianAnchor q)⟩ :
      brownianCubeBoxSpan d)⟫

/-- Exact row coefficient as the product of normalized univariate Haar tents. -/
theorem rowCoefficient_eq_product_tent {d n : ℕ}
    (q : MidpointGridIndex d n) (a : LayerIndex d n) :
    nativeLayerRowCoefficient q a =
      (∏ i : Fin d, Real.sqrt (2 : ℝ) ^ layerIndexDepth a i) *
        ∏ i : Fin d,
          (if midpointGridCoordinate n (q i) ≤
              dyadicHaarLeft (layerIndexDepth a i) (layerIndexCell a i) then 0
           else if midpointGridCoordinate n (q i) ≤
              dyadicHaarMid (layerIndexDepth a i) (layerIndexCell a i) then
                midpointGridCoordinate n (q i) -
                  dyadicHaarLeft (layerIndexDepth a i) (layerIndexCell a i)
           else if midpointGridCoordinate n (q i) ≤
              dyadicHaarRight (layerIndexDepth a i) (layerIndexCell a i) then
                dyadicHaarRight (layerIndexDepth a i) (layerIndexCell a i) -
                  midpointGridCoordinate n (q i)
           else 0) := by
  change ⟪dyadicTensorHaarVector (layerIndexDepth a) (layerIndexCell a),
      brownianSheetBoxIndicatorLp (nativeMidpointBrownianAnchor q).val⟫ = _
  rw [dyadicTensorHaarVector_inner_box_eq_product_tent
    (layerIndexDepth a) (layerIndexCell a)
    (fun i => (nativeMidpointBrownianAnchor q).val i)
    (layerIndexCell_lt a)
    (fun i => le_of_lt
      (midpointGridCoordinate_mem_Ioo n (q i)).1)]
  rfl

/-- Equivalent product formula with the one-dimensional tent packaged as a
single factor per coordinate. -/
theorem rowCoefficient_eq_normalized_tent_product {d n : ℕ}
    (q : MidpointGridIndex d n) (a : LayerIndex d n) :
    nativeLayerRowCoefficient q a =
      ∏ i : Fin d,
        (Real.sqrt (2 : ℝ) ^ layerIndexDepth a i) *
          dyadicHaarTentAt (layerIndexDepth a i) (layerIndexCell a i)
            (midpointGridCoordinate n (q i)) := by
  rw [rowCoefficient_eq_product_tent]
  rw [← Finset.prod_mul_distrib]
  congr 1

/-- A dyadic integrated Haar tent is nonnegative and at most half its support
interval's length. -/
theorem dyadicHaarTentAt_bounds {r j : ℕ} (t : ℝ)
    (hj : j < 2 ^ r) :
    0 ≤ dyadicHaarTentAt r j t ∧
      dyadicHaarTentAt r j t ≤
        (dyadicHaarRight r j - dyadicHaarLeft r j) / 2 := by
  have horder := dyadicHaar_endpoints_order hj
  have hmid := dyadicHaar_midpoint_identity r j
  by_cases hta : t ≤ dyadicHaarLeft r j
  · constructor
    · simp [dyadicHaarTentAt, hta]
    · simp [dyadicHaarTentAt, hta]
      apply div_nonneg
      · linarith [horder.1, horder.2.1, horder.2.2.1]
      · norm_num
  · by_cases htm : t ≤ dyadicHaarMid r j
    · constructor
      · simp [dyadicHaarTentAt, hta, htm]
        linarith
      · simp [dyadicHaarTentAt, hta, htm]
        nlinarith [hmid]
    · by_cases htb : t ≤ dyadicHaarRight r j
      · constructor
        · simp [dyadicHaarTentAt, hta, htm, htb]
        · simp [dyadicHaarTentAt, hta, htm, htb]
          nlinarith [hmid]
      · constructor
        · simp [dyadicHaarTentAt, hta, htm, htb]
        · simp [dyadicHaarTentAt, hta, htm, htb]
          apply div_nonneg
          · linarith [horder.1, horder.2.1, horder.2.2.1]
          · norm_num

/-- A dyadic tent is positive exactly on the strict interior of its support. -/
theorem dyadicHaarTentAt_pos_iff {r j : ℕ} (t : ℝ)
    (hj : j < 2 ^ r) :
    0 < dyadicHaarTentAt r j t ↔
      dyadicHaarLeft r j < t ∧ t < dyadicHaarRight r j := by
  have horder := dyadicHaar_endpoints_order hj
  have hmid := dyadicHaar_midpoint_identity r j
  have hp : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
  have hwidth : dyadicHaarLeft r j < dyadicHaarRight r j := by
    dsimp [dyadicHaarLeft, dyadicHaarRight]
    rw [div_lt_div_iff₀ hp hp]
    push_cast
    nlinarith [hp]
  have hleftmid : dyadicHaarLeft r j < dyadicHaarMid r j := by
    nlinarith [hmid, hwidth]
  have hmidright : dyadicHaarMid r j < dyadicHaarRight r j := by
    nlinarith [hmid, hwidth]
  constructor
  · intro hpos
    unfold dyadicHaarTentAt at hpos
    split_ifs at hpos with hta htm htb
    · norm_num at hpos
    · constructor
      · exact lt_of_not_ge hta
      · exact lt_of_le_of_lt htm hmidright
    · constructor
      · exact lt_trans hleftmid (lt_of_not_ge htm)
      · linarith
    · norm_num at hpos
  · rintro ⟨hat, htb⟩
    unfold dyadicHaarTentAt
    by_cases htm : t ≤ dyadicHaarMid r j
    · simp [not_le_of_gt hat, htm]
      linarith
    · simp [not_le_of_gt hat, htm, le_of_lt htb]
      linarith

/-- The row entry is nonnegative because it is the product of nonnegative
normalized tents. -/
theorem nativeLayerRowCoefficient_nonneg {d n : ℕ}
    (q : MidpointGridIndex d n) (a : LayerIndex d n) :
    0 ≤ nativeLayerRowCoefficient q a := by
  rw [rowCoefficient_eq_normalized_tent_product]
  apply Finset.prod_nonneg
  intro i hi
  apply mul_nonneg
  · positivity
  · exact (dyadicHaarTentAt_bounds (midpointGridCoordinate n (q i))
      (layerIndexCell_lt a i)).1

/-- Positivity of a native row coefficient is equivalent to positivity of
every coordinate tent, and therefore to strict containment of the grid point
in each addressed dyadic interval. -/
theorem nativeLayerRowCoefficient_pos_iff_tents_pos {d n : ℕ}
    (q : MidpointGridIndex d n) (a : LayerIndex d n) :
    0 < nativeLayerRowCoefficient q a ↔
      ∀ i : Fin d,
        0 < dyadicHaarTentAt (layerIndexDepth a i) (layerIndexCell a i)
          (midpointGridCoordinate n (q i)) := by
  rw [rowCoefficient_eq_normalized_tent_product]
  constructor
  · intro h i
    have hnonneg : ∀ i : Fin d,
        0 ≤ Real.sqrt (2 : ℝ) ^ layerIndexDepth a i *
          dyadicHaarTentAt (layerIndexDepth a i) (layerIndexCell a i)
            (midpointGridCoordinate n (q i)) := by
      intro j
      exact mul_nonneg (by positivity)
        (dyadicHaarTentAt_bounds _ (layerIndexCell_lt a j)).1
    have hfactor : 0 < Real.sqrt (2 : ℝ) ^ layerIndexDepth a i *
        dyadicHaarTentAt (layerIndexDepth a i) (layerIndexCell a i)
          (midpointGridCoordinate n (q i)) := by
      by_contra hn
      have hz : Real.sqrt (2 : ℝ) ^ layerIndexDepth a i *
          dyadicHaarTentAt (layerIndexDepth a i) (layerIndexCell a i)
            (midpointGridCoordinate n (q i)) = 0 :=
        le_antisymm (le_of_not_gt hn) (hnonneg i)
      have hp : ∏ j : Fin d,
          Real.sqrt (2 : ℝ) ^ layerIndexDepth a j *
            dyadicHaarTentAt (layerIndexDepth a j) (layerIndexCell a j)
              (midpointGridCoordinate n (q j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hz
      linarith
    have hscale : 0 < Real.sqrt (2 : ℝ) ^ layerIndexDepth a i :=
      pow_pos (Real.sqrt_pos.2 (by norm_num)) _
    have htent_nonneg : 0 ≤ dyadicHaarTentAt (layerIndexDepth a i)
        (layerIndexCell a i) (midpointGridCoordinate n (q i)) :=
      (dyadicHaarTentAt_bounds _ (layerIndexCell_lt a i)).1
    nlinarith
  · intro h
    apply Finset.prod_pos
    intro i hi
    exact mul_pos (pow_pos (Real.sqrt_pos.2 (by norm_num)) _)
      (h i)

/-- Geometric form of the native row support criterion. -/
theorem nativeLayerRowCoefficient_pos_iff_interior {d n : ℕ}
    (q : MidpointGridIndex d n) (a : LayerIndex d n) :
    0 < nativeLayerRowCoefficient q a ↔
      ∀ i : Fin d,
        dyadicHaarLeft (layerIndexDepth a i) (layerIndexCell a i) <
            midpointGridCoordinate n (q i) ∧
          midpointGridCoordinate n (q i) <
            dyadicHaarRight (layerIndexDepth a i) (layerIndexCell a i) := by
  rw [nativeLayerRowCoefficient_pos_iff_tents_pos]
  constructor
  · intro h i
    exact (dyadicHaarTentAt_pos_iff _ (layerIndexCell_lt a i)).1 (h i)
  · intro h i
    exact (dyadicHaarTentAt_pos_iff _ (layerIndexCell_lt a i)).2 (h i)

/-- Exact squared-coefficient bound for the finite native row. The grade of
`a` turns the product of per-coordinate tent maxima into `2^(-(n+2d))`.
-/
theorem nativeLayerRowCoefficient_sq_le {d n : ℕ}
    (q : MidpointGridIndex d n) (a : LayerIndex d n) :
    (nativeLayerRowCoefficient q a) ^ 2 ≤
      1 / (2 : ℝ) ^ (n + 2 * d) := by
  let f : Fin d → ℝ := fun i =>
    Real.sqrt (2 : ℝ) ^ layerIndexDepth a i *
      dyadicHaarTentAt (layerIndexDepth a i) (layerIndexCell a i)
        (midpointGridCoordinate n (q i))
  rw [rowCoefficient_eq_normalized_tent_product]
  change (∏ i : Fin d, f i) ^ 2 ≤ 1 / (2 : ℝ) ^ (n + 2 * d)
  have hf_nonneg (i : Fin d) : 0 ≤ f i := by
    dsimp [f]
    exact mul_nonneg (by positivity)
      (dyadicHaarTentAt_bounds _ (layerIndexCell_lt a i)).1
  have hf_sq (i : Fin d) : f i ^ 2 ≤
      1 / (2 : ℝ) ^ (layerIndexDepth a i + 2) := by
    dsimp [f]
    have htent := (dyadicHaarTentAt_bounds
      (midpointGridCoordinate n (q i)) (layerIndexCell_lt a i)).2
    have hlen : dyadicHaarRight (layerIndexDepth a i) (layerIndexCell a i) -
        dyadicHaarLeft (layerIndexDepth a i) (layerIndexCell a i) =
        1 / (2 : ℝ) ^ layerIndexDepth a i := by
      dsimp [dyadicHaarRight, dyadicHaarLeft]
      field_simp
      push_cast
      ring
    have hsqrt : (Real.sqrt (2 : ℝ) ^ layerIndexDepth a i) ^ 2 =
        (2 : ℝ) ^ layerIndexDepth a i := by
      calc
        (Real.sqrt (2 : ℝ) ^ layerIndexDepth a i) ^ 2 =
            (Real.sqrt (2 : ℝ) ^ 2) ^ layerIndexDepth a i := by
              rw [← pow_mul, Nat.mul_comm, pow_mul]
        _ = (2 : ℝ) ^ layerIndexDepth a i := by
              rw [Real.sq_sqrt (by norm_num)]
    have htent_nonneg : 0 ≤ dyadicHaarTentAt (layerIndexDepth a i)
        (layerIndexCell a i) (midpointGridCoordinate n (q i)) :=
      (dyadicHaarTentAt_bounds (midpointGridCoordinate n (q i))
        (layerIndexCell_lt a i)).1
    have hmax : dyadicHaarTentAt (layerIndexDepth a i)
        (layerIndexCell a i) (midpointGridCoordinate n (q i)) ≤
        1 / (2 * (2 : ℝ) ^ layerIndexDepth a i) := by
      rw [hlen] at htent
      calc
        _ ≤ (1 / (2 : ℝ) ^ layerIndexDepth a i) / 2 := htent
        _ = 1 / (2 * (2 : ℝ) ^ layerIndexDepth a i) := by
          field_simp
    have hsquare' : (dyadicHaarTentAt (layerIndexDepth a i)
        (layerIndexCell a i) (midpointGridCoordinate n (q i))) ^ 2 ≤
        (1 / (2 * (2 : ℝ) ^ layerIndexDepth a i)) ^ 2 := by
      nlinarith [hmax, htent_nonneg]
    rw [mul_pow, hsqrt]
    calc
      (2 : ℝ) ^ layerIndexDepth a i *
          (dyadicHaarTentAt (layerIndexDepth a i) (layerIndexCell a i)
            (midpointGridCoordinate n (q i))) ^ 2 ≤
        (2 : ℝ) ^ layerIndexDepth a i *
          (1 / (2 * (2 : ℝ) ^ layerIndexDepth a i)) ^ 2 :=
            by gcongr
      _ = 1 / (2 : ℝ) ^ (layerIndexDepth a i + 2) := by
        field_simp
        ring
  have hprod_sq : (∏ i : Fin d, f i) ^ 2 = ∏ i : Fin d, f i ^ 2 := by
    rw [Finset.prod_pow]
  have hbound : (∏ i : Fin d, f i) ^ 2 ≤
      ∏ i : Fin d, (1 / (2 : ℝ) ^ (layerIndexDepth a i + 2)) := by
    rw [hprod_sq]
    gcongr with i hi
    exact hf_sq i
  calc
    (∏ i : Fin d, f i) ^ 2 ≤
        ∏ i : Fin d, (1 / (2 : ℝ) ^ (layerIndexDepth a i + 2)) := hbound
    _ = 1 / (2 : ℝ) ^ (n + 2 * d) := by
      have hgrade := layerIndexDepth_grade a
      have hsum : (∑ i : Fin d, layerIndexDepth a i) = n := by
        simpa [layerIndexDepth, Finsupp.sum_fintype] using hgrade
      have hsum' : (∑ i : Fin d, (layerIndexDepth a i + 2)) = n + 2 * d := by
        calc
          (∑ i : Fin d, (layerIndexDepth a i + 2)) = n + d * 2 := by
            simp [Finset.sum_add_distrib, hsum]
          _ = n + 2 * d := by rw [Nat.mul_comm d 2]
      calc
        ∏ i : Fin d, (1 / (2 : ℝ) ^ (layerIndexDepth a i + 2)) =
            (1 / (2 : ℝ)) ^ (∑ i : Fin d, (layerIndexDepth a i + 2)) := by
              simp_rw [← one_div_pow]
              rw [Finset.prod_pow_eq_pow_sum]
        _ = (1 / (2 : ℝ)) ^ (n + 2 * d) := by rw [hsum']
        _ = 1 / (2 : ℝ) ^ (n + 2 * d) := by rw [one_div_pow]

end BrownianSharp
