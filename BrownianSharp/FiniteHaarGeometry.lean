import BrownianSharp.NativeRow

/-!
Finite father/mother tensor Haar coordinates on a common dyadic grid. Unlike
`LayerIndex`, this family includes the father in every coordinate, so it spans
the entire depth-`N` step space rather than only the all-mother sector.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace BrownianSharp
open HaarQuarter

/-- One coordinate of the finite depth-`N` Haar basis: `none` is the father,
and `some (r,j)` is the mother Haar function at depth `r` and cell `j`. -/
abbrev FiniteHaarAxis (N : ℕ) := Option (Σ r : Fin N, Fin (2 ^ r.val))

/-- A tensor father/mother index on `d` coordinates. -/
abbrev FiniteHaarIndex (d N : ℕ) := Fin d → FiniteHaarAxis N

/-- The shifted grade: the father has grade zero and a depth-`r` mother has
grade `r+1`. -/
def finiteHaarAxisGrade {N : ℕ} : FiniteHaarAxis N → ℕ
  | none => 0
  | some ⟨r, _⟩ => r.val + 1

/-- Total shifted grade of a tensor Haar index. -/
def finiteHaarGrade {d N : ℕ} (a : FiniteHaarIndex d N) : ℕ :=
  ∑ i : Fin d, finiteHaarAxisGrade (a i)

/-- The three anchored-box endpoints used for one coordinate of a mixed Haar
vector. Father coordinates use the full interval `[0,1]`. -/
noncomputable def finiteHaarEndpoint {N : ℕ} (a : FiniteHaarAxis N)
    (k : Fin 3) : ℝ :=
  match a with
  | none => 1
  | some ⟨r, j⟩ =>
      haarCorner (dyadicHaarLeft r.val j.val) (dyadicHaarMid r.val j.val)
        (dyadicHaarRight r.val j.val) k

/-- Corner weights for a father (a single full-interval corner) or a mother
(the standard `-1,2,-1` anchored-box expansion). -/
def finiteHaarCornerWeight {N : ℕ} (a : FiniteHaarAxis N) (k : Fin 3) : ℝ :=
  match a with
  | none => if k.val = 0 then 1 else 0
  | some _ => haarCornerWeight k

/-- L² normalization of a one-coordinate finite Haar vector. -/
noncomputable def finiteHaarAxisScale {N : ℕ} (a : FiniteHaarAxis N) : ℝ :=
  match a with
  | none => 1
  | some ⟨r, _⟩ => Real.sqrt 2 ^ r.val

/-- The mixed father/mother tensor Haar function, expanded directly as a
finite linear combination of the original anchored-box generators. -/
noncomputable def finiteHaarVectorAmbient {d N : ℕ} (a : FiniteHaarIndex d N) :
    Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
  (∏ i : Fin d, finiteHaarAxisScale (a i)) •
    ∑ k : Fin d → Fin 3,
      (∏ i : Fin d, finiteHaarCornerWeight (a i) (k i)) •
        brownianSheetBoxIndicatorLp (fun i => finiteHaarEndpoint (a i) (k i))

private theorem finiteHaarEndpoint_mem_unit {N : ℕ} (a : FiniteHaarAxis N)
    (k : Fin 3) : 0 ≤ finiteHaarEndpoint a k ∧ finiteHaarEndpoint a k ≤ 1 := by
  cases a with
  | none => simp [finiteHaarEndpoint]
  | some a =>
      exact dyadicHaarCorner_unit a.2.isLt k

/-- The actual mixed tensor Haar function belongs to the Brownian cube box
span; each corner term is one of the original anchored-box vectors. -/
noncomputable def finiteHaarVector {d N : ℕ} (a : FiniteHaarIndex d N) :
    brownianCubeBoxSpan d := by
  refine ⟨finiteHaarVectorAmbient a, ?_⟩
  unfold finiteHaarVectorAmbient
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  exact brownianCubeBoxIndicator_mem ⟨
    (fun i => finiteHaarEndpoint (a i) (k i)),
    fun i => finiteHaarEndpoint_mem_unit (a i) (k i)⟩

/-- Mixed-Haar coefficient against an anchored box, with the father factor
`t` and mother factor equal to the normalized integrated Haar tent. -/
theorem finiteHaarVector_inner_box {d N : ℕ} (a : FiniteHaarIndex d N)
    (t : Fin d → ℝ) (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    ⟪finiteHaarVector a,
      (⟨brownianSheetBoxIndicatorLp t, brownianCubeBoxIndicator_mem ⟨t, fun i => ⟨(ht i).1, (ht i).2⟩⟩⟩ :
        brownianCubeBoxSpan d)⟫ =
      (∏ i : Fin d, finiteHaarAxisScale (a i)) *
        ∏ i : Fin d,
          ∑ k : Fin 3, finiteHaarCornerWeight (a i) k *
            min (finiteHaarEndpoint (a i) k) (t i) := by
  classical
  change ⟪finiteHaarVectorAmbient a, brownianSheetBoxIndicatorLp t⟫ = _
  calc
    ⟪finiteHaarVectorAmbient a, brownianSheetBoxIndicatorLp t⟫ =
        (∏ i : Fin d, finiteHaarAxisScale (a i)) *
          ∑ k : Fin d → Fin 3,
            (∏ i : Fin d, finiteHaarCornerWeight (a i) (k i)) *
              ∏ i : Fin d, min (finiteHaarEndpoint (a i) (k i)) (t i) := by
        rw [finiteHaarVectorAmbient]
        simp only [inner_smul_left, sum_inner, inner_smul_left, starRingEnd_apply, star_trivial]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [brownianSheetBoxIndicatorLp_inner _ _
          (fun i => (finiteHaarEndpoint_mem_unit (a i) (k i)).1)
          (fun i => (ht i).1)]
    _ = (∏ i : Fin d, finiteHaarAxisScale (a i)) *
        ∑ k : Fin d → Fin 3,
          ∏ i : Fin d,
            finiteHaarCornerWeight (a i) (k i) *
              min (finiteHaarEndpoint (a i) (k i)) (t i) := by
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        rw [← Finset.prod_mul_distrib]
    _ = (∏ i : Fin d, finiteHaarAxisScale (a i)) *
        ∏ i : Fin d,
          ∑ k : Fin 3, finiteHaarCornerWeight (a i) k *
            min (finiteHaarEndpoint (a i) k) (t i) := by
        rw [Fintype.prod_sum]


/-- The one-coordinate integrated feature of a father or normalized mother. -/
theorem finiteHaarAxisIntegratedFeature {N : ℕ} (a : FiniteHaarAxis N)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    finiteHaarAxisScale a *
      (∑ k : Fin 3, finiteHaarCornerWeight a k *
        min (finiteHaarEndpoint a k) t) =
      match a with
      | none => t
      | some ⟨r, j⟩ => Real.sqrt 2 ^ r.val * dyadicHaarTentAt r.val j.val t := by
  cases a with
  | none =>
      simp only [finiteHaarAxisScale, finiteHaarCornerWeight, finiteHaarEndpoint]
      norm_num [Fin.sum_univ_succ]
      exact ht1
  | some a =>
      rcases a with ⟨r, j⟩
      have hj : j.val < 2 ^ r.val := j.isLt
      have ho := dyadicHaar_endpoints_order hj
      have hm := dyadicHaar_midpoint_identity r.val j.val
      have htent := haarCorner_min_sum_eq_tent (t := t) ho.2.1 ho.2.2.1 hm
      simp only [finiteHaarAxisScale, finiteHaarCornerWeight, finiteHaarEndpoint]
      rw [htent]
      rfl

theorem finiteHaarVector_inner_box_eq_product_feature {d N : ℕ}
    (a : FiniteHaarIndex d N) (t : Fin d → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    ⟪finiteHaarVector a,
      (⟨brownianSheetBoxIndicatorLp t,
        brownianCubeBoxIndicator_mem ⟨t, fun i => ⟨(ht i).1, (ht i).2⟩⟩⟩ :
        brownianCubeBoxSpan d)⟫ =
      ∏ i : Fin d,
        (match a i with
        | none => t i
        | some ⟨r, j⟩ => Real.sqrt 2 ^ r.val *
            dyadicHaarTentAt r.val j.val (t i)) := by
  rw [finiteHaarVector_inner_box a t ht]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact finiteHaarAxisIntegratedFeature (a i) (t i) (ht i).1 (ht i).2

/-- At one fixed dyadic depth, every normalized integrated mother feature has
square at most `2^(-(r+2))`, uniformly over the endpoint location. -/
theorem finiteHaarMotherFeature_sq_le {r j : ℕ} (hj : j < 2 ^ r) (t : ℝ) :
    (Real.sqrt 2 ^ r * dyadicHaarTentAt r j t) ^ 2 ≤
      1 / (2 : ℝ) ^ (r + 2) := by
  have hlen : dyadicHaarRight r j - dyadicHaarLeft r j =
      1 / (2 : ℝ) ^ r := by
    dsimp [dyadicHaarRight, dyadicHaarLeft]
    field_simp
    push_cast
    ring
  have ht := dyadicHaarTentAt_bounds t hj
  have htent : dyadicHaarTentAt r j t ≤ 1 / (2 * (2 : ℝ) ^ r) := by
    calc
      dyadicHaarTentAt r j t ≤
          (dyadicHaarRight r j - dyadicHaarLeft r j) / 2 := ht.2
      _ = 1 / (2 * (2 : ℝ) ^ r) := by rw [hlen]; ring
  have htentSq : (dyadicHaarTentAt r j t) ^ 2 ≤
      (1 / (2 * (2 : ℝ) ^ r)) ^ 2 := by
    nlinarith [ht.1, htent]
  have hsqrt : (Real.sqrt 2 ^ r) ^ 2 = (2 : ℝ) ^ r := by
    calc
      (Real.sqrt 2 ^ r) ^ 2 = Real.sqrt 2 ^ (r * 2) := by rw [← pow_mul]
      _ = Real.sqrt 2 ^ (2 * r) := by rw [Nat.mul_comm r 2]
      _ = (Real.sqrt 2 ^ 2) ^ r := by rw [pow_mul]
      _ = (2 : ℝ) ^ r := by rw [Real.sq_sqrt (by norm_num)]
  calc
    (Real.sqrt 2 ^ r * dyadicHaarTentAt r j t) ^ 2 =
        (2 : ℝ) ^ r * (dyadicHaarTentAt r j t) ^ 2 := by
          rw [mul_pow, hsqrt]
    _ ≤ (2 : ℝ) ^ r * (1 / (2 * (2 : ℝ) ^ r)) ^ 2 := by
          gcongr
    _ = 1 / (2 : ℝ) ^ (r + 2) := by
          field_simp
          ring

theorem finiteHaarAxisFeature_sq_le {N : ℕ} (a : FiniteHaarAxis N)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (match a with
      | none => t
      | some ⟨r, j⟩ => Real.sqrt 2 ^ r.val * dyadicHaarTentAt r.val j.val t) ^ 2 ≤
        1 / (2 : ℝ) ^ finiteHaarAxisGrade a := by
  cases a with
  | none =>
      simp only [finiteHaarAxisGrade]
      nlinarith [sq_nonneg t, ht0, ht1]
  | some a =>
      rcases a with ⟨r, j⟩
      have hstrong := finiteHaarMotherFeature_sq_le j.isLt t
      have hpow : (2 : ℝ) ^ (r.val + 1) ≤ (2 : ℝ) ^ (r.val + 2) := by
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hden : 1 / (2 : ℝ) ^ (r.val + 2) ≤
          1 / (2 : ℝ) ^ (r.val + 1) := by
        exact one_div_le_one_div_of_le (by positivity) hpow
      exact le_trans hstrong (by simpa [finiteHaarAxisGrade] using hden)

/-- Every mixed tensor box coefficient has squared size at most the inverse
power of two indexed by its total shifted grade. -/
theorem finiteHaarVector_box_inner_sq_le {d N : ℕ}
    (a : FiniteHaarIndex d N) (t : Fin d → ℝ)
    (ht : ∀ i, 0 ≤ t i ∧ t i ≤ 1) :
    ⟪finiteHaarVector a,
      (⟨brownianSheetBoxIndicatorLp t,
        brownianCubeBoxIndicator_mem ⟨t, fun i => ⟨(ht i).1, (ht i).2⟩⟩⟩ :
        brownianCubeBoxSpan d)⟫ ^ 2 ≤
      1 / (2 : ℝ) ^ finiteHaarGrade a := by
  rw [finiteHaarVector_inner_box_eq_product_feature a t ht]
  rw [← Finset.prod_pow]
  calc
    ∏ i : Fin d,
        (match a i with
        | none => t i
        | some ⟨r, j⟩ => Real.sqrt 2 ^ r.val *
            dyadicHaarTentAt r.val j.val (t i)) ^ 2 ≤
      ∏ i : Fin d, 1 / (2 : ℝ) ^ finiteHaarAxisGrade (a i) := by
        apply Finset.prod_le_prod₀
        · intro i hi
          positivity
        · intro i hi
          exact finiteHaarAxisFeature_sq_le (a i) (t i) (ht i).1 (ht i).2
    _ = 1 / (2 : ℝ) ^ finiteHaarGrade a := by
          rw [finiteHaarGrade]
          simp only [one_div]
          rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum]

noncomputable def finiteHaarAxisRawGram {N : ℕ} (a b : FiniteHaarAxis N) : ℝ :=
  ∑ k : Fin 3, ∑ l : Fin 3,
    finiteHaarCornerWeight a k * finiteHaarCornerWeight b l *
      min (finiteHaarEndpoint a k) (finiteHaarEndpoint b l)

theorem finiteHaarVector_inner {d N : ℕ} (a b : FiniteHaarIndex d N) :
    ⟪finiteHaarVector a, finiteHaarVector b⟫ =
      (∏ i : Fin d, finiteHaarAxisScale (a i)) *
        (∏ i : Fin d, finiteHaarAxisScale (b i)) *
          ∏ i : Fin d, finiteHaarAxisRawGram (a i) (b i) := by
  classical
  change ⟪finiteHaarVectorAmbient a, finiteHaarVectorAmbient b⟫ = _
  have hbox : ∀ k l : Fin d → Fin 3,
      ⟪brownianSheetBoxIndicatorLp (fun i => finiteHaarEndpoint (a i) (k i)),
        brownianSheetBoxIndicatorLp (fun i => finiteHaarEndpoint (b i) (l i))⟫ =
        ∏ i : Fin d, min (finiteHaarEndpoint (a i) (k i))
          (finiteHaarEndpoint (b i) (l i)) := by
    intro k l
    exact brownianSheetBoxIndicatorLp_inner _ _
      (fun i => (finiteHaarEndpoint_mem_unit (a i) (k i)).1)
      (fun i => (finiteHaarEndpoint_mem_unit (b i) (l i)).1)
  calc
    ⟪finiteHaarVectorAmbient a, finiteHaarVectorAmbient b⟫ =
        (∏ i : Fin d, finiteHaarAxisScale (a i)) *
          (∏ i : Fin d, finiteHaarAxisScale (b i)) *
            ∑ k : Fin d → Fin 3, ∑ l : Fin d → Fin 3,
              (∏ i : Fin d, finiteHaarCornerWeight (a i) (k i)) *
                (∏ i : Fin d, finiteHaarCornerWeight (b i) (l i)) *
                  ∏ i : Fin d, min (finiteHaarEndpoint (a i) (k i))
                    (finiteHaarEndpoint (b i) (l i)) := by
        simp [finiteHaarVectorAmbient, sum_inner, inner_sum, inner_smul_left,
          inner_smul_right, hbox, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k hk
        apply Finset.sum_congr rfl
        intro l hl
        simp_rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i hi
        ring
    _ = (∏ i : Fin d, finiteHaarAxisScale (a i)) *
          (∏ i : Fin d, finiteHaarAxisScale (b i)) *
            ∏ i : Fin d, finiteHaarAxisRawGram (a i) (b i) := by
        have hsum :
            ∑ k : Fin d → Fin 3, ∑ l : Fin d → Fin 3,
              (∏ i : Fin d, finiteHaarCornerWeight (a i) (k i)) *
                (∏ i : Fin d, finiteHaarCornerWeight (b i) (l i)) *
                  ∏ i : Fin d, min (finiteHaarEndpoint (a i) (k i))
                    (finiteHaarEndpoint (b i) (l i)) =
            ∑ k : Fin d → Fin 3, ∑ l : Fin d → Fin 3,
              ∏ i : Fin d,
                finiteHaarCornerWeight (a i) (k i) * finiteHaarCornerWeight (b i) (l i) *
                  min (finiteHaarEndpoint (a i) (k i)) (finiteHaarEndpoint (b i) (l i)) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        rw [hsum]
        rw [haarCorner_double_sum_product (fun i k l =>
          finiteHaarCornerWeight (a i) k * finiteHaarCornerWeight (b i) l *
            min (finiteHaarEndpoint (a i) k) (finiteHaarEndpoint (b i) l))]
        simp [finiteHaarAxisRawGram]

private theorem finiteHaarMother_total_at_one {r j : ℕ} (hj : j < 2 ^ r) :
    ∑ k : Fin 3, haarCornerWeight k *
      min (haarCorner (dyadicHaarLeft r j) (dyadicHaarMid r j)
        (dyadicHaarRight r j) k) 1 = 0 := by
  have ho := dyadicHaar_endpoints_order hj
  have hden : 0 < (2 : ℝ) ^ r := by positivity
  have hlr : dyadicHaarLeft r j < dyadicHaarRight r j := by
    unfold dyadicHaarLeft dyadicHaarRight
    apply (div_lt_div_iff_of_pos_right hden).2
    exact_mod_cast Nat.lt_succ_self j
  have hleft : dyadicHaarLeft r j < 1 := lt_of_lt_of_le hlr ho.2.2.2
  have hmidright : dyadicHaarMid r j < dyadicHaarRight r j := by
    have hm := dyadicHaar_midpoint_identity r j
    linarith
  have hmid : dyadicHaarMid r j < 1 :=
    lt_of_lt_of_le hmidright ho.2.2.2
  rw [haarCorner_min_sum_eq_tent ho.2.1 ho.2.2.1
    (dyadicHaar_midpoint_identity r j)]
  by_cases hright : dyadicHaarRight r j = 1
  · simp [not_le_of_gt hleft, not_le_of_gt hmid, hright]
  · have hright' : dyadicHaarRight r j < 1 := lt_of_le_of_ne ho.2.2.2 hright
    simp [not_le_of_gt hleft, not_le_of_gt hmid, not_le_of_gt hright']

theorem finiteHaarAxis_normalizedGram {N : ℕ} (a b : FiniteHaarAxis N) :
    finiteHaarAxisScale a * finiteHaarAxisScale b * finiteHaarAxisRawGram a b =
      if a = b then 1 else 0 := by
  cases a with
  | none =>
    cases b with
    | none => simp [finiteHaarAxisRawGram, finiteHaarAxisScale,
        finiteHaarCornerWeight, finiteHaarEndpoint, Fin.sum_univ_succ]
    | some b =>
        rcases b with ⟨r, j⟩
        have hj : j.val < 2 ^ r.val := j.isLt
        have hzero := finiteHaarMother_total_at_one hj
        have hzero' : ∑ l : Fin 3, haarCornerWeight l *
            min 1 (haarCorner (dyadicHaarLeft r.val j.val)
              (dyadicHaarMid r.val j.val) (dyadicHaarRight r.val j.val) l) = 0 := by
          simpa only [min_comm] using hzero
        have hraw : finiteHaarAxisRawGram none (some ⟨r, j⟩) = 0 := by
          simp [finiteHaarAxisRawGram, finiteHaarCornerWeight,
            finiteHaarEndpoint, hzero']
        rw [hraw]
        simp [finiteHaarAxisScale]
  | some a =>
    rcases a with ⟨r, j⟩
    cases b with
    | none =>
        have hj : j.val < 2 ^ r.val := j.isLt
        have hzero := finiteHaarMother_total_at_one hj
        have hzero' : ∑ k : Fin 3, haarCornerWeight k *
            min (haarCorner (dyadicHaarLeft r.val j.val)
              (dyadicHaarMid r.val j.val) (dyadicHaarRight r.val j.val) k) 1 = 0 := hzero
        rw [if_neg]
        · have hraw : finiteHaarAxisRawGram (some ⟨r, j⟩) none = 0 := by
            simp [finiteHaarAxisRawGram, finiteHaarCornerWeight,
              finiteHaarEndpoint, hzero']
          rw [hraw]
          simp [finiteHaarAxisScale]
        · intro h
          cases h
    | some b =>
        rcases b with ⟨s, k⟩
        have h := dyadicHaar_normalized_gram j.isLt k.isLt
        have heq : (some ⟨r, j⟩ : FiniteHaarAxis N) = some ⟨s, k⟩ ↔
            r.val = s.val ∧ j.val = k.val := by
          constructor
          · intro he
            cases he
            exact ⟨rfl, rfl⟩
          · rintro ⟨hrs, hjk⟩
            have hr : r = s := Fin.ext hrs
            subst s
            have hj : j = k := Fin.ext hjk
            subst k
            rfl
        simpa only [finiteHaarAxisRawGram, finiteHaarAxisScale,
          finiteHaarCornerWeight, finiteHaarEndpoint, heq] using h

/-- The complete depth-`N` tensor father/mother family is orthonormal. -/
theorem finiteHaarVector_orthonormal {d N : ℕ} (a b : FiniteHaarIndex d N) :
    ⟪finiteHaarVector a, finiteHaarVector b⟫ = if a = b then 1 else 0 := by
  rw [finiteHaarVector_inner]
  calc
    (∏ i : Fin d, finiteHaarAxisScale (a i)) *
        (∏ i : Fin d, finiteHaarAxisScale (b i)) *
          ∏ i : Fin d, finiteHaarAxisRawGram (a i) (b i) =
      ∏ i : Fin d,
        finiteHaarAxisScale (a i) * finiteHaarAxisScale (b i) *
          finiteHaarAxisRawGram (a i) (b i) := by
            simp_rw [← Finset.prod_mul_distrib]
    _ = ∏ i : Fin d, if a i = b i then 1 else 0 := by
          apply Finset.prod_congr rfl
          intro i hi
          exact finiteHaarAxis_normalizedGram (a i) (b i)
    _ = if a = b then 1 else 0 := by
          by_cases hab : a = b
          · subst b
            simp
          · rw [if_neg hab]
            have hcoord : ∃ i : Fin d, a i ≠ b i := by
              by_contra h
              push_neg at h
              apply hab
              funext i
              exact h i
            obtain ⟨i, hi⟩ := hcoord
            apply Finset.prod_eq_zero (Finset.mem_univ i)
            simp [hi]

end BrownianSharp
