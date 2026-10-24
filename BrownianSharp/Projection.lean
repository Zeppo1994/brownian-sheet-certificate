import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import BrownianSharp.BrownianCubeSpan
import BrownianSharp.BrownianCriticalProjection
import BrownianSharp.LayerIndex

/-!
Audit scaffold for the native Brownian-sheet Haar projection.

This module builds the actual dyadic tensor Haar vectors as finite
combinations of anchored-box indicators, placing them in the existing
Brownian cube isonormal domain. It also records the generic finite projection
algebra. Orthonormality, the tent coefficient factorization, and Gaussian
residual independence remain separate obligations in `work/projection.md`.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace BrownianSharp

open HaarQuarter

/-- The finite orthogonal projection associated with a finite orthonormal
family.  For the candidate Brownian layer, the family is indexed by dyadic
rectangles whose coordinate depths sum to `n`. -/
noncomputable def finiteOrthonormalProjection
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι] (e : ι → H) (x : H) : H :=
  ∑ i, ⟪x, e i⟫ • e i

/-- The formal coefficient vector for a finite native Gaussian layer.  The
function is kept separate from the random variables so that the projection
identity can be developed before the Brownian isonormal bridge is in place. -/
def nativeCoefficientVector (ι : Type*) := ι → ℝ

/-- The three anchored endpoints in the expansion
`1_[a,m) - 1_[m,b) = 2 1_[0,m) - 1_[0,a) - 1_[0,b)`.
The half-open endpoint convention is immaterial in `L²`. -/
def haarCorner (a m b : ℝ) (k : Fin 3) : ℝ :=
  if k.val = 0 then a else if k.val = 1 then m else b

/-- Coefficients of the anchored-box expansion of a univariate Haar step. -/
def haarCornerWeight (k : Fin 3) : ℝ :=
  if k.val = 1 then 2 else -1

/-- Endpoints of the dyadic interval indexed by depth `r` and cell `j`. -/
noncomputable def dyadicHaarLeft (r j : ℕ) : ℝ := (j : ℝ) / (2 : ℝ) ^ r

noncomputable def dyadicHaarRight (r j : ℕ) : ℝ := ((j + 1 : ℕ) : ℝ) / (2 : ℝ) ^ r

noncomputable def dyadicHaarMid (r j : ℕ) : ℝ :=
  (dyadicHaarLeft r j + dyadicHaarRight r j) / 2

private theorem dyadicHaarLeft_eq_realDyadicLeft (r j : ℕ) :
    dyadicHaarLeft r j = realDyadicLeft r j := rfl

private theorem dyadicHaarRight_eq_realDyadicRight (r j : ℕ) :
    dyadicHaarRight r j = realDyadicRight r j := by
  simp [dyadicHaarRight, realDyadicRight]

private theorem dyadicHaarMid_eq_realDyadicMid (r j : ℕ) :
    dyadicHaarMid r j = realDyadicMid r j := by
  simp [dyadicHaarMid, dyadicHaarLeft_eq_realDyadicLeft,
    dyadicHaarRight_eq_realDyadicRight, realDyadicLeft, realDyadicRight,
    realDyadicMid]
  ring

theorem dyadicHaar_midpoint_identity (r j : ℕ) :
    2 * dyadicHaarMid r j = dyadicHaarLeft r j + dyadicHaarRight r j := by
  unfold dyadicHaarMid
  ring

/-- A valid dyadic cell has its left endpoint, midpoint, and right endpoint in
the unit interval, in the stated order. -/
theorem dyadicHaar_endpoints_order {r j : ℕ} (hj : j < 2 ^ r) :
    0 ≤ dyadicHaarLeft r j ∧
      dyadicHaarLeft r j ≤ dyadicHaarMid r j ∧
      dyadicHaarMid r j ≤ dyadicHaarRight r j ∧
      dyadicHaarRight r j ≤ 1 := by
  have hden : 0 < (2 : ℝ) ^ r := by positivity
  have hjcast_succ : ((j + 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ r := by
    exact_mod_cast (Nat.succ_le_of_lt hj)
  have hleft_nonneg : 0 ≤ dyadicHaarLeft r j := by
    unfold dyadicHaarLeft
    positivity
  have hleft_right : dyadicHaarLeft r j ≤ dyadicHaarRight r j := by
    unfold dyadicHaarLeft dyadicHaarRight
    apply (div_le_div_iff_of_pos_right hden).2
    exact_mod_cast (Nat.le_succ j)
  have hmid_left : dyadicHaarLeft r j ≤ dyadicHaarMid r j := by
    unfold dyadicHaarMid
    linarith
  have hmid_right : dyadicHaarMid r j ≤ dyadicHaarRight r j := by
    unfold dyadicHaarMid
    linarith
  have hright_one : dyadicHaarRight r j ≤ 1 := by
    unfold dyadicHaarRight
    exact (div_le_one hden).2 hjcast_succ
  exact ⟨hleft_nonneg, hmid_left, hmid_right, hright_one⟩

/-- The three corner endpoints for a valid dyadic Haar interval stay in the
anchored unit interval. -/
theorem dyadicHaarCorner_unit {r j : ℕ} (hj : j < 2 ^ r)
    (k : Fin 3) :
    0 ≤ haarCorner (dyadicHaarLeft r j) (dyadicHaarMid r j)
        (dyadicHaarRight r j) k ∧
      haarCorner (dyadicHaarLeft r j) (dyadicHaarMid r j)
        (dyadicHaarRight r j) k ≤ 1 := by
  have h := dyadicHaar_endpoints_order hj
  have hm0 : 0 ≤ dyadicHaarMid r j := le_trans h.1 h.2.1
  have hm1 : dyadicHaarMid r j ≤ 1 := le_trans h.2.2.1 h.2.2.2
  have hb0 : 0 ≤ dyadicHaarRight r j :=
    le_trans h.1 (le_trans h.2.1 h.2.2.1)
  by_cases hk0 : k.val = 0
  · simpa [haarCorner, hk0] using
      And.intro h.1 (le_trans h.2.1 (le_trans h.2.2.1 h.2.2.2))
  · by_cases hk1 : k.val = 1
    · simpa [haarCorner, hk0, hk1] using And.intro hm0 hm1
    · have hval : k.val = 2 := by omega
      simpa [haarCorner, hk0, hk1, hval] using And.intro hb0 h.2.2.2

/-- Tensor Haar vector written as a finite linear combination of anchored
Brownian-sheet box indicators. This explicit representation is the key
geometric input needed to place native Haar coordinates in the sheet's
isonormal domain. -/
noncomputable def nativeTensorHaarVector {d : ℕ}
    (a m b : Fin d → ℝ) :
    Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
  classical
  exact ∑ k : Fin d → Fin 3,
    (∏ i, haarCornerWeight (k i)) •
      brownianSheetBoxIndicatorLp (fun i => haarCorner (a i) (m i) (b i) (k i))

/-- A native tensor Haar vector belongs to the closed span of the sheet's
anchored-box indicators. The endpoint bounds are exactly those needed to
invoke the existing Brownian cube span interface. -/
theorem nativeTensorHaarVector_mem_boxSpan {d : ℕ}
    (a m b : Fin d → ℝ)
    (hcorner : ∀ k : Fin d → Fin 3, ∀ i,
      0 ≤ haarCorner (a i) (m i) (b i) (k i) ∧
      haarCorner (a i) (m i) (b i) (k i) ≤ 1) :
    nativeTensorHaarVector a m b ∈ brownianCubeBoxSpan d := by
  classical
  unfold nativeTensorHaarVector
  apply Submodule.sum_mem
  intro k hk
  apply Submodule.smul_mem
  exact brownianCubeBoxIndicator_mem
    ⟨fun i => haarCorner (a i) (m i) (b i) (k i),
      fun i => ⟨(hcorner k i).1, (hcorner k i).2⟩⟩

/-- The dyadic tensor Haar vector at coordinate depths `r` and cell indices
`j`, written in the actual anchored-box isonormal domain. -/
noncomputable def dyadicTensorHaarVector {d : ℕ}
    (r j : Fin d → ℕ) :=
  (∏ i, Real.sqrt (2 : ℝ) ^ (r i)) •
    nativeTensorHaarVector
      (fun i => dyadicHaarLeft (r i) (j i))
      (fun i => dyadicHaarMid (r i) (j i))
      (fun i => dyadicHaarRight (r i) (j i))

/-- Every valid dyadic tensor Haar vector lies in the Brownian cube box span.
This specializes the generic corner expansion to the candidate's actual
dyadic cells. -/
theorem dyadicTensorHaarVector_mem_boxSpan {d : ℕ}
    (r j : Fin d → ℕ) (hcell : ∀ i, j i < 2 ^ (r i)) :
    dyadicTensorHaarVector r j ∈ brownianCubeBoxSpan d := by
  unfold dyadicTensorHaarVector
  apply Submodule.smul_mem
  apply nativeTensorHaarVector_mem_boxSpan
  intro k i
  exact dyadicHaarCorner_unit (hcell i) (k i)

/-- The covariance of the corner-expanded native tensor Haar vector with an
anchored box is computed from the Brownian-sheet min-product kernel. This is
the exact finite algebraic expression whose factorization gives the product
of the univariate integrated Haar tents. -/
theorem nativeTensorHaarVector_inner_box {d : ℕ}
    (a m b t : Fin d → ℝ)
    (ht : ∀ i, 0 ≤ t i)
    (hcorner : ∀ k : Fin d → Fin 3, ∀ i,
      0 ≤ haarCorner (a i) (m i) (b i) (k i) ∧
      haarCorner (a i) (m i) (b i) (k i) ≤ 1) :
    ⟪nativeTensorHaarVector a m b, brownianSheetBoxIndicatorLp t⟫ =
      ∑ k : Fin d → Fin 3,
        (∏ i, haarCornerWeight (k i)) *
          (∏ i, min (haarCorner (a i) (m i) (b i) (k i)) (t i)) := by
  classical
  simp [nativeTensorHaarVector, sum_inner, inner_smul_left,
    brownianSheetBoxIndicatorLp_inner, ht,
    fun k i => (hcorner k i).1]

/-- The ternary corner sum factors into the product of its one-coordinate
sums. -/
theorem haarCorner_sum_product {d : ℕ} (f : Fin d → Fin 3 → ℝ) :
    (∑ k : Fin d → Fin 3, ∏ i, f i (k i)) = ∏ i, ∑ k : Fin 3, f i k := by
  classical
  symm
  exact Fintype.prod_sum f

/-- In one coordinate, the three anchored corners integrate to the usual
piecewise-linear Haar tent. -/
theorem haarCorner_min_sum_eq_tent {a m b t : ℝ}
    (ham : a ≤ m) (hmb : m ≤ b) (hm : 2 * m = a + b) :
    ∑ k : Fin 3, haarCornerWeight k * min (haarCorner a m b k) t =
      if t ≤ a then 0 else if t ≤ m then t - a else if t ≤ b then b - t else 0 := by
  have hsum :
      (∑ k : Fin 3, haarCornerWeight k * min (haarCorner a m b k) t) =
        2 * min m t - min a t - min b t := by
    norm_num [haarCorner, haarCornerWeight, Fin.sum_univ_succ]
    ring
  rw [hsum]
  by_cases hta : t ≤ a
  · have hmt : t ≤ m := le_trans hta ham
    have hbt : t ≤ b := le_trans hmt hmb
    simp [hta, min_eq_right hmt, min_eq_right hbt]
    ring
  · have hat : a ≤ t := le_of_not_ge hta
    by_cases htm : t ≤ m
    · have hbt : t ≤ b := le_trans htm hmb
      simp [hta, htm, min_eq_left hat, min_eq_right hbt]
      ring
    · have hmt : m ≤ t := le_of_not_ge htm
      by_cases htb : t ≤ b
      · have hmbt : m ≤ t := hmt
        simp [hta, htm, htb, min_eq_left hat, min_eq_left hmbt]
        linarith
      · have hbt : b ≤ t := le_of_not_ge htb
        simp [hta, htm, htb, min_eq_left hat, min_eq_left hmt,
          min_eq_left hbt]
        linarith

/-- The one-dimensional cross Gram sum is the second difference of the coarse
tent at the three corners of the other Haar interval. -/
theorem haarCorner_cross_gram_eq_tent_difference
    {a m b c u v : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hm : 2 * m = a + b) :
    ∑ k : Fin 3, ∑ l : Fin 3,
      haarCornerWeight k * haarCornerWeight l *
        min (haarCorner a m b k) (haarCorner c u v l) =
      (if c ≤ a then 0 else if c ≤ m then c - a else if c ≤ b then b - c else 0) * (-1) +
      (if u ≤ a then 0 else if u ≤ m then u - a else if u ≤ b then b - u else 0) * 2 +
      (if v ≤ a then 0 else if v ≤ m then v - a else if v ≤ b then b - v else 0) * (-1) := by
  classical
  have hfirst (t : ℝ) :
      ∑ k : Fin 3, haarCornerWeight k * min (haarCorner a m b k) t =
        if t ≤ a then 0 else if t ≤ m then t - a else if t ≤ b then b - t else 0 :=
    haarCorner_min_sum_eq_tent ham hmb hm
  calc
    _ = ∑ l : Fin 3, haarCornerWeight l *
          (∑ k : Fin 3, haarCornerWeight k *
            min (haarCorner a m b k) (haarCorner c u v l)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l hl
          calc
            ∑ k : Fin 3, haarCornerWeight k * haarCornerWeight l *
                min (haarCorner a m b k) (haarCorner c u v l) =
              ∑ k : Fin 3, haarCornerWeight l *
                (haarCornerWeight k *
                  min (haarCorner a m b k) (haarCorner c u v l)) := by
                    apply Finset.sum_congr rfl
                    intro k hk
                    ring
            _ = haarCornerWeight l *
                (∑ k : Fin 3, haarCornerWeight k *
                  min (haarCorner a m b k) (haarCorner c u v l)) := by
                    rw [Finset.mul_sum]
    _ = ∑ l : Fin 3, haarCornerWeight l *
          (if haarCorner c u v l ≤ a then 0
            else if haarCorner c u v l ≤ m then haarCorner c u v l - a
            else if haarCorner c u v l ≤ b then b - haarCorner c u v l else 0) := by
          apply Finset.sum_congr rfl
          intro l hl
          rw [hfirst]
    _ = (if c ≤ a then 0 else if c ≤ m then c - a else if c ≤ b then b - c else 0) * (-1) +
        (if u ≤ a then 0 else if u ≤ m then u - a else if u ≤ b then b - u else 0) * 2 +
        (if v ≤ a then 0 else if v ≤ m then v - a else if v ≤ b then b - v else 0) * (-1) := by
          norm_num [haarCorner, haarCornerWeight, Fin.sum_univ_succ]
          simp only [neg_ite, neg_zero, neg_sub, neg_neg]
          ring_nf

/-- A finer Haar interval contained in the left half of a coarser interval is
orthogonal to the coarser Haar interval. -/
theorem haarCorner_cross_gram_zero_leftHalf
    {a m b c u v : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hm : 2 * m = a + b) (hac : a ≤ c) (hcu : c ≤ u)
    (huv : u ≤ v) (hvm : v ≤ m) (hu : 2 * u = c + v) :
    ∑ k : Fin 3, ∑ l : Fin 3,
      haarCornerWeight k * haarCornerWeight l *
        min (haarCorner a m b k) (haarCorner c u v l) = 0 := by
  rw [haarCorner_cross_gram_eq_tent_difference ham hmb hm]
  have hc0 : (if c ≤ a then 0 else if c ≤ m then c - a else if c ≤ b then b - c else 0) = c - a := by
    by_cases hca : c ≤ a
    · simp [hca]
      linarith
    · simp [hca, le_trans hcu (le_trans huv hvm)]
  have hu0 : (if u ≤ a then 0 else if u ≤ m then u - a else if u ≤ b then b - u else 0) = u - a := by
    by_cases hua : u ≤ a
    · simp [hua]
      linarith
    · simp [hua, le_trans huv hvm]
  have hv0 : (if v ≤ a then 0 else if v ≤ m then v - a else if v ≤ b then b - v else 0) = v - a := by
    by_cases hva : v ≤ a
    · simp [hva]
      linarith
    · simp [hva, hvm]
  rw [hc0, hu0, hv0]
  nlinarith [hu]

/-- The corresponding right-half nesting case. -/
theorem haarCorner_cross_gram_zero_rightHalf
    {a m b c u v : ℝ} (ham : a < m) (hmb : m < b)
    (hm : 2 * m = a + b) (hmv : m ≤ c) (hcu : c ≤ u)
    (huv : u ≤ v) (hvb : v ≤ b) (hu : 2 * u = c + v) :
    ∑ k : Fin 3, ∑ l : Fin 3,
      haarCornerWeight k * haarCornerWeight l *
        min (haarCorner a m b k) (haarCorner c u v l) = 0 := by
  rw [haarCorner_cross_gram_eq_tent_difference ham.le hmb.le hm]
  have hac : a < c := lt_of_lt_of_le ham hmv
  have hau : a < u := lt_of_lt_of_le hac hcu
  have hav : a < v := lt_of_lt_of_le hau huv
  have hcb : c ≤ b := le_trans hcu (le_trans huv hvb)
  have hub : u ≤ b := le_trans huv hvb
  have hc0 : (if c ≤ a then 0 else if c ≤ m then c - a else if c ≤ b then b - c else 0) = b - c := by
    by_cases hcm : c ≤ m
    · have hceq : c = m := le_antisymm hcm hmv
      simp [not_le_of_gt hac, hcm]
      rw [hceq]
      linarith
    · simp [not_le_of_gt hac, hcm, hcb]
  have hu0 : (if u ≤ a then 0 else if u ≤ m then u - a else if u ≤ b then b - u else 0) = b - u := by
    have hmu : m ≤ u := le_trans hmv hcu
    by_cases hum : u ≤ m
    · have hueq : u = m := le_antisymm hum hmu
      simp [not_le_of_gt hau, hum]
      rw [hueq]
      linarith
    · simp [not_le_of_gt hau, hum, hub]
  have hv0 : (if v ≤ a then 0 else if v ≤ m then v - a else if v ≤ b then b - v else 0) = b - v := by
    have hmv' : m ≤ v := le_trans hmv (le_trans hcu huv)
    by_cases hvm : v ≤ m
    · have hveq : v = m := le_antisymm hvm hmv'
      simp [not_le_of_gt hav, hvm]
      rw [hveq]
      linarith
    · simp [not_le_of_gt hav, hvm, hvb]
  rw [hc0, hu0, hv0]
  nlinarith [hu]

/-- Disjoint intervals with the second to the right have zero Haar Gram
entry, by the tent second-difference formula. -/
theorem haarCorner_cross_gram_zero_rightSeparated
    {a m b c u v : ℝ} (ham : a < m) (hmb : m < b)
    (hm : 2 * m = a + b) (hbc : b ≤ c) (hcu : c ≤ u)
    (huv : u ≤ v) :
    ∑ k : Fin 3, ∑ l : Fin 3,
      haarCornerWeight k * haarCornerWeight l *
        min (haarCorner a m b k) (haarCorner c u v l) = 0 := by
  rw [haarCorner_cross_gram_eq_tent_difference ham.le hmb.le hm]
  have hac : a < c := lt_of_lt_of_le (lt_trans ham hmb) hbc
  have hmc : m < c := lt_of_lt_of_le hmb hbc
  have hca0 : (if c ≤ a then 0 else if c ≤ m then c - a else if c ≤ b then b - c else 0) = 0 := by
    by_cases hcb : c ≤ b
    · have hceq : c = b := le_antisymm hcb hbc
      simp only [if_neg (not_le_of_gt hac), if_neg (not_le_of_gt hmc), if_pos hcb]
      rw [hceq]
      ring
    · simp only [if_neg (not_le_of_gt hac), if_neg (not_le_of_gt hmc), if_neg hcb]
  have hua : a < u := lt_of_lt_of_le hac hcu
  have hmu : m < u := lt_of_lt_of_le hmc hcu
  have hub : b ≤ u := le_trans hbc hcu
  have hu0 : (if u ≤ a then 0 else if u ≤ m then u - a else if u ≤ b then b - u else 0) = 0 := by
    by_cases hub' : u ≤ b
    · have hueq : u = b := le_antisymm hub' hub
      simp only [if_neg (not_le_of_gt hua), if_neg (not_le_of_gt hmu), if_pos hub']
      rw [hueq]
      ring
    · simp only [if_neg (not_le_of_gt hua), if_neg (not_le_of_gt hmu), if_neg hub']
  have hva : a < v := lt_of_lt_of_le hua huv
  have hmv : m < v := lt_of_lt_of_le hmu huv
  have hvb : b ≤ v := le_trans hub huv
  have hv0 : (if v ≤ a then 0 else if v ≤ m then v - a else if v ≤ b then b - v else 0) = 0 := by
    by_cases hvb' : v ≤ b
    · have hveq : v = b := le_antisymm hvb' hvb
      simp only [if_neg (not_le_of_gt hva), if_neg (not_le_of_gt hmv), if_pos hvb']
      rw [hveq]
      ring
    · simp only [if_neg (not_le_of_gt hva), if_neg (not_le_of_gt hmv), if_neg hvb']
  rw [hca0, hu0, hv0]
  ring

/-- Disjoint intervals with the second to the left have zero Haar Gram
entry. -/
theorem haarCorner_cross_gram_zero_leftSeparated
    {a m b c u v : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (hm : 2 * m = a + b) (vca : v ≤ a) (hcu : c ≤ u)
    (huv : u ≤ v) :
    ∑ k : Fin 3, ∑ l : Fin 3,
      haarCornerWeight k * haarCornerWeight l *
        min (haarCorner a m b k) (haarCorner c u v l) = 0 := by
  rw [haarCorner_cross_gram_eq_tent_difference ham hmb hm]
  have hca : c ≤ a := le_trans hcu (le_trans huv vca)
  have hua : u ≤ a := le_trans huv vca
  have hva : v ≤ a := vca
  simp [hca, hua, hva]

/-- The one-dimensional corner Gram sum vanishes for two valid dyadic cells
at different depths. The case split is the exact half-open dyadic nesting
geometry, reused from the production Haar interval development. -/
theorem dyadicHaar_cross_gram_zero_of_depth_ne {r s c d : ℕ}
    (hrs : r < s) (hc : c < 2 ^ r) (hd : d < 2 ^ s) :
    ∑ k : Fin 3, ∑ l : Fin 3,
      haarCornerWeight k * haarCornerWeight l *
        min (haarCorner (dyadicHaarLeft r c) (dyadicHaarMid r c)
          (dyadicHaarRight r c) k)
          (haarCorner (dyadicHaarLeft s d) (dyadicHaarMid s d)
            (dyadicHaarRight s d) l) = 0 := by
  have hcoarse := dyadicHaar_endpoints_order hc
  have hfine := dyadicHaar_endpoints_order hd
  have hpos := critical_fine_cell_position (r := r) (s := s) (c := c) (d := d) hrs
  have hcoarseLR : dyadicHaarLeft r c < dyadicHaarRight r c := by
    dsimp [dyadicHaarLeft, dyadicHaarRight]
    have hp : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
    apply (div_lt_div_iff_of_pos_right hp).2
    exact_mod_cast Nat.lt_succ_self c
  have hcoarse₁ : dyadicHaarLeft r c < dyadicHaarMid r c := by
    linarith [dyadicHaar_midpoint_identity r c]
  have hcoarse₂ : dyadicHaarMid r c < dyadicHaarRight r c := by
    linarith [dyadicHaar_midpoint_identity r c]
  rcases hpos with hbefore | hleft | hright | hafter
  · apply haarCorner_cross_gram_zero_leftSeparated
        hcoarse.2.1 hcoarse.2.2.1 (dyadicHaar_midpoint_identity r c)
        ?_ hfine.2.1 hfine.2.2.1
    · simpa only [dyadicHaarLeft_eq_realDyadicLeft,
        dyadicHaarMid_eq_realDyadicMid, dyadicHaarRight_eq_realDyadicRight]
        using hbefore
  · obtain ⟨ha, hv⟩ := hleft
    apply haarCorner_cross_gram_zero_leftHalf
        hcoarse.2.1 hcoarse.2.2.1 (dyadicHaar_midpoint_identity r c)
        ?_ hfine.2.1 hfine.2.2.1 ?_ (dyadicHaar_midpoint_identity s d)
    · simpa only [dyadicHaarLeft_eq_realDyadicLeft] using ha
    · simpa only [dyadicHaarRight_eq_realDyadicRight,
        dyadicHaarMid_eq_realDyadicMid] using hv
  · obtain ⟨hm, hv⟩ := hright
    apply haarCorner_cross_gram_zero_rightHalf hcoarse₁ hcoarse₂
        (dyadicHaar_midpoint_identity r c) ?_ hfine.2.1 hfine.2.2.1 ?_
        (dyadicHaar_midpoint_identity s d)
    · simpa only [dyadicHaarMid_eq_realDyadicMid,
        dyadicHaarLeft_eq_realDyadicLeft] using hm
    · simpa only [dyadicHaarRight_eq_realDyadicRight] using hv
  · apply haarCorner_cross_gram_zero_rightSeparated
        hcoarse₁ hcoarse₂ (dyadicHaar_midpoint_identity r c)
        ?_ hfine.2.1 hfine.2.2.1
    · simpa only [dyadicHaarRight_eq_realDyadicRight,
        dyadicHaarLeft_eq_realDyadicLeft] using hafter

/-- Distinct cells at the same depth have disjoint supports, hence zero
one-dimensional corner Gram entry. -/
theorem dyadicHaar_cross_gram_zero_of_cell_ne {r c d : ℕ}
    (hcd : c ≠ d) (hc : c < 2 ^ r) (hd : d < 2 ^ r) :
    ∑ k : Fin 3, ∑ l : Fin 3,
      haarCornerWeight k * haarCornerWeight l *
        min (haarCorner (dyadicHaarLeft r c) (dyadicHaarMid r c)
          (dyadicHaarRight r c) k)
          (haarCorner (dyadicHaarLeft r d) (dyadicHaarMid r d)
            (dyadicHaarRight r d) l) = 0 := by
  rcases lt_or_gt_of_ne hcd with hcd | hdc
  · have hsep := critical_right_le_left_of_lt (r := r) hcd
    have hleft := dyadicHaar_endpoints_order hc
    have hright := dyadicHaar_endpoints_order hd
    apply haarCorner_cross_gram_zero_rightSeparated
      ?_ ?_ (dyadicHaar_midpoint_identity r c) ?_
      hright.2.1 hright.2.2.1
    · have hwidth : dyadicHaarLeft r c < dyadicHaarRight r c := by
        dsimp [dyadicHaarLeft, dyadicHaarRight]
        have hp : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
        apply (div_lt_div_iff_of_pos_right hp).2
        exact_mod_cast Nat.lt_succ_self c
      linarith [dyadicHaar_midpoint_identity r c]
    · have hwidth : dyadicHaarLeft r c < dyadicHaarRight r c := by
        dsimp [dyadicHaarLeft, dyadicHaarRight]
        have hp : (0 : ℝ) < (2 : ℝ) ^ r := by positivity
        apply (div_lt_div_iff_of_pos_right hp).2
        exact_mod_cast Nat.lt_succ_self c
      linarith [dyadicHaar_midpoint_identity r c]
    · simpa only [dyadicHaarRight_eq_realDyadicRight,
        dyadicHaarLeft_eq_realDyadicLeft] using hsep
  · have hsep := critical_right_le_left_of_lt (r := r) hdc
    have hleft := dyadicHaar_endpoints_order hc
    have hright := dyadicHaar_endpoints_order hd
    apply haarCorner_cross_gram_zero_leftSeparated
      hleft.2.1 hleft.2.2.1 (dyadicHaar_midpoint_identity r c) ?_
      hright.2.1 hright.2.2.1
    simpa only [dyadicHaarRight_eq_realDyadicRight,
      dyadicHaarLeft_eq_realDyadicLeft] using hsep

/-- The native tensor coefficient expansion is the product of the univariate
integrated Haar tents. -/
theorem nativeTensorHaarVector_inner_box_eq_product_tent {d : ℕ}
    (a m b t : Fin d → ℝ)
    (ht : ∀ i, 0 ≤ t i)
    (hcorner : ∀ k : Fin d → Fin 3, ∀ i,
      0 ≤ haarCorner (a i) (m i) (b i) (k i) ∧
      haarCorner (a i) (m i) (b i) (k i) ≤ 1)
    (ham : ∀ i, a i ≤ m i) (hmb : ∀ i, m i ≤ b i)
    (hm : ∀ i, 2 * m i = a i + b i) :
    ⟪nativeTensorHaarVector a m b, brownianSheetBoxIndicatorLp t⟫ =
      ∏ i, (if t i ≤ a i then 0 else if t i ≤ m i then t i - a i
        else if t i ≤ b i then b i - t i else 0) := by
  rw [nativeTensorHaarVector_inner_box a m b t ht hcorner]
  calc
    (∑ k : Fin d → Fin 3,
        (∏ i, haarCornerWeight (k i)) *
          (∏ i, min (haarCorner (a i) (m i) (b i) (k i)) (t i))) =
      ∏ i, ∑ k : Fin 3,
        haarCornerWeight k * min (haarCorner (a i) (m i) (b i) k) (t i) := by
          calc
            _ = ∑ k : Fin d → Fin 3, ∏ i,
                haarCornerWeight (k i) *
                  min (haarCorner (a i) (m i) (b i) (k i)) (t i) := by
                  apply Finset.sum_congr rfl
                  intro k hk
                  rw [← Finset.prod_mul_distrib]
            _ = _ := by
              exact haarCorner_sum_product (fun i k =>
                haarCornerWeight k *
                  min (haarCorner (a i) (m i) (b i) k) (t i))
    _ = ∏ i, (if t i ≤ a i then 0 else if t i ≤ m i then t i - a i
          else if t i ≤ b i then b i - t i else 0) := by
          apply Finset.prod_congr rfl
          intro i hi
          exact haarCorner_min_sum_eq_tent (ham i) (hmb i) (hm i)

/-- The normalized dyadic tensor Haar vector has the proposed product tent
coefficient against every Brownian-sheet anchored-box indicator. -/
theorem dyadicTensorHaarVector_inner_box_eq_product_tent {d : ℕ}
    (r j : Fin d → ℕ) (t : Fin d → ℝ)
    (hcell : ∀ i, j i < 2 ^ (r i)) (ht : ∀ i, 0 ≤ t i) :
    ⟪dyadicTensorHaarVector r j, brownianSheetBoxIndicatorLp t⟫ =
      (∏ i, Real.sqrt (2 : ℝ) ^ (r i)) *
        ∏ i, (if t i ≤ dyadicHaarLeft (r i) (j i) then 0
          else if t i ≤ dyadicHaarMid (r i) (j i) then
            t i - dyadicHaarLeft (r i) (j i)
          else if t i ≤ dyadicHaarRight (r i) (j i) then
            dyadicHaarRight (r i) (j i) - t i else 0) := by
  unfold dyadicTensorHaarVector
  rw [inner_smul_left]
  congr 1
  apply nativeTensorHaarVector_inner_box_eq_product_tent
  · exact ht
  · intro k i
    exact dyadicHaarCorner_unit (hcell i) (k i)
  · intro i
    exact (dyadicHaar_endpoints_order (hcell i)).2.1
  · intro i
    exact (dyadicHaar_endpoints_order (hcell i)).2.2.1
  · intro i
    exact dyadicHaar_midpoint_identity (r i) (j i)

/-- Product of two finite corner sums factors coordinatewise. -/
theorem haarCorner_double_sum_product {d : ℕ}
    (f : Fin d → Fin 3 → Fin 3 → ℝ) :
    (∑ k : Fin d → Fin 3, ∑ l : Fin d → Fin 3, ∏ i, f i (k i) (l i)) =
      ∏ i, ∑ k : Fin 3, ∑ l : Fin 3, f i k l := by
  classical
  symm
  rw [Fintype.prod_sum]
  congr 1
  funext k
  exact Fintype.prod_sum (fun i => f i (k i))

/-- The unnormalized one-dimensional Haar step has squared L² norm equal to
its interval length. The formula is evaluated through the exact anchored-box
min-kernel expansion. -/
theorem haarCorner_self_gram {a m b : ℝ}
    (ham : a ≤ m) (hmb : m ≤ b) :
    ∑ k : Fin 3, ∑ l : Fin 3,
      haarCornerWeight k * haarCornerWeight l *
        min (haarCorner a m b k) (haarCorner a m b l) = b - a := by
  have hab : a ≤ b := le_trans ham hmb
  norm_num [haarCorner, haarCornerWeight, Fin.sum_univ_succ,
    min_eq_left ham, min_eq_right ham, min_eq_left hmb, min_eq_right hmb,
    min_eq_left hab, min_eq_right hab]
  linarith

/-- A valid dyadic cell's unnormalized corner Gram is its interval length. -/
theorem dyadicHaar_self_gram {r j : ℕ} (hj : j < 2 ^ r) :
    ∑ k : Fin 3, ∑ l : Fin 3,
      haarCornerWeight k * haarCornerWeight l *
        min (haarCorner (dyadicHaarLeft r j) (dyadicHaarMid r j)
          (dyadicHaarRight r j) k)
          (haarCorner (dyadicHaarLeft r j) (dyadicHaarMid r j)
            (dyadicHaarRight r j) l) =
      dyadicHaarRight r j - dyadicHaarLeft r j := by
  exact haarCorner_self_gram
    (dyadicHaar_endpoints_order hj).2.1
    (dyadicHaar_endpoints_order hj).2.2.1

private theorem dyadicHaar_cornerGram_symm {r s j k : ℕ} :
    (∑ a : Fin 3, ∑ b : Fin 3,
      haarCornerWeight a * haarCornerWeight b *
        min (haarCorner (dyadicHaarLeft r j) (dyadicHaarMid r j)
          (dyadicHaarRight r j) a)
          (haarCorner (dyadicHaarLeft s k) (dyadicHaarMid s k)
            (dyadicHaarRight s k) b)) =
    ∑ b : Fin 3, ∑ a : Fin 3,
      haarCornerWeight b * haarCornerWeight a *
        min (haarCorner (dyadicHaarLeft s k) (dyadicHaarMid s k)
          (dyadicHaarRight s k) b)
          (haarCorner (dyadicHaarLeft r j) (dyadicHaarMid r j)
            (dyadicHaarRight r j) a) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  rw [min_comm]
  ring

/-- Complete one-dimensional Gram formula for the unnormalized dyadic Haar
steps. Equal cells have their interval length; all distinct dyadic cells are
orthogonal, including across different depths. -/
theorem dyadicHaar_cornerGram {r s j k : ℕ}
    (hj : j < 2 ^ r) (hk : k < 2 ^ s) :
    ∑ a : Fin 3, ∑ b : Fin 3,
      haarCornerWeight a * haarCornerWeight b *
        min (haarCorner (dyadicHaarLeft r j) (dyadicHaarMid r j)
          (dyadicHaarRight r j) a)
          (haarCorner (dyadicHaarLeft s k) (dyadicHaarMid s k)
            (dyadicHaarRight s k) b) =
      if r = s ∧ j = k then
        dyadicHaarRight r j - dyadicHaarLeft r j else 0 := by
  by_cases hrs : r < s
  · rw [if_neg (by omega : ¬(r = s ∧ j = k))]
    exact dyadicHaar_cross_gram_zero_of_depth_ne hrs hj hk
  · by_cases hsr : s < r
    · rw [if_neg (by omega : ¬(r = s ∧ j = k))]
      rw [dyadicHaar_cornerGram_symm]
      exact dyadicHaar_cross_gram_zero_of_depth_ne hsr hk hj
    · have hrs' : r = s := by omega
      subst s
      by_cases hjk : j = k
      · subst k
        have hsame : r = r ∧ j = j := ⟨rfl, rfl⟩
        rw [if_pos hsame]
        exact dyadicHaar_self_gram hj
      · rw [if_neg (by simp [hjk])]
        exact dyadicHaar_cross_gram_zero_of_cell_ne hjk hj hk

/-- The normalization used in a one-dimensional native Haar vector turns its
raw cell-length Gram into the Kronecker delta. -/
theorem dyadicHaar_normalized_gram {r s j k : ℕ}
    (hj : j < 2 ^ r) (hk : k < 2 ^ s) :
    (Real.sqrt (2 : ℝ) ^ r) * (Real.sqrt (2 : ℝ) ^ s) *
      (∑ a : Fin 3, ∑ b : Fin 3,
        haarCornerWeight a * haarCornerWeight b *
          min (haarCorner (dyadicHaarLeft r j) (dyadicHaarMid r j)
            (dyadicHaarRight r j) a)
            (haarCorner (dyadicHaarLeft s k) (dyadicHaarMid s k)
              (dyadicHaarRight s k) b)) =
      if r = s ∧ j = k then 1 else 0 := by
  rw [dyadicHaar_cornerGram hj hk]
  by_cases hsame : r = s ∧ j = k
  · rcases hsame with ⟨rfl, rfl⟩
    rw [if_pos ⟨rfl, rfl⟩]
    have hlength : dyadicHaarRight r j - dyadicHaarLeft r j =
        1 / (2 : ℝ) ^ r := by
      dsimp [dyadicHaarRight, dyadicHaarLeft]
      field_simp
      push_cast
      ring
    have hscale : (Real.sqrt (2 : ℝ) ^ r) *
        (Real.sqrt (2 : ℝ) ^ r) = (2 : ℝ) ^ r := by
      rw [← mul_pow, Real.mul_self_sqrt (by positivity)]
    rw [hlength, hscale]
    field_simp
    simp
  · rw [if_neg hsame, if_neg hsame]
    ring

/-- Inner product of two corner-expanded tensor Haar vectors reduces exactly
to a finite product of one-dimensional corner Gram sums. -/
theorem nativeTensorHaarVector_inner {d : ℕ}
    (a m b c u v : Fin d → ℝ)
    (hcorner₁ : ∀ k : Fin d → Fin 3, ∀ i,
      0 ≤ haarCorner (a i) (m i) (b i) (k i) ∧
      haarCorner (a i) (m i) (b i) (k i) ≤ 1)
    (hcorner₂ : ∀ k : Fin d → Fin 3, ∀ i,
      0 ≤ haarCorner (c i) (u i) (v i) (k i) ∧
      haarCorner (c i) (u i) (v i) (k i) ≤ 1) :
    ⟪nativeTensorHaarVector a m b, nativeTensorHaarVector c u v⟫ =
      ∏ i, ∑ k : Fin 3, ∑ l : Fin 3,
        haarCornerWeight k * haarCornerWeight l *
          min (haarCorner (a i) (m i) (b i) k)
            (haarCorner (c i) (u i) (v i) l) := by
  classical
  calc
    ⟪nativeTensorHaarVector a m b, nativeTensorHaarVector c u v⟫ =
        ∑ l : Fin d → Fin 3, ∑ k : Fin d → Fin 3,
          (∏ i, haarCornerWeight (k i)) *
            (∏ i, haarCornerWeight (l i)) *
              (∏ i, min (haarCorner (a i) (m i) (b i) (k i))
                (haarCorner (c i) (u i) (v i) (l i))) := by
          simp [nativeTensorHaarVector, sum_inner, inner_sum, inner_smul_left,
            inner_smul_right, brownianSheetBoxIndicatorLp_inner,
            fun k i => (hcorner₁ k i).1,
            fun k i => (hcorner₂ k i).1]
          apply Finset.sum_congr rfl
          intro l hl
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = ∑ l : Fin d → Fin 3, ∑ k : Fin d → Fin 3, ∏ i,
          haarCornerWeight (k i) * haarCornerWeight (l i) *
            min (haarCorner (a i) (m i) (b i) (k i))
              (haarCorner (c i) (u i) (v i) (l i)) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ k : Fin 3, ∑ l : Fin 3,
          haarCornerWeight k * haarCornerWeight l *
            min (haarCorner (a i) (m i) (b i) k)
              (haarCorner (c i) (u i) (v i) l) := by
          rw [Finset.sum_comm]
          exact haarCorner_double_sum_product (fun i k l =>
            haarCornerWeight k * haarCornerWeight l *
              min (haarCorner (a i) (m i) (b i) k)
                (haarCorner (c i) (u i) (v i) l))

/-- Inner products of normalized native tensor Haar vectors factor into the
one-dimensional Kronecker Gram entries. -/
theorem dyadicTensorHaarVector_inner {d : ℕ}
    (r s j k : Fin d → ℕ)
    (hr : ∀ i, j i < 2 ^ (r i)) (hs : ∀ i, k i < 2 ^ (s i)) :
    ⟪dyadicTensorHaarVector r j, dyadicTensorHaarVector s k⟫ =
      ∏ i, if r i = s i ∧ j i = k i then 1 else 0 := by
  have h₁ : ∀ k' : Fin d → Fin 3, ∀ i,
      0 ≤ haarCorner (dyadicHaarLeft (r i) (j i))
        (dyadicHaarMid (r i) (j i)) (dyadicHaarRight (r i) (j i)) (k' i) ∧
      haarCorner (dyadicHaarLeft (r i) (j i))
        (dyadicHaarMid (r i) (j i)) (dyadicHaarRight (r i) (j i)) (k' i) ≤ 1 := by
    intro k' i
    exact dyadicHaarCorner_unit (hr i) (k' i)
  have h₂ : ∀ k' : Fin d → Fin 3, ∀ i,
      0 ≤ haarCorner (dyadicHaarLeft (s i) (k i))
        (dyadicHaarMid (s i) (k i)) (dyadicHaarRight (s i) (k i)) (k' i) ∧
      haarCorner (dyadicHaarLeft (s i) (k i))
        (dyadicHaarMid (s i) (k i)) (dyadicHaarRight (s i) (k i)) (k' i) ≤ 1 := by
    intro k' i
    exact dyadicHaarCorner_unit (hs i) (k' i)
  unfold dyadicTensorHaarVector
  rw [inner_smul_left, inner_smul_right]
  rw [nativeTensorHaarVector_inner _ _ _ _ _ _ h₁ h₂]
  change (∏ i, Real.sqrt (2 : ℝ) ^ r i) *
      ((∏ i, Real.sqrt (2 : ℝ) ^ s i) *
        ∏ i, ∑ a : Fin 3, ∑ b : Fin 3,
          haarCornerWeight a * haarCornerWeight b *
            min (haarCorner (dyadicHaarLeft (r i) (j i))
                (dyadicHaarMid (r i) (j i))
                (dyadicHaarRight (r i) (j i)) a)
              (haarCorner (dyadicHaarLeft (s i) (k i))
                (dyadicHaarMid (s i) (k i))
                (dyadicHaarRight (s i) (k i)) b)) =
    ∏ i, if r i = s i ∧ j i = k i then 1 else 0
  calc
      (∏ i, Real.sqrt (2 : ℝ) ^ r i) *
          ((∏ i, Real.sqrt (2 : ℝ) ^ s i) *
            ∏ i, ∑ a : Fin 3, ∑ b : Fin 3,
              haarCornerWeight a * haarCornerWeight b *
                min (haarCorner (dyadicHaarLeft (r i) (j i))
                    (dyadicHaarMid (r i) (j i))
                    (dyadicHaarRight (r i) (j i)) a)
                  (haarCorner (dyadicHaarLeft (s i) (k i))
                    (dyadicHaarMid (s i) (k i))
                    (dyadicHaarRight (s i) (k i)) b)) =
        ((∏ i, Real.sqrt (2 : ℝ) ^ r i) *
          (∏ i, Real.sqrt (2 : ℝ) ^ s i)) *
            (∏ i, ∑ a : Fin 3, ∑ b : Fin 3,
              haarCornerWeight a * haarCornerWeight b *
                min (haarCorner (dyadicHaarLeft (r i) (j i))
                    (dyadicHaarMid (r i) (j i))
                    (dyadicHaarRight (r i) (j i)) a)
                  (haarCorner (dyadicHaarLeft (s i) (k i))
                    (dyadicHaarMid (s i) (k i))
                    (dyadicHaarRight (s i) (k i)) b)) := by ring
      _ = ∏ i,
          (Real.sqrt (2 : ℝ) ^ r i) * (Real.sqrt (2 : ℝ) ^ s i) *
            (∑ a : Fin 3, ∑ b : Fin 3,
              haarCornerWeight a * haarCornerWeight b *
                min (haarCorner
                    (dyadicHaarLeft (r i) (j i))
                    (dyadicHaarMid (r i) (j i))
                    (dyadicHaarRight (r i) (j i)) a)
                  (haarCorner
                    (dyadicHaarLeft (s i) (k i))
                    (dyadicHaarMid (s i) (k i))
                    (dyadicHaarRight (s i) (k i)) b)) := by
              rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      _ = ∏ i, if r i = s i ∧ j i = k i then 1 else 0 := by
            apply Finset.prod_congr rfl
            intro i hi
            exact dyadicHaar_normalized_gram (hr i) (hs i)

/-- The actual native tensor Haar vectors indexed by a level layer form an
orthonormal family in the Brownian-sheet integrand Hilbert space. -/
theorem nativeLayer_orthonormal {d n : ℕ} :
    ∀ a b : LayerIndex d n,
      ⟪dyadicTensorHaarVector (layerIndexDepth a) (layerIndexCell a),
        dyadicTensorHaarVector (layerIndexDepth b) (layerIndexCell b)⟫ =
        if a = b then 1 else 0 := by
  classical
  intro a b
  rw [dyadicTensorHaarVector_inner (layerIndexDepth a) (layerIndexDepth b)
    (layerIndexCell a) (layerIndexCell b)
    (layerIndexCell_lt a) (layerIndexCell_lt b)]
  by_cases hab : a = b
  · subst b
    simp
  · rw [if_neg hab]
    have hcoord : ∃ i : Fin d,
        layerIndexDepth a i ≠ layerIndexDepth b i ∨
          layerIndexCell a i ≠ layerIndexCell b i := by
      by_contra h
      push_neg at h
      apply hab
      rcases a with ⟨⟨ar, har⟩, ac⟩
      rcases b with ⟨⟨br, hbr⟩, bc⟩
      have hdepth : ar = br := by
        apply Finsupp.ext
        intro i
        exact h i |>.1
      have hshape : (⟨ar, har⟩ : Shape d n) = ⟨br, hbr⟩ := by
        apply Subtype.ext
        exact hdepth
      subst br
      have hcell : ac = bc := by
        funext i
        apply Fin.ext
        exact h i |>.2
      subst bc
      rfl
    obtain ⟨i, hi⟩ := hcoord
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    by_cases hri : layerIndexDepth a i = layerIndexDepth b i
    · have hri' : ¬layerIndexDepth a i ≠ layerIndexDepth b i := by
        intro hne
        exact hne hri
      simp [hri, hi.resolve_left hri']
    · simp [hri]

/-- The same native layer family, now packaged directly in the existing
closed Brownian cube box span. -/
noncomputable def nativeLayerVector {d n : ℕ} (a : LayerIndex d n) :
    brownianCubeBoxSpan d :=
  ⟨dyadicTensorHaarVector (layerIndexDepth a) (layerIndexCell a),
    dyadicTensorHaarVector_mem_boxSpan (layerIndexDepth a)
      (layerIndexCell a) (layerIndexCell_lt a)⟩

/-- The packaged native family remains orthonormal in the inherited span
inner product, ready to instantiate the original-sheet projection theorem. -/
theorem nativeLayerVector_orthonormal {d n : ℕ} (a b : LayerIndex d n) :
    ⟪nativeLayerVector a, nativeLayerVector b⟫ = if a = b then 1 else 0 := by
  exact nativeLayer_orthonormal a b

/-- The native finite layer is the sum of its Haar coordinates against the
corresponding tensor Haar vectors. -/
noncomputable def nativeFiniteLayer
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι] (e : ι → H) (g : nativeCoefficientVector ι) : H :=
  ∑ i, g i • e i

/-- If the tensor Haar vectors form an orthonormal family, their finite
projection has exactly the Haar coefficients and is orthogonal to every
selected coordinate after subtraction. -/
theorem finiteProjection_residual_orthogonal
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι] [DecidableEq ι] (e : ι → H) (x : H)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0) (j : ι) :
    ⟪x - finiteOrthonormalProjection e x, e j⟫ = 0 := by
  classical
  simp [finiteOrthonormalProjection, inner_sub_left, sum_inner, inner_smul_left,
    he]

/-- The coefficient of a projected vector along a selected Haar coordinate is
the original coordinate. -/
theorem finiteProjection_coefficient
    {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [Fintype ι] [DecidableEq ι] (e : ι → H) (x : H)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0) (j : ι) :
    ⟪finiteOrthonormalProjection e x, e j⟫ = ⟪x, e j⟫ := by
  have h := finiteProjection_residual_orthogonal e x he j
  rw [inner_sub_left] at h
  linarith

end BrownianSharp
