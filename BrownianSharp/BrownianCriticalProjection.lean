import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import BrownianSharp.IntegratedHaarTent
import BrownianSharp.DiscrepancyHaarCoefficient

/-! Finite four-cell algebra for the one-axis critical projection used in the
Brownian-sheet residual construction. The coordinates are exact cell means:
the statements below isolate the normalization and projection arithmetic;
they do not assert the still-separate continuous cell-averaging / sheet
representation bridge. -/

open scoped BigOperators
open MeasureTheory

namespace HaarQuarter

private theorem criticalIntegral_Ioc_id_sub {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, (x - a) ∂volume = (b - a) ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun x : ℝ => (x - a) ^ 2 / 2) (f' := fun x => x - a) hab
    (by fun_prop)
    (fun x hx => by
      have h := (hasDerivAt_pow 2 (x - a)).div_const (2 : ℝ) |>.comp x
        ((hasDerivAt_id x).sub_const a)
      simpa [Function.comp_def] using h)
    ((continuousOn_id.sub continuousOn_const).intervalIntegrable)]
  ring

private theorem criticalIntegral_Ioc_sub_id {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, (b - x) ∂volume = (b - a) ^ 2 / 2 := by
  rw [← intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun x : ℝ => -((b - x) ^ 2) / 2) (f' := fun x => b - x) hab
    (by fun_prop)
    (fun x hx => by
      have h := (hasDerivAt_pow 2 (b - x)).neg.div_const (2 : ℝ) |>.comp x
        ((hasDerivAt_const x b).sub (hasDerivAt_id x))
      convert h using 1
      · funext y
        simp
      · ring)
    ((continuousOn_const.sub continuousOn_id).intervalIntegrable)]
  ring

/-- The area under a midpoint integrated-Haar tent. -/
theorem integratedHaarTent_integral {a b : ℝ} (hab : a < b) :
    ∫ x, integratedHaarTent a ((a + b) / 2) b x ∂volume = (b - a) ^ 2 / 4 := by
  let m : ℝ := (a + b) / 2
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  have hleft : Integrable
      ((Set.Ioc a m).indicator (fun x : ℝ => x - a)) volume := by
    have hp : IntegrableOn (fun x : ℝ => x - a) (Set.Ioc a m) volume :=
      (continuousOn_id.sub continuousOn_const).integrableOn_compact
        isCompact_Icc |>.mono_set Set.Ioc_subset_Icc_self
    exact hp.integrable_indicator measurableSet_Ioc
  have hright : Integrable
      ((Set.Ioc m b).indicator (fun x : ℝ => b - x)) volume := by
    have hp : IntegrableOn (fun x : ℝ => b - x) (Set.Ioc m b) volume :=
      (continuousOn_const.sub continuousOn_id).integrableOn_compact
        isCompact_Icc |>.mono_set Set.Ioc_subset_Icc_self
    exact hp.integrable_indicator measurableSet_Ioc
  change ∫ x, integratedHaarTent a m b x ∂volume = _
  calc
    ∫ x, integratedHaarTent a m b x ∂volume =
        ∫ x, (Set.Ioc a m).indicator (fun y => y - a) x +
          (Set.Ioc m b).indicator (fun y => b - y) x ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (by intro x; rfl)
    _ = _ := by
      rw [integral_add hleft hright, integral_indicator measurableSet_Ioc,
        integral_indicator measurableSet_Ioc, criticalIntegral_Ioc_id_sub ham,
        criticalIntegral_Ioc_sub_id hmb]
      dsimp [m]
      ring

theorem criticalIntegratedHaarTent_integrable (a m b : ℝ) :
    Integrable (fun x => integratedHaarTent a m b x) volume := by
  unfold integratedHaarTent
  apply Integrable.add
  · have hp : IntegrableOn (fun x : ℝ => x - a) (Set.Ioc a m) volume :=
      (continuousOn_id.sub continuousOn_const).integrableOn_compact isCompact_Icc
        |>.mono_set Set.Ioc_subset_Icc_self
    exact hp.integrable_indicator measurableSet_Ioc
  · have hp : IntegrableOn (fun x : ℝ => b - x) (Set.Ioc m b) volume :=
      (continuousOn_const.sub continuousOn_id).integrableOn_compact isCompact_Icc
        |>.mono_set Set.Ioc_subset_Icc_self
    exact hp.integrable_indicator measurableSet_Ioc

/-- Signed primitive on a dyadic parent interval: negative integrated tent on
the left half and positive integrated tent on the right half, normalized by
`sqrt(|I|)`. -/
noncomputable def criticalDyadicSignedPrimitive (r c : ℕ) (x : ℝ) : ℝ :=
  let a := realDyadicLeft r c
  let b := realDyadicRight r c
  let m := (a + b) / 2
  (integratedHaarTent m ((m + b) / 2) b x -
    integratedHaarTent a ((a + m) / 2) m x) / Real.sqrt (b - a)

/-- The signed critical primitive has mean zero, since its two half-tents
have equal area. -/
theorem criticalDyadicSignedPrimitive_integral_zero (r c : ℕ) :
    ∫ x, criticalDyadicSignedPrimitive r c x ∂volume = 0 := by
  let a := realDyadicLeft r c
  let b := realDyadicRight r c
  let m := (a + b) / 2
  let L := b - a
  have hab : a < b := by
    dsimp [a, b, realDyadicLeft, realDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  have hmid : realDyadicMid r c = m := by
    dsimp [realDyadicMid, realDyadicLeft, realDyadicRight, a, b, m]
    field_simp
    ring
  have hareaL : ∫ x, integratedHaarTent a ((a + m) / 2) m x ∂volume =
      (m - a) ^ 2 / 4 := integratedHaarTent_integral ham
  have hareaR : ∫ x, integratedHaarTent m ((m + b) / 2) b x ∂volume =
      (b - m) ^ 2 / 4 := integratedHaarTent_integral hmb
  have hleft : Integrable (fun x => integratedHaarTent a ((a + m) / 2) m x) volume :=
    criticalIntegratedHaarTent_integrable a ((a + m) / 2) m
  have hright : Integrable (fun x => integratedHaarTent m ((m + b) / 2) b x) volume :=
    criticalIntegratedHaarTent_integrable m ((m + b) / 2) b
  have hdiff : Integrable (fun x => integratedHaarTent m ((m + b) / 2) b x -
      integratedHaarTent a ((a + m) / 2) m x) volume := hright.sub hleft
  have hareas : (b - m) ^ 2 / 4 - (m - a) ^ 2 / 4 = 0 := by
    rw [show m = (a + b) / 2 by rfl]
    ring
  change ∫ x, (integratedHaarTent m ((m + b) / 2) b x -
      integratedHaarTent a ((a + m) / 2) m x) / Real.sqrt L ∂volume = 0
  rw [integral_div, integral_sub hright hleft, hareaR, hareaL, hareas]
  simp

/-- The signed tent sum obtained when the negative-left, positive-right
primitive is paired with the manuscript's parent Haar signs. -/
noncomputable def criticalDyadicPrimitiveHaarProduct (r c : ℕ) (x : ℝ) : ℝ :=
  let a := realDyadicLeft r c
  let b := realDyadicRight r c
  let m := (a + b) / 2
  (integratedHaarTent a ((a + m) / 2) m x +
    integratedHaarTent m ((m + b) / 2) b x) / Real.sqrt (b - a)

/-- Pointwise sign multiplication: the signed primitive times the integration-
friendly parent Haar is exactly the sum of its two positive half-tents. -/
theorem criticalDyadicSignedPrimitive_mul_iocHaar (r c : ℕ) (x : ℝ) :
    criticalDyadicSignedPrimitive r c x * discrepancyIocDyadicHaar r c x =
      criticalDyadicPrimitiveHaarProduct r c x := by
  let a := realDyadicLeft r c
  let b := realDyadicRight r c
  let m := (a + b) / 2
  have hab : a < b := by
    dsimp [a, b, realDyadicLeft, realDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmid : realDyadicMid r c = m := by
    dsimp [m, a, b, realDyadicMid, realDyadicLeft, realDyadicRight]
    field_simp
    ring
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  have hml : a < (a + m) / 2 := by linarith
  have hlm : (a + m) / 2 < m := by linarith
  have hmr : m < (m + b) / 2 := by linarith
  have hrb : (m + b) / 2 < b := by linarith
  have hdis : Disjoint (Set.Ioc a m) (Set.Ioc m b) :=
    Set.disjoint_left.mpr (by intro y hy₁ hy₂; exact (not_lt_of_ge hy₁.2) hy₂.1)
  by_cases hxL : x ∈ Set.Ioc a m
  · have hxR : x ∉ Set.Ioc m b := by
      intro hxR
      exact (Set.disjoint_left.mp hdis hxL hxR).elim
    have hnotR : x ∉ Set.Ioo m b := by
      intro hx
      exact hxR ⟨hx.1, hx.2.le⟩
    have htentR := integratedHaarTent_eq_zero_of_not_mem_open hmr hrb hnotR
    simp [criticalDyadicSignedPrimitive, criticalDyadicPrimitiveHaarProduct,
      discrepancyIocDyadicHaar, a, b, m, hmid, hxL, hxR, htentR]
    ring
  · by_cases hxR : x ∈ Set.Ioc m b
    · have hnotL : x ∉ Set.Ioo a m := by
        intro hx
        exact hxL ⟨hx.1, hx.2.le⟩
      have htentL := integratedHaarTent_eq_zero_of_not_mem_open hml hlm hnotL
      simp [criticalDyadicSignedPrimitive, criticalDyadicPrimitiveHaarProduct,
        discrepancyIocDyadicHaar, a, b, m, hmid, hxL, hxR, htentL]
    · have hnotL : x ∉ Set.Ioo a m := by
        intro hx
        exact hxL ⟨hx.1, hx.2.le⟩
      have hnotR : x ∉ Set.Ioo m b := by
        intro hx
        exact hxR ⟨hx.1, hx.2.le⟩
      have htentL := integratedHaarTent_eq_zero_of_not_mem_open hml hlm hnotL
      have htentR := integratedHaarTent_eq_zero_of_not_mem_open hmr hrb hnotR
      simp [criticalDyadicSignedPrimitive, criticalDyadicPrimitiveHaarProduct,
        discrepancyIocDyadicHaar, a, b, m, hmid, hxL, hxR, htentL, htentR]

theorem critical_leftHalf_eq_Ico (r c : ℕ) :
    realDyadicLeftHalf r c = Set.Ico (realDyadicLeft r c) (realDyadicMid r c) := by
  unfold realDyadicLeftHalf
  have hl : ((2 * c : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1) = realDyadicLeft r c := by
    push_cast
    simp [realDyadicLeft, pow_succ]
    ring
  have hm : ((2 * c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1) = realDyadicMid r c := by
    push_cast
    simp [realDyadicMid, pow_succ]
    ring
  rw [hl, hm]

theorem critical_rightHalf_eq_Ico (r c : ℕ) :
    realDyadicRightHalf r c = Set.Ico (realDyadicMid r c) (realDyadicRight r c) := by
  unfold realDyadicRightHalf
  have hm : ((2 * c + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1) = realDyadicMid r c := by
    push_cast
    simp [realDyadicMid, pow_succ]
    ring
  have hr : ((2 * c + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1) = realDyadicRight r c := by
    push_cast
    simp [realDyadicRight, pow_succ]
    ring
  rw [hm, hr]

/-- The endpoint convention difference between the manuscript's Ioc Haar and
the production half-open Haar is null for Lebesgue measure. -/
theorem criticalIocHaar_ae_eq_real (r c : ℕ) :
    discrepancyIocDyadicHaar r c =ᵐ[volume] realDyadicHaar r c := by
  let a := realDyadicLeft r c
  let m := realDyadicMid r c
  let b := realDyadicRight r c
  have hnull : volume ({a} ∪ {m} ∪ {b} : Set ℝ) = 0 := by
    rw [measure_union_null (measure_union_null (measure_singleton a)
      (measure_singleton m)) (measure_singleton b)]
  apply (ae_iff).2
  apply measure_mono_null (t := {a} ∪ {m} ∪ {b})
  · intro x hx
    change discrepancyIocDyadicHaar r c x ≠ realDyadicHaar r c x at hx
    by_contra hne
    have hxa : x ≠ a := by intro h; exact hne (Or.inl (Or.inl h))
    have hxm : x ≠ m := by intro h; exact hne (Or.inl (Or.inr h))
    have hxb : x ≠ b := by intro h; exact hne (Or.inr h)
    have hleft : x ∈ Set.Ico a m ↔ x ∈ Set.Ioc a m := by
      simp only [Set.mem_Ico, Set.mem_Ioc]
      constructor
      · rintro ⟨ha, hm⟩
        exact ⟨by
          by_contra hn
          exact hxa (le_antisymm ha (le_of_not_gt hn)).symm, le_of_lt hm⟩
      · rintro ⟨ha, hm⟩
        exact ⟨le_of_lt ha, by
          by_contra hn
          exact hxm (le_antisymm hm (le_of_not_gt hn))⟩
    have hright : x ∈ Set.Ico m b ↔ x ∈ Set.Ioc m b := by
      simp only [Set.mem_Ico, Set.mem_Ioc]
      constructor
      · rintro ⟨hm, hb⟩
        exact ⟨by
          by_contra hn
          exact hxm (le_antisymm (le_of_not_gt hn) hm), le_of_lt hb⟩
      · rintro ⟨hm, hb⟩
        exact ⟨le_of_lt hm, by
          by_contra hn
          exact hxb (le_antisymm hb (le_of_not_gt hn))⟩
    have hL : x ∈ realDyadicLeftHalf r c ↔ x ∈ Set.Ioc a m := by
      rw [critical_leftHalf_eq_Ico]
      exact hleft
    have hR : x ∈ realDyadicRightHalf r c ↔ x ∈ Set.Ioc m b := by
      rw [critical_rightHalf_eq_Ico]
      exact hright
    have heq : realDyadicHaar r c x = discrepancyIocDyadicHaar r c x := by
      unfold realDyadicHaar discrepancyIocDyadicHaar
      have hR' : (x ∈ realDyadicRightHalf r c) = (m < x ∧ x ≤ b) := by
        rw [hR]
        rfl
      have hL' : (x ∈ realDyadicLeftHalf r c) = (a < x ∧ x ≤ m) := by
        rw [hL]
        rfl
      simp only [Set.indicator]
      rw [hR', hL']
      rfl
    exact hx heq.symm
  · exact hnull

/-- The signed-tent product formula also holds almost everywhere for the
production half-open `realDyadicHaar`; only the three endpoints differ. -/
theorem criticalDyadicSignedPrimitive_mul_realHaar_ae (r c : ℕ) :
    (fun x => criticalDyadicSignedPrimitive r c x * realDyadicHaar r c x) =ᵐ[volume]
      criticalDyadicPrimitiveHaarProduct r c := by
  filter_upwards [criticalIocHaar_ae_eq_real r c] with x hx
  rw [← hx]
  exact criticalDyadicSignedPrimitive_mul_iocHaar r c x

/-- Exact continuous integral of the signed primitive against the parent Haar,
written after the sign multiplication as its two positive half-tents. -/
theorem criticalDyadicPrimitiveHaarProduct_integral (r c : ℕ) :
    ∫ x, criticalDyadicPrimitiveHaarProduct r c x ∂volume =
      (realDyadicRight r c - realDyadicLeft r c) *
        Real.sqrt (realDyadicRight r c - realDyadicLeft r c) / 8 := by
  let a := realDyadicLeft r c
  let b := realDyadicRight r c
  let m := (a + b) / 2
  have hab : a < b := by
    dsimp [a, b, realDyadicLeft, realDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  have hs : Real.sqrt (b - a) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr hab))
  have hmarea :
      ∫ x, integratedHaarTent a ((a + m) / 2) m x +
        integratedHaarTent m ((m + b) / 2) b x ∂volume = (b - a) ^ 2 / 8 := by
    have hareaL := integratedHaarTent_integral (a := a) (b := m) ham
    have hareaR := integratedHaarTent_integral (a := m) (b := b) hmb
    calc
      ∫ x, integratedHaarTent a ((a + m) / 2) m x +
          integratedHaarTent m ((m + b) / 2) b x ∂volume =
        (∫ x, integratedHaarTent a ((a + m) / 2) m x ∂volume) +
          ∫ x, integratedHaarTent m ((m + b) / 2) b x ∂volume :=
            integral_add (criticalIntegratedHaarTent_integrable a ((a + m) / 2) m)
              (criticalIntegratedHaarTent_integrable m ((m + b) / 2) b)
      _ = (b - a) ^ 2 / 8 := by
        rw [hareaL, hareaR]
        dsimp [m]
        ring
  have htentInt : Integrable
      (fun x => integratedHaarTent a ((a + m) / 2) m x +
        integratedHaarTent m ((m + b) / 2) b x) volume :=
    (criticalIntegratedHaarTent_integrable a ((a + m) / 2) m).add
      (criticalIntegratedHaarTent_integrable m ((m + b) / 2) b)
  change ∫ x, ((integratedHaarTent a ((a + m) / 2) m x +
      integratedHaarTent m ((m + b) / 2) b x) / Real.sqrt (b - a)) ∂volume = _
  rw [integral_div, hmarea]
  · change ((b - a) ^ 2 / 8) / Real.sqrt (b - a) =
      (b - a) * Real.sqrt (b - a) / 8
    field_simp [hs]
    have hsq : Real.sqrt (b - a) ^ 2 = b - a :=
      Real.sq_sqrt (le_of_lt (sub_pos.mpr hab))
    nlinarith [hsq]

/-- Exact Lebesgue integral of the actual signed tent primitive against the
production `realDyadicHaar` function. -/
theorem criticalDyadicSignedPrimitive_realHaar_integral (r c : ℕ) :
    ∫ x, criticalDyadicSignedPrimitive r c x * realDyadicHaar r c x ∂volume =
      (realDyadicRight r c - realDyadicLeft r c) *
        Real.sqrt (realDyadicRight r c - realDyadicLeft r c) / 8 := by
  calc
    ∫ x, criticalDyadicSignedPrimitive r c x * realDyadicHaar r c x ∂volume =
        ∫ x, criticalDyadicPrimitiveHaarProduct r c x ∂volume := by
          apply integral_congr_ae
          exact criticalDyadicSignedPrimitive_mul_realHaar_ae r c
    _ = _ := criticalDyadicPrimitiveHaarProduct_integral r c

/-- After dividing by the parent interval length, the exact projection
coefficient is `sqrt(|I|)/8`, as in the manuscript. -/
theorem criticalDyadicSignedPrimitive_realHaar_coefficient (r c : ℕ) :
    ((∫ x, criticalDyadicSignedPrimitive r c x * realDyadicHaar r c x ∂volume) /
      (realDyadicRight r c - realDyadicLeft r c)) =
        Real.sqrt (realDyadicRight r c - realDyadicLeft r c) / 8 := by
  rw [criticalDyadicSignedPrimitive_realHaar_integral]
  have hlenpos : realDyadicLeft r c < realDyadicRight r c := by
    dsimp [realDyadicRight, realDyadicLeft]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hlen : realDyadicRight r c - realDyadicLeft r c ≠ 0 :=
    (sub_pos.mpr hlenpos).ne'
  field_simp [hlen]

/-- The normalized left-child Haar minus right-child Haar pattern on the
four quarter-cells of an interval of length `L`. The unnormalized child Haar
functions have values `(-1,+1)` on their own half-intervals. -/
noncomputable def criticalFourCellE (L : ℝ) (i : Fin 4) : ℝ :=
  (if i.val = 0 then -1 else if i.val = 1 then 1 else
    if i.val = 2 then 1 else -1) / Real.sqrt L

/-- Parent Haar signs, with the manuscript convention positive on the right. -/
def criticalFourCellParentHaar (i : Fin 4) : ℝ :=
  if i.val < 2 then -1 else 1

/-- Exact averages of the signed primitive on the four quarter-cells:
negative tent on the left half and positive tent on the right half. -/
noncomputable def criticalFourCellPrimitiveMean (L : ℝ) (i : Fin 4) : ℝ :=
  (if i.val < 2 then -1 else 1) * Real.sqrt L / 8

/-- The four-cell mean-square normalization of
`e_I = (h_{I_-} - h_{I_+}) / sqrt(|I|)` is exactly one. -/
theorem criticalFourCellE_mean_square (L : ℝ) (hL : 0 < L) :
    (L / 4) * ∑ i : Fin 4, criticalFourCellE L i ^ 2 = 1 := by
  have hs : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hL)
  simp [Fin.sum_univ_succ, criticalFourCellE]
  norm_num
  field_simp [hs]
  rw [Real.sq_sqrt (le_of_lt hL)]
  ring

/-- The signed primitive's four-cell means pair with the parent Haar to give
`|I|^(3/2)/8`; dividing by `|I|` is the manuscript's `sqrt(|I|)/8`
projection coefficient. -/
theorem criticalFourCellPrimitive_parent_integral (L : ℝ) :
    (L / 4) * ∑ i : Fin 4,
        criticalFourCellPrimitiveMean L i * criticalFourCellParentHaar i =
      L * Real.sqrt L / 8 := by
  simp [Fin.sum_univ_succ, criticalFourCellPrimitiveMean,
    criticalFourCellParentHaar]
  ring

/-- For positive cell length, the coefficient normalized by the interval
length is exactly the claimed square-root scale. -/
theorem criticalFourCellPrimitive_parent_coefficient (L : ℝ) (hL : 0 < L) :
    ((L / 4) * ∑ i : Fin 4,
        criticalFourCellPrimitiveMean L i * criticalFourCellParentHaar i) / L =
      Real.sqrt L / 8 := by
  rw [criticalFourCellPrimitive_parent_integral]
  field_simp

/-- The production real Haar has absolute value one exactly on its dyadic
cell.  Half-open endpoints make this a pointwise identity. -/
private theorem critical_realDyadicHaar_sq (r c : ℕ) (x : ℝ) :
    (realDyadicHaar r c x) ^ 2 =
      (if x ∈ Set.Ico (realDyadicLeft r c) (realDyadicRight r c)
        then (1 : ℝ) else 0) := by
  classical
  let a := realDyadicLeft r c
  let m := realDyadicMid r c
  let b := realDyadicRight r c
  change (realDyadicHaar r c x) ^ 2 =
    (if x ∈ Set.Ico a b then (1 : ℝ) else 0)
  have hl : realDyadicLeftHalf r c = Set.Ico a m := by
    rw [critical_leftHalf_eq_Ico]
  have hr : realDyadicRightHalf r c = Set.Ico m b := by
    rw [critical_rightHalf_eq_Ico]
  have hab : a < b := by
    dsimp [a, b, realDyadicLeft, realDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmid : m = (a + b) / 2 := by
    dsimp [a, b, m, realDyadicMid, realDyadicLeft, realDyadicRight]
    field_simp
    ring
  have ham : a < m := by rw [hmid]; linarith
  have hmb : m < b := by rw [hmid]; linarith
  have hcell : realDyadicCell r c = Set.Ico a b := by
    simp [realDyadicCell, a, b, realDyadicLeft, realDyadicRight]
  by_cases hxL : x ∈ Set.Ico a m
  · have hxR : x ∉ Set.Ico m b := by
      intro h
      simp only [Set.mem_Ico] at hxL h
      linarith
    have hx : x ∈ realDyadicCell r c := by
      rw [hcell]
      simp only [Set.mem_Ico] at hxL
      simp only [Set.mem_Ico]
      constructor <;> linarith
    have hx' : x ∈ Set.Ico a b := by rwa [← hcell]
    simp [realDyadicHaar, hl, hr, hxL, hxR, hx']
  · by_cases hxR : x ∈ Set.Ico m b
    · have hx : x ∈ realDyadicCell r c := by
        rw [hcell]
        simp only [Set.mem_Ico] at hxR
        simp only [Set.mem_Ico]
        constructor <;> linarith
      have hx' : x ∈ Set.Ico a b := by rwa [← hcell]
      simp [realDyadicHaar, hl, hr, hxL, hxR, hx']
    · have hxL' : ¬ (a ≤ x ∧ x < m) := by simpa only [Set.mem_Ico] using hxL
      have hxR' : ¬ (m ≤ x ∧ x < b) := by simpa only [Set.mem_Ico] using hxR
      have hx' : ¬ (a ≤ x ∧ x < b) := by
        intro h
        by_cases hxm : x < m
        · exact hxL' ⟨h.1, hxm⟩
        · exact hxR' ⟨le_of_not_gt hxm, h.2⟩
      simp [realDyadicHaar, hl, hr, hxL, hxR, hx']

/-- The one-axis critical vector from Section 7, represented using the actual
production half-open Haar functions. -/
noncomputable def criticalDyadicE (r c : ℕ) (x : ℝ) : ℝ :=
  (realDyadicHaar (r + 1) (2 * c) x -
    realDyadicHaar (r + 1) (2 * c + 1) x) /
      Real.sqrt (realDyadicRight r c - realDyadicLeft r c)

private theorem critical_child_left_left (r c : ℕ) :
    realDyadicLeft (r + 1) (2 * c) = realDyadicLeft r c := by
  dsimp [realDyadicLeft]
  push_cast
  rw [pow_succ]
  field_simp

private theorem critical_child_left_right (r c : ℕ) :
    realDyadicRight (r + 1) (2 * c) = realDyadicMid r c := by
  dsimp [realDyadicRight, realDyadicMid]
  push_cast
  rw [pow_succ]
  field_simp

private theorem critical_child_right_left (r c : ℕ) :
    realDyadicLeft (r + 1) (2 * c + 1) = realDyadicMid r c := by
  dsimp [realDyadicLeft, realDyadicMid]
  push_cast
  rw [pow_succ]
  field_simp

private theorem critical_child_right_right (r c : ℕ) :
    realDyadicRight (r + 1) (2 * c + 1) = realDyadicRight r c := by
  dsimp [realDyadicRight]
  push_cast
  rw [pow_succ]
  field_simp
  ring

/-- The normalized child-Haar difference has squared value `1/|I|` on its
parent interval and zero outside. -/
theorem criticalDyadicE_sq (r c : ℕ) (x : ℝ) :
    (criticalDyadicE r c x) ^ 2 =
      if x ∈ Set.Ico (realDyadicLeft r c) (realDyadicRight r c) then
        (realDyadicRight r c - realDyadicLeft r c)⁻¹ else 0 := by
  classical
  let a := realDyadicLeft r c
  let m := realDyadicMid r c
  let b := realDyadicRight r c
  let L := b - a
  let hL := realDyadicHaar (r + 1) (2 * c) x
  let hR := realDyadicHaar (r + 1) (2 * c + 1) x
  change ((hL - hR) / Real.sqrt L) ^ 2 =
    (if x ∈ Set.Ico a b then L⁻¹ else 0)
  have hab : a < b := by
    dsimp [a, b, realDyadicLeft, realDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmid : m = (a + b) / 2 := by
    dsimp [a, b, m, realDyadicMid, realDyadicLeft, realDyadicRight]
    field_simp
    ring
  have ham : a < m := by rw [hmid]; linarith
  have hmb : m < b := by rw [hmid]; linarith
  have hll : realDyadicLeft (r + 1) (2 * c) = a := by
    rw [critical_child_left_left]
  have hlr : realDyadicRight (r + 1) (2 * c) = m := by
    rw [critical_child_left_right]
  have hrl : realDyadicLeft (r + 1) (2 * c + 1) = m := by
    rw [critical_child_right_left]
  have hrr : realDyadicRight (r + 1) (2 * c + 1) = b := by
    rw [critical_child_right_right]
  have hsqL : hL ^ 2 = if x ∈ Set.Ico a m then (1 : ℝ) else 0 := by
    change (realDyadicHaar (r + 1) (2 * c) x) ^ 2 = _
    rw [critical_realDyadicHaar_sq, hll, hlr]
  have hsqR : hR ^ 2 = if x ∈ Set.Ico m b then (1 : ℝ) else 0 := by
    change (realDyadicHaar (r + 1) (2 * c + 1) x) ^ 2 = _
    rw [critical_realDyadicHaar_sq, hrl, hrr]
  have hLpos : 0 < L := by dsimp [L, a, b]; linarith
  have hsqrt : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hLpos)
  by_cases hxL : x ∈ Set.Ico a m
  · have hxR : x ∉ Set.Ico m b := by
      intro h
      simp only [Set.mem_Ico] at hxL h
      linarith
    have hparent : x ∈ Set.Ico a b := by
      simp only [Set.mem_Ico] at hxL ⊢
      constructor <;> linarith
    have hsqL' : hL ^ 2 = 1 := by simp [hsqL, hxL]
    have hsqR' : hR ^ 2 = 0 := by simp [hsqR, hxR]
    have hRzero : hR = 0 := (sq_eq_zero_iff).1 hsqR'
    change ((hL - hR) / Real.sqrt L) ^ 2 = _
    rw [if_pos hparent]
    rw [hRzero, sub_zero]
    rw [div_pow, hsqL']
    rw [Real.sq_sqrt (le_of_lt hLpos)]
    field_simp [ne_of_gt hLpos]
  · by_cases hxR : x ∈ Set.Ico m b
    · have hparent : x ∈ Set.Ico a b := by
        simp only [Set.mem_Ico] at hxR ⊢
        constructor <;> linarith [hmid]
      have hsqL' : hL ^ 2 = 0 := by simp [hsqL, hxL]
      have hsqR' : hR ^ 2 = 1 := by simp [hsqR, hxR]
      have hLzero : hL = 0 := (sq_eq_zero_iff).1 hsqL'
      change ((hL - hR) / Real.sqrt L) ^ 2 = _
      rw [if_pos hparent]
      rw [hLzero, zero_sub, div_pow, neg_sq, hsqR']
      rw [Real.sq_sqrt (le_of_lt hLpos)]
      field_simp [ne_of_gt hLpos]
    · have hparent : x ∉ Set.Ico a b := by
        have hxL' : ¬ (a ≤ x ∧ x < m) := by simpa only [Set.mem_Ico] using hxL
        have hxR' : ¬ (m ≤ x ∧ x < b) := by simpa only [Set.mem_Ico] using hxR
        intro h
        simp only [Set.mem_Ico] at h
        by_cases hxm : x < m
        · exact hxL' ⟨h.1, hxm⟩
        · exact hxR' ⟨le_of_not_gt hxm, h.2⟩
      have hsqL' : hL ^ 2 = 0 := by simp [hsqL, hxL]
      have hsqR' : hR ^ 2 = 0 := by simp [hsqR, hxR]
      have hLzero : hL = 0 := (sq_eq_zero_iff).1 hsqL'
      have hRzero : hR = 0 := (sq_eq_zero_iff).1 hsqR'
      change ((hL - hR) / Real.sqrt L) ^ 2 = _
      rw [if_neg hparent, hLzero, hRzero, sub_self, zero_div,
        zero_pow (by norm_num : 2 ≠ 0)]

/-- The actual continuous production-Haar vector `e_I` has unit L² norm. -/
theorem criticalDyadicE_integral_sq_eq_one (r c : ℕ) :
    ∫ x, (criticalDyadicE r c x) ^ 2 ∂volume = 1 := by
  classical
  let a := realDyadicLeft r c
  let b := realDyadicRight r c
  let L := b - a
  have hab : a < b := by
    dsimp [a, b, realDyadicLeft, realDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmeas : MeasurableSet (Set.Ico a b) := measurableSet_Ico
  have hi : (∫ x, (if x ∈ Set.Ico a b then L⁻¹ else 0) ∂volume) =
      volume.real (Set.Ico a b) * L⁻¹ := by
    have h := integral_indicator_const (μ := volume) (L⁻¹) hmeas
    simpa only [Set.indicator_apply, measureReal_def, smul_eq_mul] using h
  calc
    ∫ x, (criticalDyadicE r c x) ^ 2 ∂volume =
        ∫ x, (if x ∈ Set.Ico a b then L⁻¹ else 0) ∂volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (criticalDyadicE_sq r c)
    _ = volume.real (Set.Ico a b) * L⁻¹ := hi
    _ = 1 := by
      rw [Real.volume_real_Ico_of_le hab.le]
      dsimp [L]
      field_simp [ne_of_gt (sub_pos.mpr hab)]

/-- The square of a critical vector is integrable; its exact indicator formula
reduces this to a constant on one finite dyadic interval. -/
theorem criticalDyadicE_sq_integrable (r c : ℕ) :
    Integrable (fun x => (criticalDyadicE r c x) ^ 2) volume := by
  let a := realDyadicLeft r c
  let b := realDyadicRight r c
  let L := b - a
  have hab : a < b := by
    dsimp [a, b, realDyadicLeft, realDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hs : MeasurableSet (Set.Ico a b) := measurableSet_Ico
  have hconst : IntegrableOn (fun _ : ℝ => L⁻¹) (Set.Ico a b) volume := by
    exact integrableOn_const
      (ne_of_lt (measure_Ico_lt_top (μ := volume) (a := a) (b := b)))
  have hind : Integrable (Set.indicator (Set.Ico a b) (fun _ : ℝ => L⁻¹)) volume :=
    hconst.integrable_indicator hs
  have hpoint : (fun x => (criticalDyadicE r c x) ^ 2) =
      Set.indicator (Set.Ico a b) (fun _ : ℝ => L⁻¹) := by
    funext x
    rw [criticalDyadicE_sq]
    simp [Set.indicator_apply, a, b, L]
  rw [hpoint]
  exact hind

theorem critical_right_le_left_of_lt {r c d : ℕ} (hcd : c < d) :
    realDyadicRight r c ≤ realDyadicLeft r d := by
  dsimp [realDyadicRight, realDyadicLeft]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ r)
    (by positivity : (0 : ℝ) < (2 : ℝ) ^ r)).2
  push_cast
  exact_mod_cast (Nat.mul_le_mul_right (2 ^ r) (Nat.succ_le_of_lt hcd))

private theorem critical_dyadic_left_scaled {r s c : ℕ} (hrs : r ≤ s) :
    realDyadicLeft r c =
      ((c * 2 ^ (s - r) : ℕ) : ℝ) / (2 : ℝ) ^ s := by
  have hpowN : 2 ^ r * 2 ^ (s - r) = 2 ^ s := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hrs]
  have hpow : (2 : ℝ) ^ r * (2 : ℝ) ^ (s - r) = (2 : ℝ) ^ s := by
    exact_mod_cast hpowN
  dsimp [realDyadicLeft]
  push_cast
  field_simp
  nlinarith [hpow]

private theorem critical_dyadic_right_scaled {r s c : ℕ} (hrs : r ≤ s) :
    realDyadicRight r c =
      (((c + 1) * 2 ^ (s - r) : ℕ) : ℝ) / (2 : ℝ) ^ s := by
  have hpowN : 2 ^ r * 2 ^ (s - r) = 2 ^ s := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hrs]
  have hpow : (2 : ℝ) ^ r * (2 : ℝ) ^ (s - r) = (2 : ℝ) ^ s := by
    exact_mod_cast hpowN
  dsimp [realDyadicRight]
  push_cast
  field_simp
  nlinarith [hpow]

private theorem critical_dyadic_mid_scaled {r s c : ℕ} (hrs : r < s) :
    realDyadicMid r c =
      (((2 * c + 1) * 2 ^ (s - r - 1) : ℕ) : ℝ) / (2 : ℝ) ^ s := by
  have hpowN : 2 ^ r * 2 ^ (s - r) = 2 ^ s := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hrs.le]
  have hpow : (2 : ℝ) ^ r * (2 : ℝ) ^ (s - r) = (2 : ℝ) ^ s := by
    exact_mod_cast hpowN
  have hhalf : 2 ^ (s - r) = 2 * 2 ^ (s - r - 1) := by
    have _hpos : 1 ≤ s - r := by omega
    conv_lhs => rw [show s - r = (s - r - 1) + 1 by omega]
    rw [pow_succ]
    ring
  have hhalfR : (2 : ℝ) ^ (s - r) = 2 * (2 : ℝ) ^ (s - r - 1) := by
    exact_mod_cast hhalf
  have hmid : realDyadicMid r c =
      (realDyadicLeft r c + realDyadicRight r c) / 2 := by
    dsimp [realDyadicMid, realDyadicLeft, realDyadicRight]
    field_simp
    ring
  rw [hmid, critical_dyadic_left_scaled hrs.le,
    critical_dyadic_right_scaled hrs.le]
  push_cast
  field_simp
  rw [hhalfR]
  ring

theorem critical_fine_cell_position {r s c d : ℕ} (hrs : r < s) :
    realDyadicRight s d ≤ realDyadicLeft r c ∨
      (realDyadicLeft r c ≤ realDyadicLeft s d ∧
        realDyadicRight s d ≤ realDyadicMid r c) ∨
      (realDyadicMid r c ≤ realDyadicLeft s d ∧
        realDyadicRight s d ≤ realDyadicRight r c) ∨
      realDyadicRight r c ≤ realDyadicLeft s d := by
  let A : ℕ := c * 2 ^ (s - r)
  let M : ℕ := (2 * c + 1) * 2 ^ (s - r - 1)
  let C : ℕ := (c + 1) * 2 ^ (s - r)
  have hpow : 2 ^ (s - r) = 2 * 2 ^ (s - r - 1) := by
    conv_lhs => rw [show s - r = (s - r - 1) + 1 by omega]
    rw [pow_succ]
    omega
  have hAM : M = A + 2 ^ (s - r - 1) := by
    dsimp [A, M]
    rw [hpow]
    ring
  have hMC : C = M + 2 ^ (s - r - 1) := by
    dsimp [M, C]
    rw [hpow]
    ring
  have hpos : 0 < 2 ^ (s - r - 1) := by positivity
  have hAMlt : A < M := by rw [hAM]; exact Nat.lt_add_of_pos_right hpos
  have hMClt : M < C := by rw [hMC]; exact Nat.lt_add_of_pos_right hpos
  have hcases : d + 1 ≤ A ∨ (A ≤ d ∧ d + 1 ≤ M) ∨
      (M ≤ d ∧ d + 1 ≤ C) ∨ C ≤ d := by omega
  have hden : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
  have hcmp (u v : ℕ) (huv : u ≤ v) :
      (u : ℝ) / (2 : ℝ) ^ s ≤ (v : ℝ) / (2 : ℝ) ^ s := by
    apply (div_le_div_iff₀ hden hden).2
    exact_mod_cast (Nat.mul_le_mul_right (2 ^ s) huv)
  have hleft : realDyadicLeft r c = (A : ℝ) / (2 : ℝ) ^ s := by
    simpa [A] using critical_dyadic_left_scaled (r := r) (s := s) (c := c) hrs.le
  have hmid : realDyadicMid r c = (M : ℝ) / (2 : ℝ) ^ s := by
    simpa [M] using critical_dyadic_mid_scaled (r := r) (s := s) (c := c) hrs
  have hright : realDyadicRight r c = (C : ℝ) / (2 : ℝ) ^ s := by
    simpa [C] using critical_dyadic_right_scaled (r := r) (s := s) (c := c) hrs.le
  have hfineL : realDyadicLeft s d = (d : ℝ) / (2 : ℝ) ^ s := by
    simp [realDyadicLeft]
  have hfineR : realDyadicRight s d = ((d + 1 : ℕ) : ℝ) / (2 : ℝ) ^ s := by
    simp [realDyadicRight]
  rcases hcases with hbefore | ⟨hA, hM⟩ | ⟨hM, hC⟩ | hafter
  · left
    rw [hfineR, hleft]
    exact hcmp (d + 1) A hbefore
  · right; left
    constructor
    · rw [hleft, hfineL]
      exact hcmp A d hA
    · rw [hfineR, hmid]
      exact hcmp (d + 1) M hM
  · right; right; left
    constructor
    · rw [hmid, hfineL]
      exact hcmp M d hM
    · rw [hfineR, hright]
      exact hcmp (d + 1) C hC
  · right; right; right
    rw [hright, hfineL]
    exact hcmp C d hafter

private theorem critical_realDyadicHaar_integral_zero (r c : ℕ) :
    ∫ x, realDyadicHaar r c x ∂volume = 0 := by
  classical
  let a := realDyadicLeft r c
  let m := realDyadicMid r c
  let b := realDyadicRight r c
  have hab : a < m := by
    dsimp [a, m, realDyadicLeft, realDyadicMid]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmb : m < b := by
    dsimp [m, b, realDyadicMid, realDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hL : Integrable ((Set.Ioc a m).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
    apply (integrableOn_const (ne_of_lt measure_Ioc_lt_top)).integrable_indicator
    exact measurableSet_Ioc
  have hR : Integrable ((Set.Ioc m b).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
    apply (integrableOn_const (ne_of_lt measure_Ioc_lt_top)).integrable_indicator
    exact measurableSet_Ioc
  have hareaL : ∫ x, (Set.Ioc a m).indicator (fun _ : ℝ => (1 : ℝ)) x ∂volume =
      volume.real (Set.Ioc a m) := by
    simpa only [Set.indicator_apply, measureReal_def, smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := volume) (1 : ℝ)
        (s := Set.Ioc a m) measurableSet_Ioc)
  have hareaR : ∫ x, (Set.Ioc m b).indicator (fun _ : ℝ => (1 : ℝ)) x ∂volume =
      volume.real (Set.Ioc m b) := by
    simpa only [Set.indicator_apply, measureReal_def, smul_eq_mul, mul_one] using
      (integral_indicator_const (μ := volume) (1 : ℝ)
        (s := Set.Ioc m b) measurableSet_Ioc)
  have hzeroIoc :
      ∫ x, discrepancyIocDyadicHaar r c x ∂volume = 0 := by
    change ∫ x, (Set.Ioc m b).indicator (fun _ : ℝ => (1 : ℝ)) x -
      (Set.Ioc a m).indicator (fun _ : ℝ => (1 : ℝ)) x ∂volume = 0
    rw [integral_sub hR hL, hareaR, hareaL,
      Real.volume_real_Ioc_of_le hmb.le, Real.volume_real_Ioc_of_le hab.le]
    have hm : m = (a + b) / 2 := by
      dsimp [a, m, b, realDyadicLeft, realDyadicMid, realDyadicRight]
      field_simp
      ring
    rw [hm]
    ring
  calc
    ∫ x, realDyadicHaar r c x ∂volume =
        ∫ x, discrepancyIocDyadicHaar r c x ∂volume := by
          apply integral_congr_ae
          exact (criticalIocHaar_ae_eq_real r c).symm
    _ = 0 := hzeroIoc

private theorem critical_realDyadicHaar_integrable (r c : ℕ) :
    Integrable (fun x => realDyadicHaar r c x) volume := by
  classical
  let a := realDyadicLeft r c
  let m := realDyadicMid r c
  let b := realDyadicRight r c
  have hL : Integrable ((Set.Ioc a m).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
    apply (integrableOn_const (ne_of_lt measure_Ioc_lt_top)).integrable_indicator
    exact measurableSet_Ioc
  have hR : Integrable ((Set.Ioc m b).indicator (fun _ : ℝ => (1 : ℝ))) volume := by
    apply (integrableOn_const (ne_of_lt measure_Ioc_lt_top)).integrable_indicator
    exact measurableSet_Ioc
  have hD : Integrable (fun x => discrepancyIocDyadicHaar r c x) volume := by
    change Integrable
      ((fun x => (Set.Ioc m b).indicator (fun _ : ℝ => (1 : ℝ)) x) -
        (fun x => (Set.Ioc a m).indicator (fun _ : ℝ => (1 : ℝ)) x)) volume
    exact hR.sub hL
  exact hD.congr (criticalIocHaar_ae_eq_real r c)

private theorem criticalDyadicE_integrable (r c : ℕ) :
    Integrable (fun x => criticalDyadicE r c x) volume := by
  let L := realDyadicRight r c - realDyadicLeft r c
  have hsub : Integrable (fun x =>
      realDyadicHaar (r + 1) (2 * c) x -
        realDyadicHaar (r + 1) (2 * c + 1) x) volume :=
    (critical_realDyadicHaar_integrable _ _).sub
      (critical_realDyadicHaar_integrable _ _)
  change Integrable (fun x =>
      (realDyadicHaar (r + 1) (2 * c) x -
        realDyadicHaar (r + 1) (2 * c + 1) x) / Real.sqrt L) volume
  exact hsub.div_const _

private theorem criticalDyadicE_integral_zero (r c : ℕ) :
    ∫ x, criticalDyadicE r c x ∂volume = 0 := by
  let L := realDyadicRight r c - realDyadicLeft r c
  have hleft : Integrable (fun x => realDyadicHaar (r + 1) (2 * c) x) volume :=
    critical_realDyadicHaar_integrable _ _
  have hright : Integrable (fun x => realDyadicHaar (r + 1) (2 * c + 1) x) volume :=
    critical_realDyadicHaar_integrable _ _
  have hsub : Integrable (fun x =>
      realDyadicHaar (r + 1) (2 * c) x -
        realDyadicHaar (r + 1) (2 * c + 1) x) volume :=
    hleft.sub hright
  change ∫ x, (realDyadicHaar (r + 1) (2 * c) x -
    realDyadicHaar (r + 1) (2 * c + 1) x) / Real.sqrt L ∂volume = 0
  rw [integral_div, integral_sub hleft hright]
  rw [critical_realDyadicHaar_integral_zero, critical_realDyadicHaar_integral_zero]
  simp

theorem critical_realHaar_eq_neg_one_on_left {r c : ℕ} {x : ℝ}
    (hx : x ∈ realDyadicLeftHalf r c) : realDyadicHaar r c x = -1 := by
  classical
  rw [critical_leftHalf_eq_Ico] at hx
  let a := realDyadicLeft r c
  let m := realDyadicMid r c
  let b := realDyadicRight r c
  have hR : x ∉ Set.Ico m b := by
    simp only [Set.mem_Ico] at hx ⊢
    intro h
    linarith
  have hx' : a ≤ x ∧ x < m := by simpa only [Set.mem_Ico] using hx
  have hR' : ¬ (m ≤ x ∧ x < b) := by simpa only [Set.mem_Ico] using hR
  unfold realDyadicHaar
  rw [critical_rightHalf_eq_Ico, critical_leftHalf_eq_Ico]
  simp [Set.mem_Ico, a, m, b, hR', hx']

theorem critical_realHaar_eq_one_on_right {r c : ℕ} {x : ℝ}
    (hx : x ∈ realDyadicRightHalf r c) : realDyadicHaar r c x = 1 := by
  classical
  rw [critical_rightHalf_eq_Ico] at hx
  let a := realDyadicLeft r c
  let m := realDyadicMid r c
  let b := realDyadicRight r c
  have hL : x ∉ Set.Ico a m := by
    simp only [Set.mem_Ico] at hx ⊢
    intro h
    linarith
  have hx' : m ≤ x ∧ x < b := by simpa only [Set.mem_Ico] using hx
  have hL' : ¬ (a ≤ x ∧ x < m) := by simpa only [Set.mem_Ico] using hL
  unfold realDyadicHaar
  rw [critical_rightHalf_eq_Ico, critical_leftHalf_eq_Ico]
  simp [Set.mem_Ico, a, m, b, hL', hx']

theorem critical_realHaar_zero_outside {r c : ℕ} {x : ℝ}
    (hx : x ∉ Set.Ico (realDyadicLeft r c) (realDyadicRight r c)) :
    realDyadicHaar r c x = 0 := by
  have hs := critical_realDyadicHaar_sq r c x
  rw [if_neg hx] at hs
  exact (sq_eq_zero_iff).1 hs

/-- The signed primitive is supported on its parent dyadic interval. -/
theorem criticalDyadicSignedPrimitive_zero_outside {r c : ℕ} {x : ℝ}
    (hx : x ∉ Set.Ico (realDyadicLeft r c) (realDyadicRight r c)) :
    criticalDyadicSignedPrimitive r c x = 0 := by
  let a := realDyadicLeft r c
  let b := realDyadicRight r c
  let m := (a + b) / 2
  have hab : a < b := by
    dsimp [a, b, realDyadicLeft, realDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmDyadic : realDyadicMid r c = m := by
    dsimp [realDyadicMid, realDyadicLeft, realDyadicRight, a, b, m]
    field_simp
    ring
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  have hleft : x ∉ Set.Ioo a m := by
    intro h
    apply hx
    simp only [Set.mem_Ico]
    exact ⟨le_of_lt h.1, lt_trans h.2 hmb⟩
  have hright : x ∉ Set.Ioo m b := by
    intro h
    apply hx
    simp only [Set.mem_Ico]
    exact ⟨le_trans (le_of_lt ham) (le_of_lt h.1), h.2⟩
  change (integratedHaarTent m ((m + b) / 2) b x -
    integratedHaarTent a ((a + m) / 2) m x) / Real.sqrt (b - a) = 0
  rw [integratedHaarTent_eq_zero_of_not_mem_open (a := a)
    (m := (a + m) / 2) (b := m) (x := x) (by linarith) (by linarith) hleft,
    integratedHaarTent_eq_zero_of_not_mem_open (a := m)
    (m := (m + b) / 2) (b := b) (x := x) (by linarith) (by linarith) hright]
  simp [a, m, b]

/-- A critical primitive at a finer scale is orthogonal to every coarser
production Haar function: on its support the coarser Haar is constant, while
the primitive has mean zero. -/
theorem criticalDyadicSignedPrimitive_inner_zero_of_coarserHaar
    {r s c d : ℕ} (hrs : r < s) :
    ∫ x, criticalDyadicSignedPrimitive s d x * realDyadicHaar r c x ∂volume = 0 := by
  classical
  obtain hbefore | hleft | hright | hafter := critical_fine_cell_position hrs
  · have hprod : ∀ x, criticalDyadicSignedPrimitive s d x *
        realDyadicHaar r c x = 0 := by
      intro x
      by_cases hf : x ∈ Set.Ico (realDyadicLeft s d) (realDyadicRight s d)
      · have hc : x ∉ Set.Ico (realDyadicLeft r c) (realDyadicRight r c) := by
          simp only [Set.mem_Ico] at hf ⊢
          intro hh
          linarith [hbefore]
        rw [critical_realHaar_zero_outside hc]
        simp
      · rw [criticalDyadicSignedPrimitive_zero_outside hf]
        simp
    calc
      ∫ x, criticalDyadicSignedPrimitive s d x * realDyadicHaar r c x ∂volume =
          ∫ x, (0 : ℝ) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by simp

  · rcases hleft with ⟨hL, hM⟩
    have hsub : Set.Ico (realDyadicLeft s d) (realDyadicRight s d) ⊆
        realDyadicLeftHalf r c := by
      rw [critical_leftHalf_eq_Ico]
      intro x hx
      exact ⟨le_trans hL hx.1, lt_of_lt_of_le hx.2 hM⟩
    have hprod : ∀ x, criticalDyadicSignedPrimitive s d x *
        realDyadicHaar r c x = -criticalDyadicSignedPrimitive s d x := by
      intro x
      by_cases hf : x ∈ Set.Ico (realDyadicLeft s d) (realDyadicRight s d)
      · rw [critical_realHaar_eq_neg_one_on_left (hsub hf)]
        ring
      · rw [criticalDyadicSignedPrimitive_zero_outside hf]
        simp
    calc
      ∫ x, criticalDyadicSignedPrimitive s d x * realDyadicHaar r c x ∂volume =
          ∫ x, -criticalDyadicSignedPrimitive s d x ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by
        rw [integral_neg, criticalDyadicSignedPrimitive_integral_zero]
        simp
  · rcases hright with ⟨hM, hR⟩
    have hsub : Set.Ico (realDyadicLeft s d) (realDyadicRight s d) ⊆
        realDyadicRightHalf r c := by
      rw [critical_rightHalf_eq_Ico]
      intro x hx
      exact ⟨le_trans hM hx.1, lt_of_lt_of_le hx.2 hR⟩
    have hprod : ∀ x, criticalDyadicSignedPrimitive s d x *
        realDyadicHaar r c x = criticalDyadicSignedPrimitive s d x := by
      intro x
      by_cases hf : x ∈ Set.Ico (realDyadicLeft s d) (realDyadicRight s d)
      · rw [critical_realHaar_eq_one_on_right (hsub hf)]
        ring
      · rw [criticalDyadicSignedPrimitive_zero_outside hf]
        simp
    calc
      ∫ x, criticalDyadicSignedPrimitive s d x * realDyadicHaar r c x ∂volume =
          ∫ x, criticalDyadicSignedPrimitive s d x ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := criticalDyadicSignedPrimitive_integral_zero s d
  · have hprod : ∀ x, criticalDyadicSignedPrimitive s d x *
        realDyadicHaar r c x = 0 := by
      intro x
      by_cases hf : x ∈ Set.Ico (realDyadicLeft s d) (realDyadicRight s d)
      · have hc : x ∉ Set.Ico (realDyadicLeft r c) (realDyadicRight r c) := by
          simp only [Set.mem_Ico] at hf ⊢
          intro hh
          linarith [hafter]
        rw [critical_realHaar_zero_outside hc]
        simp
      · rw [criticalDyadicSignedPrimitive_zero_outside hf]
        simp
    calc
      ∫ x, criticalDyadicSignedPrimitive s d x * realDyadicHaar r c x ∂volume =
          ∫ x, (0 : ℝ) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by simp

/-- At a fixed scale, a critical primitive and a production Haar on a distinct
cell are orthogonal by support separation. -/
theorem criticalDyadicSignedPrimitive_inner_same_level_of_ne
    {r c d : ℕ} (hcd : c ≠ d) :
    ∫ x, criticalDyadicSignedPrimitive r c x * realDyadicHaar r d x ∂volume = 0 := by
  classical
  rcases lt_or_gt_of_ne hcd with hlt | hgt
  · have hsep := critical_right_le_left_of_lt (r := r) hlt
    have hprod : ∀ x, criticalDyadicSignedPrimitive r c x * realDyadicHaar r d x = 0 := by
      intro x
      by_cases hc : x ∈ Set.Ico (realDyadicLeft r c) (realDyadicRight r c)
      · have hd : x ∉ Set.Ico (realDyadicLeft r d) (realDyadicRight r d) := by
          simp only [Set.mem_Ico] at hc ⊢
          intro hh
          linarith [hsep]
        rw [critical_realHaar_zero_outside hd]
        simp
      · rw [criticalDyadicSignedPrimitive_zero_outside hc]
        simp
    calc
      ∫ x, criticalDyadicSignedPrimitive r c x * realDyadicHaar r d x ∂volume =
          ∫ x, (0 : ℝ) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by simp
  · have hsep := critical_right_le_left_of_lt (r := r) (c := d) (d := c) hgt
    have hprod : ∀ x, criticalDyadicSignedPrimitive r c x * realDyadicHaar r d x = 0 := by
      intro x
      by_cases hc : x ∈ Set.Ico (realDyadicLeft r c) (realDyadicRight r c)
      · have hd : x ∉ Set.Ico (realDyadicLeft r d) (realDyadicRight r d) := by
          simp only [Set.mem_Ico] at hc ⊢
          intro hh
          linarith [hsep]
        rw [critical_realHaar_zero_outside hd]
        simp
      · rw [criticalDyadicSignedPrimitive_zero_outside hc]
        simp
    calc
      ∫ x, criticalDyadicSignedPrimitive r c x * realDyadicHaar r d x ∂volume =
          ∫ x, (0 : ℝ) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by simp

/-- Ordinary production Haar functions at distinct depths are orthogonal.
The proof uses actual dyadic interval nesting and zero integral of the finer
Haar function. -/
theorem critical_realDyadicHaar_inner_of_depth_ne {r s c d : ℕ}
    (hrs : r < s) :
    ∫ x, realDyadicHaar r c x * realDyadicHaar s d x ∂volume = 0 := by
  classical
  obtain hbefore | hleft | hright | hafter := critical_fine_cell_position hrs
  · have hprod : ∀ x, realDyadicHaar r c x * realDyadicHaar s d x = 0 := by
      intro x
      by_cases hf : x ∈ Set.Ico (realDyadicLeft s d) (realDyadicRight s d)
      · have hc : x ∉ Set.Ico (realDyadicLeft r c) (realDyadicRight r c) := by
          simp only [Set.mem_Ico] at hf ⊢
          intro h
          linarith [hbefore]
        simp [critical_realHaar_zero_outside hc]
      · simp [critical_realHaar_zero_outside hf]
    calc
      ∫ x, realDyadicHaar r c x * realDyadicHaar s d x ∂volume =
          ∫ x, (0 : ℝ) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by simp
  · rcases hleft with ⟨hL, hM⟩
    have hsub : Set.Ico (realDyadicLeft s d) (realDyadicRight s d) ⊆
        realDyadicLeftHalf r c := by
      rw [critical_leftHalf_eq_Ico]
      intro x hx
      exact ⟨le_trans hL hx.1, lt_of_lt_of_le hx.2 hM⟩
    have hprod : ∀ x, realDyadicHaar r c x * realDyadicHaar s d x =
        -realDyadicHaar s d x := by
      intro x
      by_cases hf : x ∈ Set.Ico (realDyadicLeft s d) (realDyadicRight s d)
      · rw [critical_realHaar_eq_neg_one_on_left (hsub hf)]
        ring
      · have hz := critical_realHaar_zero_outside (r := s) (c := d) hf
        simp [hz]
    calc
      ∫ x, realDyadicHaar r c x * realDyadicHaar s d x ∂volume =
          ∫ x, -realDyadicHaar s d x ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by rw [integral_neg, critical_realDyadicHaar_integral_zero]; simp
  · rcases hright with ⟨hM, hR⟩
    have hsub : Set.Ico (realDyadicLeft s d) (realDyadicRight s d) ⊆
        realDyadicRightHalf r c := by
      rw [critical_rightHalf_eq_Ico]
      intro x hx
      exact ⟨le_trans hM hx.1, lt_of_lt_of_le hx.2 hR⟩
    have hprod : ∀ x, realDyadicHaar r c x * realDyadicHaar s d x =
        realDyadicHaar s d x := by
      intro x
      by_cases hf : x ∈ Set.Ico (realDyadicLeft s d) (realDyadicRight s d)
      · rw [critical_realHaar_eq_one_on_right (hsub hf)]
        ring
      · have hz := critical_realHaar_zero_outside (r := s) (c := d) hf
        simp [hz]
    calc
      ∫ x, realDyadicHaar r c x * realDyadicHaar s d x ∂volume =
          ∫ x, realDyadicHaar s d x ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := critical_realDyadicHaar_integral_zero s d
  · have hprod : ∀ x, realDyadicHaar r c x * realDyadicHaar s d x = 0 := by
      intro x
      by_cases hc : x ∈ Set.Ico (realDyadicLeft r c) (realDyadicRight r c)
      · have hf : x ∉ Set.Ico (realDyadicLeft s d) (realDyadicRight s d) := by
          simp only [Set.mem_Ico] at hc ⊢
          intro h
          linarith [hafter]
        simp [critical_realHaar_zero_outside (r := s) (c := d) hf]
      · simp [critical_realHaar_zero_outside (r := r) (c := c) hc]
    calc
      ∫ x, realDyadicHaar r c x * realDyadicHaar s d x ∂volume =
          ∫ x, (0 : ℝ) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by simp

private theorem critical_realDyadicHaar_product_integrable
    (r c s d : ℕ) :
    Integrable (fun x => realDyadicHaar r c x * realDyadicHaar s d x) volume := by
  have hleft : Integrable (fun x => realDyadicHaar r c x) volume :=
    critical_realDyadicHaar_integrable r c
  have hright : Integrable (fun x => realDyadicHaar s d x) volume :=
    critical_realDyadicHaar_integrable s d
  have hbound : ∀ᵐ x ∂volume, ‖realDyadicHaar s d x‖ ≤ 1 := by
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]
      exact realDyadicHaar_abs_le_one s d x)
  exact hleft.mul_bdd hright.aestronglyMeasurable hbound

/-- The continuous child-Haar differences are orthogonal across distinct
scales. This is the one-axis critical-vector cross-scale statement. -/
theorem criticalDyadicE_inner_of_depth_ne {r s c d : ℕ} (hrs : r < s) :
    ∫ x, criticalDyadicE r c x * criticalDyadicE s d x ∂volume = 0 := by
  let h₁ := realDyadicHaar (r + 1) (2 * c)
  let h₂ := realDyadicHaar (r + 1) (2 * c + 1)
  let g₁ := realDyadicHaar (s + 1) (2 * d)
  let g₂ := realDyadicHaar (s + 1) (2 * d + 1)
  let α := Real.sqrt (realDyadicRight r c - realDyadicLeft r c)
  let β := Real.sqrt (realDyadicRight s d - realDyadicLeft s d)
  let f₁₁ := fun x => h₁ x * g₁ x
  let f₁₂ := fun x => h₁ x * g₂ x
  let f₂₁ := fun x => h₂ x * g₁ x
  let f₂₂ := fun x => h₂ x * g₂ x
  let f₃ := fun x => f₁₁ x - f₁₂ x - f₂₁ x
  have h₁₁ : Integrable f₁₁ volume :=
    critical_realDyadicHaar_product_integrable (r + 1) (2 * c) (s + 1) (2 * d)
  have h₁₂ : Integrable f₁₂ volume :=
    critical_realDyadicHaar_product_integrable (r + 1) (2 * c) (s + 1) (2 * d + 1)
  have h₂₁ : Integrable f₂₁ volume :=
    critical_realDyadicHaar_product_integrable (r + 1) (2 * c + 1) (s + 1) (2 * d)
  have h₂₂ : Integrable f₂₂ volume :=
    critical_realDyadicHaar_product_integrable (r + 1) (2 * c + 1) (s + 1) (2 * d + 1)
  have h₃ : Integrable f₃ volume := (h₁₁.sub h₁₂).sub h₂₁
  have hcomb : Integrable (fun x => f₃ x + f₂₂ x) volume :=
    (h₁₁.sub h₁₂).sub h₂₁ |>.add h₂₂
  have hpoint (x : ℝ) :
      criticalDyadicE r c x * criticalDyadicE s d x =
        (f₃ x + f₂₂ x) / (α * β) := by
    dsimp [criticalDyadicE, h₁, h₂, g₁, g₂, α, β, f₁₁, f₁₂, f₂₁, f₂₂]
    ring
  calc
    ∫ x, criticalDyadicE r c x * criticalDyadicE s d x ∂volume =
        ∫ x, (f₁₁ x - f₁₂ x - f₂₁ x + f₂₂ x) / (α * β) ∂volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = (∫ x, f₃ x + f₂₂ x ∂volume) / (α * β) := by rw [integral_div]
    _ = 0 := by
      have h₁₁z : ∫ x, f₁₁ x ∂volume = 0 := by
        change ∫ x, realDyadicHaar (r + 1) (2 * c) x *
          realDyadicHaar (s + 1) (2 * d) x ∂volume = 0
        exact critical_realDyadicHaar_inner_of_depth_ne (Nat.succ_lt_succ hrs)
      have h₁₂z : ∫ x, f₁₂ x ∂volume = 0 := by
        change ∫ x, realDyadicHaar (r + 1) (2 * c) x *
          realDyadicHaar (s + 1) (2 * d + 1) x ∂volume = 0
        exact critical_realDyadicHaar_inner_of_depth_ne (Nat.succ_lt_succ hrs)
      have h₂₁z : ∫ x, f₂₁ x ∂volume = 0 := by
        change ∫ x, realDyadicHaar (r + 1) (2 * c + 1) x *
          realDyadicHaar (s + 1) (2 * d) x ∂volume = 0
        exact critical_realDyadicHaar_inner_of_depth_ne (Nat.succ_lt_succ hrs)
      have h₂₂z : ∫ x, f₂₂ x ∂volume = 0 := by
        change ∫ x, realDyadicHaar (r + 1) (2 * c + 1) x *
          realDyadicHaar (s + 1) (2 * d + 1) x ∂volume = 0
        exact critical_realDyadicHaar_inner_of_depth_ne (Nat.succ_lt_succ hrs)
      have hnumZero : ∫ x, f₃ x + f₂₂ x ∂volume = 0 := by
        rw [integral_add h₃ h₂₂]
        change (∫ x, f₁₁ x - f₁₂ x - f₂₁ x ∂volume) +
          ∫ x, f₂₂ x ∂volume = 0
        have hfirst : (∫ x, f₁₁ x - f₁₂ x - f₂₁ x ∂volume) =
            (∫ x, f₁₁ x ∂volume) - (∫ x, f₁₂ x ∂volume) -
              (∫ x, f₂₁ x ∂volume) := by
          calc
            ∫ x, f₁₁ x - f₁₂ x - f₂₁ x ∂volume =
                (∫ x, f₁₁ x - f₁₂ x ∂volume) - ∫ x, f₂₁ x ∂volume := by
                  exact integral_sub (h₁₁.sub h₁₂) h₂₁
            _ = _ := by rw [integral_sub h₁₁ h₁₂]
        rw [hfirst, h₁₁z, h₁₂z, h₂₁z, h₂₂z]
        simp
      rw [hnumZero]
      simp

/-- Distinct critical vectors at one scale are orthogonal in continuous L²;
their half-open parent supports are disjoint. -/
theorem criticalDyadicE_inner_same_level_of_ne {r c d : ℕ} (hcd : c ≠ d) :
    ∫ x, criticalDyadicE r c x * criticalDyadicE r d x ∂volume = 0 := by
  classical
  rcases lt_or_gt_of_ne hcd with hlt | hgt
  · have hsep := critical_right_le_left_of_lt (r := r) hlt
    have hprod : ∀ x, criticalDyadicE r c x * criticalDyadicE r d x = 0 := by
      intro x
      by_cases hc : x ∈ Set.Ico (realDyadicLeft r c) (realDyadicRight r c)
      · by_cases hd : x ∈ Set.Ico (realDyadicLeft r d) (realDyadicRight r d)
        · simp only [Set.mem_Ico] at hc hd
          have : x < realDyadicRight r c := hc.2
          have : realDyadicRight r c ≤ realDyadicLeft r d := hsep
          linarith
        · have hz : criticalDyadicE r d x = 0 := by
            have hs := criticalDyadicE_sq r d x
            rw [if_neg hd] at hs
            exact (sq_eq_zero_iff).1 hs
          simp [hz]
      · have hz : criticalDyadicE r c x = 0 := by
          have hs := criticalDyadicE_sq r c x
          rw [if_neg hc] at hs
          exact (sq_eq_zero_iff).1 hs
        simp [hz]
    calc
      ∫ x, criticalDyadicE r c x * criticalDyadicE r d x ∂volume =
          ∫ x, (0 : ℝ) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by simp
  · have hsep := critical_right_le_left_of_lt (r := r) (c := d) (d := c) hgt
    have hprod : ∀ x, criticalDyadicE r c x * criticalDyadicE r d x = 0 := by
      intro x
      by_cases hc : x ∈ Set.Ico (realDyadicLeft r c) (realDyadicRight r c)
      · by_cases hd : x ∈ Set.Ico (realDyadicLeft r d) (realDyadicRight r d)
        · simp only [Set.mem_Ico] at hc hd
          have : x < realDyadicRight r d := hd.2
          have : realDyadicRight r d ≤ realDyadicLeft r c := hsep
          linarith
        · have hz : criticalDyadicE r d x = 0 := by
            have hs := criticalDyadicE_sq r d x
            rw [if_neg hd] at hs
            exact (sq_eq_zero_iff).1 hs
          simp [hz]
      · have hz : criticalDyadicE r c x = 0 := by
          have hs := criticalDyadicE_sq r c x
          rw [if_neg hc] at hs
          exact (sq_eq_zero_iff).1 hs
        simp [hz]
    calc
      ∫ x, criticalDyadicE r c x * criticalDyadicE r d x ∂volume =
          ∫ x, (0 : ℝ) ∂volume := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall hprod
      _ = 0 := by simp

end HaarQuarter
