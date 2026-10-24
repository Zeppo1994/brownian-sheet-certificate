import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
import BrownianSharp.DyadicRealCells
import BrownianSharp.DyadicRealCells

open MeasureTheory
open scoped BigOperators

namespace HaarQuarter

/-- The half-open dyadic interval in `[0,1]` indexed by level and cell. -/
noncomputable def realDyadicInterval (r k : ℕ) : Set ℝ :=
  Set.Ico ((k : ℝ) / (2 : ℝ) ^ r) (((k : ℝ) + 1) / (2 : ℝ) ^ r)

noncomputable def realDyadicLeft (r k : ℕ) : ℝ := (k : ℝ) / (2 : ℝ) ^ r

noncomputable def realDyadicMid (r k : ℕ) : ℝ := ((k : ℝ) + (1 / 2 : ℝ)) / (2 : ℝ) ^ r

noncomputable def realDyadicRight (r k : ℕ) : ℝ := ((k : ℝ) + 1) / (2 : ℝ) ^ r

/-- Real Haar function, with the positive half on the right. -/
noncomputable def discrepancyIocDyadicHaar (r k : ℕ) (x : ℝ) : ℝ :=
  (Set.Ioc (realDyadicMid r k) (realDyadicRight r k)).indicator 1 x -
    (Set.Ioc (realDyadicLeft r k) (realDyadicMid r k)).indicator 1 x

noncomputable def realPointTail (p x : ℝ) : ℝ := if p < x then 1 else 0

private theorem realDyadicLeftHalf_eq_Ico (r k : ℕ) :
    realDyadicLeftHalf r k = Set.Ico (realDyadicLeft r k) (realDyadicMid r k) := by
  unfold realDyadicLeftHalf
  have hleft : ((2 * k : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1) = realDyadicLeft r k := by
    push_cast
    simp [realDyadicLeft, pow_succ]
    ring
  have hmid : ((2 * k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1) = realDyadicMid r k := by
    push_cast
    simp [realDyadicMid, pow_succ]
    ring
  rw [hleft, hmid]

private theorem realDyadicRightHalf_eq_Ico (r k : ℕ) :
    realDyadicRightHalf r k = Set.Ico (realDyadicMid r k) (realDyadicRight r k) := by
  unfold realDyadicRightHalf
  have hmid : ((2 * k + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1) = realDyadicMid r k := by
    push_cast
    simp [realDyadicMid, pow_succ]
    ring
  have hright : ((2 * k + 2 : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1) = realDyadicRight r k := by
    push_cast
    simp [realDyadicRight, pow_succ]
    ring
  rw [hmid, hright]

private theorem discrepancyIocDyadicHaar_ae_eq_realDyadicHaar (r k : ℕ) :
    discrepancyIocDyadicHaar r k =ᵐ[volume] realDyadicHaar r k := by
  let a := realDyadicLeft r k
  let m := realDyadicMid r k
  let b := realDyadicRight r k
  have hnull : volume ({a} ∪ {m} ∪ {b} : Set ℝ) = 0 := by
    rw [measure_union_null (measure_union_null (measure_singleton a)
      (measure_singleton m)) (measure_singleton b)]
  apply (ae_iff).2
  apply measure_mono_null (t := {a} ∪ {m} ∪ {b})
  · intro x hx
    change discrepancyIocDyadicHaar r k x ≠ realDyadicHaar r k x at hx
    by_contra hne
    have hxa : x ≠ a := by
      intro h
      exact hne (Or.inl (Or.inl h))
    have hxm : x ≠ m := by
      intro h
      exact hne (Or.inl (Or.inr h))
    have hxb : x ≠ b := by
      intro h
      exact hne (Or.inr h)
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
    have hL : x ∈ realDyadicLeftHalf r k ↔ x ∈ Set.Ioc a m := by
      rw [realDyadicLeftHalf_eq_Ico]
      exact hleft
    have hR : x ∈ realDyadicRightHalf r k ↔ x ∈ Set.Ioc m b := by
      rw [realDyadicRightHalf_eq_Ico]
      exact hright
    have heq : realDyadicHaar r k x = discrepancyIocDyadicHaar r k x := by
      unfold realDyadicHaar discrepancyIocDyadicHaar
      have hR' : (x ∈ realDyadicRightHalf r k) = (m < x ∧ x ≤ b) := by
        rw [hR]
        rfl
      have hL' : (x ∈ realDyadicLeftHalf r k) = (a < x ∧ x ≤ m) := by
        rw [hL]
        rfl
      simp only [Set.indicator]
      rw [hR', hL']
      rfl
    exact hx heq.symm
  · exact hnull

/-- The production real Haar takes values in `{-1,0,1}` everywhere. -/
theorem realDyadicHaar_abs_le_one (r k : ℕ) (x : ℝ) :
    |realDyadicHaar r k x| ≤ 1 := by
  have hdis : Disjoint (realDyadicLeftHalf r k) (realDyadicRightHalf r k) := by
    rw [realDyadicLeftHalf_eq_Ico, realDyadicRightHalf_eq_Ico]
    exact Set.disjoint_left.mpr (by
      intro y hyL hyR
      exact (not_lt_of_ge hyR.1) hyL.2)
  unfold realDyadicHaar
  by_cases hR : x ∈ realDyadicRightHalf r k
  · by_cases hL : x ∈ realDyadicLeftHalf r k
    · exact (Set.disjoint_left.mp hdis hL hR).elim
    · simp [hR, hL]
  · by_cases hL : x ∈ realDyadicLeftHalf r k <;> simp [hR, hL]

private theorem integral_id_Ioc {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, x ∂volume = (b ^ 2 - a ^ 2) / 2 := by
  rw [← intervalIntegral.integral_of_le hab]
  change (∫ x in a..b, id x) = _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun x : ℝ => x ^ 2 / 2) (f' := id) hab
    (by fun_prop)
    (fun x hx => by
      have h := (hasDerivAt_pow 2 x).div_const (2 : ℝ)
      convert h using 1
      norm_num)
    (continuousOn_id.intervalIntegrable)]
  ring

private theorem integrable_id_on_Icc (a b : ℝ) :
    IntegrableOn (fun x : ℝ => x) (Set.Icc a b) volume := by
  exact ContinuousOn.integrableOn_compact isCompact_Icc continuousOn_id

private theorem integrable_id_on_subset_Icc {a b : ℝ} {s : Set ℝ}
    (hs : s ⊆ Set.Icc a b) : IntegrableOn (fun x : ℝ => x) s volume :=
  (integrable_id_on_Icc a b).mono_set hs

private theorem integrable_one_on_Icc (a b : ℝ) :
    IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc a b) volume := by
  exact ContinuousOn.integrableOn_compact isCompact_Icc continuousOn_const

private theorem integrable_one_on_subset_Icc {a b : ℝ} {s : Set ℝ}
    (hs : s ⊆ Set.Icc a b) : IntegrableOn (fun _ : ℝ => (1 : ℝ)) s volume :=
  (integrable_one_on_Icc a b).mono_set hs

private theorem finite_restrict_Ioc (a b : ℝ) :
    IsFiniteMeasure (volume.restrict (Set.Ioc a b)) := by
  rw [MeasureTheory.isFiniteMeasure_restrict]
  have hsub : Set.Ioc a b ⊆ Set.Icc a b := by
    intro x hx
    exact ⟨le_of_lt hx.1, hx.2⟩
  apply ne_of_lt
  exact lt_of_le_of_lt (measure_mono hsub)
    (IsCompact.measure_lt_top (K := Set.Icc a b) isCompact_Icc)

private theorem measurable_realPointTail (p : ℝ) : Measurable (realPointTail p) := by
  unfold realPointTail
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    measurable_const measurable_const

private theorem measurable_realDyadicHaar (r k : ℕ) :
    Measurable (discrepancyIocDyadicHaar r k) := by
  unfold discrepancyIocDyadicHaar
  exact Measurable.sub
    (measurable_const.indicator measurableSet_Ioc)
    (measurable_const.indicator measurableSet_Ioc)

private theorem norm_realPointTail_le_one (p x : ℝ) : ‖realPointTail p x‖ ≤ 1 := by
  unfold realPointTail
  split_ifs <;> norm_num

private theorem norm_realDyadicHaar_le_one (r k : ℕ) (x : ℝ) :
    ‖discrepancyIocDyadicHaar r k x‖ ≤ 1 := by
  unfold discrepancyIocDyadicHaar
  by_cases hxR : x ∈ Set.Ioc (realDyadicMid r k) (realDyadicRight r k)
  <;> by_cases hxL : x ∈ Set.Ioc (realDyadicLeft r k) (realDyadicMid r k)
  <;> simp [Set.indicator, hxR, hxL]

private theorem integrableOn_Ioc_of_bound {a b : ℝ} {f : ℝ → ℝ} {C : ℝ}
    (hf : Measurable f) (hbound : ∀ x ∈ Set.Ioc a b, ‖f x‖ ≤ C) :
    Integrable f (volume.restrict (Set.Ioc a b)) := by
  letI := finite_restrict_Ioc a b
  exact Integrable.of_bound hf.aestronglyMeasurable C
    ((MeasureTheory.ae_restrict_iff
      (p := fun x => ‖f x‖ ≤ C) (measurableSet_le hf.norm measurable_const)).2
      (Filter.Eventually.of_forall hbound))

private theorem integrable_tailHaar_on_Ioc (p : ℝ) (r k : ℕ) :
    Integrable (fun x => realPointTail p x * discrepancyIocDyadicHaar r k x)
      (volume.restrict (Set.Ioc (realDyadicLeft r k) (realDyadicRight r k))) := by
  apply integrableOn_Ioc_of_bound
    ((measurable_realPointTail p).mul (measurable_realDyadicHaar r k))
  intro x hx
  calc
    ‖realPointTail p x * discrepancyIocDyadicHaar r k x‖ =
        ‖realPointTail p x‖ * ‖discrepancyIocDyadicHaar r k x‖ := norm_mul _ _
    _ ≤ 1 * 1 := mul_le_mul (norm_realPointTail_le_one p x)
      (norm_realDyadicHaar_le_one r k x) (norm_nonneg _) (by norm_num)
    _ = 1 := by norm_num

private theorem integral_one_Ioc {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, (1 : ℝ) ∂volume = b - a := by
  rw [← intervalIntegral.integral_of_le hab, intervalIntegral.integral_const]
  norm_num

private theorem realDyadicHaar_integral_zero (r k : ℕ) :
    ∫ x in realDyadicInterval r k, discrepancyIocDyadicHaar r k x ∂volume = 0 := by
  let a := realDyadicLeft r k
  let m := realDyadicMid r k
  let b := realDyadicRight r k
  have hden : 0 < (2 : ℝ) ^ r := by positivity
  have hab : a ≤ m := by
    dsimp [a, m, realDyadicLeft, realDyadicMid]
    exact (div_le_div_iff₀ (by norm_num) hden).2 (by norm_num)
  have hmb : m ≤ b := by
    dsimp [m, b, realDyadicMid, realDyadicRight]
    exact (div_le_div_iff₀ (by norm_num) hden).2 (by norm_num)
  have hS : Set.Ioc a b ⊆ Set.Icc a b := by
    intro x hx
    exact ⟨le_of_lt hx.1, hx.2⟩
  have hR : IntegrableOn ((Set.Ioc m b).indicator (fun _ : ℝ => (1 : ℝ)))
      (Set.Ioc a b) volume :=
    (integrable_one_on_subset_Icc (a := a) (b := b) hS).indicator measurableSet_Ioc
  have hL : IntegrableOn ((Set.Ioc a m).indicator (fun _ : ℝ => (1 : ℝ)))
      (Set.Ioc a b) volume :=
    (integrable_one_on_subset_Icc (a := a) (b := b) hS).indicator measurableSet_Ioc
  have has : Set.Ioc a b ∩ Set.Ioc m b = Set.Ioc m b :=
    Set.inter_eq_right.mpr (by
      intro x hx
      exact ⟨lt_of_le_of_lt hab hx.1, hx.2⟩)
  have hleft : Set.Ioc a b ∩ Set.Ioc a m = Set.Ioc a m :=
    Set.inter_eq_right.mpr (by
      intro x hx
      exact ⟨hx.1, le_trans hx.2 hmb⟩)
  change ∫ x in Set.Ico a b,
      ((Set.Ioc m b).indicator 1 x - (Set.Ioc a m).indicator 1 x) ∂volume = 0
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
  change ∫ x in Set.Ioc a b,
      ((Set.Ioc m b).indicator 1 x - (Set.Ioc a m).indicator 1 x) ∂volume = 0
  change (∫ x, ((Set.Ioc m b).indicator (fun _ : ℝ => (1 : ℝ)) x -
      (Set.Ioc a m).indicator (fun _ : ℝ => (1 : ℝ)) x)
      ∂(volume.restrict (Set.Ioc a b))) = 0
  have hR' : Integrable ((Set.Ioc m b).indicator (fun _ : ℝ => (1 : ℝ)))
      (volume.restrict (Set.Ioc a b)) := hR
  have hL' : Integrable ((Set.Ioc a m).indicator (fun _ : ℝ => (1 : ℝ)))
      (volume.restrict (Set.Ioc a b)) := hL
  have hsplit := MeasureTheory.integral_sub hR' hL'
  rw [hsplit,
      MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      has, hleft,
      integral_one_Ioc hmb, integral_one_Ioc hab]
  dsimp [a, m, b, realDyadicLeft, realDyadicMid, realDyadicRight]
  field_simp
  <;> ring

/-- The affine moment of the positive-right Haar function on a dyadic interval. -/
private theorem discrepancyIocDyadicHaar_affine_moment (r k : ℕ) :
    ∫ x in realDyadicInterval r k, x * discrepancyIocDyadicHaar r k x ∂volume =
      ((2 : ℝ) ^ r)⁻¹ ^ 2 / 4 := by
  let a := realDyadicLeft r k
  let m := realDyadicMid r k
  let b := realDyadicRight r k
  have hden : 0 < (2 : ℝ) ^ r := by positivity
  have hab : a ≤ m := by
    dsimp [a, m, realDyadicLeft, realDyadicMid]
    exact (div_le_div_iff₀ (by norm_num) hden).2 (by norm_num)
  have hmb : m ≤ b := by
    dsimp [m, b, realDyadicMid, realDyadicRight]
    exact (div_le_div_iff₀ (by norm_num) hden).2 (by norm_num)
  have has : Set.Ioc a b ∩ Set.Ioc m b = Set.Ioc m b :=
    Set.inter_eq_right.mpr (by
      intro x hx
      exact ⟨lt_of_le_of_lt hab hx.1, hx.2⟩)
  have hleft : Set.Ioc a b ∩ Set.Ioc a m = Set.Ioc a m :=
    Set.inter_eq_right.mpr (by
      intro x hx
      exact ⟨hx.1, le_trans hx.2 hmb⟩)
  have hR : IntegrableOn ((Set.Ioc m b).indicator (fun x : ℝ => x)) (Set.Ioc a b) volume := by
    exact (integrable_id_on_subset_Icc (a := a) (b := b) (s := Set.Ioc a b) (by
      intro x hx
      exact ⟨le_of_lt hx.1, hx.2⟩)).indicator measurableSet_Ioc
  have hL : IntegrableOn ((Set.Ioc a m).indicator (fun x : ℝ => x)) (Set.Ioc a b) volume := by
    exact (integrable_id_on_subset_Icc (a := a) (b := b) (s := Set.Ioc a b) (by
      intro x hx
      exact ⟨le_of_lt hx.1, hx.2⟩)).indicator measurableSet_Ioc
  change ∫ x in Set.Ico a b, x * discrepancyIocDyadicHaar r k x ∂volume = _
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc]
  simp only [discrepancyIocDyadicHaar]
  have hpoint : ∀ x : ℝ,
      x * ((Set.Ioc m b).indicator 1 x - (Set.Ioc a m).indicator 1 x) =
        (Set.Ioc m b).indicator (fun y : ℝ => y) x -
          (Set.Ioc a m).indicator (fun y : ℝ => y) x := by
    intro x
    by_cases hxR : x ∈ Set.Ioc m b <;> by_cases hxL : x ∈ Set.Ioc a m <;>
      simp [Set.indicator, hxR, hxL]
  rw [show (fun x : ℝ => x * ((Set.Ioc m b).indicator 1 x -
      (Set.Ioc a m).indicator 1 x)) =
      (Set.Ioc m b).indicator (fun y : ℝ => y) -
        (Set.Ioc a m).indicator (fun y : ℝ => y) from funext hpoint]
  change ∫ x in Set.Ioc a b,
      ((Set.Ioc m b).indicator (fun y : ℝ => y) x -
        (Set.Ioc a m).indicator (fun y : ℝ => y) x) ∂volume = _
  rw [MeasureTheory.integral_sub hR hL]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      has, hleft]
  rw [integral_id_Ioc hmb, integral_id_Ioc hab]
  dsimp [a, m, b, realDyadicLeft, realDyadicMid, realDyadicRight]
  have hp : (2 : ℝ) ^ r ≠ 0 := by positivity
  field_simp
  ring

/-- A point outside a dyadic interval contributes zero to its Haar coefficient. -/
theorem realPointTail_dyadicHaar_integral_eq_zero {r k : ℕ} {p : ℝ}
    (hp : p < realDyadicLeft r k ∨ realDyadicRight r k ≤ p) :
    ∫ x in realDyadicInterval r k,
      realPointTail p x * discrepancyIocDyadicHaar r k x ∂volume = 0 := by
  rcases hp with hleft | hright
  · have htail : ∀ x ∈ realDyadicInterval r k, realPointTail p x = 1 := by
      intro x hx
      simp only [realDyadicInterval, Set.mem_Ico] at hx
      simp [realPointTail, lt_of_lt_of_le hleft hx.1]
    change ∫ x in Set.Ico (realDyadicLeft r k) (realDyadicRight r k),
      realPointTail p x * discrepancyIocDyadicHaar r k x ∂volume = 0
    rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ico]
    · exact realDyadicHaar_integral_zero r k
    · exact Filter.Eventually.of_forall (fun x hx => by rw [htail x hx]; ring)
  · have htail : ∀ x ∈ realDyadicInterval r k, realPointTail p x = 0 := by
      intro x hx
      simp only [realDyadicInterval, Set.mem_Ico] at hx
      have hxle : x ≤ p := le_trans (le_of_lt hx.2) hright
      simp [realPointTail, not_lt_of_ge hxle]
    change ∫ x in Set.Ico (realDyadicLeft r k) (realDyadicRight r k),
      realPointTail p x * discrepancyIocDyadicHaar r k x ∂volume = 0
    calc
      ∫ x in Set.Ico (realDyadicLeft r k) (realDyadicRight r k),
          realPointTail p x * discrepancyIocDyadicHaar r k x ∂volume =
        ∫ x in Set.Ico (realDyadicLeft r k) (realDyadicRight r k), (0 : ℝ) ∂volume :=
          MeasureTheory.setIntegral_congr_ae measurableSet_Ico
            (Filter.Eventually.of_forall (fun x hx => by rw [htail x hx]; ring))
      _ = 0 := by simp

/-- Product Fubini for coordinatewise factors on a finite real rectangle. -/
theorem realRectangle_product_integral_eq_prod {d : ℕ}
    (a b : Fin d → ℝ) (f : Fin d → ℝ → ℝ) :
    ∫ x : Fin d → ℝ, ∏ i, f i (x i) ∂Measure.pi
      (fun i => volume.restrict (Set.Ioc (a i) (b i))) =
      ∏ i, ∫ x in Set.Ioc (a i) (b i), f i x ∂volume := by
  simpa using (MeasureTheory.integral_fintype_prod_eq_prod
    (μ := fun i => volume.restrict (Set.Ioc (a i) (b i))) f)

/-- The affine product moment on a dyadic rectangle factors into the one-dimensional moments. -/
private theorem discrepancyIocRectangle_affine_moment {d : ℕ}
    (r k : Fin d → ℕ) :
    ∫ x : Fin d → ℝ, (∏ i, x i) * (∏ i, discrepancyIocDyadicHaar (r i) (k i) (x i))
      ∂Measure.pi (fun i => volume.restrict
        (Set.Ioc (realDyadicLeft (r i) (k i)) (realDyadicRight (r i) (k i)))) =
      ∏ i, (((2 : ℝ) ^ (r i))⁻¹ ^ 2 / 4) := by
  have hprod : (fun x : Fin d → ℝ =>
      (∏ i, x i) * (∏ i, discrepancyIocDyadicHaar (r i) (k i) (x i))) =
      (fun x => ∏ i, x i * discrepancyIocDyadicHaar (r i) (k i) (x i)) := by
    funext x
    rw [← Finset.prod_mul_distrib]
  rw [hprod, realRectangle_product_integral_eq_prod
    (a := fun i => realDyadicLeft (r i) (k i))
    (b := fun i => realDyadicRight (r i) (k i))
    (f := fun i x => x * discrepancyIocDyadicHaar (r i) (k i) x)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← MeasureTheory.integral_Ico_eq_integral_Ioc]
  exact discrepancyIocDyadicHaar_affine_moment (r i) (k i)

/-- An empty dyadic rectangle has only the negative affine term in its discrepancy Haar coefficient. -/
private theorem discrepancyIocEmptyRectangle_coefficient
    {d m : ℕ} (r k : Fin d → ℕ) (p : Fin m → Fin d → ℝ) (w : Fin m → ℝ)
    (hempty : ∀ i : Fin m, ¬ ∀ j : Fin d,
      p i j ∈ realDyadicInterval (r j) (k j)) :
    ∫ x : Fin d → ℝ,
      ((∑ i, w i * ∏ j, realPointTail (p i j) (x j)) - ∏ j, x j) *
        (∏ j, discrepancyIocDyadicHaar (r j) (k j) (x j))
      ∂Measure.pi (fun j => volume.restrict
        (Set.Ioc (realDyadicLeft (r j) (k j)) (realDyadicRight (r j) (k j)))) =
      - ∏ j, (((2 : ℝ) ^ (r j))⁻¹ ^ 2 / 4) := by
  classical
  let μ := Measure.pi (fun j : Fin d => volume.restrict
    (Set.Ioc (realDyadicLeft (r j) (k j)) (realDyadicRight (r j) (k j))))
  have hcoordAffine : ∀ j : Fin d,
      Integrable (fun x : ℝ => x * discrepancyIocDyadicHaar (r j) (k j) x)
        (volume.restrict (Set.Ioc (realDyadicLeft (r j) (k j))
          (realDyadicRight (r j) (k j)))) := by
    intro j
    apply integrableOn_Ioc_of_bound
      ((measurable_id.mul (measurable_realDyadicHaar (r j) (k j))) )
    intro x hx
    change realDyadicLeft (r j) (k j) < x ∧
      x ≤ realDyadicRight (r j) (k j) at hx
    have hxnorm : ‖x‖ ≤ |realDyadicLeft (r j) (k j)| +
        |realDyadicRight (r j) (k j)| + 1 := by
      rw [Real.norm_eq_abs]
      apply abs_le.mpr
      constructor
      · have hleft := neg_abs_le (realDyadicLeft (r j) (k j))
        have hbound : -( |realDyadicLeft (r j) (k j)| +
            |realDyadicRight (r j) (k j)| + 1) ≤ realDyadicLeft (r j) (k j) := by
          linarith [abs_nonneg (realDyadicRight (r j) (k j))]
        exact hbound.trans (le_of_lt hx.1)
      · have hright := le_abs_self (realDyadicRight (r j) (k j))
        have hbound : realDyadicRight (r j) (k j) ≤
            |realDyadicLeft (r j) (k j)| + |realDyadicRight (r j) (k j)| + 1 := by
          linarith [abs_nonneg (realDyadicLeft (r j) (k j))]
        exact hx.2.trans hbound
    have hC : 0 ≤ |realDyadicLeft (r j) (k j)| +
        |realDyadicRight (r j) (k j)| + 1 := by positivity
    calc
      ‖x * discrepancyIocDyadicHaar (r j) (k j) x‖ =
          ‖x‖ * ‖discrepancyIocDyadicHaar (r j) (k j) x‖ := norm_mul _ _
      _ ≤ (|realDyadicLeft (r j) (k j)| +
          |realDyadicRight (r j) (k j)| + 1) * 1 :=
            mul_le_mul hxnorm (norm_realDyadicHaar_le_one (r j) (k j) x)
              (norm_nonneg _) hC
      _ = |realDyadicLeft (r j) (k j)| +
          |realDyadicRight (r j) (k j)| + 1 := by ring
  have hcoordPoint : ∀ (i : Fin m) (j : Fin d),
      Integrable (fun x : ℝ => realPointTail (p i j) x * discrepancyIocDyadicHaar (r j) (k j) x)
        (volume.restrict (Set.Ioc (realDyadicLeft (r j) (k j))
          (realDyadicRight (r j) (k j)))) := by
    intro i j
    exact integrable_tailHaar_on_Ioc (p i j) (r j) (k j)
  have hAffineInt : Integrable
      (fun x : Fin d → ℝ =>
        (∏ j, x j) * (∏ j, discrepancyIocDyadicHaar (r j) (k j) (x j))) μ := by
    convert MeasureTheory.Integrable.fintype_prod hcoordAffine using 1
    funext x
    rw [← Finset.prod_mul_distrib]
  have hPointInt (i : Fin m) : Integrable
      (fun x : Fin d → ℝ =>
        ∏ j, realPointTail (p i j) (x j) * discrepancyIocDyadicHaar (r j) (k j) (x j)) μ := by
    exact MeasureTheory.Integrable.fintype_prod (hcoordPoint i)
  have hSumInt : Integrable
      (fun x : Fin d → ℝ =>
        ∑ i, w i * ∏ j, realPointTail (p i j) (x j) *
          discrepancyIocDyadicHaar (r j) (k j) (x j)) μ := by
    apply MeasureTheory.integrable_finsetSum (s := Finset.univ)
    intro i hi
    exact (hPointInt i).const_mul (w i)
  have hemptyTerm (i : Fin m) :
      ∫ x : Fin d → ℝ,
        ∏ j, realPointTail (p i j) (x j) * discrepancyIocDyadicHaar (r j) (k j) (x j) ∂μ = 0 := by
    rw [realRectangle_product_integral_eq_prod
      (a := fun j => realDyadicLeft (r j) (k j))
      (b := fun j => realDyadicRight (r j) (k j))
      (f := fun j x => realPointTail (p i j) x * discrepancyIocDyadicHaar (r j) (k j) x)]
    obtain ⟨j, hj⟩ : ∃ j : Fin d,
        p i j < realDyadicLeft (r j) (k j) ∨
          realDyadicRight (r j) (k j) ≤ p i j := by
      by_contra h
      push Not at h
      apply hempty i
      intro j
      simp only [realDyadicInterval, Set.mem_Ico]
      exact ⟨h j |>.1, h j |>.2⟩
    have hzero :
        ∫ x in Set.Ioc (realDyadicLeft (r j) (k j))
            (realDyadicRight (r j) (k j)),
          realPointTail (p i j) x * discrepancyIocDyadicHaar (r j) (k j) x ∂volume = 0 := by
      rw [← MeasureTheory.integral_Ico_eq_integral_Ioc]
      exact realPointTail_dyadicHaar_integral_eq_zero (r := r j) (k := k j) hj
    exact Finset.prod_eq_zero (Finset.mem_univ j) hzero
  change ∫ x : Fin d → ℝ,
      ((∑ i, w i * ∏ j, realPointTail (p i j) (x j)) - ∏ j, x j) *
        (∏ j, discrepancyIocDyadicHaar (r j) (k j) (x j)) ∂μ = _
  have hintegrand : ∀ x : Fin d → ℝ,
      ((∑ i, w i * ∏ j, realPointTail (p i j) (x j)) - ∏ j, x j) *
        (∏ j, discrepancyIocDyadicHaar (r j) (k j) (x j)) =
      (∑ i, w i * ∏ j,
        realPointTail (p i j) (x j) * discrepancyIocDyadicHaar (r j) (k j) (x j)) -
        (∏ j, x j) * (∏ j, discrepancyIocDyadicHaar (r j) (k j) (x j)) := by
    intro x
    rw [sub_mul, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      calc
        (w i * ∏ j, realPointTail (p i j) (x j)) *
            (∏ j, discrepancyIocDyadicHaar (r j) (k j) (x j)) =
          w i * ((∏ j, realPointTail (p i j) (x j)) *
            (∏ j, discrepancyIocDyadicHaar (r j) (k j) (x j))) := by ring
        _ = w i * ∏ j,
            realPointTail (p i j) (x j) * discrepancyIocDyadicHaar (r j) (k j) (x j) := by
          rw [← Finset.prod_mul_distrib]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hintegrand),
      MeasureTheory.integral_sub hSumInt hAffineInt,
      MeasureTheory.integral_finsetSum Finset.univ (by
        intro i hi
        exact (hPointInt i).const_mul (w i))]
  simp_rw [MeasureTheory.integral_const_mul, hemptyTerm]
  dsimp [μ]
  rw [discrepancyIocRectangle_affine_moment]
  simp

/-- The production `Ico` Haar and the integral-friendly `Ioc` expression
agree almost everywhere; their only differences are endpoints. -/
theorem realDyadicHaar_affine_moment (r k : ℕ) :
    ∫ x in realDyadicInterval r k, x * realDyadicHaar r k x ∂volume =
      ((2 : ℝ) ^ r)⁻¹ ^ 2 / 4 := by
  have hae : ∀ᵐ x ∂volume,
      x * realDyadicHaar r k x = x * discrepancyIocDyadicHaar r k x :=
    (discrepancyIocDyadicHaar_ae_eq_realDyadicHaar r k).symm.mono fun x h => by
      rw [h]
  change ∫ x in Set.Ico (realDyadicLeft r k) (realDyadicRight r k),
      x * realDyadicHaar r k x ∂volume = _
  rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ico
    (hae.mono fun x h _ => h)]
  simpa [realDyadicInterval, realDyadicLeft, realDyadicRight] using
    discrepancyIocDyadicHaar_affine_moment r k

private theorem realDyadicRectangleHaar_ae_eq_ioc {d : ℕ}
    (r k : Fin d → ℕ) :
    (fun x : Fin d → ℝ => ∏ j, realDyadicHaar (r j) (k j) (x j)) =ᵐ[
      Measure.pi (fun j => volume.restrict
        (Set.Ioc (realDyadicLeft (r j) (k j)) (realDyadicRight (r j) (k j))))]
    (fun x => ∏ j, discrepancyIocDyadicHaar (r j) (k j) (x j)) := by
  have hcoord : ∀ j : Fin d,
      realDyadicHaar (r j) (k j) =ᵐ[
        volume.restrict (Set.Ioc (realDyadicLeft (r j) (k j))
          (realDyadicRight (r j) (k j)))] discrepancyIocDyadicHaar (r j) (k j) := by
    intro j
    exact MeasureTheory.ae_restrict_of_ae
      (discrepancyIocDyadicHaar_ae_eq_realDyadicHaar (r j) (k j)).symm
  filter_upwards [Measure.ae_eq_pi hcoord] with x hx
  exact congrArg (fun f : Fin d → ℝ => ∏ j, f j) hx

/-- Product affine moment for the production Haar, obtained by transporting
the coordinate integrals across the measure-zero endpoint convention. -/
theorem realDyadicRectangle_affine_moment {d : ℕ}
    (r k : Fin d → ℕ) :
    ∫ x : Fin d → ℝ, (∏ i, x i) * (∏ i, realDyadicHaar (r i) (k i) (x i))
      ∂Measure.pi (fun i => volume.restrict
        (Set.Ioc (realDyadicLeft (r i) (k i)) (realDyadicRight (r i) (k i)))) =
      ∏ i, (((2 : ℝ) ^ (r i))⁻¹ ^ 2 / 4) := by
  have hae := realDyadicRectangleHaar_ae_eq_ioc r k
  have hmul : (fun x : Fin d → ℝ =>
      (∏ i, x i) * (∏ i, realDyadicHaar (r i) (k i) (x i))) =ᵐ[
        Measure.pi (fun i => volume.restrict
          (Set.Ioc (realDyadicLeft (r i) (k i)) (realDyadicRight (r i) (k i))))]
      (fun x => (∏ i, x i) *
        (∏ i, discrepancyIocDyadicHaar (r i) (k i) (x i))) :=
    hae.mono fun x hx => congrArg (HMul.hMul (∏ i, x i)) hx
  rw [MeasureTheory.integral_congr_ae hmul]
  exact discrepancyIocRectangle_affine_moment r k

/-- Empty-rectangle coefficient formula for the production real Haar.
Endpoint choices do not affect Lebesgue integrals. -/
theorem emptyRealDyadicRectangle_discrepancy_coefficient
    {d m : ℕ} (r k : Fin d → ℕ) (p : Fin m → Fin d → ℝ) (w : Fin m → ℝ)
    (hempty : ∀ i : Fin m, ¬ ∀ j : Fin d,
      p i j ∈ realDyadicInterval (r j) (k j)) :
    ∫ x : Fin d → ℝ,
      ((∑ i, w i * ∏ j, realPointTail (p i j) (x j)) - ∏ j, x j) *
        (∏ j, realDyadicHaar (r j) (k j) (x j))
      ∂Measure.pi (fun j => volume.restrict
        (Set.Ioc (realDyadicLeft (r j) (k j)) (realDyadicRight (r j) (k j)))) =
      - ∏ j, (((2 : ℝ) ^ (r j))⁻¹ ^ 2 / 4) := by
  have hae := realDyadicRectangleHaar_ae_eq_ioc r k
  have hmul : (fun x : Fin d → ℝ =>
      ((∑ i, w i * ∏ j, realPointTail (p i j) (x j)) - ∏ j, x j) *
        (∏ j, realDyadicHaar (r j) (k j) (x j))) =ᵐ[
        Measure.pi (fun j => volume.restrict
          (Set.Ioc (realDyadicLeft (r j) (k j)) (realDyadicRight (r j) (k j))))]
      (fun x =>
        ((∑ i, w i * ∏ j, realPointTail (p i j) (x j)) - ∏ j, x j) *
          (∏ j, discrepancyIocDyadicHaar (r j) (k j) (x j))) :=
    hae.mono fun x hx => congrArg
      (HMul.hMul ((∑ i, w i * ∏ j, realPointTail (p i j) (x j)) - ∏ j, x j)) hx
  rw [MeasureTheory.integral_congr_ae hmul]
  exact discrepancyIocEmptyRectangle_coefficient r k p w hempty

end HaarQuarter
