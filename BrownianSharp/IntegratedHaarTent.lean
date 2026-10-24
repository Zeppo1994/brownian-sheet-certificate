import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic
import BrownianSharp.DyadicRealCells

/-! Deterministic integrated one-dimensional Haar tents. -/

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace HaarQuarter

/-- The open interior of the level-`r`, cell-`c` dyadic interval. -/
noncomputable def integratedTentDyadicOpenInterval (r c : ℕ) : Set ℝ :=
  Set.Ioo ((c : ℝ) / (2 : ℝ) ^ r)
    (((c : ℝ) + 1) / (2 : ℝ) ^ r)

noncomputable def integratedTentDyadicLeft (r c : ℕ) : ℝ :=
  (c : ℝ) / (2 : ℝ) ^ r

noncomputable def integratedTentDyadicRight (r c : ℕ) : ℝ :=
  ((c : ℝ) + 1) / (2 : ℝ) ^ r

/-- Distinct cells at a common dyadic level have disjoint open interiors. -/
theorem integratedTentDyadicOpenInterval_disjoint_of_ne
    {r c c' : ℕ} (hne : c ≠ c') :
    Disjoint (integratedTentDyadicOpenInterval r c)
      (integratedTentDyadicOpenInterval r c') := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rcases lt_or_gt_of_ne hne with hcc' | hc'c
  · have hnat : c + 1 ≤ c' := Nat.succ_le_of_lt hcc'
    have hcast : (c : ℝ) + 1 ≤ (c' : ℝ) := by exact_mod_cast hnat
    have hden : 0 < (2 : ℝ) ^ r := by positivity
    have hend : ((c : ℝ) + 1) / (2 : ℝ) ^ r ≤ (c' : ℝ) / (2 : ℝ) ^ r :=
      (div_le_div_iff₀ hden hden).2 (mul_le_mul_of_nonneg_right hcast (le_of_lt hden))
    exact (not_lt_of_ge hend) (lt_trans hx'.1 hx.2)
  · have hnat : c' + 1 ≤ c := Nat.succ_le_of_lt hc'c
    have hcast : (c' : ℝ) + 1 ≤ (c : ℝ) := by exact_mod_cast hnat
    have hden : 0 < (2 : ℝ) ^ r := by positivity
    have hend : ((c' : ℝ) + 1) / (2 : ℝ) ^ r ≤ (c : ℝ) / (2 : ℝ) ^ r :=
      (div_le_div_iff₀ hden hden).2 (mul_le_mul_of_nonneg_right hcast (le_of_lt hden))
    exact (not_lt_of_ge hend) (lt_trans hx.1 hx'.2)

/-- The positive geometric tent associated to a mean-zero Haar step. For the
repository's `+`-on-right Haar convention its primitive from the left endpoint
is the negative of this function. Here `a < m < b` and `m` is the midpoint. -/
noncomputable def integratedHaarTent (a m b x : ℝ) : ℝ :=
  (Set.Ioc a m).indicator (fun y => y - a) x +
    (Set.Ioc m b).indicator (fun y => b - y) x

/-- For a midpoint, the indicator formula is the continuous positive-part
tent `max 0 (min (x-a) (b-x))`. -/
theorem integratedHaarTent_eq_max_min {a b x : ℝ} (hab : a < b) :
    integratedHaarTent a ((a + b) / 2) b x = max 0 (min (x - a) (b - x)) := by
  let m : ℝ := (a + b) / 2
  have ham : a < m := by dsimp [m]; linarith
  have hmb : m < b := by dsimp [m]; linarith
  by_cases hxm : x ≤ m
  · by_cases hax : a < x
    · have hmx : x - a ≤ b - x := by dsimp [m] at hxm; linarith
      unfold integratedHaarTent
      simp [Set.mem_Ioc, m, hax, hxm,
        max_eq_right (sub_nonneg.mpr (le_of_lt hax)), min_eq_left hmx]
    · have hxa : x ≤ a := le_of_not_gt hax
      unfold integratedHaarTent
      have hmin : min (x - a) (b - x) ≤ 0 := le_trans (min_le_left _ _) (sub_nonpos.mpr hxa)
      simp [Set.mem_Ioc, m, hax, hxm, hxa, max_eq_left hmin]
  · have hmx : m < x := lt_of_not_ge hxm
    by_cases hxb : x < b
    · have hmin : b - x ≤ x - a := by dsimp [m] at hmx; linarith
      have hax : a < x := lt_trans ham hmx
      unfold integratedHaarTent
      simp [Set.mem_Ioc, m, hax, hxm, hxb, hxb.le,
        max_eq_right (sub_nonneg.mpr hxb.le), min_eq_right hmin]
    · have hbx : b ≤ x := le_of_not_gt hxb
      by_cases hxeq : x = b
      · subst x
        unfold integratedHaarTent
        simp [Set.mem_Ioc, m, hmb]
      · have hb_lt : b < x := lt_of_le_of_ne hbx (Ne.symm hxeq)
        unfold integratedHaarTent
        have hmin : min (x - a) (b - x) ≤ 0 := le_trans (min_le_right _ _) (sub_nonpos.mpr hbx)
        simp [Set.mem_Ioc, m, hxm, hbx, hb_lt, max_eq_left hmin]

/-- Continuous positive-part version of the midpoint tent. -/
noncomputable def continuousIntegratedTent (a b x : ℝ) : ℝ :=
  max 0 (min (x - a) (b - x))

@[fun_prop]
theorem continuous_continuousIntegratedTent (a b : ℝ) :
    Continuous (continuousIntegratedTent a b) := by
  unfold continuousIntegratedTent
  fun_prop

theorem continuousIntegratedTent_eq_zero_of_not_mem {a b x : ℝ}
    (hx : x ∉ Set.Icc a b) : continuousIntegratedTent a b x = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rcases hx with hxa | hxb
  · have hmin : min (x - a) (b - x) ≤ 0 :=
      le_trans (min_le_left _ _) (sub_nonpos.mpr (le_of_lt hxa))
    simp [continuousIntegratedTent, max_eq_left hmin]
  · have hmin : min (x - a) (b - x) ≤ 0 :=
      le_trans (min_le_right _ _) (sub_nonpos.mpr (le_of_lt hxb))
    simp [continuousIntegratedTent, max_eq_left hmin]

theorem continuousIntegratedTent_hasCompactSupport (a b : ℝ) :
    HasCompactSupport (continuousIntegratedTent a b) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  apply Function.support_subset_iff'.2
  intro x hx
  exact continuousIntegratedTent_eq_zero_of_not_mem hx

theorem continuousIntegratedTent_memLp_two (a b : ℝ) :
    MemLp (continuousIntegratedTent a b) 2 volume := by
  exact (continuous_continuousIntegratedTent a b).memLp_of_hasCompactSupport
    (continuousIntegratedTent_hasCompactSupport a b)

/-- Continuous tensor tent on a finite-dimensional Euclidean product. -/
noncomputable def continuousTensorIntegratedTent {d : ℕ}
    (a b : Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∏ i, continuousIntegratedTent (a i) (b i) (x i)

theorem continuous_continuousTensorIntegratedTent {d : ℕ} (a b : Fin d → ℝ) :
    Continuous (continuousTensorIntegratedTent a b) := by
  unfold continuousTensorIntegratedTent
  fun_prop

theorem continuousTensorIntegratedTent_hasCompactSupport {d : ℕ}
    (a b : Fin d → ℝ) :
    HasCompactSupport (continuousTensorIntegratedTent a b) := by
  let box : Set (Fin d → ℝ) := Set.pi Set.univ (fun i => Set.Icc (a i) (b i))
  have hbox : IsCompact box := by
    apply isCompact_univ_pi
    intro i
    exact isCompact_Icc
  apply HasCompactSupport.of_support_subset_isCompact hbox
  apply Function.support_subset_iff'.2
  intro x hx
  have hnot : ¬ ∀ i, x i ∈ Set.Icc (a i) (b i) := by
    intro hall
    apply hx
    exact Set.mem_pi.mpr (by intro i hi; exact hall i)
  obtain ⟨i, hi⟩ := not_forall.mp hnot
  unfold continuousTensorIntegratedTent
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (continuousIntegratedTent_eq_zero_of_not_mem hi)

theorem continuousTensorIntegratedTent_memLp_two {d : ℕ}
    (a b : Fin d → ℝ) :
    MemLp (continuousTensorIntegratedTent a b) 2
      (Measure.pi fun _ : Fin d => volume) := by
  exact (continuous_continuousTensorIntegratedTent a b).memLp_of_hasCompactSupport
    (continuousTensorIntegratedTent_hasCompactSupport a b)

theorem integratedHaarTent_sq_eq_indicator_sum (a m b x : ℝ) :
    integratedHaarTent a m b x ^ 2 =
      (Set.Ioc a m).indicator (fun y => (y - a) ^ 2) x +
        (Set.Ioc m b).indicator (fun y => (b - y) ^ 2) x := by
  unfold integratedHaarTent
  by_cases h₁ : x ∈ Set.Ioc a m <;>
    by_cases h₂ : x ∈ Set.Ioc m b
  · have : False := by exact not_lt_of_ge h₁.2 h₂.1
    exact this.elim
  · simp [h₁, h₂]
  · simp [h₁, h₂]
  · simp [h₁, h₂]

private theorem integral_Ioc_sub_sq {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, (x - a) ^ 2 ∂volume = (b - a) ^ 3 / 3 := by
  rw [← intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun x : ℝ => (x - a) ^ 3 / 3)
    (f' := fun x => (x - a) ^ 2) hab
    (by fun_prop)
    (fun x hx => by
      have hbase : HasDerivAt (fun y : ℝ => y ^ 3)
          (3 * (x - a) ^ 2) (x - a) := by
        simpa using (hasDerivAt_pow 3 (x - a))
      have hpow := (hbase.div_const (3 : ℝ)).comp x
        ((hasDerivAt_id x).sub_const a)
      simpa [Function.comp_def] using hpow)
    ((continuousOn_id.sub continuousOn_const).pow 2).intervalIntegrable]
  ring

private theorem integral_Ioc_sq_sub {a b : ℝ} (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, (b - x) ^ 2 ∂volume = (b - a) ^ 3 / 3 := by
  rw [← intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f := fun x : ℝ => -((b - x) ^ 3) / 3)
    (f' := fun x => (b - x) ^ 2) hab
    (by fun_prop)
    (fun x hx => by
      have hbase : HasDerivAt (fun y : ℝ => y ^ 3)
          (3 * (b - x) ^ 2) (b - x) := by
        simpa using (hasDerivAt_pow 3 (b - x))
      have hpow := (hbase.neg.div_const (3 : ℝ)).comp x
        ((hasDerivAt_const x b).sub (hasDerivAt_id x))
      convert hpow using 1
      · funext y
        simp
      · ring)
    ((continuousOn_const.sub continuousOn_id).pow 2).intervalIntegrable]
  ring

/-- Squared area under the integrated Haar tent.  At the Haar midpoint,
both halves have width `(b-a)/2`, giving the exact factor `1/12`. -/
theorem integratedHaarTent_sq_integral {a b : ℝ} (hab : a < b) :
    ∫ x, integratedHaarTent a ((a + b) / 2) b x ^ 2 ∂volume =
      (b - a) ^ 3 / 12 := by
  let m : ℝ := (a + b) / 2
  have ham : a ≤ m := by dsimp [m]; linarith
  have hmb : m ≤ b := by dsimp [m]; linarith
  have hleft : Integrable
      ((Set.Ioc a m).indicator (fun x : ℝ => (x - a) ^ 2)) volume := by
    have hpoly : IntegrableOn (fun x : ℝ => (x - a) ^ 2) (Set.Ioc a m) volume :=
      (((continuousOn_id.sub continuousOn_const).pow 2).integrableOn_compact
        isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    exact hpoly.integrable_indicator measurableSet_Ioc
  have hright : Integrable
      ((Set.Ioc m b).indicator (fun x : ℝ => (b - x) ^ 2)) volume := by
    have hpoly : IntegrableOn (fun x : ℝ => (b - x) ^ 2) (Set.Ioc m b) volume :=
      (((continuousOn_const.sub continuousOn_id).pow 2).integrableOn_compact
        isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
    exact hpoly.integrable_indicator measurableSet_Ioc
  change ∫ x, integratedHaarTent a m b x ^ 2 ∂volume = _
  calc
    ∫ x, integratedHaarTent a m b x ^ 2 ∂volume =
        ∫ x, (Set.Ioc a m).indicator (fun y => (y - a) ^ 2) x +
          (Set.Ioc m b).indicator (fun y => (b - y) ^ 2) x ∂volume := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (integratedHaarTent_sq_eq_indicator_sum a m b)
    _ = ∫ x, (Set.Ioc a m).indicator (fun y => (y - a) ^ 2) x ∂volume +
        ∫ x, (Set.Ioc m b).indicator (fun y => (b - y) ^ 2) x ∂volume :=
      integral_add hleft hright
    _ = _ := by
      rw [integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc,
        integral_Ioc_sub_sq ham, integral_Ioc_sq_sub hmb]
      dsimp [m]
      field_simp
      ring

/-- The integrated tent is supported on its dyadic interval. -/
theorem integratedHaarTent_eq_zero_of_not_mem {a m b x : ℝ}
    (ham : a ≤ m) (hmb : m ≤ b)
    (hx : x ∉ Set.Icc a b) : integratedHaarTent a m b x = 0 := by
  unfold integratedHaarTent
  have h₁ : x ∉ Set.Ioc a m := by
    intro h
    exact hx ⟨le_of_lt h.1, le_trans h.2 hmb⟩
  have h₂ : x ∉ Set.Ioc m b := by
    intro h
    exact hx ⟨le_trans ham (le_of_lt h.1), h.2⟩
  simp [h₁, h₂]

/-- The tent vanishes outside the open interval, including both endpoints. -/
theorem integratedHaarTent_eq_zero_of_not_mem_open {a m b x : ℝ}
    (ham : a < m) (hmb : m < b)
    (hx : x ∉ Set.Ioo a b) : integratedHaarTent a m b x = 0 := by
  by_cases hxb : x = b
  · subst x
    unfold integratedHaarTent
    have hnot : b ∉ Set.Ioc a m := by
      simp only [Set.mem_Ioc, not_and]
      intro _ h
      linarith
    simp [hnot]
  unfold integratedHaarTent
  have h₁ : x ∉ Set.Ioc a m := by
    intro h
    exact hx ⟨h.1, lt_of_le_of_lt h.2 hmb⟩
  have h₂ : x ∉ Set.Ioc m b := by
    intro h
    exact hx ⟨lt_trans ham h.1, lt_of_le_of_ne h.2 hxb⟩
  simp [h₁, h₂]

/-- Tents with disjoint open supports are pointwise orthogonal. -/
theorem integratedHaarTent_mul_eq_zero_of_disjoint_support
    {a m b c n d x : ℝ}
    (ham : a < m) (hmb : m < b) (hcn : c < n) (hnd : n < d)
    (hdisj : Disjoint (Set.Ioo a b) (Set.Ioo c d)) :
    integratedHaarTent a m b x * integratedHaarTent c n d x = 0 := by
  by_cases h₁ : integratedHaarTent a m b x = 0
  · simp [h₁]
  by_cases h₂ : integratedHaarTent c n d x = 0
  · simp [h₂]
  have hx₁ : x ∈ Set.Ioo a b := by
    by_contra hx
    exact h₁ (integratedHaarTent_eq_zero_of_not_mem_open ham hmb hx)
  have hx₂ : x ∈ Set.Ioo c d := by
    by_contra hx
    exact h₂ (integratedHaarTent_eq_zero_of_not_mem_open hcn hnd hx)
  exact (Set.disjoint_left.mp hdisj hx₁ hx₂).elim

/-- The integral of the product of tents with disjoint open supports is zero. -/
theorem integratedHaarTent_inner_eq_zero_of_disjoint_support
    {a m b c n d : ℝ}
    (ham : a < m) (hmb : m < b) (hcn : c < n) (hnd : n < d)
    (hdisj : Disjoint (Set.Ioo a b) (Set.Ioo c d)) :
    ∫ x, integratedHaarTent a m b x * integratedHaarTent c n d x ∂volume = 0 := by
  have hzero : (fun x : ℝ => integratedHaarTent a m b x *
      integratedHaarTent c n d x) = 0 := by
    funext x
    exact integratedHaarTent_mul_eq_zero_of_disjoint_support
      ham hmb hcn hnd hdisj
  rw [hzero]
  simp

/-- Same-level dyadic integrated tents are orthogonal when their cells differ. -/
theorem integratedTentDyadic_inner_eq_zero_of_ne
    {r c c' : ℕ} (hne : c ≠ c') :
    ∫ x, integratedHaarTent (integratedTentDyadicLeft r c)
        ((integratedTentDyadicLeft r c + integratedTentDyadicRight r c) / 2)
        (integratedTentDyadicRight r c) x *
      integratedHaarTent (integratedTentDyadicLeft r c')
        ((integratedTentDyadicLeft r c' + integratedTentDyadicRight r c') / 2)
        (integratedTentDyadicRight r c') x ∂volume = 0 := by
  have hlen : integratedTentDyadicLeft r c < integratedTentDyadicRight r c := by
    dsimp [integratedTentDyadicLeft, integratedTentDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hlen' : integratedTentDyadicLeft r c' < integratedTentDyadicRight r c' := by
    dsimp [integratedTentDyadicLeft, integratedTentDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmid₁ : integratedTentDyadicLeft r c <
      (integratedTentDyadicLeft r c + integratedTentDyadicRight r c) / 2 := by
    linarith
  have hmid₂ : (integratedTentDyadicLeft r c + integratedTentDyadicRight r c) / 2 <
      integratedTentDyadicRight r c := by linarith
  have hmid₁' : integratedTentDyadicLeft r c' <
      (integratedTentDyadicLeft r c' + integratedTentDyadicRight r c') / 2 := by
    linarith
  have hmid₂' : (integratedTentDyadicLeft r c' + integratedTentDyadicRight r c') / 2 <
      integratedTentDyadicRight r c' := by linarith
  exact integratedHaarTent_inner_eq_zero_of_disjoint_support
    hmid₁ hmid₂ hmid₁' hmid₂'
    (by simpa [integratedTentDyadicOpenInterval, integratedTentDyadicLeft,
      integratedTentDyadicRight] using integratedTentDyadicOpenInterval_disjoint_of_ne hne)

/-- Tensor product of one-dimensional integrated Haar tents on a finite
product Euclidean space. -/
noncomputable def tensorIntegratedHaarTent {d : ℕ}
    (a m b : Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∏ i, integratedHaarTent (a i) (m i) (b i) (x i)

/-- Exact tensor-product squared norm, before simplifying the product of
side lengths. This is the finite-dimensional Fubini bridge used for Brownian
sheet Haar integrands. -/
theorem tensorIntegratedHaarTent_sq_integral {d : ℕ}
    (a m b : Fin d → ℝ) (hleft : ∀ i, a i < m i)
    (hright : ∀ i, m i < b i)
    (hmid : ∀ i, m i = (a i + b i) / 2) :
    ∫ x : Fin d → ℝ, tensorIntegratedHaarTent a m b x ^ 2 ∂
        (Measure.pi fun _ : Fin d => volume) =
      ∏ i, ((b i - a i) ^ 3 / 12) := by
  rw [show (fun x : Fin d → ℝ => tensorIntegratedHaarTent a m b x ^ 2) =
      (fun x => ∏ i, integratedHaarTent (a i) (m i) (b i) (x i) ^ 2) by
        funext x
        simp [tensorIntegratedHaarTent, Finset.prod_pow]]
  convert (integral_fintype_prod_eq_prod
    (f := fun i y => integratedHaarTent (a i) (m i) (b i) y ^ 2)
    (μ := fun _ : Fin d => (volume : Measure ℝ))) using 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hmid i]
    exact (integratedHaarTent_sq_integral (lt_trans (hleft i) (hright i))).symm

/-- Same norm identity in the manuscript's `12^{-d}|R|^3` form. -/
theorem tensorIntegratedHaarTent_sq_integral_eq_volume_cubed {d : ℕ}
    (a m b : Fin d → ℝ) (hleft : ∀ i, a i < m i)
    (hright : ∀ i, m i < b i)
    (hmid : ∀ i, m i = (a i + b i) / 2) :
    ∫ x : Fin d → ℝ, tensorIntegratedHaarTent a m b x ^ 2 ∂
        (Measure.pi fun _ : Fin d => volume) =
      (∏ i, (b i - a i)) ^ 3 / (12 : ℝ) ^ d := by
  rw [tensorIntegratedHaarTent_sq_integral a m b hleft hright hmid]
  rw [Finset.prod_div_distrib, ← Finset.prod_pow]
  simp

/-- The indicator-form tensor tent belongs to the Brownian sheet's L²
integrand space; we obtain this from its continuous compactly supported
midpoint representative. -/
theorem tensorIntegratedHaarTent_memLp_two {d : ℕ}
    (a m b : Fin d → ℝ) (hab : ∀ i, a i < b i)
    (hmid : ∀ i, m i = (a i + b i) / 2) :
    MemLp (tensorIntegratedHaarTent a m b) 2
      (Measure.pi fun _ : Fin d => volume) := by
  have hpoint : ∀ x, tensorIntegratedHaarTent a m b x =
      continuousTensorIntegratedTent a b x := by
    intro x
    simp [tensorIntegratedHaarTent, continuousTensorIntegratedTent,
      continuousIntegratedTent, integratedHaarTent_eq_max_min, hab, hmid]
  exact (memLp_congr_ae (Filter.Eventually.of_forall hpoint)).2
    (continuousTensorIntegratedTent_memLp_two a b)

/-- The tensor tent represented as an element of the real Hilbert space
`L²(volume)`. -/
noncomputable def tensorIntegratedHaarTentLp {d : ℕ}
    (a m b : Fin d → ℝ) (hab : ∀ i, a i < b i)
    (hmid : ∀ i, m i = (a i + b i) / 2) :
    Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) :=
  (tensorIntegratedHaarTent_memLp_two a m b hab hmid).toLp
    (tensorIntegratedHaarTent a m b)

/-- The Hilbert inner product of the L² representative is its ordinary
integral inner product. -/
theorem tensorIntegratedHaarTentLp_inner_self {d : ℕ}
    (a m b : Fin d → ℝ) (hab : ∀ i, a i < b i)
    (hmid : ∀ i, m i = (a i + b i) / 2) :
    ⟪tensorIntegratedHaarTentLp a m b hab hmid,
      tensorIntegratedHaarTentLp a m b hab hmid⟫ =
      ∫ x : Fin d → ℝ, tensorIntegratedHaarTent a m b x ^ 2 ∂
        (Measure.pi fun _ : Fin d => volume) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (tensorIntegratedHaarTent_memLp_two a m b hab hmid)]
    with x hx
  simp [tensorIntegratedHaarTentLp, hx, real_inner_self_eq_norm_sq]

/-- The represented L² tent has the manuscript's exact squared norm. -/
theorem tensorIntegratedHaarTentLp_inner_self_eq_volume_cubed {d : ℕ}
    (a m b : Fin d → ℝ) (hab : ∀ i, a i < b i)
    (hmid : ∀ i, m i = (a i + b i) / 2) :
    ⟪tensorIntegratedHaarTentLp a m b hab hmid,
      tensorIntegratedHaarTentLp a m b hab hmid⟫ =
      (∏ i, (b i - a i)) ^ 3 / (12 : ℝ) ^ d := by
  have hleft : ∀ i, a i < m i := by
    intro i
    rw [hmid i]
    linarith [hab i]
  have hright : ∀ i, m i < b i := by
    intro i
    rw [hmid i]
    linarith [hab i]
  rw [tensorIntegratedHaarTentLp_inner_self a m b hab hmid]
  exact tensorIntegratedHaarTent_sq_integral_eq_volume_cubed
    a m b hleft hright hmid

/-- Two tensor tents have pointwise disjoint support whenever one coordinate
has disjoint open intervals. -/
theorem tensorIntegratedHaarTent_mul_eq_zero_of_coordinate_disjoint {d : ℕ}
    (a m b c n q : Fin d → ℝ) (j : Fin d)
    (ham : a j < m j) (hmb : m j < b j)
    (hcn : c j < n j) (hnq : n j < q j)
    (hdisj : Disjoint (Set.Ioo (a j) (b j)) (Set.Ioo (c j) (q j))) :
    ∀ x, tensorIntegratedHaarTent a m b x *
        tensorIntegratedHaarTent c n q x = 0 := by
  intro x
  unfold tensorIntegratedHaarTent
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  exact integratedHaarTent_mul_eq_zero_of_disjoint_support
    ham hmb hcn hnq hdisj

/-- The corresponding tensor-product inner product vanishes. -/
theorem tensorIntegratedHaarTent_inner_eq_zero_of_coordinate_disjoint {d : ℕ}
    (a m b c n q : Fin d → ℝ) (j : Fin d)
    (ham : a j < m j) (hmb : m j < b j)
    (hcn : c j < n j) (hnq : n j < q j)
    (hdisj : Disjoint (Set.Ioo (a j) (b j)) (Set.Ioo (c j) (q j))) :
    ∫ x : Fin d → ℝ,
        tensorIntegratedHaarTent a m b x *
          tensorIntegratedHaarTent c n q x ∂(Measure.pi fun _ : Fin d => volume) = 0 := by
  have hzero : (fun x : Fin d → ℝ => tensorIntegratedHaarTent a m b x *
      tensorIntegratedHaarTent c n q x) = 0 := by
    funext x
    exact tensorIntegratedHaarTent_mul_eq_zero_of_coordinate_disjoint
      a m b c n q j ham hmb hcn hnq hdisj x
  rw [hzero]
  simp

/-- Product integrated tent for a dyadic rectangle shape and cell vector. -/
noncomputable def tensorIntegratedTentDyadic {d : ℕ}
    (profile cells : Fin d → ℕ) (x : Fin d → ℝ) : ℝ :=
  ∏ i, integratedHaarTent (integratedTentDyadicLeft (profile i) (cells i))
    ((integratedTentDyadicLeft (profile i) (cells i) +
      integratedTentDyadicRight (profile i) (cells i)) / 2)
    (integratedTentDyadicRight (profile i) (cells i)) (x i)

/-- The exact Brownian-sheet squared norm for a dyadic product rectangle of
arbitrary coordinate profile. -/
theorem tensorIntegratedTentDyadic_sq_integral {d : ℕ}
    (profile cells : Fin d → ℕ) :
    ∫ x : Fin d → ℝ, tensorIntegratedTentDyadic profile cells x ^ 2 ∂
        (Measure.pi fun _ : Fin d => volume) =
      (∏ i, (integratedTentDyadicRight (profile i) (cells i) -
        integratedTentDyadicLeft (profile i) (cells i))) ^ 3 / (12 : ℝ) ^ d := by
  have hlen : ∀ i, integratedTentDyadicLeft (profile i) (cells i) <
      integratedTentDyadicRight (profile i) (cells i) := by
    intro i
    dsimp [integratedTentDyadicLeft, integratedTentDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hleft : ∀ i, integratedTentDyadicLeft (profile i) (cells i) <
      (integratedTentDyadicLeft (profile i) (cells i) +
        integratedTentDyadicRight (profile i) (cells i)) / 2 := by
    intro i
    linarith [hlen i]
  have hright : ∀ i,
      (integratedTentDyadicLeft (profile i) (cells i) +
        integratedTentDyadicRight (profile i) (cells i)) / 2 <
      integratedTentDyadicRight (profile i) (cells i) := by
    intro i
    linarith [hlen i]
  simpa [tensorIntegratedTentDyadic, tensorIntegratedHaarTent] using
    (tensorIntegratedHaarTent_sq_integral_eq_volume_cubed
      (a := fun i => integratedTentDyadicLeft (profile i) (cells i))
      (m := fun i => (integratedTentDyadicLeft (profile i) (cells i) +
        integratedTentDyadicRight (profile i) (cells i)) / 2)
      (b := fun i => integratedTentDyadicRight (profile i) (cells i))
      hleft hright (fun _ => rfl))

/-- Distinct cell vectors at a fixed shape produce orthogonal tensor tents. -/
theorem tensorIntegratedTentDyadic_inner_eq_zero_of_coordinate_ne {d : ℕ}
    (profile cells cells' : Fin d → ℕ) (j : Fin d) (hne : cells j ≠ cells' j) :
    ∫ x : Fin d → ℝ,
      tensorIntegratedTentDyadic profile cells x *
        tensorIntegratedTentDyadic profile cells' x ∂
          (Measure.pi fun _ : Fin d => volume) = 0 := by
  have hlen : integratedTentDyadicLeft (profile j) (cells j) <
      integratedTentDyadicRight (profile j) (cells j) := by
    dsimp [integratedTentDyadicLeft, integratedTentDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hlen' : integratedTentDyadicLeft (profile j) (cells' j) <
      integratedTentDyadicRight (profile j) (cells' j) := by
    dsimp [integratedTentDyadicLeft, integratedTentDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmid₁ : integratedTentDyadicLeft (profile j) (cells j) <
      (integratedTentDyadicLeft (profile j) (cells j) +
        integratedTentDyadicRight (profile j) (cells j)) / 2 := by
    linarith
  have hmid₂ : (integratedTentDyadicLeft (profile j) (cells j) +
      integratedTentDyadicRight (profile j) (cells j)) / 2 <
      integratedTentDyadicRight (profile j) (cells j) := by
    linarith
  have hmid₁' : integratedTentDyadicLeft (profile j) (cells' j) <
      (integratedTentDyadicLeft (profile j) (cells' j) +
        integratedTentDyadicRight (profile j) (cells' j)) / 2 := by
    linarith
  have hmid₂' : (integratedTentDyadicLeft (profile j) (cells' j) +
      integratedTentDyadicRight (profile j) (cells' j)) / 2 <
      integratedTentDyadicRight (profile j) (cells' j) := by
    linarith
  have hdisj : Disjoint
      (Set.Ioo (integratedTentDyadicLeft (profile j) (cells j))
        (integratedTentDyadicRight (profile j) (cells j)))
      (Set.Ioo (integratedTentDyadicLeft (profile j) (cells' j))
        (integratedTentDyadicRight (profile j) (cells' j))) := by
    simpa [integratedTentDyadicOpenInterval, integratedTentDyadicLeft,
      integratedTentDyadicRight] using integratedTentDyadicOpenInterval_disjoint_of_ne hne
  simpa [tensorIntegratedTentDyadic, tensorIntegratedHaarTent] using
    (tensorIntegratedHaarTent_inner_eq_zero_of_coordinate_disjoint
      (a := fun i => integratedTentDyadicLeft (profile i) (cells i))
      (m := fun i => (integratedTentDyadicLeft (profile i) (cells i) +
        integratedTentDyadicRight (profile i) (cells i)) / 2)
      (b := fun i => integratedTentDyadicRight (profile i) (cells i))
      (c := fun i => integratedTentDyadicLeft (profile i) (cells' i))
      (n := fun i => (integratedTentDyadicLeft (profile i) (cells' i) +
        integratedTentDyadicRight (profile i) (cells' i)) / 2)
      (q := fun i => integratedTentDyadicRight (profile i) (cells' i))
      j hmid₁ hmid₂ hmid₁' hmid₂' hdisj)

/-- The dyadic product tent as an element of the Brownian sheet integrand
Hilbert space `L²([0,1]^d)`. -/
noncomputable def tensorIntegratedTentDyadicLp {d : ℕ}
    (profile cells : Fin d → ℕ) :
    Lp ℝ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))) := by
  let a : Fin d → ℝ := fun i => integratedTentDyadicLeft (profile i) (cells i)
  let b : Fin d → ℝ := fun i => integratedTentDyadicRight (profile i) (cells i)
  let m : Fin d → ℝ := fun i => (a i + b i) / 2
  have hab : ∀ i, a i < b i := by
    intro i
    dsimp [a, b, integratedTentDyadicLeft, integratedTentDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmid : ∀ i, m i = (a i + b i) / 2 := by intro i; rfl
  exact tensorIntegratedHaarTentLp a m b hab hmid

/-- Exact Hilbert norm of a dyadic tensor tent, before simplification to the
rectangle-volume notation. -/
theorem tensorIntegratedTentDyadicLp_inner_self {d : ℕ}
    (profile cells : Fin d → ℕ) :
    ⟪tensorIntegratedTentDyadicLp profile cells,
      tensorIntegratedTentDyadicLp profile cells⟫ =
      (∏ i, (integratedTentDyadicRight (profile i) (cells i) -
        integratedTentDyadicLeft (profile i) (cells i))) ^ 3 / (12 : ℝ) ^ d := by
  let a : Fin d → ℝ := fun i => integratedTentDyadicLeft (profile i) (cells i)
  let b : Fin d → ℝ := fun i => integratedTentDyadicRight (profile i) (cells i)
  let m : Fin d → ℝ := fun i => (a i + b i) / 2
  have hab : ∀ i, a i < b i := by
    intro i
    dsimp [a, b, integratedTentDyadicLeft, integratedTentDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmid : ∀ i, m i = (a i + b i) / 2 := by intro i; rfl
  change ⟪tensorIntegratedHaarTentLp a m b hab hmid,
    tensorIntegratedHaarTentLp a m b hab hmid⟫ = _
  rw [tensorIntegratedHaarTentLp_inner_self_eq_volume_cubed a m b hab hmid]

/-- At a fixed rectangle shape, distinct dyadic cells give orthogonal vectors
in the actual `L²` integrand space. -/
theorem tensorIntegratedTentDyadicLp_inner_eq_zero_of_coordinate_ne {d : ℕ}
    (profile cells cells' : Fin d → ℕ) (j : Fin d)
    (hne : cells j ≠ cells' j) :
    ⟪tensorIntegratedTentDyadicLp profile cells,
      tensorIntegratedTentDyadicLp profile cells'⟫ = 0 := by
  rw [L2.inner_def]
  have htent := tensorIntegratedTentDyadic_inner_eq_zero_of_coordinate_ne
    profile cells cells' j hne
  have hmem := tensorIntegratedHaarTent_memLp_two
    (a := fun i => integratedTentDyadicLeft (profile i) (cells i))
    (m := fun i => (integratedTentDyadicLeft (profile i) (cells i) +
      integratedTentDyadicRight (profile i) (cells i)) / 2)
    (b := fun i => integratedTentDyadicRight (profile i) (cells i))
    (hab := by
      intro i
      dsimp [integratedTentDyadicLeft, integratedTentDyadicRight]
      apply div_lt_div_of_pos_right
      · norm_num
      · positivity)
    (hmid := fun _ => rfl)
  have hmem' := tensorIntegratedHaarTent_memLp_two
    (a := fun i => integratedTentDyadicLeft (profile i) (cells' i))
    (m := fun i => (integratedTentDyadicLeft (profile i) (cells' i) +
      integratedTentDyadicRight (profile i) (cells' i)) / 2)
    (b := fun i => integratedTentDyadicRight (profile i) (cells' i))
    (hab := by
      intro i
      dsimp [integratedTentDyadicLeft, integratedTentDyadicRight]
      apply div_lt_div_of_pos_right
      · norm_num
      · positivity)
    (hmid := fun _ => rfl)
  have hLpCoe : ∀ᵐ x ∂(Measure.pi fun _ : Fin d => volume),
      (tensorIntegratedTentDyadicLp profile cells) x =
        tensorIntegratedTentDyadic profile cells x := by
    filter_upwards [MemLp.coeFn_toLp hmem] with x hx
    simpa [tensorIntegratedTentDyadicLp, tensorIntegratedHaarTentLp,
      tensorIntegratedTentDyadic, tensorIntegratedHaarTent, hx]
  have hLpCoe' : ∀ᵐ x ∂(Measure.pi fun _ : Fin d => volume),
      (tensorIntegratedTentDyadicLp profile cells') x =
        tensorIntegratedTentDyadic profile cells' x := by
    filter_upwards [MemLp.coeFn_toLp hmem'] with x hx
    simpa [tensorIntegratedTentDyadicLp, tensorIntegratedHaarTentLp,
      tensorIntegratedTentDyadic, tensorIntegratedHaarTent, hx]
  have hint : ∫ x : Fin d → ℝ,
      (tensorIntegratedTentDyadicLp profile cells) x *
        (tensorIntegratedTentDyadicLp profile cells') x ∂
          (Measure.pi fun _ : Fin d => volume) =
      ∫ x : Fin d → ℝ, tensorIntegratedTentDyadic profile cells x *
        tensorIntegratedTentDyadic profile cells' x ∂
          (Measure.pi fun _ : Fin d => volume) := by
    apply integral_congr_ae
    filter_upwards [hLpCoe, hLpCoe'] with x hx hx'
    rw [hx, hx']
  have hreal : ∀ x y : ℝ, ⟪x, y⟫ = x * y := by
    intro x y
    simp [mul_comm]
  simp_rw [hreal]
  rw [hint, htent]

end HaarQuarter
