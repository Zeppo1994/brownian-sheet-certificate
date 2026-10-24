import BrownianSharp.GaussianHeatSupport
import BrownianSharp.GaussianCDFCalculus

/-! Range and spatial-infinity conditions in Borell's Gaussian heat argument.
All limits are for the actual finite-product Gaussian heat average. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace BrownianSharp
open Concentration

theorem gaussianQuantile_mono_Ioo {u v : ℝ} (hu0 : 0 < u) (hu1 : u < 1)
    (hv0 : 0 < v) (hv1 : v < 1) (huv : u ≤ v) :
    standardGaussianQuantile u ≤ standardGaussianQuantile v := by
  apply standardGaussianCDF_strictMono.le_iff_le.mp
  rw [standardGaussianCDF_standardGaussianQuantile hu0 hu1,
    standardGaussianCDF_standardGaussianQuantile hv0 hv1]
  exact huv

theorem gaussianHeat_mem_Icc {κ : Type*} [Fintype κ]
    (q : (κ → ℝ) → ℝ) (hq : Continuous q) {a b : ℝ}
    (hrange : ∀ x, q x ∈ Set.Icc a b) (t : ℝ) (x : κ → ℝ) :
    gaussianHeat q t x ∈ Set.Icc a b := by
  have hb : ∀ u, |q u| ≤ |a| + |b| := by
    intro u
    rw [abs_le]
    rcases hrange u with ⟨hlo, hhi⟩
    constructor <;> linarith [neg_abs_le a, le_abs_self b, abs_nonneg a, abs_nonneg b]
  have hInt := gaussianHeat_integrable_of_bounded q hq t x hb
  constructor
  · have h := integral_mono (integrable_const a) hInt (fun z => (hrange _).1)
    simpa [gaussianHeat] using h
  · have h := integral_mono hInt (integrable_const b) (fun z => (hrange _).2)
    simpa [gaussianHeat] using h

theorem gaussianHeat_quantile_mem_Icc {κ : Type*} [Fintype κ]
    (q : (κ → ℝ) → ℝ) (hq : Continuous q) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (hrange : ∀ x, q x ∈ Set.Icc a b) (t : ℝ) (x : κ → ℝ) :
    standardGaussianQuantile (gaussianHeat q t x) ∈
      Set.Icc (standardGaussianQuantile a) (standardGaussianQuantile b) := by
  have h := gaussianHeat_mem_Icc q hq hrange t x
  have ha1 : a < 1 := hab.trans_lt hb
  have hb0 : 0 < b := ha.trans_le hab
  exact ⟨gaussianQuantile_mono_Ioo ha ha1 (ha.trans_le h.1) (h.2.trans_lt hb) h.1,
    gaussianQuantile_mono_Ioo (ha.trans_le h.1) (h.2.trans_lt hb) hb0 hb h.2⟩

theorem gaussianHeat_quantile_uniform_limit_at_infinity {κ : Type*} [Fintype κ]
    (q : (κ → ℝ) → ℝ) (hq : Continuous q)
    {δ M R T : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hM : 0 ≤ M) (hT : 0 < T)
    (hbounded : ∀ u, |q u - δ| ≤ M)
    (houtside : ∀ u, R < ‖u‖ → q u = δ) :
    ∀ ε : ℝ, 0 < ε → ∃ L : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x : κ → ℝ, L < ‖x‖ →
        |standardGaussianQuantile (gaussianHeat q t x) - standardGaussianQuantile δ| < ε := by
  intro ε hε
  obtain ⟨η, hη, hηprop⟩ := Metric.continuousAt_iff.mp
    (standardGaussianQuantile_continuousAt hδ0 hδ1) ε hε
  obtain ⟨L, hL⟩ := gaussianHeat_uniform_limit_at_infinity q hq hM hT hbounded houtside η hη
  refine ⟨L, ?_⟩
  intro t ht x hx
  have h := hL t ht x hx
  exact hηprop (by simpa only [Real.dist_eq] using h)

/-- The comparison function from Borell's two-point heat maximum principle. -/
def borellHeatDifference {κ : Type*} [Fintype κ]
    (a b : ℝ) (f g h : (κ → ℝ) → ℝ) (t : ℝ)
    (xy : (κ → ℝ) × (κ → ℝ)) : ℝ :=
  standardGaussianQuantile (gaussianHeat h t (a • xy.1 + b • xy.2)) -
    a * standardGaussianQuantile (gaussianHeat f t xy.1) -
    b * standardGaussianQuantile (gaussianHeat g t xy.2)

/-- The actual heat comparison satisfies the spatial liminf condition in
Borell's maximum principle whenever the initial exterior constants obey the
explicit two endpoint inequalities. -/
theorem borellHeatDifference_uniform_liminf {κ : Type*} [Fintype κ]
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (f g h : (κ → ℝ) → ℝ) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
    {δ α β Rf Rg T : ℝ} (hδ0 : 0 < δ) (hα1 : α < 1) (hδα : δ ≤ α)
    (hβ0 : 0 < β) (hβα : β ≤ α) (hT : 0 < T)
    (hfRange : ∀ x, f x ∈ Set.Icc δ α) (hgRange : ∀ x, g x ∈ Set.Icc δ α)
    (hhRange : ∀ x, h x ∈ Set.Icc β α)
    (hfOutside : ∀ x, Rf < ‖x‖ → f x = δ)
    (hgOutside : ∀ x, Rg < ‖x‖ → g x = δ)
    (hbase1 : a * standardGaussianQuantile δ + b * standardGaussianQuantile α ≤
      standardGaussianQuantile β)
    (hbase2 : a * standardGaussianQuantile α + b * standardGaussianQuantile δ ≤
      standardGaussianQuantile β) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ,
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ xy : (κ → ℝ) × (κ → ℝ), R < ‖xy‖ →
        -ε < borellHeatDifference a b f g h t xy := by
  intro ε hε
  have hfBound : ∀ x, |f x - δ| ≤ α - δ := by
    intro x
    rw [abs_of_nonneg (sub_nonneg.mpr (hfRange x).1)]
    linarith [(hfRange x).2]
  have hgBound : ∀ x, |g x - δ| ≤ α - δ := by
    intro x
    rw [abs_of_nonneg (sub_nonneg.mpr (hgRange x).1)]
    linarith [(hgRange x).2]
  obtain ⟨Lf, hLf⟩ := gaussianHeat_quantile_uniform_limit_at_infinity
    f hf hδ0 (hδα.trans_lt hα1) (sub_nonneg.mpr hδα) hT hfBound hfOutside ε hε
  obtain ⟨Lg, hLg⟩ := gaussianHeat_quantile_uniform_limit_at_infinity
    g hg hδ0 (hδα.trans_lt hα1) (sub_nonneg.mpr hδα) hT hgBound hgOutside ε hε
  refine ⟨max Lf Lg, ?_⟩
  intro t ht xy hxy
  have hH := (gaussianHeat_quantile_mem_Icc h hh hβ0 hα1 hβα hhRange t (a • xy.1 + b • xy.2)).1
  have hF := (gaussianHeat_quantile_mem_Icc f hf hδ0 hα1 hδα hfRange t xy.1).2
  have hG := (gaussianHeat_quantile_mem_Icc g hg hδ0 hα1 hδα hgRange t xy.2).2
  have hsplit : Lf < ‖xy.1‖ ∨ Lg < ‖xy.2‖ := by
    rw [Prod.norm_def] at hxy
    rcases lt_max_iff.mp hxy with hx | hy
    · exact Or.inl ((le_max_left _ _).trans_lt hx)
    · exact Or.inr ((le_max_right _ _).trans_lt hy)
  unfold borellHeatDifference
  rcases hsplit with hx | hy
  · have hclose := (abs_lt.mp (hLf t ht xy.1 hx)).2
    have ha1 : a ≤ 1 := by linarith
    have hcF := mul_lt_mul_of_pos_left hclose ha
    have hcG := mul_le_mul_of_nonneg_left hG hb.le
    have heps := mul_le_mul_of_nonneg_right ha1 hε.le
    linarith
  · have hclose := (abs_lt.mp (hLg t ht xy.2 hy)).2
    have hb1 : b ≤ 1 := by linarith
    have hcG := mul_lt_mul_of_pos_left hclose hb
    have hcF := mul_le_mul_of_nonneg_left hF ha.le
    have heps := mul_le_mul_of_nonneg_right hb1 hε.le
    linarith

end BrownianSharp
