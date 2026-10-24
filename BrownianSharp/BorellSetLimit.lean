import BrownianSharp.BorellRegularization
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric

/-! Compact-set passage from the regularized Gaussian functional inequality. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff
namespace BrownianSharp
open Concentration

/-- The analytic output of the Gaussian heat maximum principle. All functions
are literal smooth compact plateaus and all constants are in the open
probability range. This is a proposition to prove, not an axiom. -/
def RegularizedGaussianFunctionalInequality (κ : Type*) [Fintype κ] : Prop :=
  ∀ a b : ℝ, 0 < a → 0 < b → a+b=1 →
  ∀ F G H : (κ → ℝ) → ℝ,
    ContDiff ℝ ∞ F → ContDiff ℝ ∞ G → ContDiff ℝ ∞ H →
    HasCompactSupport F → HasCompactSupport G → HasCompactSupport H →
    (∀ x, F x ∈ Set.Icc (0 : ℝ) 1) →
    (∀ x, G x ∈ Set.Icc (0 : ℝ) 1) →
    (∀ x, H x ∈ Set.Icc (0 : ℝ) 1) →
  ∀ δ α β : ℝ, 0 < δ → α < 1 → δ ≤ α → 0 < β → β ≤ α →
    a*standardGaussianQuantile δ + b*standardGaussianQuantile α ≤ standardGaussianQuantile β →
    a*standardGaussianQuantile α + b*standardGaussianQuantile δ ≤ standardGaussianQuantile β →
    (∀ x y, a*standardGaussianQuantile (δ+(α-δ)*F x) +
      b*standardGaussianQuantile (δ+(α-δ)*G y) ≤
      standardGaussianQuantile (β+(α-β)*H (a • x+b • y))) →
    standardGaussianCDF
      (a*standardGaussianQuantile (∫ x, δ+(α-δ)*F x ∂productStandardGaussian κ) +
       b*standardGaussianQuantile (∫ x, δ+(α-δ)*G x ∂productStandardGaussian κ)) ≤
      ∫ x, β+(α-β)*H x ∂productStandardGaussian κ

/-- Bounds on the literal integral of a continuous probability plateau. -/
theorem borell_plateau_integral_mem_Icc {κ : Type*} [Fintype κ]
    (F : (κ → ℝ) → ℝ) (hF : Continuous F)
    (hFr : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1) :
    (∫ x, F x ∂productStandardGaussian κ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hi : Integrable F (productStandardGaussian κ) :=
    (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hFr x).1]; exact (hFr x).2)
  exact ⟨integral_nonneg fun x => (hFr x).1,
    by simpa using integral_mono hi (integrable_const (1 : ℝ)) (fun x => (hFr x).2)⟩

theorem borell_plateau_integrable {κ : Type*} [Fintype κ]
    (F : (κ → ℝ) → ℝ) (hF : Continuous F)
    (hFr : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1) :
    Integrable F (productStandardGaussian κ) :=
  (integrable_const (1 : ℝ)).mono' hF.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hFr x).1]; exact (hFr x).2)

/-- A plateau equal to one on K has integral at least the actual mass of K. -/
theorem borell_plateau_integral_ge {κ : Type*} [Fintype κ]
    (F : (κ → ℝ) → ℝ) (hF : Continuous F)
    (hFr : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1)
    (K : Set (κ → ℝ)) (hK : MeasurableSet K) (hone : ∀ x ∈ K, F x=1) :
    (productStandardGaussian κ).real K ≤ ∫ x, F x ∂productStandardGaussian κ := by
  rw [← integral_indicator_one hK]
  apply integral_mono ((integrable_const (1 : ℝ)).indicator hK)
    (borell_plateau_integrable F hF hFr)
  intro x
  by_cases hx : x ∈ K
  · simp [hx, hone x hx]
  · simp only [Set.indicator_of_notMem hx, Pi.zero_apply]
    exact (hFr x).1

/-- A plateau vanishing outside K has integral at most the mass of K. -/
theorem borell_plateau_integral_le {κ : Type*} [Fintype κ]
    (F : (κ → ℝ) → ℝ) (hF : Continuous F)
    (hFr : ∀ x, F x ∈ Set.Icc (0 : ℝ) 1)
    (K : Set (κ → ℝ)) (hK : MeasurableSet K) (hzero : ∀ x, x ∉ K → F x=0) :
    (∫ x, F x ∂productStandardGaussian κ) ≤ (productStandardGaussian κ).real K := by
  rw [← integral_indicator_one hK]
  apply integral_mono (borell_plateau_integrable F hF hFr)
    ((integrable_const (1 : ℝ)).indicator hK)
  intro x
  by_cases hx : x ∈ K
  · simpa [hx] using (hFr x).2
  · simp [hx, hzero x hx]

/-- Shrinking the twice-enlarged compact weighted sum recovers its mass. -/
theorem borell_compact_thickening_limit {κ : Type*} [Fintype κ]
    (C : Set (κ → ℝ)) (hC : IsCompact C) (z : ℝ)
    (hbound : ∀ ε : ℝ, 0 < ε → z ≤
      (productStandardGaussian κ).real (Metric.cthickening (2*ε) C)) :
    z ≤ (productStandardGaussian κ).real C := by
  have ht := tendsto_measure_cthickening_of_isClosed
    (μ := productStandardGaussian κ) ⟨1, by norm_num, measure_ne_top _ _⟩ hC.isClosed
  have hr := (ENNReal.tendsto_toReal (measure_ne_top (productStandardGaussian κ) C)).comp ht
  have hscale : Tendsto (fun ε : ℝ => 2*ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hs : Continuous (fun ε : ℝ => 2*ε) := by fun_prop
    simpa using hs.continuousAt.tendsto.mono_left (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds (hr.comp hscale)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hbound ε hε

/-- The regularized functional heat inequality implies the full compact-set
Gaussian interpolation inequality, using actual smooth plateaus and limits. -/
theorem compactGaussianEhrhard_of_regularizedFunctional {κ : Type*} [Fintype κ]
    (hfunctional : RegularizedGaussianFunctionalInequality κ)
    (K L : Set (κ → ℝ)) (hK : IsCompact K) (hL : IsCompact L)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hKm : (productStandardGaussian κ).real K ∈ Set.Ioo (0 : ℝ) 1)
    (hLm : (productStandardGaussian κ).real L ∈ Set.Ioo (0 : ℝ) 1) :
    standardGaussianCDF
      (a*standardGaussianQuantile ((productStandardGaussian κ).real K) +
       b*standardGaussianQuantile ((productStandardGaussian κ).real L)) ≤
      (productStandardGaussian κ).real (weightedMinkowski a K b L) := by
  apply borell_compact_thickening_limit _ (isCompact_weightedMinkowski a b hK hL)
  intro ε hε
  obtain ⟨F, hFs, hFr, hFone, hFzero, hFc⟩ := exists_borell_smooth_bump K hK hε
  obtain ⟨G, hGs, hGr, hGone, hGzero, hGc⟩ := exists_borell_smooth_bump L hL hε
  obtain ⟨H, hHs, hHr, hHc, hHone, hHzero⟩ :=
    exists_borell_comparison_bump a b ha hb hab K L hK hL hε
  have hFI := borell_plateau_integrable F hFs.continuous hFr
  have hGI := borell_plateau_integrable G hGs.continuous hGr
  have hHI := borell_plateau_integrable H hHs.continuous hHr
  obtain ⟨c, q, hc, hq, hcq, hq1, hqbase1, hqbase2⟩ :=
    exists_borell_regularization_slopes ha hb hab
  apply le_trans (b := ∫ x, H x ∂productStandardGaussian κ)
  · apply borell_regularization_lower_mass_limit ha hb hc hq hKm hLm
      (borell_plateau_integral_mem_Icc F hFs.continuous hFr)
      (borell_plateau_integral_mem_Icc G hGs.continuous hGr)
      (borell_plateau_integral_ge F hFs.continuous hFr K hK.measurableSet hFone)
      (borell_plateau_integral_ge G hGs.continuous hGr L hL.measurableSet hGone)
    intro t ht
    obtain ⟨hδ, hα, hδα, hβ, hβα, hbase1, hbase2⟩ :=
      borell_regularization_endpoints ha hb hab hc hq hcq hq1 hqbase1 hqbase2 ht
    have hinit := borell_regularization_initial a b ha hb hab K L ε F G H hFr hGr hHr
      hFzero hGzero hHone hδ hα hδα hβ hβα hbase1 hbase2
    have h := hfunctional a b ha hb hab F G H hFs hGs hHs hFc hGc hHc hFr hGr hHr
      _ _ _ hδ hα hδα hβ hβα hbase1 hbase2 hinit
    rw [integral_borell_regularization _ F hFI,
      integral_borell_regularization _ G hGI,
      integral_borell_regularization _ H hHI] at h
    exact h
  · exact borell_plateau_integral_le H hHs.continuous hHr _
      Metric.isClosed_cthickening.measurableSet hHzero

end BrownianSharp
