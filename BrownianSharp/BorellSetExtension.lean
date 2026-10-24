import BrownianSharp.BorellSetLimit
import Mathlib.MeasureTheory.Measure.Regular

/-! Inner-regular extension of the compact Gaussian interpolation inequality. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology
namespace BrownianSharp
open Concentration

/-- Compact subsets approximate the literal real mass of a measurable set. -/
theorem exists_compact_real_mass_approximation {κ : Type*} [Fintype κ]
    (A : Set (κ → ℝ)) (hA : MeasurableSet A) {ε : ℝ} (hε : 0 < ε) :
    ∃ K, K ⊆ A ∧ IsCompact K ∧
      (productStandardGaussian κ).real A - ε < (productStandardGaussian κ).real K ∧
      (productStandardGaussian κ).real K ≤ (productStandardGaussian κ).real A := by
  let μ := productStandardGaussian κ
  obtain ⟨K, hKA, hK, hm⟩ := hA.exists_isCompact_lt_add (μ := μ)
    (measure_ne_top μ A) (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  refine ⟨K, hKA, hK, ?_, measureReal_mono hKA (measure_ne_top _ _)⟩
  have hr := (ENNReal.toReal_lt_toReal (measure_ne_top μ A)
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top μ K, ENNReal.ofReal_ne_top⟩)).mpr hm
  rw [ENNReal.toReal_add (measure_ne_top μ K) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hε.le] at hr
  change (μ A).toReal - ε < (μ K).toReal
  linarith

/-- An interior-mass set has compact approximants whose masses remain strictly
inside (0,1) and converge to its actual mass. -/
theorem exists_compact_mass_approximating_sequence {κ : Type*} [Fintype κ]
    (A : Set (κ → ℝ)) (hA : MeasurableSet A)
    (hAm : (productStandardGaussian κ).real A ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ K : ℕ → Set (κ → ℝ),
      (∀ n, K n ⊆ A ∧ IsCompact (K n) ∧
        (productStandardGaussian κ).real (K n) ∈ Set.Ioo (0 : ℝ) 1) ∧
      Tendsto (fun n => (productStandardGaussian κ).real (K n)) atTop
        (𝓝 ((productStandardGaussian κ).real A)) := by
  let m := (productStandardGaussian κ).real A
  let ε : ℕ → ℝ := fun n => (m/2) / ((n:ℝ)+1)
  have hmpos : 0 < m := hAm.1
  have hepos : ∀ n, 0 < ε n := by intro n; dsimp [ε]; positivity
  choose K hKA hK hKlo hKhi using
    (fun n => exists_compact_real_mass_approximation A hA (hepos n))
  have hele : ∀ n, ε n ≤ m/2 := by
    intro n
    dsimp [ε]
    apply div_le_self (by dsimp [m]; linarith [hAm.1])
    linarith [Nat.cast_nonneg (α := ℝ) n]
  refine ⟨K, ?_, ?_⟩
  · intro n
    refine ⟨hKA n, hK n, ?_, (hKhi n).trans_lt hAm.2⟩
    have hl := hKlo n
    have he := hele n
    dsimp [m] at he
    linarith [hAm.1]
  · have hezero : Tendsto ε atTop (𝓝 0) := by
      have hd : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
        tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
      exact tendsto_const_nhds.div_atTop hd
    have hdiff : Tendsto (fun n => m - (productStandardGaussian κ).real (K n))
        atTop (𝓝 0) := by
      apply squeeze_zero (fun n => sub_nonneg.mpr (hKhi n))
        (fun n => (by have h := hKlo n; dsimp [m]; linarith :
          m - (productStandardGaussian κ).real (K n) ≤ ε n)) hezero
    have hres := (tendsto_const_nhds (x := m)).sub hdiff
    simpa only [sub_sub_cancel, sub_zero, m] using hres

/-- Compact Gaussian interpolation extends to all measurable input sets by
inner regularity. The output Minkowski set is measured by its actual outer
measure, so no unproved image-measurability assertion is used. -/
theorem measurableGaussianEhrhard_of_regularizedFunctional {κ : Type*} [Fintype κ]
    (hfunctional : RegularizedGaussianFunctionalInequality κ)
    (A B : Set (κ → ℝ)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hAm : (productStandardGaussian κ).real A ∈ Set.Ioo (0 : ℝ) 1)
    (hBm : (productStandardGaussian κ).real B ∈ Set.Ioo (0 : ℝ) 1) :
    standardGaussianCDF
      (a*standardGaussianQuantile ((productStandardGaussian κ).real A) +
       b*standardGaussianQuantile ((productStandardGaussian κ).real B)) ≤
      (productStandardGaussian κ).real (weightedMinkowski a A b B) := by
  obtain ⟨K, hK, hKm⟩ := exists_compact_mass_approximating_sequence A hA hAm
  obtain ⟨L, hL, hLm⟩ := exists_compact_mass_approximating_sequence B hB hBm
  have hKq := (standardGaussianQuantile_continuousAt hAm.1 hAm.2).tendsto.comp hKm
  have hLq := (standardGaussianQuantile_continuousAt hBm.1 hBm.2).tendsto.comp hLm
  have hlim := standardGaussianCDF_continuous.continuousAt.tendsto.comp
    ((hKq.const_mul a).add (hLq.const_mul b))
  apply le_of_tendsto_of_tendsto hlim tendsto_const_nhds
  filter_upwards [] with n
  apply (compactGaussianEhrhard_of_regularizedFunctional hfunctional (K n) (L n)
    (hK n).2.1 (hL n).2.1 a b ha hb hab (hK n).2.2 (hL n).2.2).trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  rintro z ⟨x, hx, y, hy, hz⟩
  exact ⟨x, (hK n).1 hx, y, (hL n).1 hy, hz⟩

/-- The smooth functional heat inequality supplies precisely the set-level
Ehrhard property used by the finite-grid concentration argument. Convex
frontiers are Gaussian-null by the checked absolute-continuity theorem. -/
theorem gaussianEhrhard_of_regularizedFunctional {κ : Type*} [Fintype κ]
    (hfunctional : RegularizedGaussianFunctionalInequality κ) :
    GaussianEhrhard (κ → ℝ) (productStandardGaussian κ) := by
  intro A B hA hB a b ha hb hab hA0 hA1 hB0 hB1
  have hAf : (productStandardGaussian κ) (frontier A) = 0 :=
    GaussianDensity.standardGaussian_absolutelyContinuous (hA.addHaar_frontier
      (μ := (volume : Measure (κ → ℝ))))
  have hBf : (productStandardGaussian κ) (frontier B) = 0 :=
    GaussianDensity.standardGaussian_absolutelyContinuous (hB.addHaar_frontier
      (μ := (volume : Measure (κ → ℝ))))
  have hAm : (productStandardGaussian κ).real (interior A) =
      (productStandardGaussian κ).real A :=
    congrArg ENNReal.toReal (measure_interior_of_null_frontier hAf)
  have hBm : (productStandardGaussian κ).real (interior B) =
      (productStandardGaussian κ).real B :=
    congrArg ENNReal.toReal (measure_interior_of_null_frontier hBf)
  have h := measurableGaussianEhrhard_of_regularizedFunctional hfunctional
    (interior A) (interior B) isOpen_interior.measurableSet isOpen_interior.measurableSet
    a b ha hb hab (by simpa [hAm] using And.intro hA0 hA1)
      (by simpa [hBm] using And.intro hB0 hB1)
  rw [hAm, hBm] at h
  apply h.trans
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  rintro z ⟨x, hx, y, hy, hz⟩
  exact ⟨x, interior_subset hx, y, interior_subset hy, hz⟩

end BrownianSharp
