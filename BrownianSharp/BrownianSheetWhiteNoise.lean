import BrownianSharp.BrownianHaarCovariance

/-! A concrete white-noise bridge for finite collections of Brownian-sheet
anchored boxes.  The box vectors are actual L² indicators; their inner
products give the sheet covariance, and any isonormal Gaussian family maps
them to a jointly Gaussian Brownian-sheet finite-dimensional law. -/

open MeasureTheory InnerProductSpace ProbabilityTheory
open scoped RealInnerProductSpace ENNReal

namespace HaarQuarter

/-- The L² indicator of the anchored box `[0,t]` in the product parameter
space. -/
noncomputable def brownianSheetBoxIndicatorLp {d : ℕ} (t : Fin d → ℝ) :
    Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) := by
  let box : Set (Fin d → ℝ) := Set.pi Set.univ (fun i => Set.Icc 0 (t i))
  have hs : MeasurableSet box := by
    dsimp [box]
    exact MeasurableSet.univ_pi fun i => measurableSet_Icc
  have hμ : (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) box ≠ ∞ := by
    rw [show box = Set.pi Set.univ (fun i => Set.Icc (0 : ℝ) (t i)) by rfl,
      Measure.pi_pi]
    apply ne_of_lt
    apply ENNReal.prod_lt_top
    intro i hi
    simp [Real.volume_Icc]
  exact indicatorConstLp (2 : ℝ≥0∞) hs hμ 1

/-- The inner product of anchored-box indicators is the usual Brownian-sheet
covariance `prod i, min (s i) (t i)`. -/
theorem brownianSheetBoxIndicatorLp_inner {d : ℕ}
    (s t : Fin d → ℝ) (hs : ∀ i, 0 ≤ s i) (ht : ∀ i, 0 ≤ t i) :
    ⟪brownianSheetBoxIndicatorLp s,
      brownianSheetBoxIndicatorLp t⟫ = ∏ i, min (s i) (t i) := by
  let boxS : Set (Fin d → ℝ) := Set.pi Set.univ (fun i => Set.Icc 0 (s i))
  let boxT : Set (Fin d → ℝ) := Set.pi Set.univ (fun i => Set.Icc 0 (t i))
  let μ : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => (volume : Measure ℝ)
  have hS : (brownianSheetBoxIndicatorLp s : Lp ℝ 2 μ) =ᵐ[μ]
      boxS.indicator (fun _ => (1 : ℝ)) := by
    rw [brownianSheetBoxIndicatorLp]
    exact indicatorConstLp_coeFn
  have hT : (brownianSheetBoxIndicatorLp t : Lp ℝ 2 μ) =ᵐ[μ]
      boxT.indicator (fun _ => (1 : ℝ)) := by
    rw [brownianSheetBoxIndicatorLp]
    exact indicatorConstLp_coeFn
  have hμid : μ = Measure.pi (fun _ : Fin d => (volume : Measure ℝ)) := rfl
  rw [L2.inner_def]
  have hmeas : MeasurableSet (boxS ∩ boxT) := by
    exact (MeasurableSet.univ_pi fun i => measurableSet_Icc).inter
      (MeasurableSet.univ_pi fun i => measurableSet_Icc)
  have hbox : boxS ∩ boxT = Set.pi Set.univ
      (fun i => Set.Icc (0 : ℝ) (min (s i) (t i))) := by
    rw [← Set.pi_inter_distrib]
    congr 1
    funext i
    ext x
    simp
    tauto
  calc
    ∫ x, ⟪brownianSheetBoxIndicatorLp s x,
        brownianSheetBoxIndicatorLp t x⟫ ∂μ =
        ∫ x, (boxS.indicator (fun _ => (1 : ℝ)) x) *
        (boxT.indicator (fun _ => (1 : ℝ)) x) ∂
          μ := by
            apply integral_congr_ae
            filter_upwards [hS, hT] with x hxS hxT
            rw [hxS, hxT]
            rw [Real.inner_apply]
    _ =
        ∫ x, (boxS ∩ boxT).indicator (fun _ => (1 : ℝ)) x ∂
          μ := by
            apply integral_congr_ae
            filter_upwards with x
            by_cases hxS : x ∈ boxS <;> by_cases hxT : x ∈ boxT <;>
              simp [Set.indicator_apply, hxS, hxT]
    _ = μ.real (boxS ∩ boxT) :=
      integral_indicator_one hmeas
    _ = ∏ i, min (s i) (t i) := by
      rw [hbox, Measure.real_def, hμid,
        Measure.pi_pi (fun _ : Fin d => (volume : Measure ℝ))]
      rw [ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Real.volume_Icc]
      rw [sub_zero]
      exact ENNReal.toReal_ofReal (le_min (hs i) (ht i))

end HaarQuarter
