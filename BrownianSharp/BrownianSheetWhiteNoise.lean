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

/-- A finite family of anchored-box evaluations from white noise is jointly
Gaussian. This gives the finite-dimensional Gaussian process law of the
Brownian sheet once an isonormal family on the product L² space is supplied. -/
theorem brownianSheetBoxEval_jointlyGaussian {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) Ω ι P)
    (t : ι → Fin d → ℝ) :
    HasGaussianLaw
      (fun ω i => W.eval (brownianSheetBoxIndicatorLp (t i)) ω) P := by
  exact W.jointlyGaussian (fun i => brownianSheetBoxIndicatorLp (t i))

/-- The covariance of the finite anchored-box process is the Brownian-sheet
kernel, derived from the actual L² inner product of its indicators. -/
theorem brownianSheetBoxEval_covariance {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) Ω ι P)
    (t : ι → Fin d → ℝ) (ht : ∀ i k, 0 ≤ t i k) (i j : ι) :
    cov[fun ω => W.eval (brownianSheetBoxIndicatorLp (t i)) ω,
        fun ω => W.eval (brownianSheetBoxIndicatorLp (t j)) ω; P] =
      ∏ k, min (t i k) (t j k) := by
  rw [W.covariance_eq_inner]
  exact brownianSheetBoxIndicatorLp_inner (t i) (t j) (ht i) (ht j)

/-- Each anchored-box coordinate has the centered Gaussian marginal with
variance equal to its rectangle volume. -/
theorem brownianSheetBoxEval_coordinate_law {d : ℕ} {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
    (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) Ω ι P)
    (t : ι → Fin d → ℝ) (ht : ∀ i k, 0 ≤ t i k) (i : ι) :
    P.map (fun ω => W.eval (brownianSheetBoxIndicatorLp (t i)) ω) =
      gaussianReal 0 (∏ k, t i k).toNNReal := by
  have h := W.coordinate_law (fun j => brownianSheetBoxIndicatorLp (t j)) i
  have hnorm := brownianSheetBoxIndicatorLp_inner (t i) (t i) (ht i) (ht i)
  rw [hnorm] at h
  simpa [min_self] using h

end HaarQuarter
