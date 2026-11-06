import BrownianSharp.AlignmentPaperAnchoredLp
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section
open MeasureTheory Filter HaarQuarter
open scoped ENNReal BigOperators Topology

namespace BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLp

instance cubeProbability (d : ℕ) : IsProbabilityMeasure (cubeMeasure d) := by
  haveI : IsProbabilityMeasure
      ((volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  rw [cubeMeasure, AlignmentFractionalTensor.unitCube_measure_eq_pi]
  infer_instance

def rectangleKernel {d : ℕ} (t : BrownianCubeAnchor d)
    (u : Fin d → ℝ) : ℝ :=
  ∏ i, if u i < t.val i then 1 else 0

theorem rectangleKernel_eq {d : ℕ} (t : BrownianCubeAnchor d) (u : Fin d → ℝ) :
    rectangleKernel t u = Latest.fractionalTensorKernel (fun _ : Fin d => 1) t u := by
  simp [rectangleKernel, Latest.fractionalTensorKernel]

theorem rectangleKernel_measurable {d : ℕ} (t : BrownianCubeAnchor d) :
    Measurable (rectangleKernel t) := by
  classical
  unfold rectangleKernel
  apply Finset.measurable_prod
  intro i _
  exact Measurable.ite (measurableSet_lt (measurable_pi_apply i) measurable_const)
    measurable_const measurable_const

theorem rectangleKernel_norm_le {d : ℕ} (t : BrownianCubeAnchor d)
    (u : Fin d → ℝ) : ‖rectangleKernel t u‖ ≤ 1 := by
  classical
  unfold rectangleKernel
  rw [norm_prod]
  apply Finset.prod_le_one₀
  · intro i _
    exact norm_nonneg _
  · intro i _
    split_ifs <;> norm_num

theorem rectangleKernel_continuousAt_ae {d : ℕ} (x : BrownianCubeAnchor d) :
    ∀ᵐ u ∂cubeMeasure d, ContinuousAt (fun t : BrownianCubeAnchor d =>
      rectangleKernel t u) x := by
  classical
  have hne : ∀ᵐ u ∂cubeMeasure d, ∀ i : Fin d, u i ≠ x.val i := by
    rw [cubeMeasure, AlignmentFractionalTensor.unitCube_measure_eq_pi]
    exact ae_all_iff.mpr (fun i =>
      Measure.ae_eval_ne (fun _ : Fin d =>
        (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) i (x.val i))
  filter_upwards [hne] with u hu
  have hi : ∀ i : Fin d, ∀ᶠ t : BrownianCubeAnchor d in 𝓝 x,
      (if u i < t.val i then (1 : ℝ) else 0) =
        (if u i < x.val i then (1 : ℝ) else 0) := by
    intro i
    have hcoord : Continuous (fun t : BrownianCubeAnchor d => t.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    by_cases hx : u i < x.val i
    · have he : ∀ᶠ t : BrownianCubeAnchor d in 𝓝 x, u i < t.val i :=
        (isOpen_lt continuous_const hcoord).mem_nhds hx
      filter_upwards [he] with t ht
      simp [ht, hx]
    · have hx' : x.val i < u i := lt_of_le_of_ne (le_of_not_gt hx) (hu i).symm
      have he : ∀ᶠ t : BrownianCubeAnchor d in 𝓝 x, t.val i < u i :=
        (isOpen_lt hcoord continuous_const).mem_nhds hx'
      filter_upwards [he] with t ht
      simp [hx, not_lt_of_ge ht.le]
  apply Filter.EventuallyEq.continuousAt
  have hall := Filter.eventually_all.mpr hi
  filter_upwards [hall] with t ht
  exact Finset.prod_congr rfl (fun i _ => ht i)

theorem continuous_rectangular_integral {d : ℕ} (g : (Fin d → ℝ) → ℝ)
    (hg : Integrable g (cubeMeasure d)) :
    Continuous (fun t : BrownianCubeAnchor d =>
      ∫ u, rectangleKernel t u * g u ∂cubeMeasure d) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hmeas : ∀ᶠ t : BrownianCubeAnchor d in 𝓝 x,
      AEStronglyMeasurable (fun u => rectangleKernel t u * g u) (cubeMeasure d) :=
    Eventually.of_forall (fun t =>
      (rectangleKernel_measurable t).aestronglyMeasurable.mul hg.aestronglyMeasurable)
  have hbound : ∀ᶠ t : BrownianCubeAnchor d in 𝓝 x,
      ∀ᵐ u ∂cubeMeasure d, ‖rectangleKernel t u * g u‖ ≤ ‖g u‖ := by
    apply Eventually.of_forall
    intro t
    exact ae_of_all _ (fun u => by
      rw [norm_mul]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (rectangleKernel_norm_le t u) (norm_nonneg (g u)))
  have hlim : ∀ᵐ u ∂cubeMeasure d,
      Tendsto (fun t : BrownianCubeAnchor d => rectangleKernel t u * g u)
        (𝓝 x) (𝓝 (rectangleKernel x u * g u)) := by
    filter_upwards [rectangleKernel_continuousAt_ae x] with u hu
    exact (hu.mul_const (g u)).tendsto
  exact tendsto_integral_filter_of_dominated_convergence (fun u => ‖g u‖)
    hmeas hbound hg.norm hlim

theorem integrable_kernel_mul {d : ℕ} (g : (Fin d → ℝ) → ℝ)
    (hg : Integrable g (cubeMeasure d)) (t : BrownianCubeAnchor d) :
    Integrable (fun u => rectangleKernel t u * g u) (cubeMeasure d) := by
  refine hg.norm.mono' ((rectangleKernel_measurable t).aestronglyMeasurable.mul
    hg.aestronglyMeasurable) ?_
  exact ae_of_all _ (fun u => by
    rw [norm_mul]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (rectangleKernel_norm_le t u) (norm_nonneg (g u)))

theorem norm_rectangular_integral_le {d : ℕ} (g : (Fin d → ℝ) → ℝ)
    (hg : Integrable g (cubeMeasure d)) (t : BrownianCubeAnchor d) :
    ‖∫ u, rectangleKernel t u * g u ∂cubeMeasure d‖ ≤
      ∫ u, ‖g u‖ ∂cubeMeasure d := by
  refine (norm_integral_le_integral_norm _).trans ?_
  apply integral_mono (integrable_kernel_mul g hg t).norm hg.norm
  intro u
  change ‖rectangleKernel t u * g u‖ ≤ ‖g u‖
  rw [norm_mul]
  simpa only [one_mul] using
    mul_le_mul_of_nonneg_right (rectangleKernel_norm_le t u) (norm_nonneg (g u))

/-- Every actual Lp density has a continuous rectangular-integral path. -/
def integrationPath {d : ℕ} (p : ℝ) (hp : 1 < p)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    C(BrownianCubeAnchor d, ℝ) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  exact ⟨fun t => anchoredLpValue p g t, by
    simpa only [anchoredLpValue, ← rectangleKernel_eq] using
      continuous_rectangular_integral (g : (Fin d → ℝ) → ℝ) ((Lp.memLp g).integrable hp1)⟩

@[simp] theorem integrationPath_apply {d : ℕ} (p : ℝ) (hp : 1 < p)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) (t : BrownianCubeAnchor d) :
    integrationPath p hp g t = anchoredLpValue p g t := rfl

theorem integrationPath_norm_le {d : ℕ} (p : ℝ) (hp : 1 < p)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) :
    ‖integrationPath p hp g‖ ≤ ‖g‖ := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p) := ⟨by simpa using ENNReal.ofReal_le_ofReal hp.le⟩
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  have hmem1 : MemLp (g : (Fin d → ℝ) → ℝ) 1 (cubeMeasure d) :=
    (Lp.memLp g).mono_exponent hp1
  let g1 : Lp ℝ 1 (cubeMeasure d) := hmem1.toLp g
  have hnorm1 : ‖g1‖ ≤ ‖g‖ := by
    rw [Lp.norm_def, Lp.norm_def]
    rw [eLpNorm_congr_ae hmem1.coeFn_toLp]
    exact ENNReal.toReal_mono (Lp.memLp g).eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le hp1)
  have hint : (∫ u, ‖g u‖ ∂cubeMeasure d) = ‖g1‖ := by
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae (hmem1.coeFn_toLp.symm.mono fun u hu => congrArg norm hu)
  apply (ContinuousMap.norm_le (integrationPath p hp g) (norm_nonneg g)).2
  intro t
  have hrect := norm_rectangular_integral_le (g : (Fin d → ℝ) → ℝ)
    ((Lp.memLp g).integrable hp1) t
  have hbound := hrect.trans (hint.le.trans hnorm1)
  simpa only [integrationPath_apply, anchoredLpValue, ← rectangleKernel_eq] using hbound

def integrationLinearMap {d : ℕ} (p : ℝ) (hp : 1 < p) :
    Lp ℝ (ENNReal.ofReal p) (cubeMeasure d) →ₗ[ℝ] C(BrownianCubeAnchor d, ℝ) where
  toFun := integrationPath p hp
  map_add' g h := by
    have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
      simpa using ENNReal.ofReal_le_ofReal hp.le
    ext t
    simp only [integrationPath_apply, ContinuousMap.add_apply, anchoredLpValue,
      ← rectangleKernel_eq]
    calc
      (∫ u, rectangleKernel t u * (g + h) u ∂cubeMeasure d) =
          ∫ u, (rectangleKernel t u * g u + rectangleKernel t u * h u) ∂cubeMeasure d := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_add g h] with u hu
            rw [hu]
            simp only [Pi.add_apply]
            ring
      _ = _ := integral_add
        (integrable_kernel_mul _ ((Lp.memLp g).integrable hp1) t)
        (integrable_kernel_mul _ ((Lp.memLp h).integrable hp1) t)
  map_smul' c g := by
    ext t
    simp only [integrationPath_apply, ContinuousMap.smul_apply, anchoredLpValue,
      ← rectangleKernel_eq, RingHom.id_apply, smul_eq_mul]
    calc
      (∫ u, rectangleKernel t u * (c • g) u ∂cubeMeasure d) =
          ∫ u, c * (rectangleKernel t u * g u) ∂cubeMeasure d := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_smul c g] with u hu
            rw [hu]
            simp only [Pi.smul_apply, smul_eq_mul]
            ring
      _ = _ := integral_const_mul c _

/-- The manuscript's actual bounded linear operator T_{d,p}, not a partially
defined path predicate. Its norm is at most one on the unit-volume cube. -/
def anchoredIntegrationOperator {d : ℕ} (p : ℝ) (hp : 1 < p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)] :
    Lp ℝ (ENNReal.ofReal p) (cubeMeasure d) →L[ℝ] C(BrownianCubeAnchor d, ℝ) :=
  (integrationLinearMap p hp).mkContinuous 1
    (by
      intro g
      change ‖integrationPath p hp g‖ ≤ 1 * ‖g‖
      simpa only [one_mul] using integrationPath_norm_le p hp g)

@[simp] theorem anchoredIntegrationOperator_apply {d : ℕ} (p : ℝ) (hp : 1 < p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)]
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) (t : BrownianCubeAnchor d) :
    anchoredIntegrationOperator p hp g t = anchoredLpValue p g t := rfl

/-- The image set `anchoredIntegrationLpImage` is exactly the true continuous operator's
image of its closed source unit ball. -/
theorem anchoredIntegrationOperator_image_eq {d : ℕ} (p : ℝ) (hp : 1 < p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)] :
    anchoredIntegrationOperator (d := d) p hp '' Metric.closedBall 0 1 =
      anchoredIntegrationLpImage d p := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, by simpa using hg, fun _ => rfl⟩
  · rintro ⟨g, hg, hgf⟩
    refine ⟨g, by simpa using hg, ?_⟩
    ext t
    exact hgf t

theorem anchoredIntegrationLpImage_two_eq_KdUnitCube (d : ℕ) :
    anchoredIntegrationLpImage d 2 = CameronMartin.KdUnitCube d := by
  apply Set.Subset.antisymm
  · exact anchoredIntegrationLpImage_subset_KdUnitCube (by norm_num : (2:ℝ) ≤ 2)
  · exact KdUnitCube_subset_anchoredIntegrationLpImage (by norm_num : (1:ℝ) < 2)
      (by norm_num : (2:ℝ) ≤ 2)

end BrownianSharp.AlignmentPaperAnchoredLpOperator
