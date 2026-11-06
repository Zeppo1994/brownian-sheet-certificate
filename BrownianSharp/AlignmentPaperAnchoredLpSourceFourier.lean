import BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
import BrownianSharp.AlignmentPaperAnchoredLpOperator
import BrownianSharp.UnitTorusMeasure
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open MeasureTheory
open intervalIntegral

namespace BrownianSharp.AlignmentPaperAnchoredLpSourceFourier

open BrownianSharp.AlignmentPaperAnchoredLpReflection
open BrownianSharp.AlignmentPaperAnchoredLpReflectionTensor
open BrownianSharp.AlignmentPaperAnchoredLpPeriodicExtension
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.Torus
open HaarQuarter

theorem measurable_rectangleKernel_joint {d : ℕ} :
    Measurable (fun z : BrownianCubeAnchor d × (Fin d → ℝ) =>
      rectangleKernel z.1 z.2) := by
  classical
  unfold rectangleKernel
  apply Finset.measurable_prod
  intro i hi
  have hleft : Measurable (fun z : BrownianCubeAnchor d × (Fin d → ℝ) =>
      z.2 i) := measurable_pi_apply i |>.comp measurable_snd
  have hright : Measurable (fun z : BrownianCubeAnchor d × (Fin d → ℝ) =>
      z.1.val i) := by
    have hcont : Continuous (fun z : BrownianCubeAnchor d × (Fin d → ℝ) => z.1.val i) :=
      (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
    exact hcont.measurable
  exact Measurable.ite (measurableSet_lt hleft hright)
    measurable_const measurable_const

theorem unitInterval_tailIndicator_integral (v : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (∫ t, (if v < t then (1:ℝ) else 0) ∂unitIntervalMeasure) = 1-v := by
  have hfun : (fun t : ℝ => if v < t then (1:ℝ) else 0) =
      Set.indicator (Set.Ioi v) (fun _ => (1:ℝ)) := by
    funext t
    by_cases h : v < t <;> simp [Set.indicator, h, Set.mem_Ioi]
  rw [hfun, integral_indicator_const (e := (1:ℝ)) measurableSet_Ioi]
  simp only [smul_eq_mul, mul_one]
  have hset : Set.Ioi v ∩ Set.Icc (0:ℝ) 1 = Set.Ioc v 1 := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨htv, ⟨ht0, ht1⟩⟩
      exact ⟨htv, ht1⟩
    · rintro ⟨htv, ht1⟩
      exact ⟨htv, ⟨le_trans hv0 htv.le, ht1⟩⟩
  have hmeasure : unitIntervalMeasure (Set.Ioi v) = ENNReal.ofReal (1-v) := by
    rw [unitIntervalMeasure, Measure.restrict_apply measurableSet_Ioi, hset,
      Real.volume_Ioc]
  rw [measureReal_def, hmeasure]
  simp [sub_nonneg.mpr hv1]

local instance : MeasureSpace UnitAddCircle :=
  @AddCircle.measureSpace (1:ℝ) ⟨by norm_num⟩
/-- The folded circle coordinate has uniform distribution on the unit
interval. -/
theorem triangleWave_map_volume :
    Measure.map triangleWave (volume : Measure UnitAddCircle) = unitIntervalMeasure := by
  haveI : IsFiniteMeasure (volume : Measure UnitAddCircle) := inferInstance
  haveI : IsFiniteMeasure unitIntervalMeasure := by
    dsimp [unitIntervalMeasure]
    infer_instance
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [MeasureTheory.integral_map continuous_triangleWave.measurable.aemeasurable
    f.continuous.aestronglyMeasurable]
  calc
    (∫ x : UnitAddCircle, f (triangleWave x) ∂volume) =
        ∫ t in Set.Ioc (0:ℝ) 1,
          f (triangleWave ((t:ℝ):UnitAddCircle)) ∂volume := by
            simpa only [zero_add] using (UnitAddCircle.integral_preimage 0
              (fun x => f (triangleWave x))).symm
    _ = ∫ t in Set.Ioc (0:ℝ) 1,
          f (foldUnitInterval (2*t)) ∂volume := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
            by_cases ht1 : t = 1
            · subst t
              simp [foldUnitInterval, triangleWave_eq_fold_representative,
                circleIcoRepresentative]
            · have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
              have htlt' : t < 0+1 := by simpa using htlt
              have hrep : t ∈ Set.Ico (0:ℝ) (0+1) := ⟨le_of_lt ht.1, htlt'⟩
              rw [triangleWave, AddCircle.liftIco_coe_apply hrep]
    _ = ∫ t in (0:ℝ)..1, f (foldUnitInterval (2*t)) := by
          rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    _ = (1/2:ℝ) * ∫ t in (0:ℝ)..2, f (foldUnitInterval t) := by
          rw [intervalIntegral.integral_comp_mul_left
            (f := fun t => f (foldUnitInterval t)) (by norm_num : (2:ℝ) ≠ 0)]
          norm_num [smul_eq_mul]
    _ = ∫ t in (0:ℝ)..1, f t := by
          have hfold := integral_foldUnitInterval (fun t => f t)
            (f.continuous.integrableOn_Icc)
          rw [hfold]
          ring
    _ = ∫ t in Set.Icc (0:ℝ) 1, f t ∂volume := by
          rw [integral_Icc_eq_integral_Ioc]
          rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]

/-- Coordinatewise folding sends normalized torus volume to the source cube
product measure. -/
theorem measurePreserving_foldCoordinates (d : ℕ) :
    MeasurePreserving (fun x : UnitAddTorus (Fin d) =>
        fun i => triangleWave (x i))
      (volume : Measure (UnitAddTorus (Fin d)))
      (Measure.pi (fun _ : Fin d => unitIntervalMeasure)) := by
  haveI : IsFiniteMeasure unitIntervalMeasure := by
    dsimp [unitIntervalMeasure]
    infer_instance
  haveI : ∀ i : Fin d, SigmaFinite unitIntervalMeasure := by
    intro i
    infer_instance
  have hcoord : MeasurePreserving triangleWave
      (volume : Measure UnitAddCircle) unitIntervalMeasure := by
    refine ⟨continuous_triangleWave.measurable, ?_⟩
    exact triangleWave_map_volume
  have hpi := measurePreserving_pi
    (fun _ : Fin d => (volume : Measure UnitAddCircle))
    (fun _ : Fin d => unitIntervalMeasure)
    (fun _ => hcoord)
  simpa [BrownianSharp.unitAddTorus_volume_eq_productHaar,
    BrownianSharp.unitAddCircle_volume_eq_haar] using hpi

theorem ae_unitCube_coordinates (d : ℕ) :
    ∀ᵐ u ∂Measure.pi (fun _ : Fin d => unitIntervalMeasure),
      ∀ i, u i ∈ Set.Icc (0:ℝ) 1 := by
  change ∀ᵐ u ∂Measure.pi (fun _ : Fin d =>
    volume.restrict (Set.Icc (0:ℝ) 1)), ∀ i, u i ∈ Set.Icc (0:ℝ) 1
  rw [← Measure.restrict_pi_pi]
  have hs : MeasurableSet
      (Set.univ.pi (fun _ : Fin d => Set.Icc (0:ℝ) 1)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hmem : ∀ᵐ u ∂(Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (Set.univ.pi (fun _ : Fin d => Set.Icc (0:ℝ) 1)),
      u ∈ Set.univ.pi (fun _ : Fin d => Set.Icc (0:ℝ) 1) :=
    ae_restrict_mem hs
  filter_upwards [hmem] with u hu
  intro i
  exact (Set.mem_univ_pi.mp hu) i

/-- Source kernel for the `k`th Fourier coefficient of an anchored path.
It averages the Fourier character over the torus rectangle above each source
point. -/
def anchoredSourceFourierKernel {d : ℕ} (k : Fin d → ℤ) (v : Fin d → ℝ) : ℂ :=
  ∫ x : UnitAddTorus (Fin d), UnitAddTorus.mFourier (-k) x *
    ((rectangleKernel (periodicFoldAnchor d x) v : ℝ) : ℂ) ∂volume

/-- Exact Fourier/source identity for the genuine periodic extension of an
Lp rectangular-integral path. This kernel form retains all coordinate-zero
components; for nonzero coordinates it can be evaluated by the usual
one-dimensional Fourier integral, while zero coordinates give weighted
marginals. -/
theorem periodicIntegrationPath_fourierCoeff_sourceKernel {d : ℕ} {p : ℝ}
    (hp : 1 < p)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff
      (fun x : UnitAddTorus (Fin d) =>
        ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ)) k =
      ∫ v, anchoredSourceFourierKernel k v * (g v : ℂ) ∂cubeMeasure d := by
  let μ : Measure (UnitAddTorus (Fin d)) := volume
  let ν : Measure (Fin d → ℝ) := cubeMeasure d
  have hμ : μ = Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle) := by
    dsimp [μ]
    exact unitAddTorus_volume_eq_productHaar d
  let A : (UnitAddTorus (Fin d) × (Fin d → ℝ)) → ℂ := fun z =>
    UnitAddTorus.mFourier (-k) z.1 *
      ((rectangleKernel (periodicFoldAnchor d z.1) z.2 : ℝ) : ℂ)
  let q : (UnitAddTorus (Fin d) × (Fin d → ℝ)) → ℂ := fun z =>
    A z * (g z.2 : ℂ)
  have hgInt : Integrable (g : (Fin d → ℝ) → ℝ) ν := by
    have hp1 : (1:ENNReal) ≤ ENNReal.ofReal p := by
      simpa using ENNReal.ofReal_le_ofReal hp.le
    exact (Lp.memLp g).integrable hp1
  haveI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hbaseReal : Integrable (fun z : UnitAddTorus (Fin d) × (Fin d → ℝ) =>
      ‖g z.2‖) (μ.prod ν) := by
    exact hgInt.norm.comp_snd μ
  have hbase : Integrable (fun z : UnitAddTorus (Fin d) × (Fin d → ℝ) =>
      (g z.2 : ℂ)) (μ.prod ν) := by
    have hbase' : Integrable (fun z : UnitAddTorus (Fin d) × (Fin d → ℝ) =>
        g z.2) (μ.prod ν) := hgInt.comp_snd μ
    exact Complex.ofRealCLM.integrable_comp hbase'
  have hkernelMeas : Measurable (fun z : UnitAddTorus (Fin d) × (Fin d → ℝ) =>
      rectangleKernel (periodicFoldAnchor d z.1) z.2) := by
    have hanchor : Measurable (fun z : UnitAddTorus (Fin d) × (Fin d → ℝ) =>
        periodicFoldAnchor d z.1) :=
      (continuous_periodicFoldAnchor d).measurable.comp measurable_fst
    exact measurable_rectangleKernel_joint.comp (hanchor.prodMk measurable_snd)
  have hAmeas : Measurable A := by
    exact ((UnitAddTorus.mFourier (-k)).continuous.measurable.comp measurable_fst).mul
      (Complex.continuous_ofReal.measurable.comp hkernelMeas)
  have hAbound : ∀ᵐ z ∂(μ.prod ν), ‖A z‖ ≤ 1 := by
    filter_upwards [] with z
    dsimp [A]
    rw [norm_mul, Complex.norm_real]
    calc
      ‖UnitAddTorus.mFourier (-k) z.1‖ *
          ‖(rectangleKernel (periodicFoldAnchor d z.1) z.2 : ℝ)‖ ≤
        1 * 1 := by
          gcongr
          · calc
              ‖UnitAddTorus.mFourier (-k) z.1‖ ≤ ‖UnitAddTorus.mFourier (-k)‖ :=
                (UnitAddTorus.mFourier (-k)).norm_coe_le_norm z.1
              _ = 1 := UnitAddTorus.mFourier_norm
          · exact rectangleKernel_norm_le _ _
      _ = 1 := by norm_num
  have hq : Integrable q (μ.prod ν) := by
    refine hbase.bdd_smul 1 hAmeas.aestronglyMeasurable ?_
    simpa [q, smul_eq_mul] using hAbound
  have hinner (x : UnitAddTorus (Fin d)) :
      ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ) =
        ∫ v, ((rectangleKernel (periodicFoldAnchor d x) v * g v : ℝ) : ℂ)
          ∂cubeMeasure d := by
    change ((integrationPath p hp g (periodicFoldAnchor d x) : ℝ) : ℂ) = _
    rw [integrationPath_apply, anchoredLpValue]
    calc
      ((∫ u, Latest.fractionalTensorKernel (fun _ : Fin d => (1:ℝ))
          (periodicFoldAnchor d x) u * g u ∂cubeMeasure d : ℝ) : ℂ) =
        ∫ u, ((Latest.fractionalTensorKernel (fun _ : Fin d => (1:ℝ))
          (periodicFoldAnchor d x) u * g u : ℝ) : ℂ) ∂cubeMeasure d :=
          (integral_complex_ofReal).symm
      _ = ∫ u, ((rectangleKernel (periodicFoldAnchor d x) u * g u : ℝ) : ℂ)
          ∂cubeMeasure d := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with u
            exact congrArg (fun a : ℝ => ((a * g u : ℝ) : ℂ))
              (AlignmentPaperAnchoredLpOperator.rectangleKernel_eq
                (periodicFoldAnchor d x) u).symm
  calc
    UnitAddTorus.mFourierCoeff
      (fun x : UnitAddTorus (Fin d) =>
        ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ)) k =
      ∫ x, UnitAddTorus.mFourier (-k) x *
        ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ) ∂μ := by
          unfold UnitAddTorus.mFourierCoeff
          rw [hμ]
          change (∫ t, UnitAddTorus.mFourier (-k) t •
            (fun x => ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ)) t
            ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) = _
          exact MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall fun x => by simp [smul_eq_mul])
    _ = ∫ x, ∫ v, q (x,v) ∂ν ∂μ := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with x
          dsimp [q, A]
          rw [hinner, ← MeasureTheory.integral_const_mul]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with v
          push_cast
          ring
    _ = ∫ z, q z ∂μ.prod ν := (MeasureTheory.integral_prod q hq).symm
    _ = ∫ v, ∫ x, q (x,v) ∂μ ∂ν := MeasureTheory.integral_prod_symm q hq
    _ = ∫ v, anchoredSourceFourierKernel k v * (g v : ℂ) ∂ν := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with v
          dsimp [q, A, anchoredSourceFourierKernel]
          rw [MeasureTheory.integral_mul_const]
    _ = ∫ v, anchoredSourceFourierKernel k v * (g v : ℂ)
        ∂cubeMeasure d := rfl

/-- One folded coordinate's exact scalar Fourier kernel. The zero frequency
contains the positive weight `(1-v)`; every nonzero frequency is retained
without discarding mixed-coordinate terms. -/
def anchoredScalarFourierKernel (n : ℤ) (v : ℝ) : ℂ :=
  ∫ x : UnitAddCircle,
    fourier (-n) x * (if v < triangleWave x then (1:ℂ) else 0) ∂volume

theorem anchoredScalarFourierKernel_zero (v : ℝ)
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    anchoredScalarFourierKernel 0 v = ((1-v:ℝ):ℂ) := by
  haveI : IsFiniteMeasure unitIntervalMeasure := by
    dsimp [unitIntervalMeasure]
    infer_instance
  let f : ℝ → ℂ := fun y => if v < y then (1:ℂ) else 0
  have hfmeas : Measurable f := by
    apply Measurable.ite
    · exact measurableSet_lt measurable_const measurable_id
    · exact measurable_const
    · exact measurable_const
  have hf : Integrable f unitIntervalMeasure := by
    refine Integrable.mono (μ := unitIntervalMeasure)
      (integrable_const (μ := unitIntervalMeasure) (1:ℂ))
      hfmeas.aestronglyMeasurable ?_
    filter_upwards [] with y
    by_cases h : v < y <;> simp [f, h]
  have hfmap : Integrable f (Measure.map triangleWave volume) := by
    rw [triangleWave_map_volume]
    exact hf
  calc
    anchoredScalarFourierKernel 0 v = ∫ x : UnitAddCircle, f (triangleWave x) ∂volume := by
      simp [anchoredScalarFourierKernel, f, fourier_zero]
    _ = ∫ y, f y ∂Measure.map triangleWave volume := by
      symm
      exact MeasureTheory.integral_map
        continuous_triangleWave.measurable.aemeasurable hfmap.aestronglyMeasurable
    _ = ∫ y, f y ∂unitIntervalMeasure := by rw [triangleWave_map_volume]
    _ = ((∫ y, (if v < y then (1:ℝ) else 0) ∂unitIntervalMeasure : ℝ) : ℂ) := by
      have hR : (∫ y, f y ∂unitIntervalMeasure).re =
          ∫ y, (if v < y then (1:ℝ) else 0) ∂unitIntervalMeasure := by
        change RCLike.re (∫ y, f y ∂unitIntervalMeasure) = _
        rw [← integral_re hf]
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        by_cases h : v < y <;> simp [f, h]
      have hI : (∫ y, f y ∂unitIntervalMeasure).im = 0 := by
        change RCLike.im (∫ y, f y ∂unitIntervalMeasure) = 0
        rw [← integral_im hf]
        calc
          (∫ y, (f y).im ∂unitIntervalMeasure) = ∫ y, (0:ℝ) ∂unitIntervalMeasure := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [] with y
            by_cases h : v < y <;> simp [f, h]
          _ = 0 := by simp
      apply Complex.ext
      · simpa [unitInterval_tailIndicator_integral v hv0 hv1] using hR
      · simpa using hI
    _ = ((1-v:ℝ):ℂ) := by
      rw [unitInterval_tailIndicator_integral v hv0 hv1]

/-- The full rectangle kernel separates into its one-dimensional coordinate
kernels. This is the exact frequency identity needed for blocks that include
coordinate-zero modes. -/
theorem anchoredSourceFourierKernel_eq_prod {d : ℕ}
    (k : Fin d → ℤ) (v : Fin d → ℝ) :
    anchoredSourceFourierKernel k v =
      ∏ i, anchoredScalarFourierKernel (k i) (v i) := by
  unfold anchoredSourceFourierKernel anchoredScalarFourierKernel
  have hfun : (fun x : UnitAddTorus (Fin d) =>
      UnitAddTorus.mFourier (-k) x *
        ((rectangleKernel (periodicFoldAnchor d x) v : ℝ) : ℂ)) =
      fun x => ∏ i, (fourier (-(k i)) (x i) *
        (if v i < triangleWave (x i) then (1:ℂ) else 0)) := by
    funext x
    simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply,
      rectangleKernel, periodicFoldAnchor, Complex.ofReal_prod]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    by_cases h : v i < triangleWave (x i) <;> simp [h]
  rw [hfun]
  rw [show (volume : Measure (UnitAddTorus (Fin d))) =
      Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle) by
        exact unitAddTorus_volume_eq_productHaar d]
  calc
    (∫ x : UnitAddTorus (Fin d),
        ∏ i, (fourier (-(k i)) (x i) *
          (if v i < triangleWave (x i) then (1:ℂ) else 0))
        ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) =
      ∏ i, ∫ x : UnitAddCircle,
        fourier (-(k i)) x * (if v i < triangleWave x then (1:ℂ) else 0)
        ∂AddCircle.haarAddCircle := by
          exact MeasureTheory.integral_fintype_prod_eq_prod
            (ι := Fin d) (E := fun _ : Fin d => UnitAddCircle)
            (μ := fun _ : Fin d => AddCircle.haarAddCircle)
            (fun i x => fourier (-(k i)) x *
              (if v i < triangleWave x then (1:ℂ) else 0))
    _ = ∏ i, anchoredScalarFourierKernel (k i) (v i) := by
      simp [anchoredScalarFourierKernel, unitAddCircle_volume_eq_haar]

/-- Mixed frequencies keep the coordinate-zero face weights explicitly.
The zero set contributes the factors `(1-vᵢ)`; all other coordinates retain
their scalar folded Fourier kernel. -/
theorem anchoredSourceFourierKernel_eq_mixedProd {d : ℕ}
    (k : Fin d → ℤ) (v : Fin d → ℝ)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) :
    anchoredSourceFourierKernel k v =
      ∏ i, if k i = 0 then ((1-v i:ℝ):ℂ)
        else anchoredScalarFourierKernel (k i) (v i) := by
  rw [anchoredSourceFourierKernel_eq_prod]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : k i = 0
  · simpa [h] using
      (anchoredScalarFourierKernel_zero (v i) (hv0 i) (hv1 i))
  · simp [h]

/-- Exact mixed-mode Fourier coefficients of the actual anchored periodic
path. This keeps every zero-coordinate lower-face contribution and has only
the canonical Lp representative as input. -/
theorem periodicIntegrationPath_fourierCoeff_mixedKernel {d : ℕ} {p : ℝ}
    (hp : 1 < p)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) (k : Fin d → ℤ) :
    UnitAddTorus.mFourierCoeff
      (fun x : UnitAddTorus (Fin d) =>
        ((periodicFoldExtension (integrationPath p hp g) x : ℝ) : ℂ)) k =
      ∫ v, (∏ i, if k i = 0 then ((1-v i:ℝ):ℂ)
          else anchoredScalarFourierKernel (k i) (v i)) * (g v : ℂ)
        ∂cubeMeasure d := by
  have hmeasure : cubeMeasure d =
      Measure.pi (fun _ : Fin d => unitIntervalMeasure) := by
    simp [cubeMeasure, AlignmentFractionalTensor.unitCube_measure_eq_pi,
      unitIntervalMeasure]
  have hbounds : ∀ᵐ v ∂cubeMeasure d, ∀ i, v i ∈ Set.Icc (0:ℝ) 1 := by
    rw [hmeasure]
    exact ae_unitCube_coordinates d
  rw [periodicIntegrationPath_fourierCoeff_sourceKernel]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hbounds] with v hv
  rw [anchoredSourceFourierKernel_eq_mixedProd k v
    (fun i => (hv i).1) (fun i => (hv i).2)]

end BrownianSharp.AlignmentPaperAnchoredLpSourceFourier
