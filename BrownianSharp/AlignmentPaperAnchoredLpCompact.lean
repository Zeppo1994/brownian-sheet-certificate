import BrownianSharp.AlignmentPaperAnchoredLpOperator
import BrownianSharp.CameronMartinFeatureModulus
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Topology.UniformSpace.Ascoli

/-! Compactness of the closure of the anchored `Lᵖ` integration image, `1 < p < ∞`:
the Arzelà–Ascoli step of the proof of Theorem 1.2. Closedness, via reflexivity
of `Lᵖ`, is proved in `AlignmentPaperAnchoredLpClosed`. -/

noncomputable section

set_option maxHeartbeats 600000

open MeasureTheory
open Set
open scoped ENNReal Topology

namespace BrownianSharp.AlignmentPaperAnchoredLpCompact

open BrownianSharp.AlignmentPaperAnchoredLp
open BrownianSharp.AlignmentPaperAnchoredLpOperator
open HaarQuarter

private def anchoredBoxSet {d : ℕ} (t : BrownianCubeAnchor d) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (0 : ℝ) (t.val i))

private theorem anchoredBoxSet_measurable {d : ℕ} (t : BrownianCubeAnchor d) :
    MeasurableSet (anchoredBoxSet t) := by
  exact MeasurableSet.univ_pi fun i => measurableSet_Icc

private theorem anchoredBoxSet_subset_cube {d : ℕ} (t : BrownianCubeAnchor d) :
    anchoredBoxSet t ⊆ CameronMartin.unitCubeSet d := by
  intro u hu i hi
  have hi' := (Set.mem_pi.mp hu) i hi
  exact ⟨hi'.1, hi'.2.trans (t.property i).2⟩

private theorem cube_measure_symmDiff_eq_ambient {d : ℕ}
    (x y : BrownianCubeAnchor d) :
    cubeMeasure d (symmDiff (anchoredBoxSet x) (anchoredBoxSet y)) =
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ))
        (symmDiff (anchoredBoxSet x) (anchoredBoxSet y)) := by
  rw [cubeMeasure, Measure.restrict_apply
    ((anchoredBoxSet_measurable x).symmDiff (anchoredBoxSet_measurable y))]
  congr 1
  apply Set.inter_eq_left.mpr
  intro u hu
  rcases hu with ⟨hxu, hyu⟩ | ⟨hyu, hxu⟩
  · exact anchoredBoxSet_subset_cube x hxu
  · exact anchoredBoxSet_subset_cube y hyu

private theorem ambient_box_measure_ne_top {d : ℕ} (t : BrownianCubeAnchor d) :
    (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) (anchoredBoxSet t) ≠ ∞ := by
  rw [show anchoredBoxSet t = Set.pi Set.univ
    (fun i => Set.Icc (0 : ℝ) (t.val i)) by rfl, Measure.pi_pi]
  apply ne_of_lt
  apply ENNReal.prod_lt_top
  intro i hi
  simp [Real.volume_Icc]

private theorem box_symmDiff_measure_eq_feature_norm_sq {d : ℕ}
    (x y : BrownianCubeAnchor d) :
    (cubeMeasure d).real (symmDiff (anchoredBoxSet x) (anchoredBoxSet y)) =
      ‖(CameronMartin.featureVector x : CameronMartin.AmbientL2 d) -
        (CameronMartin.featureVector y : CameronMartin.AmbientL2 d)‖ ^ 2 := by
  let μ : Measure (Fin d → ℝ) := Measure.pi fun _ : Fin d => (volume : Measure ℝ)
  have hcube : cubeMeasure d (symmDiff (anchoredBoxSet x) (anchoredBoxSet y)) =
      μ (symmDiff (anchoredBoxSet x) (anchoredBoxSet y)) := by
    simpa [μ] using cube_measure_symmDiff_eq_ambient x y
  change (cubeMeasure d (symmDiff (anchoredBoxSet x) (anchoredBoxSet y))).toReal = _
  rw [hcube]
  have hμx : μ (anchoredBoxSet x) ≠ ∞ := by
    simpa [μ] using ambient_box_measure_ne_top x
  have hμy : μ (anchoredBoxSet y) ≠ ∞ := by
    simpa [μ] using ambient_box_measure_ne_top y
  have hμxy : μ (symmDiff (anchoredBoxSet x) (anchoredBoxSet y)) ≠ ∞ := by
    apply measure_ne_top_of_subset (μ := μ) (s := CameronMartin.unitCubeSet d)
    · intro u hu
      rcases hu with ⟨hxu, hyu⟩ | ⟨hyu, hxu⟩
      · exact anchoredBoxSet_subset_cube x hxu
      · exact anchoredBoxSet_subset_cube y hyu
    · rw [CameronMartin.unitCubeSet, Measure.pi_pi]
      apply ne_of_lt
      apply ENNReal.prod_lt_top
      intro i hi
      simp [Real.volume_Icc]
  have hdist : dist (CameronMartin.featureVector x : CameronMartin.AmbientL2 d)
      (CameronMartin.featureVector y : CameronMartin.AmbientL2 d) =
      (μ.real (symmDiff (anchoredBoxSet x) (anchoredBoxSet y))) ^ (1 / 2 : ℝ) := by
    change dist (HaarQuarter.brownianSheetBoxIndicatorLp x.val)
      (HaarQuarter.brownianSheetBoxIndicatorLp y.val) = _
    change dist
      (MeasureTheory.indicatorConstLp (μ := μ) 2 (anchoredBoxSet_measurable x)
        hμx (1 : ℝ))
      (MeasureTheory.indicatorConstLp (μ := μ) 2 (anchoredBoxSet_measurable y)
        hμy (1 : ℝ)) = _
    rw [MeasureTheory.dist_indicatorConstLp_eq_norm (hμs := hμx) (hμt := hμy),
      MeasureTheory.norm_indicatorConstLp (hμs := hμxy) (by norm_num) (by norm_num)]
    simp [μ]
  have hsq := congrArg (fun z : ℝ => z ^ 2) hdist
  have hpow : (μ.real (symmDiff (anchoredBoxSet x) (anchoredBoxSet y)) ^ (1 / 2 : ℝ)) ^ 2 =
      μ.real (symmDiff (anchoredBoxSet x) (anchoredBoxSet y)) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt (by positivity)
  rw [hpow] at hsq
  have hdistnorm : dist (CameronMartin.featureVector x : CameronMartin.AmbientL2 d)
      (CameronMartin.featureVector y : CameronMartin.AmbientL2 d) =
      ‖(CameronMartin.featureVector x : CameronMartin.AmbientL2 d) -
        CameronMartin.featureVector y‖ := dist_eq_norm _ _
  rw [hdistnorm] at hsq
  simpa [μ, MeasureTheory.measureReal_def] using hsq.symm

private theorem tendsto_box_symmDiff_measure {d : ℕ} (x : BrownianCubeAnchor d) :
    Filter.Tendsto (fun y : BrownianCubeAnchor d =>
      cubeMeasure d (symmDiff (anchoredBoxSet y) (anchoredBoxSet x))) (𝓝 x) (𝓝 0) := by
  -- The measure is the squared distance between the actual L² box features.
  have hcont : Filter.Tendsto (fun y : BrownianCubeAnchor d =>
      ‖(CameronMartin.featureVector y : CameronMartin.AmbientL2 d) -
        CameronMartin.featureVector x‖ ^ 2) (𝓝 x) (𝓝 0) := by
    have hfeatureCont : Continuous (fun y : BrownianCubeAnchor d =>
        (CameronMartin.featureVector y : CameronMartin.AmbientL2 d)) :=
      continuous_subtype_val.comp (CameronMartin.featureVector_continuous d)
    have hfeature : Filter.Tendsto (fun y : BrownianCubeAnchor d =>
        (CameronMartin.featureVector y : CameronMartin.AmbientL2 d)) (𝓝 x)
        (𝓝 (CameronMartin.featureVector x)) :=
      hfeatureCont.continuousAt
    have hsub : Filter.Tendsto (fun y : BrownianCubeAnchor d =>
        (CameronMartin.featureVector y : CameronMartin.AmbientL2 d) -
          (CameronMartin.featureVector x : CameronMartin.AmbientL2 d)) (𝓝 x) (𝓝 0) :=
      by simpa using hfeature.sub (tendsto_const_nhds :
        Filter.Tendsto (fun _ : BrownianCubeAnchor d =>
          (CameronMartin.featureVector x : CameronMartin.AmbientL2 d)) (𝓝 x)
          (𝓝 (CameronMartin.featureVector x)))
    have hnorm := hsub.norm
    simpa using hnorm.pow 2
  have hreal : Filter.Tendsto (fun y : BrownianCubeAnchor d =>
      (cubeMeasure d).real (symmDiff (anchoredBoxSet y) (anchoredBoxSet x)))
      (𝓝 x) (𝓝 0) := by
    simpa only [box_symmDiff_measure_eq_feature_norm_sq] using hcont
  have htoENN := ENNReal.tendsto_ofReal hreal
  have htoENN' : Filter.Tendsto
      (fun y : BrownianCubeAnchor d =>
        ENNReal.ofReal ((cubeMeasure d).real
          (symmDiff (anchoredBoxSet y) (anchoredBoxSet x)))) (𝓝 x) (𝓝 0) := by
    simpa using htoENN
  apply Filter.Tendsto.congr' ?_ htoENN'
  filter_upwards with y
  exact ENNReal.ofReal_toReal (measure_ne_top (cubeMeasure d)
    (symmDiff (anchoredBoxSet y) (anchoredBoxSet x)))

private def boxIndicatorLp {d : ℕ} (q : ℝ) (t : BrownianCubeAnchor d) :
    Lp ℝ (ENNReal.ofReal q) (cubeMeasure d) :=
  MeasureTheory.indicatorConstLp (ENNReal.ofReal q) (anchoredBoxSet_measurable t)
    (by
      haveI := cubeProbability d
      finiteness) (1 : ℝ)

private theorem continuous_boxIndicatorLp {d : ℕ} (q : ℝ) (hq : 1 < q)
    [Fact (1 ≤ ENNReal.ofReal q)] :
    Continuous (fun t : BrownianCubeAnchor d => boxIndicatorLp q t) := by
  haveI := cubeProbability d
  have hqtop : ENNReal.ofReal q ≠ ∞ := ENNReal.ofReal_ne_top
  simpa [boxIndicatorLp] using
    (MeasureTheory.continuous_indicatorConstLp_set (μ := cubeMeasure d)
      (p := ENNReal.ofReal q) (c := (1 : ℝ)) hqtop tendsto_box_symmDiff_measure)

private theorem boxIndicatorLp_coeFn_eq_rectangleKernel {d : ℕ}
    (q : ℝ) (t : BrownianCubeAnchor d) :
    (boxIndicatorLp q t : (Fin d → ℝ) → ℝ) =ᵐ[cubeMeasure d]
      rectangleKernel t := by
  have hrep : (boxIndicatorLp q t : (Fin d → ℝ) → ℝ) =ᵐ[cubeMeasure d]
      (anchoredBoxSet t).indicator (fun _ => (1 : ℝ)) := by
    simpa [boxIndicatorLp] using (MeasureTheory.indicatorConstLp_coeFn
    (p := ENNReal.ofReal q) (μ := cubeMeasure d)
    (hs := anchoredBoxSet_measurable t) (hμs := by
      haveI := cubeProbability d
      finiteness) (c := (1 : ℝ)))
  have hne : ∀ᵐ u ∂cubeMeasure d, ∀ i : Fin d, u i ≠ t.val i := by
    rw [cubeMeasure, AlignmentFractionalTensor.unitCube_measure_eq_pi]
    exact ae_all_iff.mpr (fun i =>
      Measure.ae_eval_ne (fun _ : Fin d =>
        (volume : Measure ℝ).restrict (Set.Icc (0 : ℝ) 1)) i (t.val i))
  have hcube : ∀ᵐ u ∂cubeMeasure d, u ∈ CameronMartin.unitCubeSet d :=
    MeasureTheory.ae_restrict_mem (CameronMartin.measurableSet_unitCubeSet d)
  filter_upwards [hrep, hne, hcube] with u hu hne huCube
  rw [hu]
  have hbox : u ∈ anchoredBoxSet t ↔ ∀ i, u i < t.val i := by
    rw [anchoredBoxSet, Set.mem_pi]
    constructor
    · intro hb i
      have hcoord := hb i (Set.mem_univ i)
      exact lt_of_le_of_ne hcoord.2 (hne i)
    · intro hb i hi
      exact ⟨(huCube i hi).1, (hb i).le⟩
  have hprod : (∏ i : Fin d, if u i < t.val i then (1 : ℝ) else 0) =
      (if ∀ i, u i < t.val i then 1 else 0) := by
    classical
    by_cases hall : ∀ i, u i < t.val i
    · simp [hall]
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      rw [if_neg hall]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  simpa [rectangleKernel, Set.indicator, hbox] using hprod.symm

private theorem norm_Lp_eq_integral_rpow {d : ℕ} {r : ℝ} (hr : 0 < r)
    (g : Lp ℝ (ENNReal.ofReal r) (cubeMeasure d)) :
    ‖g‖ = (∫ u, ‖g u‖ ^ r ∂cubeMeasure d) ^ (1 / r) := by
  rw [Lp.norm_def, (Lp.memLp g).eLpNorm_eq_integral_rpow_norm
    (ne_of_gt (ENNReal.ofReal_pos.mpr hr)) ENNReal.ofReal_ne_top]
  rw [ENNReal.toReal_ofReal]
  · simp [ENNReal.toReal_ofReal hr.le]
  · positivity

private theorem anchoredLpValue_eq_box_pairing {d : ℕ} {p q : ℝ}
    (hp : 1 < p) (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d)) (hq : 1 < q)
    (t : BrownianCubeAnchor d) :
    anchoredLpValue p g t = ∫ u, (boxIndicatorLp q t) u * g u ∂cubeMeasure d := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp.le
  have hgint : Integrable (fun u => rectangleKernel t u * g u) (cubeMeasure d) :=
    integrable_kernel_mul _ ((Lp.memLp g).integrable hp1) t
  have hboxint : Integrable (fun u => (boxIndicatorLp q t) u * g u) (cubeMeasure d) := by
    apply hgint.congr
    filter_upwards [boxIndicatorLp_coeFn_eq_rectangleKernel q t] with u hu
    simp [hu]
  unfold anchoredLpValue
  calc
    (∫ u, Latest.fractionalTensorKernel (fun _ : Fin d => (1 : ℝ)) t u * g u
        ∂cubeMeasure d) =
        ∫ u, (boxIndicatorLp q t) u * g u ∂cubeMeasure d := by
          apply integral_congr_ae
          filter_upwards [boxIndicatorLp_coeFn_eq_rectangleKernel q t] with u hu
          rw [← rectangleKernel_eq t u, ← hu]
    _ = _ := rfl

private theorem anchoredLpValue_sub_le_boxDistance {d : ℕ} {p q : ℝ}
    (hp : 1 < p) (hpq : p.HolderConjugate q) (hq : 1 < q)
    (g : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d))
    (x y : BrownianCubeAnchor d) :
    |anchoredLpValue p g x - anchoredLpValue p g y| ≤
      ‖g‖ * dist (boxIndicatorLp q x) (boxIndicatorLp q y) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal q) := ⟨by
    have hq' : 1 ≤ q := le_of_lt hq
    simpa using ENNReal.ofReal_le_ofReal hq'⟩
  let kx := boxIndicatorLp q x
  let ky := boxIndicatorLp q y
  have hx := anchoredLpValue_eq_box_pairing hp g hq x
  have hy := anchoredLpValue_eq_box_pairing hp g hq y
  have hix : Integrable (fun u => kx u * g u) (cubeMeasure d) := by
    have h := (integrable_kernel_mul _ ((Lp.memLp g).integrable (by
      have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
        have : 1 ≤ p := le_of_lt hp
        simpa using ENNReal.ofReal_le_ofReal this
      exact this)) x)
    apply h.congr
    filter_upwards [boxIndicatorLp_coeFn_eq_rectangleKernel q x] with u hu
    simp [kx, ← rectangleKernel_eq, hu]
  have hiy : Integrable (fun u => ky u * g u) (cubeMeasure d) := by
    have h := (integrable_kernel_mul _ ((Lp.memLp g).integrable (by
      have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
        have : 1 ≤ p := le_of_lt hp
        simpa using ENNReal.ofReal_le_ofReal this
      exact this)) y)
    apply h.congr
    filter_upwards [boxIndicatorLp_coeFn_eq_rectangleKernel q y] with u hu
    simp [ky, ← rectangleKernel_eq, hu]
  let kdiff : Lp ℝ (ENNReal.ofReal q) (cubeMeasure d) := kx - ky
  have hdiffInt : Integrable (fun u => kdiff u * g u) (cubeMeasure d) := by
    have h := hix.sub hiy
    apply h.congr
    filter_upwards [Lp.coeFn_sub kx ky] with u hu
    rw [hu]
    simp only [Pi.sub_apply]
    ring
  have hrepr : anchoredLpValue p g x - anchoredLpValue p g y =
      ∫ u, kdiff u * g u ∂cubeMeasure d := by
    rw [hx, hy]
    rw [← integral_sub hix hiy]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub kx ky] with u hu
    rw [hu]
    simp only [Pi.sub_apply]
    ring
  have hHolder := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hpq
    (Lp.memLp g) (Lp.memLp kdiff)
  have hnormG := norm_Lp_eq_integral_rpow (d := d) hpq.pos g
  have hnormK := norm_Lp_eq_integral_rpow (d := d) hpq.symm.pos kdiff
  have hbound : ∫ u, ‖g u‖ * ‖kdiff u‖ ∂cubeMeasure d ≤ ‖g‖ * ‖kdiff‖ := by
    calc
      _ ≤ (∫ u, ‖g u‖ ^ p ∂cubeMeasure d) ^ (1 / p) *
          (∫ u, ‖kdiff u‖ ^ q ∂cubeMeasure d) ^ (1 / q) := hHolder
      _ = ‖g‖ * ‖kdiff‖ := by rw [hnormG, hnormK]
  have hnormInt := norm_integral_le_integral_norm (μ := cubeMeasure d)
    (fun u => kdiff u * g u)
  rw [hrepr]
  calc
    |∫ u, kdiff u * g u ∂cubeMeasure d| ≤
        ∫ u, ‖kdiff u * g u‖ ∂cubeMeasure d := by
          simpa [Real.norm_eq_abs] using hnormInt
    _ = ∫ u, ‖g u‖ * ‖kdiff u‖ ∂cubeMeasure d := by
      apply integral_congr_ae
      filter_upwards with u
      rw [norm_mul, mul_comm]
    _ ≤ ‖g‖ * ‖kdiff‖ := hbound
    _ = ‖g‖ * dist kx ky := by
      congr 1
      change ‖kx - ky‖ = dist kx ky
      exact (dist_eq_norm_sub kx ky).symm

private theorem exists_holder_conjugate {p : ℝ} (hp : 1 < p) :
    ∃ q : ℝ, p.HolderConjugate q ∧ 1 < q := by
  refine ⟨p / (p - 1), ?_, ?_⟩
  · apply Real.holderConjugate_iff.mpr
    constructor
    · linarith
    · field_simp
      <;> linarith
  · have hden : 0 < p - 1 := by linarith
    have hq : p / (p - 1) = 1 + 1 / (p - 1) := by field_simp <;> ring
    rw [hq]
    have : 0 < 1 / (p - 1) := one_div_pos.mpr hden
    linarith

theorem anchoredIntegrationLpImage_equicontinuous {d : ℕ} {p : ℝ}
    (hp : 1 < p) :
    Equicontinuous ((↑) : anchoredIntegrationLpImage d p →
      BrownianCubeAnchor d → ℝ) := by
  rcases exists_holder_conjugate hp with ⟨q, hpq, hq⟩
  haveI : Fact (1 ≤ ENNReal.ofReal q) := ⟨by
    simpa using ENNReal.ofReal_le_ofReal hq.le⟩
  haveI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    simpa using ENNReal.ofReal_le_ofReal hp.le⟩
  have hbox : Continuous (fun t : BrownianCubeAnchor d => boxIndicatorLp q t) :=
    continuous_boxIndicatorLp q hq
  have hboxOn : ContinuousOn (fun t : BrownianCubeAnchor d => boxIndicatorLp q t)
      Set.univ := continuousOn_univ.mpr hbox
  have hboxUC : UniformContinuousOn (fun t : BrownianCubeAnchor d => boxIndicatorLp q t)
      Set.univ := isCompact_univ.uniformContinuousOn_of_continuous hboxOn
  intro x
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.uniformContinuousOn_iff.mp hboxUC) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro y hy f
  rcases f.property with ⟨g, hg, hfg⟩
  have hinc := anchoredLpValue_sub_le_boxDistance hp hpq hq g x y
  have hdist : dist (f.val x) (f.val y) =
      |anchoredLpValue p g x - anchoredLpValue p g y| := by
    rw [Real.dist_eq, ← hfg x, ← hfg y]
  calc
    dist (f.val x) (f.val y) =
        |anchoredLpValue p g x - anchoredLpValue p g y| := hdist
    _ ≤ ‖g‖ * dist (boxIndicatorLp q x) (boxIndicatorLp q y) := hinc
    _ ≤ dist (boxIndicatorLp q x) (boxIndicatorLp q y) := by
      exact (mul_le_mul_of_nonneg_right hg dist_nonneg).trans_eq (one_mul _)
    _ < ε := hclose x (Set.mem_univ x) y (Set.mem_univ y)
      (by simpa [dist_comm] using hy)

private theorem anchoredIntegrationLpImage_pointwise_norm_le_one {d : ℕ}
    {p : ℝ} (hp : 1 < p) (f : C(BrownianCubeAnchor d, ℝ))
    (hf : f ∈ anchoredIntegrationLpImage d p) (t : BrownianCubeAnchor d) :
    ‖f t‖ ≤ 1 := by
  rcases hf with ⟨g, hg, hfg⟩
  have hnorm : ‖integrationPath p hp g‖ ≤ 1 :=
    (integrationPath_norm_le p hp g).trans hg
  have heval : ‖integrationPath p hp g t‖ ≤ ‖integrationPath p hp g‖ := by
    exact (ContinuousMap.norm_le (integrationPath p hp g) (norm_nonneg _)).mp le_rfl t
  simpa [integrationPath_apply, hfg t] using heval.trans hnorm

/-- The anchored `Lᵖ` image is relatively compact in the uniform norm (Arzelà–Ascoli). -/
theorem anchoredIntegrationLpImage_closure_isCompact {d : ℕ} {p : ℝ}
    (hp : 1 < p) : IsCompact (closure (anchoredIntegrationLpImage d p)) := by
  let 𝔖 : Set (Set (BrownianCubeAnchor d)) := {K | IsCompact K}
  have h𝔖 : ∀ K ∈ 𝔖, IsCompact K := by intro K hK; exact hK
  have hcover : ⋃₀ 𝔖 = Set.univ := by
    ext x
    constructor
    · intro _
      simp
    · intro _
      rw [Set.mem_sUnion]
      exact ⟨{x}, isCompact_singleton, by simp⟩
  haveI : T2Space (UniformOnFun (BrownianCubeAnchor d) ℝ 𝔖) :=
    UniformOnFun.t2Space_of_covering hcover
  have hF : Topology.IsClosedEmbedding
      ((UniformOnFun.ofFun 𝔖) ∘ fun f : C(BrownianCubeAnchor d, ℝ) => (f : BrownianCubeAnchor d → ℝ)) := by
    change Topology.IsClosedEmbedding ContinuousMap.toUniformOnFunIsCompact
    exact ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding
  have hEq : ∀ K ∈ 𝔖,
      EquicontinuousOn
        ((fun f : C(BrownianCubeAnchor d, ℝ) => (f : BrownianCubeAnchor d → ℝ)) ∘
          ((↑) : anchoredIntegrationLpImage d p → C(BrownianCubeAnchor d, ℝ))) K := by
    intro K hK
    exact (anchoredIntegrationLpImage_equicontinuous hp).equicontinuousOn K
  have hPoint : ∀ K ∈ 𝔖, ∀ x ∈ K,
      ∃ Q : Set ℝ, IsCompact Q ∧
        ∀ f ∈ anchoredIntegrationLpImage d p, f x ∈ Q := by
    intro K hK x hx
    refine ⟨Metric.closedBall 0 1, isCompact_closedBall 0 1, ?_⟩
    intro f hf
    have hnorm := anchoredIntegrationLpImage_pointwise_norm_le_one hp f hf x
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
  exact ArzelaAscoli.isCompact_closure_of_isClosedEmbedding h𝔖 hF hEq hPoint

/-- The actual anchored integration operator is compact for every finite
`p > 1`. This is the operator-compactness conclusion; it does not assert that
the image of the closed source ball is itself closed when `p ≠ 2`. -/
theorem anchoredIntegrationOperator_isCompact {d : ℕ} {p : ℝ} (hp : 1 < p)
    [Fact ((1 : ℝ≥0∞) ≤ ENNReal.ofReal p)] :
    IsCompactOperator (anchoredIntegrationOperator (d := d) p hp :
      Lp ℝ (ENNReal.ofReal p) (cubeMeasure d) →ₛₗ[RingHom.id ℝ]
        C(BrownianCubeAnchor d, ℝ)) := by
  let u : Lp ℝ (ENNReal.ofReal p) (cubeMeasure d) →ₛₗ[RingHom.id ℝ]
      C(BrownianCubeAnchor d, ℝ) := anchoredIntegrationOperator (d := d) p hp
  change IsCompactOperator u
  rw [isCompactOperator_iff_isCompact_closure_image_closedBall
    (f := u) (r := 1) (by norm_num)]
  change IsCompact (closure
    (anchoredIntegrationOperator (d := d) p hp '' Metric.closedBall 0 1))
  rw [anchoredIntegrationOperator_image_eq]
  exact anchoredIntegrationLpImage_closure_isCompact hp

end BrownianSharp.AlignmentPaperAnchoredLpCompact
