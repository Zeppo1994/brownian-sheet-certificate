import BrownianSharp.CameronMartin
import BrownianSharp.AlignmentGaussianRates
import BrownianSharp.AlignmentLatestStatements
import BrownianSharp.AlignmentFractionalTranslation
import BrownianSharp.AlignmentL2TensorProduct
import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.BrownianSheetCubeIsonormal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-!
# Bochner-integrated Brownian sheet features

This file constructs positive-order integrated Gaussian coordinates through
the sheet's existing isonormal feature-space realization.  The construction
does not assume an integrated Gaussian process as input.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianBochner

open HaarQuarter BrownianSharp.CameronMartin
open BrownianSharp.AlignmentFractionalL2 BrownianSharp.AlignmentFractionalTranslation

noncomputable section

/-- The scalar box indicator as a vector in unit-interval `L²`. -/
noncomputable def unitBoxFeature (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    AlignmentFractionalL2.UnitL2 :=
  indicatorConstLp 2 (s := Set.Icc (0 : ℝ) t) measurableSet_Icc
    (measure_ne_top _ _) 1

/-- At order one, the translated causal kernel is the Brownian box feature;
the closed/strict endpoint convention differs only on null singletons. -/
theorem unitBoxFeature_eq_orderOneKernel (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    unitBoxFeature t ht0 ht1 =
      AlignmentFractionalL2.kernelVector 1 t (by norm_num) ht0 ht1 := by
  apply Lp.ext
  let μ := volume.restrict (Set.Icc (0 : ℝ) 1)
  have hkernel :
      AlignmentFractionalL2.kernelVector 1 t (by norm_num) ht0 ht1 =ᵐ[μ]
        (fun u : ℝ => if u < t then (1 : ℝ) else 0) := by
    have hrepr :=
      (AlignmentFractionalL2.causalKernel_memLp_unit (α := 1) (by norm_num) ht0 ht1).coeFn_toLp
    filter_upwards [hrepr] with u hu
    have hgamma : Real.Gamma (1 : ℝ) = 1 := by
      simpa using Real.Gamma_nat_eq_factorial 0
    by_cases h : u < t
    · simpa [AlignmentFractionalL2.kernelVector,
        AlignmentFractionalL2.causalKernel,
        AlignmentFractionalKernel.kernel, h, hgamma] using hu
    · simpa [AlignmentFractionalL2.kernelVector,
        AlignmentFractionalL2.causalKernel, h] using hu
  have hbox : unitBoxFeature t ht0 ht1 =ᵐ[μ]
      (Set.Icc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) :=
    indicatorConstLp_coeFn
  filter_upwards [hkernel, hbox, Measure.ae_ne μ 0, Measure.ae_ne μ t,
    ae_restrict_mem measurableSet_Icc] with u hk hb hne0 hnet hunit
  have hu0 : 0 ≤ u := hunit.1
  have hmem : u ∈ Set.Icc (0 : ℝ) t ↔ u < t := by
    constructor
    · rintro ⟨_, hut⟩
      exact lt_of_le_of_ne hut hnet
    · intro hut
      exact ⟨hu0, le_of_lt hut⟩
  by_cases h : u < t
  · have h' : u ∈ Set.Icc (0 : ℝ) t := hmem.mpr h
    simp [Set.indicator, h, h', hk, hb]
  · have h' : u ∉ Set.Icc (0 : ℝ) t := fun q => h (hmem.mp q)
    simp [Set.indicator, h, h', hk, hb]

/-- Pairing a translated scalar kernel feature against a source is the scalar
Riemann--Liouville evaluation functional. -/
theorem inner_translatedKernel_eq_fractionalRL (α : ℝ) (hα : 1/2 < α)
    (g : AlignmentFractionalL2.UnitL2) (t : AlignmentFractionalL2.UnitInterval) :
    ⟪g, AlignmentFractionalTranslation.translatedUnitKernelFamily α hα t⟫ =
      AlignmentFractionalTranslation.fractionalRL α hα g t := by
  rw [AlignmentFractionalTranslation.translatedUnitKernelFamily_eq_kernelVector
    α t.1 hα t.2.1 t.2.2]
  rw [AlignmentFractionalTranslation.fractionalRL_apply α hα g t.1 t.2.1 t.2.2,
    L2.inner_def]
  have hk := (AlignmentFractionalL2.causalKernel_memLp_unit hα t.2.1 t.2.2).coeFn_toLp
  apply integral_congr_ae
  filter_upwards [hk] with u hu
  have hu' : AlignmentFractionalL2.kernelVector α t.1 hα t.2.1 t.2.2 u =
      AlignmentFractionalL2.causalKernel α t.1 u := by
    simpa [AlignmentFractionalL2.kernelVector] using hu
  rw [hu']
  simp [mul_comm]

private instance featureSpanComplete (d : ℕ) : CompleteSpace (brownianCubeBoxSpan d) :=
  completeSpace_coe_iff_isComplete.mpr
    (Submodule.isClosed_topologicalClosure _).isComplete

/-- Feature at the point obtained by scaling the `i`th coordinate of `x` by
`v`; clamping extends the curve continuously to all real `v`. -/
def scaledSheetFeature {d : ℕ} (i : Fin d) (x : BrownianCubeAnchor d)
    (v : ℝ) : brownianCubeBoxSpan d :=
  featureVector (brownianCubeClamp d (Function.update x.val i (x.val i * v)))

theorem continuous_scaledSheetFeature {d : ℕ} (i : Fin d)
    (x : BrownianCubeAnchor d) : Continuous (scaledSheetFeature i x) := by
  unfold scaledSheetFeature
  exact (featureVector_continuous d).comp
    ((continuous_brownianCubeClamp d).comp (by fun_prop))

/-- The canonical `L²` class of an evaluation of a continuous Gaussian sheet. -/
noncomputable def brownianEvalToLp {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (x : BrownianCubeAnchor d) : Lp ℝ 2 P :=
  (show MemLp (B.eval x) 2 P from by
    change MemLp (fun ω => B.path ω x) 2 P
    exact (B.gaussian.hasGaussianLaw_eval x).memLp_two).toLp (B.eval x)

@[simp] theorem brownianEvalToLp_eq {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (x : BrownianCubeAnchor d) :
    brownianEvalToLp B x =
      ((B.gaussian.hasGaussianLaw_eval x).memLp_two).toLp (B.eval x) := by
  simp [brownianEvalToLp]

theorem brownianEvalToLp_norm_le_one {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (x : BrownianCubeAnchor d) :
    ‖brownianEvalToLp B x‖ ≤ 1 := by
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Unit) B
  rw [brownianEvalToLp_eq]
  rw [← hT x]
  rw [T.norm_map]
  simpa [featureVector] using featureVector_norm_le_one x

/-- The second moment of each unit-cube Brownian sheet evaluation is bounded
by one, using the isonormal feature realization. -/
theorem brownianEval_integral_sq_le_one {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (x : BrownianCubeAnchor d) :
    ∫ ω, (B.eval x ω) ^ 2 ∂P ≤ 1 := by
  let hmem : MemLp (B.eval x) 2 P := (B.eval_gaussian x).memLp_two
  let f : Lp ℝ 2 P := brownianEvalToLp B x
  have hrep : (fun ω => f ω) =ᵐ[P] B.eval x := by
    simpa [f, brownianEvalToLp] using hmem.coeFn_toLp
  have hsqint : Integrable (fun ω => (B.eval x ω) ^ 2) P := by
    convert hmem.integrable_mul hmem using 1
    ext ω
    simp [pow_two]
  have hsq : ∫ ω, (B.eval x ω) ^ 2 ∂P = ‖f‖ ^ 2 := by
    calc
      ∫ ω, (B.eval x ω) ^ 2 ∂P = ∫ ω, (f ω) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hrep] with ω hω
        simp [hω]
      _ = ⟪f, f⟫ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards with ω
        change (f ω) ^ 2 = (f ω) * (f ω)
        ring
      _ = ‖f‖ ^ 2 := real_inner_self_eq_norm_sq f
  have hnorm := brownianEvalToLp_norm_le_one B x
  rw [hsq]
  nlinarith [norm_nonneg f]

/-- On a probability space, the first absolute moment of a unit-cube sheet
evaluation is at most one. -/
theorem brownianEval_integral_norm_le_one {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (x : BrownianCubeAnchor d) :
    ∫ ω, ‖B.eval x ω‖ ∂P ≤ 1 := by
  let hmem : MemLp (B.eval x) 2 P := (B.eval_gaussian x).memLp_two
  have hnormint : Integrable (fun ω => ‖B.eval x ω‖) P := hmem.norm.integrable (by norm_num)
  have hsqint : Integrable (fun ω => (B.eval x ω) ^ 2) P := by
    convert hmem.integrable_mul hmem using 1
    ext ω
    simp [pow_two]
  have hmajor : ∀ ω, ‖B.eval x ω‖ ≤ (1 + (B.eval x ω) ^ 2) / 2 := by
    intro ω
    have habs : ‖B.eval x ω‖ = |B.eval x ω| := Real.norm_eq_abs _
    rw [habs]
    by_cases h : 0 ≤ B.eval x ω
    · rw [abs_of_nonneg h]
      nlinarith [sq_nonneg (B.eval x ω - 1)]
    · rw [abs_of_nonpos (le_of_not_ge h)]
      nlinarith [sq_nonneg (B.eval x ω + 1)]
  have hright : Integrable (fun ω => (1 + (B.eval x ω) ^ 2) / 2) P := by
    have heq : (fun ω => (1 + (B.eval x ω) ^ 2) / 2) =
        (fun _ : Ω => (1 / 2 : ℝ)) +
          (fun ω => (1 / 2 : ℝ) * (B.eval x ω) ^ 2) := by
      ext ω
      simp
      ring
    rw [heq]
    exact (integrable_const (1 / 2 : ℝ)).add (hsqint.const_mul (1 / 2 : ℝ))
  calc
    ∫ ω, ‖B.eval x ω‖ ∂P ≤
        ∫ ω, (1 + (B.eval x ω) ^ 2) / 2 ∂P :=
      integral_mono_ae hnormint hright (Filter.Eventually.of_forall hmajor)
    _ = (1 + ∫ ω, (B.eval x ω) ^ 2 ∂P) / 2 := by
      calc
        _ = ∫ ω, (1 / 2 : ℝ) + (1 / 2) * (B.eval x ω) ^ 2 ∂P := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun ω => by ring)
        _ = (∫ _ω, (1 / 2 : ℝ) ∂P) +
            ∫ ω, (1 / 2 : ℝ) * (B.eval x ω) ^ 2 ∂P :=
          integral_add (integrable_const (1 / 2 : ℝ))
            (hsqint.const_mul (1 / 2 : ℝ))
        _ = (1 + ∫ ω, (B.eval x ω) ^ 2 ∂P) / 2 := by
          rw [integral_const, integral_const_mul]
          simp
          ring
    _ ≤ 1 := by
      have hsq := brownianEval_integral_sq_le_one B x
      linarith

/-- The clamped coordinate curve used by the pathwise integration operator. -/
def integratedSheetAnchor {d : ℕ} (i : Fin d)
    (x : BrownianCubeAnchor d) (v : ℝ) : BrownianCubeAnchor d :=
  brownianCubeClamp d (Function.update x.val i (x.val i * v))

/-- The deterministic feature of a Brownian sheet path integrated once in
coordinate `i`, using the same affine parametrization as the path operator. -/
def integratedSheetFeature {d : ℕ} (i : Fin d) (x : BrownianCubeAnchor d) :
    brownianCubeBoxSpan d :=
  ∫ v in Set.Icc (0 : ℝ) 1, x.val i • scaledSheetFeature i x v ∂volume

theorem continuous_integratedSheetAnchor {d : ℕ} (i : Fin d)
    (x : BrownianCubeAnchor d) : Continuous (integratedSheetAnchor i x) := by
  unfold integratedSheetAnchor
  exact continuous_brownianCubeClamp d |>.comp (by fun_prop)

/-- Joint measurability of the sheet along an integration curve and the
sample variable. -/
theorem measurable_brownianSheetEvalCurve {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) (i : Fin d)
    (x : BrownianCubeAnchor d) :
    Measurable (fun p : ℝ × Ω => B.eval (integratedSheetAnchor i x p.1) p.2) := by
  let hpair : ℝ × Ω → C(BrownianCubeAnchor d, ℝ) × BrownianCubeAnchor d :=
    fun p => (B.path p.2, integratedSheetAnchor i x p.1)
  have hmeas : Measurable hpair := by
    apply Measurable.prodMk
    · exact B.measurable_path.comp measurable_snd
    · exact (continuous_integratedSheetAnchor i x).measurable.comp measurable_fst
  exact ContinuousEval.continuous_eval.measurable.comp hmeas

/-- Evaluation along a compact coordinate curve is integrable on the product
of the coordinate interval and the probability space. This is the Fubini
bridge needed to identify pathwise integrals with their `L²` Bochner forms. -/
theorem integrable_brownianSheetEvalCurve {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (i : Fin d)
    (x : BrownianCubeAnchor d) :
    Integrable
      (fun p : ℝ × Ω => B.eval (integratedSheetAnchor i x p.1) p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod P) := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let F : ℝ × Ω → ℝ := fun p => B.eval (integratedSheetAnchor i x p.1) p.2
  have hF : Measurable F := measurable_brownianSheetEvalCurve B i x
  have hsm : StronglyMeasurable F := hF.stronglyMeasurable
  have hnormsm : StronglyMeasurable (fun p => ‖F p‖) := hsm.norm
  have hinner : StronglyMeasurable (fun v => ∫ ω, ‖F (v, ω)‖ ∂P) :=
    hnormsm.integral_prod_right'
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by
    exact integrableOn_const (by rw [Real.volume_Icc]; norm_num)
  have hsecond : Integrable (fun v => ∫ ω, ‖F (v, ω)‖ ∂P) μ := by
    apply hconst.mono hinner.aestronglyMeasurable
    filter_upwards with v
    have hv := brownianEval_integral_norm_le_one B (integratedSheetAnchor i x v)
    have hnonneg : 0 ≤ ∫ ω, |B.eval (integratedSheetAnchor i x v) ω| ∂P :=
      integral_nonneg fun ω => abs_nonneg _
    simpa [F, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hv
  have hfirst : ∀ᵐ v ∂μ, Integrable (fun ω => F (v, ω)) P := by
    filter_upwards with v
    exact ((B.eval_gaussian (integratedSheetAnchor i x v)).memLp_two).integrable (by norm_num)
  change Integrable F (μ.prod P)
  exact (integrable_prod_iff hsm.aestronglyMeasurable).2 ⟨hfirst, hsecond⟩

/-- The actual samplewise once-integrated coordinate, defined by applying the
path operator to the given Brownian sheet path. -/
noncomputable def integratedCoordinatePathEval {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) (i : Fin d)
    (x : BrownianCubeAnchor d) (ω : Ω) : ℝ :=
  BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath i (B.path ω) x

theorem integratedCoordinatePathEval_eq_integral {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) (i : Fin d)
    (x : BrownianCubeAnchor d) (ω : Ω) :
    integratedCoordinatePathEval B i x ω =
      ∫ v in Set.Icc (0 : ℝ) 1,
        x.val i * B.eval (integratedSheetAnchor i x v) ω ∂volume := by
  rw [integratedCoordinatePathEval,
    BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath_apply]
  rfl

theorem integrable_integratedCoordinatePathEval {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (i : Fin d)
    (x : BrownianCubeAnchor d) :
    Integrable (integratedCoordinatePathEval B i x) P := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let F : ℝ × Ω → ℝ := fun p => x.val i *
    B.eval (integratedSheetAnchor i x p.1) p.2
  have hF : Integrable F (μ.prod P) := by
    have h := integrable_brownianSheetEvalCurve B i x
    change Integrable (fun p : ℝ × Ω => B.eval
      (integratedSheetAnchor i x p.1) p.2) (μ.prod P) at h
    convert h.const_mul (x.val i) using 1
  have hswap := hF.swap
  have hint : Integrable (fun ω => ∫ v, F (v, ω) ∂μ) P :=
    hswap.integral_prod_left
  have heq : integratedCoordinatePathEval B i x =
      fun ω => ∫ v, F (v, ω) ∂μ := by
    funext ω
    rw [integratedCoordinatePathEval_eq_integral]
  rw [heq]
  exact hint

theorem integratedCoordinatePathEval_mean_zero {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (i : Fin d)
    (x : BrownianCubeAnchor d) :
    ∫ ω, integratedCoordinatePathEval B i x ω ∂P = 0 := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let F : ℝ × Ω → ℝ := fun p => x.val i *
    B.eval (integratedSheetAnchor i x p.1) p.2
  have hF : Integrable F (μ.prod P) := by
    have h := integrable_brownianSheetEvalCurve B i x
    change Integrable (fun p : ℝ × Ω => B.eval
      (integratedSheetAnchor i x p.1) p.2) (μ.prod P) at h
    convert h.const_mul (x.val i) using 1
  have heq : integratedCoordinatePathEval B i x =
      fun ω => ∫ v, F (v, ω) ∂μ := by
    funext ω
    rw [integratedCoordinatePathEval_eq_integral]
  have hswap : Integrable (Function.uncurry (fun ω v => F (v, ω))) (P.prod μ) := by
    change Integrable (F ∘ Prod.swap) (P.prod μ)
    exact hF.swap
  calc
    ∫ ω, integratedCoordinatePathEval B i x ω ∂P =
        ∫ ω, ∫ v, F (v, ω) ∂μ ∂P := by rw [heq]
    _ = ∫ v, ∫ ω, F (v, ω) ∂P ∂μ := integral_integral_swap hswap
    _ = ∫ v, x.val i *
          (∫ ω, B.eval (integratedSheetAnchor i x v) ω ∂P) ∂μ := by
      apply integral_congr_ae
      filter_upwards with v
      simp [F, integral_const_mul]
    _ = 0 := by simp [B.eval_mean_zero]

/-- The samplewise coordinate integral and its isonormal feature integral
agree almost everywhere. -/
theorem integratedCoordinatePathEval_ae_eq_of_isonormal {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P)
    (T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P)
    (W : IsonormalGaussianFamily (brownianCubeBoxSpan d) Ω Unit P)
    (hT_eval : ∀ z, brownianEvalToLp B z = T (featureVector z))
    (hW : ∀ z, W.eval z =ᵐ[P] fun ω => T z ω)
    (i : Fin d) (x : BrownianCubeAnchor d) :
      HasGaussianLaw
        (fun ω => T (integratedSheetFeature i x) ω) P ∧
      integratedCoordinatePathEval B i x =ᵐ[P]
        fun ω => T (integratedSheetFeature i x) ω := by
  have hcurve (v : ℝ) :
      brownianEvalToLp B (integratedSheetAnchor i x v) =
        T (scaledSheetFeature i x v) := by
    simpa [scaledSheetFeature, integratedSheetAnchor] using
      hT_eval (integratedSheetAnchor i x v)
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let φ : ℝ → Lp ℝ 2 P := fun v =>
    x.val i • brownianEvalToLp B (integratedSheetAnchor i x v)
  have hφcont : Continuous φ := by
    have hc : Continuous (fun v : ℝ => x.val i • T (scaledSheetFeature i x v)) :=
      (continuous_const : Continuous (fun _ : ℝ => x.val i)).smul
        ((T.continuous).comp (continuous_scaledSheetFeature i x))
    convert hc using 1
    funext v
    exact congrArg (fun z : Lp ℝ 2 P => x.val i • z) (hcurve v)
  have hφint : Integrable φ μ :=
    hφcont.continuousOn.integrableOn_compact
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hfeature : T (integratedSheetFeature i x) = ∫ v, φ v ∂μ := by
    change T (∫ v in Set.Icc (0 : ℝ) 1,
        x.val i • scaledSheetFeature i x v ∂volume) = _
    rw [← T.integral_comp_comm (μ := μ)
      (fun v => x.val i • scaledSheetFeature i x v)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    change T (x.val i • scaledSheetFeature i x v) =
      x.val i • brownianEvalToLp B (integratedSheetAnchor i x v)
    rw [map_smul, hcurve]
  have hpathInt : Integrable (integratedCoordinatePathEval B i x) P :=
    integrable_integratedCoordinatePathEval B i x
  have hnormalInt : Integrable (fun ω => T (integratedSheetFeature i x) ω) P :=
    (Lp.memLp _).integrable (by norm_num)
  have hsets : ∀ A : Set Ω, MeasurableSet A → P A < ⊤ →
      ∫ ω in A, integratedCoordinatePathEval B i x ω ∂P =
        ∫ ω in A, T (integratedSheetFeature i x) ω ∂P := by
    intro A hA hAfinite
    let F : ℝ × Ω → ℝ := fun p =>
      x.val i * B.eval (integratedSheetAnchor i x p.1) p.2
    have hF : Integrable F (μ.prod P) := by
      have h := integrable_brownianSheetEvalCurve B i x
      change Integrable (fun p : ℝ × Ω =>
        B.eval (integratedSheetAnchor i x p.1) p.2) (μ.prod P) at h
      exact h.const_mul (x.val i)
    have hFA : Integrable F (μ.prod (P.restrict A)) :=
      hF.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    have hswap :
        Integrable (Function.uncurry (fun ω v => F (v, ω)))
          ((P.restrict A).prod μ) := by
      change Integrable (F ∘ Prod.swap) ((P.restrict A).prod μ)
      exact hFA.swap
    have hleft :
        ∫ ω in A, integratedCoordinatePathEval B i x ω ∂P =
          ∫ v, ∫ ω in A,
            x.val i * B.eval (integratedSheetAnchor i x v) ω ∂P ∂μ := by
      have heqpath : integratedCoordinatePathEval B i x = fun ω =>
          ∫ v, F (v, ω) ∂μ := by
        funext ω
        rw [integratedCoordinatePathEval_eq_integral]
      rw [heqpath]
      change ∫ ω, ∫ v, F (v, ω) ∂μ ∂(P.restrict A) = _
      rw [integral_integral_swap hswap]
    let g : Lp ℝ 2 P := indicatorConstLp 2 hA hAfinite.ne 1
    let L : Lp ℝ 2 P →L[ℝ] ℝ := innerSL ℝ g
    have hL_eval (z : BrownianCubeAnchor d) :
        L (brownianEvalToLp B z) = ∫ ω in A, B.eval z ω ∂P := by
      change ⟪g, brownianEvalToLp B z⟫ = _
      rw [L2.inner_indicatorConstLp_one hA hAfinite.ne]
      have hmem : MemLp (B.eval z) 2 P := (B.eval_gaussian z).memLp_two
      have hrep : (fun ω => brownianEvalToLp B z ω) =ᵐ[P] B.eval z := by
        simpa [brownianEvalToLp] using hmem.coeFn_toLp
      apply setIntegral_congr_ae hA
      filter_upwards [hrep] with ω hω hωA
      exact hω
    have hLfeature :
        L (T (integratedSheetFeature i x)) =
          ∫ ω in A, T (integratedSheetFeature i x) ω ∂P := by
      change ⟪g, T (integratedSheetFeature i x)⟫ = _
      exact L2.inner_indicatorConstLp_one hA hAfinite.ne _
    have hright :
        ∫ ω in A, T (integratedSheetFeature i x) ω ∂P =
          ∫ v, ∫ ω in A,
            x.val i * B.eval (integratedSheetAnchor i x v) ω ∂P ∂μ := by
      rw [← hLfeature, hfeature, ← L.integral_comp_comm hφint]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      change L (x.val i • brownianEvalToLp B (integratedSheetAnchor i x v)) = _
      rw [map_smul, hL_eval]
      simp [integral_const_mul]
    exact hleft.trans hright.symm
  have hWlaw :
      HasGaussianLaw (fun ω => W.eval (integratedSheetFeature i x) ω) P := by
    have h := (W.jointlyGaussian
      (fun _ : Unit => integratedSheetFeature i x)).eval ()
    simpa using h
  have hTlaw := hWlaw.congr (hW (integratedSheetFeature i x))
  exact ⟨hTlaw,
    Integrable.ae_eq_of_forall_setIntegral_eq _ _ hpathInt hnormalInt hsets⟩

/-- The samplewise coordinate integral and its isonormal feature integral
agree almost everywhere. -/
theorem integratedCoordinatePathEval_ae_eq_isonormal {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (i : Fin d)
    (x : BrownianCubeAnchor d) :
    ∃ T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P,
      (∀ z, brownianEvalToLp B z = T (featureVector z)) ∧
      HasGaussianLaw
        (fun ω => T (integratedSheetFeature i x) ω) P ∧
      integratedCoordinatePathEval B i x =ᵐ[P]
        fun ω => T (integratedSheetFeature i x) ω := by
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Unit) B
  have hT_eval (z : BrownianCubeAnchor d) :
      brownianEvalToLp B z = T (featureVector z) := by
    rw [brownianEvalToLp_eq, ← hT z]
    apply congrArg T
    apply Subtype.ext
    rfl
  obtain ⟨hLaw, hae⟩ :=
    integratedCoordinatePathEval_ae_eq_of_isonormal B T W hT_eval hW i x
  exact ⟨T, hT_eval, hLaw, hae⟩

/-- The actual samplewise once-integrated coordinate is Gaussian, by its
almost-everywhere identification with the isonormal feature integral. -/
theorem integratedCoordinatePathEval_hasGaussianLaw {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (i : Fin d)
    (x : BrownianCubeAnchor d) :
    HasGaussianLaw (integratedCoordinatePathEval B i x) P := by
  obtain ⟨T, hT, hLaw, hae⟩ := integratedCoordinatePathEval_ae_eq_isonormal B i x
  exact hLaw.congr hae.symm

/-- The entire actual once-integrated coordinate field is a Gaussian process.
All anchors use one shared isonormal realization, and the samplewise path
integrals agree with its feature integrals almost surely at each anchor. -/
theorem integratedCoordinatePath_isGaussianProcess {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (i : Fin d) :
    IsGaussianProcess
      (fun x ω => integratedCoordinatePathEval B i x ω) P := by
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Unit) B
  have hT_eval (z : BrownianCubeAnchor d) :
      brownianEvalToLp B z = T (featureVector z) := by
    rw [brownianEvalToLp_eq, ← hT z]
    apply congrArg T
    apply Subtype.ext
    rfl
  have hTprocess : IsGaussianProcess
      (fun z : brownianCubeBoxSpan d => fun ω => T z ω) P := by
    refine ⟨fun I => ?_⟩
    obtain ⟨W', hW'⟩ :=
      brownianSheetCube_isonormal_of_covariance_isometry (ι := ↥I) B T hT
    have hLaw := W'.jointlyGaussian (fun z : ↥I => z.1)
    have hae : (fun ω (z : ↥I) => W'.eval z.1 ω) =ᵐ[P]
        (fun ω z => T z.1 ω) := by
      have hall := ae_all_iff.mpr (fun z : ↥I => hW' z.1)
      filter_upwards [hall] with ω hω
      funext z
      exact hω z
    exact hLaw.congr hae
  have hfeatureProcess :=
    hTprocess.comp_right (fun x : BrownianCubeAnchor d =>
      integratedSheetFeature i x)
  have hpathAE : ∀ x : BrownianCubeAnchor d,
      (fun ω => T (integratedSheetFeature i x) ω) =ᵐ[P]
        integratedCoordinatePathEval B i x := by
    intro x
    exact (integratedCoordinatePathEval_ae_eq_of_isonormal
      B T W hT_eval hW i x).2.symm
  exact hfeatureProcess.congr hpathAE

/-- Covariance of actual once-integrated path evaluations is the inner
product of their integrated Brownian-sheet features. -/
theorem integratedCoordinatePathEval_covariance {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (i : Fin d)
    (x y : BrownianCubeAnchor d) :
    cov[fun ω => integratedCoordinatePathEval B i x ω,
        fun ω => integratedCoordinatePathEval B i y ω; P] =
      ⟪integratedSheetFeature i x, integratedSheetFeature i y⟫ := by
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Unit) B
  have hT_eval (z : BrownianCubeAnchor d) :
      brownianEvalToLp B z = T (featureVector z) := by
    rw [brownianEvalToLp_eq, ← hT z]
    apply congrArg T
    apply Subtype.ext
    rfl
  have hpathAE (z : BrownianCubeAnchor d) :
      integratedCoordinatePathEval B i z =ᵐ[P]
        fun ω => T (integratedSheetFeature i z) ω := by
    exact (integratedCoordinatePathEval_ae_eq_of_isonormal
      B T W hT_eval hW i z).2
  let fx := integratedSheetFeature i x
  let fy := integratedSheetFeature i y
  have hX : MemLp (integratedCoordinatePathEval B i x) 2 P :=
    (integratedCoordinatePathEval_hasGaussianLaw B i x).memLp_two
  have hY : MemLp (integratedCoordinatePathEval B i y) 2 P :=
    (integratedCoordinatePathEval_hasGaussianLaw B i y).memLp_two
  have hfx : MemLp (fun ω => T fx ω) 2 P := Lp.memLp (T fx)
  have hfy : MemLp (fun ω => T fy ω) 2 P := Lp.memLp (T fy)
  have hmeanX : ∫ ω, integratedCoordinatePathEval B i x ω ∂P = 0 := by
    calc
      ∫ ω, integratedCoordinatePathEval B i x ω ∂P = ∫ ω, T fx ω ∂P :=
        integral_congr_ae (hpathAE x)
      _ = ∫ ω, W.eval fx ω ∂P := integral_congr_ae (hW fx).symm
      _ = 0 := W.mean_zero fx
  have hmeanY : ∫ ω, integratedCoordinatePathEval B i y ω ∂P = 0 := by
    calc
      ∫ ω, integratedCoordinatePathEval B i y ω ∂P = ∫ ω, T fy ω ∂P :=
        integral_congr_ae (hpathAE y)
      _ = ∫ ω, W.eval fy ω ∂P := integral_congr_ae (hW fy).symm
      _ = 0 := W.mean_zero fy
  have hTmeanX : ∫ ω, T fx ω ∂P = 0 := by
    calc
      ∫ ω, T fx ω ∂P = ∫ ω, W.eval fx ω ∂P :=
        integral_congr_ae (hW fx).symm
      _ = 0 := W.mean_zero fx
  have hTmeanY : ∫ ω, T fy ω ∂P = 0 := by
    calc
      ∫ ω, T fy ω ∂P = ∫ ω, W.eval fy ω ∂P :=
        integral_congr_ae (hW fy).symm
      _ = 0 := W.mean_zero fy
  have hprod :
      (fun ω => integratedCoordinatePathEval B i x ω *
          integratedCoordinatePathEval B i y ω) =ᵐ[P]
        (fun ω => T fx ω * T fy ω) := (hpathAE x).mul (hpathAE y)
  have hTprod : (fun ω => T fx ω * T fy ω) =ᵐ[P]
      (fun ω => W.eval fx ω * W.eval fy ω) := (hW fx).symm.mul (hW fy).symm
  have hWfxMem : MemLp (W.eval fx) 2 P :=
    ((W.jointlyGaussian (fun _ : Unit => fx)).eval ()).memLp_two
  have hWfyMem : MemLp (W.eval fy) 2 P :=
    ((W.jointlyGaussian (fun _ : Unit => fy)).eval ()).memLp_two
  have hWmeanX : ∫ ω, W.eval fx ω ∂P = 0 := W.mean_zero fx
  have hWmeanY : ∫ ω, W.eval fy ω ∂P = 0 := W.mean_zero fy
  have hcovT : cov[fun ω => T fx ω, fun ω => T fy ω; P] =
      cov[fun ω => W.eval fx ω, fun ω => W.eval fy ω; P] := by
    calc
      cov[fun ω => T fx ω, fun ω => T fy ω; P] =
          ∫ ω, T fx ω * T fy ω ∂P := by
            rw [covariance_eq_sub hfx hfy]
            simp [hTmeanX, hTmeanY]
      _ = ∫ ω, W.eval fx ω * W.eval fy ω ∂P := by
            apply integral_congr_ae
            exact hTprod
      _ = cov[fun ω => W.eval fx ω, fun ω => W.eval fy ω; P] := by
            rw [covariance_eq_sub hWfxMem hWfyMem]
            simp [hWmeanX, hWmeanY]
  calc
    cov[fun ω => integratedCoordinatePathEval B i x ω,
        fun ω => integratedCoordinatePathEval B i y ω; P] =
        ∫ ω, integratedCoordinatePathEval B i x ω *
          integratedCoordinatePathEval B i y ω ∂P := by
            rw [covariance_eq_sub hX hY]
            simp [hmeanX, hmeanY]
    _ = ∫ ω, T fx ω * T fy ω ∂P := integral_congr_ae hprod
    _ = cov[fun ω => T fx ω, fun ω => T fy ω; P] := by
          rw [covariance_eq_sub hfx hfy]
          simp [hTmeanX, hTmeanY]
    _ = cov[fun ω => W.eval fx ω, fun ω => W.eval fy ω; P] := hcovT
    _ = ⟪fx, fy⟫ := W.covariance_eq_inner fx fy


/-- Coordinate integration acting on a continuous field of deterministic
Brownian-sheet features. This is the feature-space counterpart of the
sample-path operator in `AlignmentGaussianRates`. -/
def integrateCoordinateFeature {d : ℕ} (i : Fin d)
    (f : C(BrownianCubeAnchor d, brownianCubeBoxSpan d)) :
    C(BrownianCubeAnchor d, brownianCubeBoxSpan d) := by
  let g : BrownianCubeAnchor d → ℝ → brownianCubeBoxSpan d := fun x v =>
    x.val i • f (brownianCubeClamp d (Function.update x.val i (x.val i * v)))
  have hu : Continuous (fun p : BrownianCubeAnchor d × ℝ =>
      Function.update p.1.val i (p.1.val i * p.2)) := by
    apply continuous_pi
    intro j
    have hc : Continuous (fun p : BrownianCubeAnchor d × ℝ => p.1.val j) := by
      exact (continuous_apply j).comp
        (continuous_subtype_val.comp continuous_fst)
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      exact hc.mul continuous_snd
    · simpa [Function.update_of_ne hji] using hc
  have hg : Continuous g.uncurry := by
    dsimp [g]
    have hcoord : Continuous (fun p : BrownianCubeAnchor d × ℝ => p.1.val i) := by
      exact (continuous_apply i).comp
        (continuous_subtype_val.comp continuous_fst)
    have hfield : Continuous (fun p : BrownianCubeAnchor d × ℝ =>
        f (brownianCubeClamp d (Function.update p.1.val i (p.1.val i * p.2)))) := by
      exact f.continuous.comp ((continuous_brownianCubeClamp d).comp hu)
    exact hcoord.smul hfield
  have hcont : Continuous (fun x =>
      ∫ v in Set.Icc (0 : ℝ) 1, g x v ∂volume) :=
    continuous_parametric_integral_of_continuous hg
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  exact ⟨fun x => ∫ v in Set.Icc (0 : ℝ) 1, g x v ∂volume, hcont⟩

@[simp] theorem integrateCoordinateFeature_apply {d : ℕ} (i : Fin d)
    (f : C(BrownianCubeAnchor d, brownianCubeBoxSpan d))
    (x : BrownianCubeAnchor d) :
    integrateCoordinateFeature i f x =
      ∫ v in Set.Icc (0 : ℝ) 1,
        x.val i • f (brownianCubeClamp d (Function.update x.val i (x.val i * v)))
          ∂volume := rfl

def iterateCoordinateFeature {d : ℕ} (i : Fin d) :
    ℕ → C(BrownianCubeAnchor d, brownianCubeBoxSpan d) →
      C(BrownianCubeAnchor d, brownianCubeBoxSpan d)
  | 0, f => f
  | n + 1, f => integrateCoordinateFeature i (iterateCoordinateFeature i n f)

def integrateSheetFeatureField {d : ℕ} (m : Fin d → ℕ)
    (f : C(BrownianCubeAnchor d, brownianCubeBoxSpan d)) :
    C(BrownianCubeAnchor d, brownianCubeBoxSpan d) :=
  (Finset.univ.toList : List (Fin d)).foldl
    (fun f i => iterateCoordinateFeature i (m i) f)
    f

noncomputable def integratedFeatureField {d : ℕ} (m : Fin d → ℕ) :
    C(BrownianCubeAnchor d, brownianCubeBoxSpan d) :=
  integrateSheetFeatureField m ⟨featureVector, featureVector_continuous d⟩

/-- One-dimensional integer-order integration of a causal power increments
the order by one, with exactly the factorial normalization used by the
Riemann--Liouville kernel. -/
theorem intervalIntegral_normalizedPower_succ (n : ℕ) (u t : ℝ) :
    (∫ s in u..t, ((n.factorial : ℝ)⁻¹) * (t - s) ^ n) =
      ((n + 1).factorial : ℝ)⁻¹ * (t - u) ^ (n + 1) := by
  rw [intervalIntegral.integral_const_mul]
  have hpow : (∫ s in u..t, (t - s) ^ n) =
      (t - u) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
    rw [intervalIntegral.integral_comp_sub_left (fun z : ℝ => z ^ n) t]
    rw [show t - t = 0 by ring, integral_pow]
    simp
  rw [hpow]
  have hfac : ((n + 1).factorial : ℝ) =
      ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ n
  rw [hfac]
  field_simp

/-- The matching left-anchored normalized power recurrence. -/
theorem intervalIntegral_leftNormalizedPower_succ (n : ℕ) (u t : ℝ) :
    (∫ s in u..t, ((n.factorial : ℝ)⁻¹) * (s - u) ^ n) =
      ((n + 1).factorial : ℝ)⁻¹ * (t - u) ^ (n + 1) := by
  rw [intervalIntegral.integral_const_mul]
  have hpow : (∫ s in u..t, (s - u) ^ n) =
      (t - u) ^ (n + 1) / ((n + 1 : ℕ) : ℝ) := by
    have hshift := intervalIntegral.integral_comp_add_left
      (a := (0 : ℝ)) (b := t - u) (fun z : ℝ => (z - u) ^ n) u
    have hshift' : (∫ x in (0 : ℝ)..(t - u),
        (u + x - u) ^ n) = ∫ s in u..t, (s - u) ^ n := by
      simpa only [add_zero, show u + (t - u) = t by ring] using hshift
    rw [← hshift']
    have hcongr : (∫ x in (0 : ℝ)..(t - u), (u + x - u) ^ n) =
        ∫ x in (0 : ℝ)..(t - u), x ^ n := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    rw [hcongr, integral_pow]
    simp
  rw [hpow]
  have hfac : ((n + 1).factorial : ℝ) =
      ((n + 1 : ℕ) : ℝ) * (n.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_succ n
  rw [hfac]
  field_simp

/-- Fubini swaps the two integrations over the causal triangle. The only
integrability input is the one-dimensional source integrand; finiteness of
the time interval supplies the other factor. -/
theorem volterraTriangle_integral_swap {μ : Measure ℝ} [IsFiniteMeasure μ]
    {f : ℝ → ℝ} (hf : Integrable f μ) :
    (∫ s, ∫ u, (if u ≤ s then f u else 0) ∂μ ∂μ) =
      ∫ u, ∫ s, (if u ≤ s then f u else 0) ∂μ ∂μ := by
  let S : Set (ℝ × ℝ) := {p | p.2 ≤ p.1}
  let F : ℝ × ℝ → ℝ := S.indicator (fun p => f p.2)
  have hS : MeasurableSet S := by
    exact measurableSet_le measurable_snd measurable_fst
  have hF : Integrable F (μ.prod μ) := by
    change Integrable (S.indicator (fun p : ℝ × ℝ => f p.2)) (μ.prod μ)
    exact (hf.comp_snd μ).indicator hS
  calc
    (∫ s, ∫ u, (if u ≤ s then f u else 0) ∂μ ∂μ) =
        ∫ p, F p ∂(μ.prod μ) := by
          symm
          rw [MeasureTheory.integral_prod F hF]
          rfl
    _ = ∫ p, F p.swap ∂(μ.prod μ) := by
          simpa [F, S] using (MeasureTheory.integral_prod_swap F).symm
    _ = ∫ u, ∫ s, (if u ≤ s then f u else 0) ∂μ ∂μ := by
          rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => F p.swap) hF.swap]
          rfl

/-- The same triangle swap with a measurable bounded multiplier depending on
both variables. This is the Fubini form used for normalized Volterra powers. -/
theorem volterraTriangle_integral_swap_mul {μ : Measure ℝ} [IsFiniteMeasure μ]
    {W : ℝ × ℝ → ℝ} (hW : Measurable W)
    (hWbound : ∀ᵐ p ∂(μ.prod μ), ‖W p‖ ≤ 1)
    {f : ℝ → ℝ} (hf : Integrable f μ) :
    (∫ s, ∫ u, (if u ≤ s then W (s, u) * f u else 0) ∂μ ∂μ) =
      ∫ u, ∫ s, (if u ≤ s then W (s, u) * f u else 0) ∂μ ∂μ := by
  let S : Set (ℝ × ℝ) := {p | p.2 ≤ p.1}
  let F : ℝ × ℝ → ℝ := S.indicator (fun p => W p * f p.2)
  have hS : MeasurableSet S := measurableSet_le measurable_snd measurable_fst
  have hbase : Integrable (fun p : ℝ × ℝ => W p * f p.2) (μ.prod μ) := by
    exact (hf.comp_snd μ).bdd_mul hW.aestronglyMeasurable hWbound
  have hF : Integrable F (μ.prod μ) := by
    change Integrable (S.indicator (fun p : ℝ × ℝ => W p * f p.2)) (μ.prod μ)
    exact hbase.indicator hS
  calc
    (∫ s, ∫ u, (if u ≤ s then W (s, u) * f u else 0) ∂μ ∂μ) =
        ∫ p, F p ∂(μ.prod μ) := by
          symm
          rw [MeasureTheory.integral_prod F hF]
          rfl
    _ = ∫ p, F p.swap ∂(μ.prod μ) := by
          simpa [F, S] using (MeasureTheory.integral_prod_swap F).symm
    _ = ∫ u, ∫ s, (if u ≤ s then W (s, u) * f u else 0) ∂μ ∂μ := by
          rw [MeasureTheory.integral_prod (fun p : ℝ × ℝ => F p.swap) hF.swap]
          rfl

/-- The inner integral after swapping the causal triangle is its interval
length times the source value. -/
theorem volterraTriangle_inner_integral {t u c : ℝ}
    (hu0 : 0 < u) (hut : u ≤ t) :
    (∫ s, (if u ≤ s then c else 0)
      ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) = (t - u) * c := by
  let A : Set ℝ := Set.Icc u t
  have hA : MeasurableSet A := measurableSet_Icc
  have hsub : A ⊆ Set.Ioc (0 : ℝ) t := by
    intro s hs
    exact ⟨lt_of_lt_of_le hu0 hs.1, hs.2⟩
  have hlength : (volume.restrict (Set.Ioc (0 : ℝ) t)).real A = t - u := by
    rw [Measure.real_def, Measure.restrict_apply hA,
      Set.inter_eq_left.mpr hsub, Real.volume_Icc]
    simp [ENNReal.toReal_ofReal (sub_nonneg.mpr hut)]
  have hae : (fun s : ℝ => if u ≤ s then c else 0) =ᵐ[
      volume.restrict (Set.Ioc (0 : ℝ) t)] A.indicator (fun _ => c) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hmem : s ∈ A ↔ u ≤ s := by
      constructor
      · exact fun h => h.1
      · intro h
        exact ⟨h, hs.2⟩
    simp [Set.indicator_apply, hmem]
  calc
    _ = ∫ s, A.indicator (fun _ => c) s
        ∂(volume.restrict (Set.Ioc (0 : ℝ) t)) := integral_congr_ae hae
    _ = (volume.restrict (Set.Ioc (0 : ℝ) t)).real A • c :=
      integral_indicator_const c hA
    _ = (t - u) * c := by rw [hlength, smul_eq_mul]

/-- The weighted inner integral over the causal triangle is the next
factorial-normalized truncated power. -/
theorem volterraTriangle_inner_normalizedPower {t u c : ℝ} (n : ℕ)
    (hu0 : 0 < u) (hut : u ≤ t) :
    (∫ s, (if u ≤ s then
      ((n.factorial : ℝ)⁻¹ * (s - u) ^ n) * c else 0)
      ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) =
      (((n + 1).factorial : ℝ)⁻¹ * (t - u) ^ (n + 1)) * c := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t)
  let A : Set ℝ := Set.Icc u t
  let h : ℝ → ℝ := fun s => ((n.factorial : ℝ)⁻¹ * (s - u) ^ n) * c
  have hA : MeasurableSet A := measurableSet_Icc
  have hsub : A ⊆ Set.Ioc (0 : ℝ) t := by
    intro s hs
    exact ⟨lt_of_lt_of_le hu0 hs.1, hs.2⟩
  have hae : (fun s : ℝ => if u ≤ s then h s else 0) =ᵐ[μ]
      A.indicator h := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hmem : s ∈ A ↔ u ≤ s := by
      constructor
      · exact fun q => q.1
      · intro q
        exact ⟨q, hs.2⟩
    simp [Set.indicator_apply, hmem, h]
  have hmeas : μ.restrict A = volume.restrict A := by
    dsimp [μ]
    rw [Measure.restrict_restrict hA, Set.inter_eq_left.mpr hsub]
  have hIoc : (∫ s in A, h s ∂volume) = (∫ s in u..t, h s) := by
    rw [show A = Set.Icc u t by rfl, integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hut]
  calc
    (∫ s, (if u ≤ s then h s else 0) ∂μ) = ∫ s, A.indicator h s ∂μ :=
      integral_congr_ae hae
    _ = ∫ s, h s ∂(μ.restrict A) := by rw [integral_indicator hA]
    _ = ∫ s in A, h s ∂volume := by rw [hmeas]
    _ = (∫ s in u..t, ((n.factorial : ℝ)⁻¹ * (s - u) ^ n)) * c := by
      rw [hIoc, intervalIntegral.integral_mul_const]
    _ = (((n + 1).factorial : ℝ)⁻¹ * (t - u) ^ (n + 1)) * c := by
      rw [intervalIntegral_leftNormalizedPower_succ]

/-- Repeated Volterra composition raises the causal power by one and adds
the corresponding factorial normalization. This is the scalar induction step
for integer-order integrated sheet kernels. -/
theorem volterraIntegral_normalizedPower_succ {t : ℝ} (ht1 : t ≤ 1)
    {f : ℝ → ℝ}
    (hf : Integrable f (volume.restrict (Set.Ioc (0 : ℝ) t))) (n : ℕ) :
    (∫ s in Set.Ioc (0 : ℝ) t,
      ∫ u in Set.Ioc (0 : ℝ) s,
        ((n.factorial : ℝ)⁻¹ * (s - u) ^ n) * f u ∂volume ∂volume) =
    ∫ u in Set.Ioc (0 : ℝ) t,
      (((n + 1).factorial : ℝ)⁻¹ * (t - u) ^ (n + 1)) * f u ∂volume := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t)
  let W : ℝ × ℝ → ℝ := fun p =>
    ((n.factorial : ℝ)⁻¹) * (p.1 - p.2) ^ n
  have hμ : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hWmeas : Measurable W := by
    exact (measurable_const.mul
      ((measurable_fst.sub measurable_snd).pow_const n))
  have hfactor : ((n.factorial : ℝ)⁻¹) ≤ 1 := by
    have hfac : (1 : ℝ) ≤ (n.factorial : ℝ) := by
      exact_mod_cast Nat.one_le_of_lt n.factorial_pos
    exact (inv_le_one₀ (by positivity)).2 hfac
  have hmem : ∀ᵐ x ∂μ, x ∈ Set.Ioc (0 : ℝ) t :=
    ae_restrict_mem measurableSet_Ioc
  have hfirst : ∀ᵐ p ∂(μ.prod μ), p.1 ∈ Set.Ioc (0 : ℝ) t := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    filter_upwards [hmem] with s hs
    exact Filter.Eventually.of_forall (fun _ => hs)
  have hsecond : ∀ᵐ p ∂(μ.prod μ), p.2 ∈ Set.Ioc (0 : ℝ) t := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    exact Filter.Eventually.of_forall (fun _ => hmem)
  have hWbound : ∀ᵐ p ∂(μ.prod μ), ‖W p‖ ≤ 1 := by
    filter_upwards [hfirst, hsecond] with p hp1 hp2
    have hdiff : |p.1 - p.2| ≤ 1 := by
      have hs0 := hp1.1
      have hu0 := hp2.1
      have hst := hp1.2
      have hut := hp2.2
      rw [abs_le]
      constructor <;> linarith
    have hpow : |p.1 - p.2| ^ n ≤ 1 := pow_le_one₀ (abs_nonneg _ ) hdiff
    have hpow_norm : ‖(p.1 - p.2) ^ n‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_pow]
      exact hpow
    rw [show W p = ((n.factorial : ℝ)⁻¹) * (p.1 - p.2) ^ n by rfl,
      norm_mul]
    exact (mul_le_mul_of_nonneg_left hpow_norm (by positivity)).trans
      (by simpa [Real.norm_eq_abs] using hfactor)
  have hinner (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) t) :
      (∫ u, (if u ≤ s then W (s, u) * f u else 0) ∂μ) =
        ∫ u in Set.Ioc (0 : ℝ) s, W (s, u) * f u ∂volume := by
    have hio : MeasurableSet (Set.Iic s) := measurableSet_Iic
    have hsets : Set.Iic s ∩ Set.Ioc (0 : ℝ) t = Set.Ioc (0 : ℝ) s := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨hus, hu0, hut⟩
        exact ⟨hu0, hus⟩
      · rintro ⟨hu0, hus⟩
        exact ⟨hus, hu0, le_trans hus hs.2⟩
    calc
      _ = ∫ u, (Set.Iic s).indicator (fun u => W (s, u) * f u) u ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => by simp [Set.indicator_apply])
      _ = ∫ u, W (s, u) * f u ∂(μ.restrict (Set.Iic s)) := by
        rw [integral_indicator hio]
      _ = ∫ u in Set.Ioc (0 : ℝ) s, W (s, u) * f u ∂volume := by
        rw [show μ.restrict (Set.Iic s) =
          volume.restrict (Set.Ioc (0 : ℝ) s) by
            dsimp [μ]
            rw [Measure.restrict_restrict hio, hsets]]
  have hswap := volterraTriangle_integral_swap_mul hWmeas hWbound hf
  calc
    (∫ s in Set.Ioc (0 : ℝ) t,
      ∫ u in Set.Ioc (0 : ℝ) s,
        ((n.factorial : ℝ)⁻¹ * (s - u) ^ n) * f u ∂volume ∂volume) =
        ∫ s, ∫ u, (if u ≤ s then W (s, u) * f u else 0) ∂μ ∂μ := by
          apply integral_congr_ae
          filter_upwards [hmem] with s hs
          have hleft := hinner s hs
          simpa [μ, W, Set.mem_Ioc] using hleft.symm
    _ = ∫ u, ∫ s, (if u ≤ s then W (s, u) * f u else 0) ∂μ ∂μ := hswap
    _ = ∫ u in Set.Ioc (0 : ℝ) t,
        (((n + 1).factorial : ℝ)⁻¹ * (t - u) ^ (n + 1)) * f u ∂volume := by
          apply integral_congr_ae
          filter_upwards [hmem] with u hu
          have htu : u ≤ t := hu.2
          rw [show (∫ s, (if u ≤ s then W (s, u) * f u else 0) ∂μ) =
            ∫ s, (if u ≤ s then
              ((n.factorial : ℝ)⁻¹ * (s - u) ^ n) * f u else 0) ∂μ by
                apply integral_congr_ae
                filter_upwards [hmem] with s hs
                rfl]
          exact volterraTriangle_inner_normalizedPower n hu.1 htu

/-- Integer-order scalar kernels are the factorial-normalized powers used in
the Volterra recurrence. -/
theorem causalKernel_natSucc_eq_normalizedPower (n : ℕ) (t u : ℝ) :
    AlignmentFractionalL2.causalKernel ((n : ℝ) + 1) t u =
      if u < t then ((n.factorial : ℝ)⁻¹) * (t - u) ^ n else 0 := by
  by_cases hu : u < t
  · have hgamma : Real.Gamma ((n : ℝ) + 1) = (n.factorial : ℝ) := by
      simpa using Real.Gamma_nat_eq_factorial n
    simp [AlignmentFractionalL2.causalKernel,
      AlignmentFractionalKernel.kernel, hu, hgamma]
  · simp [AlignmentFractionalL2.causalKernel, hu]

/-- Scalar RL evaluation at integer order `n+1` is precisely Volterra
integration against the normalized power on the anchored interval. -/
theorem fractionalRL_natSucc_eq_volterra {n : ℕ}
    (g : AlignmentFractionalL2.UnitL2) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    AlignmentFractionalTranslation.fractionalRL ((n : ℝ) + 1) (by nlinarith)
        g ⟨t, ⟨ht0, ht1⟩⟩ =
      ∫ u in Set.Ioc (0 : ℝ) t,
        ((n.factorial : ℝ)⁻¹ * (t-u)^n) * g u ∂volume := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let A : Set ℝ := Set.Ioc (0 : ℝ) t
  have hsub : A ⊆ Set.Icc (0 : ℝ) 1 := by
    intro u hu
    exact ⟨hu.1.le, le_trans hu.2 ht1⟩
  have hkernel :
      (fun u : ℝ => AlignmentFractionalL2.causalKernel ((n : ℝ)+1) t u * g u) =ᵐ[μ]
        A.indicator (fun u => ((n.factorial : ℝ)⁻¹ * (t-u)^n) * g u) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      Measure.ae_ne μ 0, Measure.ae_ne μ t] with u hu hzero hdiag
    have hpow := causalKernel_natSucc_eq_normalizedPower n t u
    by_cases h : u < t
    · have hA : u ∈ A := ⟨lt_of_le_of_ne hu.1 (Ne.symm hzero), le_of_lt h⟩
      simp [Set.indicator, hA, hpow, h]
    · have hA : u ∉ A := by
        intro hA
        exact h (lt_of_le_of_ne hA.2 hdiag)
      simp [Set.indicator, hA, hpow, h]
  have hmeasure : μ.restrict A = volume.restrict A := by
    dsimp [μ, A]
    rw [Measure.restrict_restrict measurableSet_Ioc]
    congr 1
    exact Set.inter_eq_left.mpr hsub
  calc
    AlignmentFractionalTranslation.fractionalRL ((n : ℝ)+1) (by nlinarith)
        g ⟨t, ⟨ht0, ht1⟩⟩ =
      ∫ u, AlignmentFractionalL2.causalKernel ((n : ℝ)+1) t u * g u ∂μ :=
        AlignmentFractionalTranslation.fractionalRL_apply _ _ _ _ ht0 ht1
    _ = ∫ u, A.indicator
          (fun u => ((n.factorial : ℝ)⁻¹ * (t-u)^n) * g u) u ∂μ :=
        integral_congr_ae hkernel
    _ = ∫ u, ((n.factorial : ℝ)⁻¹ * (t-u)^n) * g u ∂(μ.restrict A) := by
        rw [integral_indicator measurableSet_Ioc]
    _ = ∫ u in A, ((n.factorial : ℝ)⁻¹ * (t-u)^n) * g u ∂volume := by
        rw [hmeasure]

set_option maxHeartbeats 1000000
/-- Composing integer-order scalar RL evaluation with one ordinary anchored
integration increments the order by one. The proof is the Volterra triangle
Fubini identity, including the source-space integrability condition. -/
theorem fractionalRL_natSucc_comp_integral {n : ℕ}
    (g : AlignmentFractionalL2.UnitL2) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ v in Set.Icc (0 : ℝ) 1,
        t * AlignmentFractionalTranslation.fractionalRL ((n : ℝ)+1) (by nlinarith)
          g (AlignmentFractionalL2.clipUnit (t*v)) ∂volume) =
      AlignmentFractionalTranslation.fractionalRL ((n : ℝ)+2) (by nlinarith)
        g ⟨t, ⟨ht0, ht1⟩⟩ := by
  let H : ℝ → ℝ := fun s =>
    AlignmentFractionalTranslation.fractionalRL ((n : ℝ)+1) (by nlinarith)
      g (AlignmentFractionalL2.clipUnit s)
  have hclip_mul (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
      AlignmentFractionalL2.clipUnit (t*v) =
        ⟨t*v, ⟨mul_nonneg ht0 hv.1,
          (mul_le_mul_of_nonneg_left hv.2 ht0).trans (by simpa using ht1)⟩⟩ := by
    apply Subtype.ext
    simp [AlignmentFractionalL2.clipUnit,
      max_eq_right (mul_nonneg ht0 hv.1),
      min_eq_right ((mul_le_mul_of_nonneg_left hv.2 ht0).trans (by simpa using ht1))]
  have hclip_s (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) t) :
      AlignmentFractionalL2.clipUnit s =
        ⟨s, ⟨le_of_lt hs.1, (le_trans hs.2 ht1)⟩⟩ := by
    apply Subtype.ext
    simp [AlignmentFractionalL2.clipUnit, max_eq_right hs.1.le,
      min_eq_right (le_trans hs.2 ht1)]
  have hinner (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) t) :
      H s = ∫ u in Set.Ioc (0 : ℝ) s,
        ((n.factorial : ℝ)⁻¹ * (s-u)^n) * g u ∂volume := by
    dsimp [H]
    rw [hclip_s s hs]
    exact fractionalRL_natSucc_eq_volterra g s (le_of_lt hs.1) (le_trans hs.2 ht1)
  have hgCube : Integrable (fun u : ℝ => g u)
      (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (Lp.memLp g).integrable (by norm_num)
  have hg : Integrable (fun u : ℝ => g u)
      (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
    apply hgCube.mono_measure
      (volume.restrict_mono_set (show Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) 1 by
        intro u hu
        exact ⟨hu.1.le, le_trans hu.2 ht1⟩))
  have hscale :
      (∫ v in Set.Icc (0 : ℝ) 1, t * H (t*v) ∂volume) =
        ∫ s in Set.Ioc (0 : ℝ) t, H s ∂volume := by
    rw [integral_const_mul]
    change t * (∫ v in Set.Icc (0 : ℝ) 1, H (t*v) ∂volume) = _
    calc
      t * (∫ v in Set.Icc (0 : ℝ) 1, H (t*v) ∂volume) =
          t • (∫ v in (0 : ℝ)..1, H (t*v)) := by
            rw [integral_Icc_eq_integral_Ioc,
              ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
            rfl
      _ = ∫ s in t*0..t*1, H s := by
            simpa [smul_eq_mul] using
              (intervalIntegral.smul_integral_comp_mul_left
                (f := H) (a := (0 : ℝ)) (b := 1) (c := t))
      _ = ∫ s in (0 : ℝ)..t, H s := by simp
      _ = ∫ s in Set.Ioc (0 : ℝ) t, H s ∂volume := by
            rw [intervalIntegral.integral_of_le ht0]
  have houter :
      (∫ s in Set.Ioc (0 : ℝ) t, H s ∂volume) =
        ∫ s in Set.Ioc (0 : ℝ) t,
          ∫ u in Set.Ioc (0 : ℝ) s,
            ((n.factorial : ℝ)⁻¹ * (s-u)^n) * g u ∂volume ∂volume := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hinner s hs
  calc
    (∫ v in Set.Icc (0 : ℝ) 1,
        t * AlignmentFractionalTranslation.fractionalRL ((n : ℝ)+1) (by nlinarith)
          g (AlignmentFractionalL2.clipUnit (t*v)) ∂volume) =
        ∫ v in Set.Icc (0 : ℝ) 1, t * H (t*v) ∂volume := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
          rfl
    _ = ∫ s in Set.Ioc (0 : ℝ) t, H s ∂volume := hscale
    _ = ∫ s in Set.Ioc (0 : ℝ) t,
          ∫ u in Set.Ioc (0 : ℝ) s,
            ((n.factorial : ℝ)⁻¹ * (s-u)^n) * g u ∂volume ∂volume := houter
    _ = ∫ u in Set.Ioc (0 : ℝ) t,
          (((n+1).factorial : ℝ)⁻¹ * (t-u)^(n+1)) * g u ∂volume :=
          volterraIntegral_normalizedPower_succ ht1 hg n
    _ = AlignmentFractionalTranslation.fractionalRL ((n : ℝ)+2) (by nlinarith)
          g ⟨t, ⟨ht0, ht1⟩⟩ := by
          symm
          have h := fractionalRL_natSucc_eq_volterra (n := n+1) g t ht0 ht1
          have hRL :
              AlignmentFractionalTranslation.fractionalRL ((n : ℝ)+2) (by nlinarith) =
                AlignmentFractionalTranslation.fractionalRL (((n+1 : ℕ) : ℝ)+1)
                  (by nlinarith) := by
            congr 1 <;> norm_num [Nat.cast_add] <;> ring
          rw [hRL]
          exact h

/-- Scalar RL evaluation is inner product against its translated L² kernel
feature. -/
theorem fractionalRL_eq_inner_translated (α : ℝ) (hα : 1/2 < α)
    (g : AlignmentFractionalL2.UnitL2) (t : AlignmentFractionalL2.UnitInterval) :
    AlignmentFractionalTranslation.fractionalRL α hα g t =
      ⟪g, AlignmentFractionalTranslation.translatedUnitKernelFamily α hα t⟫ := by
  rw [AlignmentFractionalTranslation.fractionalRL_apply α hα g t.1 t.2.1 t.2.2,
    AlignmentFractionalTranslation.translatedUnitKernelFamily_eq_kernelVector
      α t.1 hα t.2.1 t.2.2,
    L2.inner_def]
  apply integral_congr_ae
  filter_upwards [
    AlignmentFractionalL2.causalKernel_memLp_unit hα t.2.1 t.2.2 |>.coeFn_toLp]
    with u hu
  dsimp [AlignmentFractionalL2.kernelVector]
  simp [hu, mul_comm]

/-- One actual Bochner integration of an order-`n+1` scalar feature is the
order-`n+2` feature in the fixed unit-interval L² space. -/
noncomputable def scalarIntegratedKernelFeature (n : ℕ)
    (t : AlignmentFractionalL2.UnitInterval) : AlignmentFractionalL2.UnitL2 :=
  ∫ v in Set.Icc (0 : ℝ) 1,
    t.1 • AlignmentFractionalTranslation.translatedUnitKernelFamily
      ((n : ℝ) + 1) (by nlinarith)
      (AlignmentFractionalL2.clipUnit (t.1 * v)) ∂volume

theorem scalarIntegratedKernelFeature_eq_kernelVector (n : ℕ)
    (t : AlignmentFractionalL2.UnitInterval) :
    scalarIntegratedKernelFeature n t =
      AlignmentFractionalL2.kernelVector ((n : ℝ) + 2) t.1
        (by nlinarith) t.2.1 t.2.2 := by
  apply ext_inner_left ℝ
  intro g
  let F : ℝ → AlignmentFractionalL2.UnitL2 := fun v =>
    t.1 • AlignmentFractionalTranslation.translatedUnitKernelFamily
      ((n : ℝ) + 1) (by nlinarith)
      (AlignmentFractionalL2.clipUnit (t.1 * v))
  have hF : Integrable F (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hcont : Continuous F := by
      dsimp [F]
      exact (continuous_const : Continuous (fun _ : ℝ => t.1)).smul
        ((AlignmentFractionalTranslation.translatedUnitKernelFamily
          ((n : ℝ) + 1) (by nlinarith)).continuous.comp
          (AlignmentFractionalL2.clipUnit_continuous.comp (continuous_const.mul continuous_id)))
    exact hcont.continuousOn.integrableOn_compact
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  calc
    ⟪g, scalarIntegratedKernelFeature n t⟫ =
        ∫ v in Set.Icc (0 : ℝ) 1, ⟪g, F v⟫ ∂volume := by
          dsimp [scalarIntegratedKernelFeature, F]
          exact (integral_inner hF g).symm
    _ = ∫ v in Set.Icc (0 : ℝ) 1,
        t.1 * AlignmentFractionalTranslation.fractionalRL
          ((n : ℝ) + 1) (by nlinarith) g
          (AlignmentFractionalL2.clipUnit (t.1 * v)) ∂volume := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
          dsimp [F]
          rw [real_inner_smul_right,
            fractionalRL_eq_inner_translated ((n : ℝ) + 1) (by nlinarith) g
              (AlignmentFractionalL2.clipUnit (t.1 * v))]
    _ = AlignmentFractionalTranslation.fractionalRL ((n : ℝ) + 2) (by nlinarith)
          g t := by
          have ht0 := t.2.1
          have ht1 := t.2.2
          rw [fractionalRL_natSucc_comp_integral (n := n) g t.1 ht0 ht1]
    _ = ⟪g, AlignmentFractionalL2.kernelVector ((n : ℝ) + 2) t.1
          (by nlinarith) t.2.1 t.2.2⟫ :=
          by
            rw [fractionalRL_eq_inner_translated ((n : ℝ) + 2) (by nlinarith) g t,
              AlignmentFractionalTranslation.translatedUnitKernelFamily_eq_kernelVector
                ((n : ℝ) + 2) t.1 (by nlinarith) t.2.1 t.2.2]

/-- Zero extension is a continuous linear isometry from the cube source into
the ambient source space. -/
private theorem unitCubeZeroExtend_coe_ae {d : ℕ}
    (g : CameronMartin.UnitCubeL2 d) :
    (CameronMartin.unitCubeZeroExtend g : CameronMartin.AmbientL2 d) =ᵐ[
      Measure.pi (fun _ : Fin d => (volume : Measure ℝ))]
      (CameronMartin.unitCubeSet d).indicator (g : (Fin d → ℝ) → ℝ) := by
  exact (memLp_indicator_iff_restrict
    (CameronMartin.measurableSet_unitCubeSet d)).2 (Lp.memLp g) |>.coeFn_toLp

def unitCubeZeroExtendCLM (d : ℕ) :
    CameronMartin.UnitCubeL2 d →L[ℝ] CameronMartin.AmbientL2 d := by
  let L : CameronMartin.UnitCubeL2 d →ₗ[ℝ] CameronMartin.AmbientL2 d := {
    toFun := CameronMartin.unitCubeZeroExtend
    map_add' := by
      intro g h
      apply Lp.ext
      have hadd : ∀ᵐ u ∂(Measure.pi (fun _ : Fin d => (volume : Measure ℝ))),
          u ∈ CameronMartin.unitCubeSet d → g u + h u = (g + h) u :=
        (ae_restrict_iff' (CameronMartin.measurableSet_unitCubeSet d)).1
          (Lp.coeFn_add g h).symm
      filter_upwards [unitCubeZeroExtend_coe_ae (g + h),
        unitCubeZeroExtend_coe_ae g, unitCubeZeroExtend_coe_ae h,
        hadd, Lp.coeFn_add
          (CameronMartin.unitCubeZeroExtend g) (CameronMartin.unitCubeZeroExtend h)]
        with u h0 h1 h2 h3 h4
      by_cases hu : u ∈ CameronMartin.unitCubeSet d
      · calc
          CameronMartin.unitCubeZeroExtend (g + h) u =
              (CameronMartin.unitCubeSet d).indicator (g + h) u := h0
          _ = (CameronMartin.unitCubeSet d).indicator g u +
              (CameronMartin.unitCubeSet d).indicator h u := by
                simp [Set.indicator, hu, h3 hu]
          _ = CameronMartin.unitCubeZeroExtend g u +
              CameronMartin.unitCubeZeroExtend h u := by rw [h1, h2]
          _ = (CameronMartin.unitCubeZeroExtend g +
              CameronMartin.unitCubeZeroExtend h) u := h4.symm
      · calc
          CameronMartin.unitCubeZeroExtend (g + h) u =
              (CameronMartin.unitCubeSet d).indicator (g + h) u := h0
          _ = 0 := by simp [Set.indicator, hu]
          _ = (CameronMartin.unitCubeZeroExtend g +
              CameronMartin.unitCubeZeroExtend h) u := by
                rw [h4]
                simp [h1, h2, Set.indicator, hu]
    map_smul' := by
      intro c g
      apply Lp.ext
      have hsmul : ∀ᵐ u ∂(Measure.pi (fun _ : Fin d => (volume : Measure ℝ))),
          u ∈ CameronMartin.unitCubeSet d → c * g u = (c • g) u :=
        (ae_restrict_iff' (CameronMartin.measurableSet_unitCubeSet d)).1
          (Lp.coeFn_smul c g).symm
      filter_upwards [unitCubeZeroExtend_coe_ae (c • g),
        unitCubeZeroExtend_coe_ae g, hsmul,
        Lp.coeFn_smul c (CameronMartin.unitCubeZeroExtend g)] with u h0 h1 h2 h3
      by_cases hu : u ∈ CameronMartin.unitCubeSet d
      · calc
          CameronMartin.unitCubeZeroExtend (c • g) u =
              (CameronMartin.unitCubeSet d).indicator (c • g) u := h0
          _ = c * (CameronMartin.unitCubeSet d).indicator g u := by
                simp [Set.indicator, hu, h2 hu]
          _ = c * CameronMartin.unitCubeZeroExtend g u := by rw [h1]
          _ = (c • CameronMartin.unitCubeZeroExtend g) u := h3.symm
      · calc
          CameronMartin.unitCubeZeroExtend (c • g) u =
              (CameronMartin.unitCubeSet d).indicator (c • g) u := h0
          _ = 0 := by simp [Set.indicator, hu]
          _ = (c • CameronMartin.unitCubeZeroExtend g) u := by
                rw [h3]
                simp [h1, Set.indicator, hu]
  }
  exact L.mkContinuous 1 (by
    intro g
    change ‖CameronMartin.unitCubeZeroExtend g‖ ≤ 1 * ‖g‖
    rw [CameronMartin.unitCubeZeroExtend_norm]
    simp)

/-- The tensor product map with every factor frozen except `i`, extended by
zero to the ambient feature space, is a continuous linear map in the free
factor. -/
def frozenTensorFeatureCLM (d : ℕ) (i : Fin d)
    (v : Fin d → AlignmentFractionalL2.UnitL2) :
    AlignmentFractionalL2.UnitL2 →L[ℝ] CameronMartin.AmbientL2 d := by
  let TC := BrownianSharp.AlignmentL2TensorProduct.tensorContinuous
    (μ := fun _ : Fin d => volume.restrict (Set.Icc (0 : ℝ) 1))
  have hupd (z : AlignmentFractionalL2.UnitL2) :
      ‖TC (Function.update v i z)‖ =
        ‖z‖ * ∏ j ∈ Finset.univ \ {i}, ‖v j‖ := by
    rw [BrownianSharp.AlignmentL2TensorProduct.tensorContinuous_apply,
      BrownianSharp.AlignmentL2TensorProduct.productVector_norm]
    have hfun : (fun j : Fin d => ‖Function.update v i z j‖) =
        Function.update (fun j => ‖v j‖) i ‖z‖ := by
      funext j
      by_cases h : j = i <;> simp [Function.update, h]
    rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i)]
  let L : AlignmentFractionalL2.UnitL2 →ₗ[ℝ]
      AlignmentFractionalTensorOperator.ProductCubeL2 d := {
    toFun := fun z => TC (Function.update v i z)
    map_add' := by
      intro z w
      exact TC.map_update_add v i z w
    map_smul' := by
      intro c z
      exact TC.map_update_smul v i c z
  }
  let LC : AlignmentFractionalL2.UnitL2 →L[ℝ]
      AlignmentFractionalTensorOperator.ProductCubeL2 d :=
    L.mkContinuous (∏ j ∈ Finset.univ \ {i}, ‖v j‖) (by
      intro z
      change ‖TC (Function.update v i z)‖ ≤ _
      rw [hupd]
      simp [mul_comm])
  exact (unitCubeZeroExtendCLM d).comp
    ((AlignmentFractionalTensorOperator.productToCube d).comp LC)

/-- The scalar kernel feature at a positive integer order.  The order is
stored as the number of integrations, so `n` denotes RL order `n+1`. -/
noncomputable def naturalOrderUnitKernel (n : ℕ) (t : UnitInterval) :
    AlignmentFractionalL2.UnitL2 :=
  AlignmentFractionalTranslation.translatedUnitKernelFamily
    ((n : ℝ) + 1) (by nlinarith) t

/-- The actual ambient tensor feature with integer coordinate orders. -/
noncomputable def naturalTensorFeature {d : ℕ} (m : Fin d → ℕ)
    (x : BrownianCubeAnchor d) : CameronMartin.AmbientL2 d :=
  unitCubeZeroExtendCLM d
    (AlignmentFractionalTensorOperator.productToCube d
      (BrownianSharp.AlignmentL2TensorProduct.tensorContinuous
        (μ := fun _ : Fin d => volume.restrict (Set.Icc (0 : ℝ) 1))
        (fun j => naturalOrderUnitKernel (m j)
          (AlignmentFractionalTensorOperator.cubeCoordinate j x))))

theorem frozenTensorFeatureCLM_apply_natural {d : ℕ} (m : Fin d → ℕ)
    (i : Fin d) (x : BrownianCubeAnchor d) :
    frozenTensorFeatureCLM d i
        (fun j => naturalOrderUnitKernel (m j)
          (AlignmentFractionalTensorOperator.cubeCoordinate j x))
        (naturalOrderUnitKernel (m i)
          (AlignmentFractionalTensorOperator.cubeCoordinate i x)) =
      naturalTensorFeature m x := by
  change unitCubeZeroExtendCLM d
    (AlignmentFractionalTensorOperator.productToCube d
      (BrownianSharp.AlignmentL2TensorProduct.tensorContinuous
        (μ := fun _ : Fin d => volume.restrict (Set.Icc (0 : ℝ) 1))
        (Function.update
          (fun j => naturalOrderUnitKernel (m j)
            (AlignmentFractionalTensorOperator.cubeCoordinate j x)) i
          (naturalOrderUnitKernel (m i)
            (AlignmentFractionalTensorOperator.cubeCoordinate i x))))) =
    unitCubeZeroExtendCLM d
      (AlignmentFractionalTensorOperator.productToCube d
        (BrownianSharp.AlignmentL2TensorProduct.tensorContinuous
          (μ := fun _ : Fin d => volume.restrict (Set.Icc (0 : ℝ) 1))
          (fun j => naturalOrderUnitKernel (m j)
            (AlignmentFractionalTensorOperator.cubeCoordinate j x))))
  simp only [BrownianSharp.AlignmentL2TensorProduct.tensorContinuous_apply]
  apply congrArg (fun z : AlignmentFractionalTensorOperator.ProductCubeL2 d =>
    unitCubeZeroExtendCLM d (AlignmentFractionalTensorOperator.productToCube d z))
  apply congrArg BrownianSharp.AlignmentL2TensorProduct.productVector
  funext j
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update, h]

theorem scalarIntegratedKernelFeature_eq_naturalOrder (n : ℕ)
    (t : AlignmentFractionalL2.UnitInterval) :
    scalarIntegratedKernelFeature n t = naturalOrderUnitKernel (n + 1) t := by
  have ht := Set.mem_Icc.mp t.property
  calc
    scalarIntegratedKernelFeature n t =
        AlignmentFractionalL2.kernelVector ((n : ℝ) + 2) t.1
          (by nlinarith) ht.1 ht.2 := scalarIntegratedKernelFeature_eq_kernelVector n t
    _ = AlignmentFractionalTranslation.translatedUnitKernelFamily
          ((n : ℝ) + 2) (by nlinarith) t := by
      exact (AlignmentFractionalTranslation.translatedUnitKernelFamily_eq_kernelVector
        ((n : ℝ) + 2) t.1 (by nlinarith) ht.1 ht.2).symm
    _ = naturalOrderUnitKernel (n + 1) t := by
      unfold naturalOrderUnitKernel
      congr 1
      push_cast
      ring_nf

theorem frozenTensorFeatureCLM_congr_other {d : ℕ} (i : Fin d)
    (v w : Fin d → AlignmentFractionalL2.UnitL2)
    (h : ∀ j, j ≠ i → v j = w j) :
    frozenTensorFeatureCLM d i v = frozenTensorFeatureCLM d i w := by
  apply ContinuousLinearMap.ext
  intro z
  change unitCubeZeroExtendCLM d
      (AlignmentFractionalTensorOperator.productToCube d
        (BrownianSharp.AlignmentL2TensorProduct.tensorContinuous
          (μ := fun _ : Fin d => volume.restrict (Set.Icc (0 : ℝ) 1))
          (Function.update v i z))) =
    unitCubeZeroExtendCLM d
      (AlignmentFractionalTensorOperator.productToCube d
        (BrownianSharp.AlignmentL2TensorProduct.tensorContinuous
          (μ := fun _ : Fin d => volume.restrict (Set.Icc (0 : ℝ) 1))
          (Function.update w i z)))
  apply congrArg (fun q : AlignmentFractionalTensorOperator.ProductCubeL2 d =>
    unitCubeZeroExtendCLM d (AlignmentFractionalTensorOperator.productToCube d q))
  simp only [BrownianSharp.AlignmentL2TensorProduct.tensorContinuous_apply]
  apply congrArg BrownianSharp.AlignmentL2TensorProduct.productVector
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [Function.update, hji, h j hji]

/-- Repeated integration in a single cube coordinate has the explicit
factorial-normalized truncated-power kernel, for every continuous path. -/
theorem iterateCoordinatePath_eq_normalizedPower {d : ℕ} (i : Fin d)
    (f : C(BrownianCubeAnchor d, ℝ)) :
    ∀ n (x : BrownianCubeAnchor d),
      BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath i (n + 1) f x =
        ∫ u in Set.Ioc (0 : ℝ) (x.val i),
          ((n.factorial : ℝ)⁻¹ * (x.val i - u) ^ n) *
            brownianCubeGlobalExtension f (Function.update x.val i u) ∂volume := by
  intro n
  induction n with
  | zero =>
      intro x
      change BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath i f x = _
      rw [BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath_eq_intervalIntegral,
        intervalIntegral.integral_of_le (x.property i).1]
      simp
  | succ n ih =>
      intro x
      let t := x.val i
      let g : ℝ → ℝ := fun u =>
        brownianCubeGlobalExtension f (Function.update x.val i u)
      have hgc : Continuous g := by
        dsimp [g]
        exact (brownianCubeGlobalExtension f).continuous.comp (by fun_prop)
      have hg : Integrable g (volume.restrict (Set.Ioc (0 : ℝ) t)) := by
        have hIcc : IntegrableOn g (Set.Icc (0 : ℝ) t) volume :=
          hgc.continuousOn.integrableOn_compact
            (isCompact_Icc (a := (0 : ℝ)) (b := t))
        have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) t := by
          intro u hu
          exact ⟨hu.1.le, hu.2⟩
        exact hIcc.mono_set hsub
      have ht1 : t ≤ 1 := (x.property i).2
      have hcoordinate (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) t) :
          (brownianCubeClamp d (Function.update x.val i s)).val i = s := by
        simp [brownianCubeClamp, Function.update_self,
          max_eq_right hs.1.le, min_eq_right (le_trans hs.2 ht1)]
      change BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath i
        (BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath i (n + 1) f) x = _
      rw [BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath_eq_intervalIntegral,
        intervalIntegral.integral_of_le (x.property i).1]
      calc
        (∫ s in Set.Ioc (0 : ℝ) t,
          brownianCubeGlobalExtension
            (BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath i (n + 1) f)
            (Function.update x.val i s) ∂volume) =
          ∫ s in Set.Ioc (0 : ℝ) t,
            BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath i (n + 1) f
              (brownianCubeClamp d (Function.update x.val i s)) ∂volume := by
                apply integral_congr_ae
                filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
                rw [brownianCubeGlobalExtension_apply]
        _ = ∫ s in Set.Ioc (0 : ℝ) t,
            ∫ u in Set.Ioc (0 : ℝ) s,
              ((n.factorial : ℝ)⁻¹ * (s - u) ^ n) * g u ∂volume ∂volume := by
                apply integral_congr_ae
                filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
                have hIH := ih (brownianCubeClamp d (Function.update x.val i s))
                have hz := hcoordinate s hs
                have hzval : (brownianCubeClamp d (Function.update x.val i s)).val =
                    Function.update x.val i s := by
                  funext j
                  by_cases hji : j = i
                  · subst j
                    simpa using hz
                  · simp [brownianCubeClamp, Function.update_of_ne hji,
                      (x.property j).1, (x.property j).2]
                rw [hz] at hIH
                calc
                  _ = ∫ u in Set.Ioc (0 : ℝ) s,
                      ((n.factorial : ℝ)⁻¹ * (s - u) ^ n) *
                        brownianCubeGlobalExtension f
                          (Function.update
                            (brownianCubeClamp d (Function.update x.val i s)).val i u)
                        ∂volume := by simpa only [hz] using hIH
                  _ = ∫ u in Set.Ioc (0 : ℝ) s,
                      ((n.factorial : ℝ)⁻¹ * (s - u) ^ n) * g u ∂volume := by
                        apply integral_congr_ae
                        filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
                        have hupdate : Function.update
                            (brownianCubeClamp d (Function.update x.val i s)).val i u =
                              Function.update x.val i u := by
                          rw [hzval]
                          simp
                        rw [hupdate]
        _ = ∫ u in Set.Ioc (0 : ℝ) t,
            (((n + 1).factorial : ℝ)⁻¹ * (t - u) ^ (n + 1)) * g u ∂volume :=
              volterraIntegral_normalizedPower_succ ht1 hg n
        _ = ∫ u in Set.Ioc (0 : ℝ) (x.val i),
            (((n + 1).factorial : ℝ)⁻¹ * (x.val i - u) ^ (n + 1)) *
              brownianCubeGlobalExtension f (Function.update x.val i u) ∂volume := by
                simp [t, g]

/-- The affine parameterization used by the coordinate integration operator
stays inside the anchor cube, so clamping fixes the updated anchor. -/
theorem brownianCubeClamp_update_scaled {d : ℕ}
    (x : BrownianCubeAnchor d) (i : Fin d) (v : ℝ)
    (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    brownianCubeClamp d (Function.update x.val i (x.val i * v)) =
      Function.update x.val i (x.val i * v) := by
  apply funext
  intro j
  by_cases hji : j = i
  · subst j
    simp only [brownianCubeClamp, Function.update_self]
    have hlow : 0 ≤ x.val i * v := mul_nonneg (x.property i).1 hv.1
    have hupp : x.val i * v ≤ 1 := by
      calc
        x.val i * v ≤ 1 * v := mul_le_mul_of_nonneg_right (x.property i).2 hv.1
        _ ≤ 1 := by nlinarith [hv.2]
    rw [min_eq_right hupp, max_eq_right hlow]
  · simp [brownianCubeClamp, Function.update_of_ne hji,
      max_eq_right (x.property j).1, min_eq_right (x.property j).2]

theorem integratedSheetAnchor_val {d : ℕ} (i : Fin d)
    (x : BrownianCubeAnchor d) (v : ℝ) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    (integratedSheetAnchor i x v).val = Function.update x.val i (x.val i * v) :=
  by
    exact brownianCubeClamp_update_scaled x i v hv

/-- One pathwise feature integration increments exactly one tensor RL order.
This is the actual Bochner-integral realization, rather than a postulated
kernel identity. -/
theorem integrateCoordinateFeature_naturalTensor {d : ℕ}
    (m : Fin d → ℕ) (i : Fin d)
    (f : C(BrownianCubeAnchor d, brownianCubeBoxSpan d))
    (hF : ∀ z, brownianCubeSpanEmbedding d (f z) = naturalTensorFeature m z)
    (x : BrownianCubeAnchor d) :
    brownianCubeSpanEmbedding d (integrateCoordinateFeature i f x) =
      naturalTensorFeature (Function.update m i (m i + 1)) x := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let t : AlignmentFractionalL2.UnitInterval :=
    AlignmentFractionalTensorOperator.cubeCoordinate i x
  let vfixed : Fin d → AlignmentFractionalL2.UnitL2 := fun j =>
    naturalOrderUnitKernel (m j) (AlignmentFractionalTensorOperator.cubeCoordinate j x)
  let L : AlignmentFractionalL2.UnitL2 →L[ℝ] CameronMartin.AmbientL2 d :=
    frozenTensorFeatureCLM d i vfixed
  have hparam (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      AlignmentFractionalTensorOperator.cubeCoordinate i
          (integratedSheetAnchor i x s) = AlignmentFractionalL2.clipUnit (x.val i * s) := by
    apply Subtype.ext
    change (integratedSheetAnchor i x s).val i =
      (AlignmentFractionalL2.clipUnit (x.val i * s)).1
    have hlow : 0 ≤ x.val i * s := mul_nonneg (x.property i).1 hs.1
    have hupp : x.val i * s ≤ 1 := by
      calc
        x.val i * s ≤ 1 * s := mul_le_mul_of_nonneg_right (x.property i).2 hs.1
        _ ≤ 1 := by nlinarith [hs.2]
    rw [integratedSheetAnchor_val i x s hs]
    simp [AlignmentFractionalTensorOperator.cubeCoordinate,
      AlignmentFractionalL2.clipUnit, hlow, hupp]
  have hparamOther (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
      (j : Fin d) (hji : j ≠ i) :
      AlignmentFractionalTensorOperator.cubeCoordinate j
          (integratedSheetAnchor i x s) =
        AlignmentFractionalTensorOperator.cubeCoordinate j x := by
    apply Subtype.ext
    change (integratedSheetAnchor i x s).val j = x.val j
    rw [integratedSheetAnchor_val i x s hs]
    simp [Function.update_of_ne hji]
  have hLparam (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      frozenTensorFeatureCLM d i
        (fun j => naturalOrderUnitKernel (m j)
          (AlignmentFractionalTensorOperator.cubeCoordinate j
            (integratedSheetAnchor i x s))) = L := by
    apply frozenTensorFeatureCLM_congr_other
    intro j hji
    rw [hparamOther s hs j hji]
  have hrepr (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      brownianCubeSpanEmbedding d
        (f (integratedSheetAnchor i x s)) =
      L (naturalOrderUnitKernel (m i)
        (AlignmentFractionalL2.clipUnit (x.val i * s))) := by
    rw [hF, ← frozenTensorFeatureCLM_apply_natural m i
      (integratedSheetAnchor i x s), hLparam s hs, hparam s hs]
  let φ : ℝ → AlignmentFractionalL2.UnitL2 := fun s =>
    x.val i • naturalOrderUnitKernel (m i)
      (AlignmentFractionalL2.clipUnit (x.val i * s))
  have hφcont : Continuous φ := by
    dsimp [φ, naturalOrderUnitKernel]
    exact (continuous_const : Continuous (fun _ : ℝ => x.val i)).smul
      ((AlignmentFractionalTranslation.translatedUnitKernelFamily
        ((m i : ℝ) + 1) (by nlinarith)).continuous.comp
          (AlignmentFractionalL2.clipUnit_continuous.comp (continuous_const.mul continuous_id)))
  have hφint : Integrable φ μ := hφcont.continuousOn.integrableOn_compact
    (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hsourceCont : Continuous (fun s : ℝ =>
      x.val i • f (integratedSheetAnchor i x s)) := by
    exact (continuous_const : Continuous (fun _ : ℝ => x.val i)).smul
      (f.continuous.comp (continuous_integratedSheetAnchor i x))
  have hsourceInt : Integrable (fun s : ℝ =>
      x.val i • f (integratedSheetAnchor i x s)) μ :=
    hsourceCont.continuousOn.integrableOn_compact
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hfinal : naturalTensorFeature (Function.update m i (m i + 1)) x =
      L (naturalOrderUnitKernel (m i + 1) t) := by
    have hmaps : frozenTensorFeatureCLM d i
        (fun j => naturalOrderUnitKernel (Function.update m i (m i + 1) j)
          (AlignmentFractionalTensorOperator.cubeCoordinate j x)) = L := by
      apply frozenTensorFeatureCLM_congr_other
      intro j hji
      simp [vfixed, Function.update, hji]
    calc
      naturalTensorFeature (Function.update m i (m i + 1)) x =
          frozenTensorFeatureCLM d i
            (fun j => naturalOrderUnitKernel (Function.update m i (m i + 1) j)
              (AlignmentFractionalTensorOperator.cubeCoordinate j x))
            (naturalOrderUnitKernel (Function.update m i (m i + 1) i)
              (AlignmentFractionalTensorOperator.cubeCoordinate i x)) :=
        (frozenTensorFeatureCLM_apply_natural (Function.update m i (m i + 1)) i x).symm
      _ = L (naturalOrderUnitKernel (m i + 1) t) := by
        rw [hmaps]
        simp [Function.update, t]
  calc
    brownianCubeSpanEmbedding d (integrateCoordinateFeature i f x) =
        ∫ s, brownianCubeSpanEmbedding d
          (x.val i • f (integratedSheetAnchor i x s)) ∂μ := by
      change brownianCubeSpanEmbedding d
          (∫ s in Set.Icc (0 : ℝ) 1,
            x.val i • f (integratedSheetAnchor i x s) ∂volume) = _
      rw [← (brownianCubeSpanEmbedding d).integral_comp_comm (μ := μ)
        (fun s => x.val i • f (integratedSheetAnchor i x s))]
    _ = ∫ s, L (φ s) ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      change x.val i • brownianCubeSpanEmbedding d
          (f (integratedSheetAnchor i x s)) = L (φ s)
      rw [map_smul, hrepr s hs]
    _ = L (∫ s, φ s ∂μ) := by
      exact L.integral_comp_comm hφint
    _ = L (scalarIntegratedKernelFeature (m i) t) := by
      congr 1
    _ = L (naturalOrderUnitKernel (m i + 1) t) := by
      rw [scalarIntegratedKernelFeature_eq_naturalOrder]
    _ = naturalTensorFeature (Function.update m i (m i + 1)) x := hfinal.symm

/-- At order one in every coordinate, the tensor kernel is precisely the
original anchored box feature. -/
theorem naturalTensorFeature_zero_eq_feature {d : ℕ}
    (x : BrownianCubeAnchor d) :
    naturalTensorFeature (fun _ : Fin d => 0) x =
      brownianCubeSpanEmbedding d (featureVector x) := by
  let μ : Measure (Fin d → ℝ) := Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
  let B : Set (Fin d → ℝ) := Set.univ.pi
    (fun i : Fin d => Set.Icc (0 : ℝ) (x.val i))
  let v : Fin d → AlignmentFractionalL2.UnitL2 := fun i =>
    unitBoxFeature (x.val i) (x.property i).1 (x.property i).2
  have hvkernel (i : Fin d) :
      naturalOrderUnitKernel 0
        (AlignmentFractionalTensorOperator.cubeCoordinate i x) = v i := by
    let t := AlignmentFractionalTensorOperator.cubeCoordinate i x
    have ht := Set.mem_Icc.mp t.property
    calc
      naturalOrderUnitKernel 0 t =
          AlignmentFractionalL2.kernelVector 1 t.1 (by norm_num) ht.1 ht.2 := by
            dsimp [naturalOrderUnitKernel]
            convert AlignmentFractionalTranslation.translatedUnitKernelFamily_eq_kernelVector
              ((0 : ℝ) + 1) t.1 (by norm_num) ht.1 ht.2 using 1 <;> norm_num
      _ = v i := by
        dsimp [v]
        have hvx := unitBoxFeature_eq_orderOneKernel t.1 ht.1 ht.2
        exact hvx.symm
  have hten : naturalTensorFeature (fun _ : Fin d => 0) x =
      unitCubeZeroExtendCLM d
        (AlignmentFractionalTensorOperator.productToCube d
          (BrownianSharp.AlignmentL2TensorProduct.productVector v)) := by
    change unitCubeZeroExtendCLM d
        (AlignmentFractionalTensorOperator.productToCube d
          (BrownianSharp.AlignmentL2TensorProduct.tensorContinuous
            (μ := fun _ : Fin d => volume.restrict (Set.Icc (0 : ℝ) 1))
            (fun i => naturalOrderUnitKernel 0
              (AlignmentFractionalTensorOperator.cubeCoordinate i x)))) = _
    rw [BrownianSharp.AlignmentL2TensorProduct.tensorContinuous_apply]
    apply congrArg (unitCubeZeroExtendCLM d)
    apply congrArg (AlignmentFractionalTensorOperator.productToCube d)
    apply congrArg BrownianSharp.AlignmentL2TensorProduct.productVector
    exact funext hvkernel
  have hv : ∀ i, v i =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)]
      (Set.Icc (0 : ℝ) (x.val i)).indicator (fun _ => (1 : ℝ)) := by
    intro i
    exact indicatorConstLp_coeFn
  have hprod :
      BrownianSharp.AlignmentL2TensorProduct.productVector v =ᵐ[
        Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0 : ℝ) 1))]
        (fun z => ∏ i, (Set.Icc (0 : ℝ) (x.val i)).indicator
          (fun _ => (1 : ℝ)) (z i)) := by
    have hp := BrownianSharp.AlignmentL2TensorProduct.productVector_ae v
    have hf := Measure.ae_eq_pi hv
    filter_upwards [hp, hf] with z hp hf
    rw [hp]
    apply Finset.prod_congr rfl
    intro i hi
    exact congrFun hf i
  have hto : AlignmentFractionalTensorOperator.productToCube d
      (BrownianSharp.AlignmentL2TensorProduct.productVector v) =ᵐ[
        (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
          (CameronMartin.unitCubeSet d)]
      (BrownianSharp.AlignmentL2TensorProduct.productVector v) := by
    exact AlignmentFractionalTensorOperator.productToCube_ae _
  have hprodCube : BrownianSharp.AlignmentL2TensorProduct.productVector v =ᵐ[
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet d)]
      (fun z => ∏ i, (Set.Icc (0 : ℝ) (x.val i)).indicator
        (fun _ => (1 : ℝ)) (z i)) := by
    rw [BrownianSharp.AlignmentFractionalTensor.unitCube_measure_eq_pi]
    exact hprod
  have hzero := unitCubeZeroExtend_coe_ae
    (AlignmentFractionalTensorOperator.productToCube d
      (BrownianSharp.AlignmentL2TensorProduct.productVector v))
  have hfeature : (featureVector x : CameronMartin.AmbientL2 d) =ᵐ[μ]
      B.indicator (fun _ => (1 : ℝ)) := by
    change (brownianSheetBoxIndicatorLp x.val : CameronMartin.AmbientL2 d) =ᵐ[μ]
      B.indicator (fun _ => (1 : ℝ))
    rw [brownianSheetBoxIndicatorLp]
    exact indicatorConstLp_coeFn
  have hBcube : B ⊆ CameronMartin.unitCubeSet d := by
    intro z hz
    change ∀ i ∈ (Set.univ : Set (Fin d)), z i ∈ Set.Icc (0 : ℝ) 1
    intro i hi
    have hzi := (Set.mem_pi.mp hz) i hi
    exact ⟨hzi.1, le_trans hzi.2 (x.property i).2⟩
  have hprodB (z : Fin d → ℝ) :
      (∏ i, (Set.Icc (0 : ℝ) (x.val i)).indicator
          (fun _ => (1 : ℝ)) (z i)) = B.indicator (fun _ => (1 : ℝ)) z := by
    by_cases hz : z ∈ B
    · have hzi : ∀ i, z i ∈ Set.Icc (0 : ℝ) (x.val i) := by
        intro i
        exact (Set.mem_pi.mp hz) i (Set.mem_univ i)
      have hzIcc : z ∈ Set.Icc (fun _ : Fin d => (0 : ℝ)) x.val := by
        apply Set.mem_Icc.mpr
        constructor
        · intro i
          exact (hzi i).1
        · intro i
          exact (hzi i).2
      rw [Set.indicator_of_mem hz]
      simp [Set.indicator, hzIcc, hzi]
    · have hzi : ∃ i, z i ∉ Set.Icc (0 : ℝ) (x.val i) := by
        by_contra hn
        push_neg at hn
        apply hz
        exact Set.mem_pi.mpr (fun i hi => hn i)
      obtain ⟨i, hi⟩ := hzi
      have hterm : (Set.Icc (0 : ℝ) (x.val i)).indicator
          (fun _ => (1 : ℝ)) (z i) = 0 := by
        simp [Set.indicator, hi]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hterm]
      have hnIcc : z ∉ Set.Icc (fun _ : Fin d => (0 : ℝ)) x.val := by
        intro hzIcc
        exact hi ⟨(Set.mem_Icc.mp hzIcc).1 i, (Set.mem_Icc.mp hzIcc).2 i⟩
      have hnB : z ∉ B := by
        intro hzB
        exact hi ((Set.mem_pi.mp hzB) i (Set.mem_univ i))
      simp [Set.indicator, hnB]
  apply Lp.ext
  have htoAmbient := (ae_restrict_iff' (CameronMartin.measurableSet_unitCubeSet d)).1 hto
  have hprodAmbient := (ae_restrict_iff' (CameronMartin.measurableSet_unitCubeSet d)).1 hprodCube
  filter_upwards [hzero, htoAmbient, hprodAmbient, hfeature]
    with z hzext hto hp hfeat
  change naturalTensorFeature (fun _ : Fin d => 0) x z =
      (brownianCubeSpanEmbedding d (featureVector x)) z
  rw [hten]
  change (unitCubeZeroExtend
      (AlignmentFractionalTensorOperator.productToCube d
        (BrownianSharp.AlignmentL2TensorProduct.productVector v))) z = _
  rw [hzext]
  by_cases hcube : z ∈ CameronMartin.unitCubeSet d
  · rw [Set.indicator_of_mem hcube, hto hcube, hp hcube, hprodB z]
    change B.indicator (fun _ => (1 : ℝ)) z = (featureVector x : CameronMartin.AmbientL2 d) z
    rw [← hfeat]
  · simp [Set.indicator, hcube]
    have hnB : z ∉ B := fun hz => hcube (hBcube hz)
    have hfeat0 : (brownianCubeSpanEmbedding d (featureVector x)) z = 0 := by
      change (featureVector x : CameronMartin.AmbientL2 d) z = 0
      rw [hfeat]
      simp [Set.indicator, hnB]
    simp [Set.indicator, hcube, hfeat0]

theorem iterateCoordinateFeature_naturalTensor {d : ℕ} (i : Fin d) :
    ∀ (n : ℕ) (q : Fin d → ℕ)
      (f : C(BrownianCubeAnchor d, brownianCubeBoxSpan d)),
      (∀ z, brownianCubeSpanEmbedding d (f z) = naturalTensorFeature q z) →
      ∀ x, brownianCubeSpanEmbedding d
        (iterateCoordinateFeature i n f x) =
          naturalTensorFeature (Function.update q i (q i + n)) x := by
  intro n
  induction n with
  | zero =>
      intro q f hF x
      simpa [iterateCoordinateFeature] using hF x
  | succ n ih =>
      intro q f hF x
      have hprev : ∀ z, brownianCubeSpanEmbedding d
          (iterateCoordinateFeature i n f z) =
            naturalTensorFeature (Function.update q i (q i + n)) z :=
        ih q f hF
      change brownianCubeSpanEmbedding d
        (integrateCoordinateFeature i (iterateCoordinateFeature i n f) x) =
          naturalTensorFeature (Function.update q i (q i + (n + 1))) x
      rw [integrateCoordinateFeature_naturalTensor
        (Function.update q i (q i + n)) i
        (iterateCoordinateFeature i n f) hprev x]
      congr 1
      funext j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self]
        omega
      · simp [Function.update_of_ne hji]

theorem foldlFeatureField_naturalTensor {d : ℕ} (m : Fin d → ℕ) :
    ∀ (l : List (Fin d)) (q : Fin d → ℕ)
      (f : C(BrownianCubeAnchor d, brownianCubeBoxSpan d)),
      (∀ z, brownianCubeSpanEmbedding d (f z) = naturalTensorFeature q z) →
      ∀ x, brownianCubeSpanEmbedding d
        (l.foldl (fun f i => iterateCoordinateFeature i (m i) f) f x) =
          naturalTensorFeature
            (l.foldl (fun q i => Function.update q i (q i + m i)) q) x := by
  intro l
  induction l with
  | nil =>
      intro q f hF x
      simpa using hF x
  | cons i l ih =>
      intro q f hF x
      have hfirst : ∀ z, brownianCubeSpanEmbedding d
          (iterateCoordinateFeature i (m i) f z) =
            naturalTensorFeature (Function.update q i (q i + m i)) z := by
        intro z
        exact iterateCoordinateFeature_naturalTensor i (m i) q f hF z
      simpa [List.foldl_cons] using
        (ih (Function.update q i (q i + m i))
          (iterateCoordinateFeature i (m i) f) hfirst x)

private theorem foldl_update_at_of_not_mem {d : ℕ} (j : Fin d)
    (m : Fin d → ℕ) : ∀ (l : List (Fin d)) (q : Fin d → ℕ),
      j ∉ l → (l.foldl (fun q i => Function.update q i (q i + m i)) q) j = q j := by
  intro l
  induction l with
  | nil =>
      intro q _
      rfl
  | cons i l ih =>
      intro q hn
      have hji : j ≠ i := by
        intro h
        apply hn
        simp [h]
      have htail : j ∉ l := by
        intro h
        apply hn
        simp [h]
      rw [List.foldl_cons, ih (Function.update q i (q i + m i)) htail]
      simp [Function.update_of_ne hji]

private theorem foldl_update_at_of_mem_nodup {d : ℕ} (j : Fin d)
    (m : Fin d → ℕ) : ∀ (l : List (Fin d)) (q : Fin d → ℕ),
      l.Nodup → j ∈ l → (l.foldl (fun q i => Function.update q i (q i + m i)) q) j =
        q j + m j := by
  intro l
  induction l with
  | nil =>
      intro q _ hj
      simp at hj
  | cons i l ih =>
      intro q hn hj
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp hj with hji | hjtail
      · subst j
        rw [List.foldl_cons]
        rw [foldl_update_at_of_not_mem i m l
          (Function.update q i (q i + m i)) hnot]
        simp [Function.update]
      · have hji : j ≠ i := by
          intro h
          subst j
          exact hnot hjtail
        rw [List.foldl_cons, ih (Function.update q i (q i + m i)) hnodup hjtail]
        simp [Function.update_of_ne hji]

theorem integrateSheetFeatureField_naturalTensor {d : ℕ}
    (m : Fin d → ℕ) (x : BrownianCubeAnchor d) :
    brownianCubeSpanEmbedding d (integratedFeatureField m x) = naturalTensorFeature m x := by
  let q0 : Fin d → ℕ := fun _ => 0
  have hbase : ∀ z, brownianCubeSpanEmbedding d
      ((⟨featureVector, featureVector_continuous d⟩ :
        C(BrownianCubeAnchor d, brownianCubeBoxSpan d)) z) = naturalTensorFeature q0 z := by
    intro z
    simpa [q0] using (naturalTensorFeature_zero_eq_feature z).symm
  have hfold := foldlFeatureField_naturalTensor m
    (Finset.univ.toList) q0
    (⟨featureVector, featureVector_continuous d⟩ :
      C(BrownianCubeAnchor d, brownianCubeBoxSpan d)) hbase x
  have hq : (Finset.univ.toList : List (Fin d)).foldl
      (fun q i => Function.update q i (q i + m i)) q0 = m := by
    funext j
    rw [foldl_update_at_of_mem_nodup j m (Finset.univ.toList) q0
      (Finset.nodup_toList _) (by simp)]
    simp [q0]
  unfold integratedFeatureField integrateSheetFeatureField
  rw [hq] at hfold
  exact hfold

theorem unitCubeZeroExtendCLM_inner {d : ℕ}
    (f g : CameronMartin.UnitCubeL2 d) :
    ⟪unitCubeZeroExtendCLM d f, unitCubeZeroExtendCLM d g⟫ = ⟪f, g⟫ := by
  have hnorm (u : CameronMartin.UnitCubeL2 d) :
      ‖unitCubeZeroExtendCLM d u‖ = ‖u‖ := by
    change ‖CameronMartin.unitCubeZeroExtend u‖ = ‖u‖
    exact CameronMartin.unitCubeZeroExtend_norm u
  calc
    ⟪unitCubeZeroExtendCLM d f, unitCubeZeroExtendCLM d g⟫ =
        (‖unitCubeZeroExtendCLM d f + unitCubeZeroExtendCLM d g‖^2 -
          ‖unitCubeZeroExtendCLM d f‖^2 - ‖unitCubeZeroExtendCLM d g‖^2) / 2 := by
            rw [norm_add_sq_real]
            ring
    _ = (‖unitCubeZeroExtendCLM d (f + g)‖^2 -
          ‖unitCubeZeroExtendCLM d f‖^2 - ‖unitCubeZeroExtendCLM d g‖^2) / 2 := by
            rw [map_add]
    _ = (‖f + g‖^2 - ‖f‖^2 - ‖g‖^2) / 2 := by rw [hnorm, hnorm, hnorm]
    _ = ⟪f, g⟫ := by rw [norm_add_sq_real]; ring

theorem naturalTensorFeature_eq_fractionalKernel {d : ℕ}
    (m : Fin d → ℕ) (x : BrownianCubeAnchor d) :
    naturalTensorFeature m x =
      unitCubeZeroExtendCLM d
        (AlignmentFractionalTensorOperator.tensorKernelFamily
          (fun i => (m i : ℝ) + 1)
          (by intro i; have h : (0 : ℝ) ≤ (m i : ℝ) := Nat.cast_nonneg _; linarith) x) := by
  change unitCubeZeroExtendCLM d
      (AlignmentFractionalTensorOperator.productToCube d
        (BrownianSharp.AlignmentL2TensorProduct.tensorContinuous
          (μ := fun _ : Fin d => volume.restrict (Set.Icc (0 : ℝ) 1))
          (fun i => naturalOrderUnitKernel (m i)
            (AlignmentFractionalTensorOperator.cubeCoordinate i x)))) = _
  apply congrArg (unitCubeZeroExtendCLM d)
  change AlignmentFractionalTensorOperator.productToCube d
      (BrownianSharp.AlignmentL2TensorProduct.tensorContinuous
        (μ := fun _ : Fin d => volume.restrict (Set.Icc (0 : ℝ) 1))
        (fun i => naturalOrderUnitKernel (m i)
          (AlignmentFractionalTensorOperator.cubeCoordinate i x))) =
    AlignmentFractionalTensorOperator.productToCube d
      (AlignmentFractionalTensorOperator.productKernelFamily
        (fun i => (m i : ℝ) + 1)
        (by intro i; have h : (0 : ℝ) ≤ (m i : ℝ) := Nat.cast_nonneg _; linarith) x)
  apply congrArg (AlignmentFractionalTensorOperator.productToCube d)
  rw [AlignmentFractionalTensorOperator.productKernelFamily,
    BrownianSharp.AlignmentL2TensorProduct.tensorContinuous_apply]
  congr 1

theorem integratedFeatureField_fractionalIntegrationValue {d : ℕ}
    (m : Fin d → ℕ) (g : CameronMartin.UnitCubeL2 d)
    (x : BrownianCubeAnchor d) :
    ⟪brownianCubeSpanEmbedding d (integratedFeatureField m x),
      unitCubeZeroExtendCLM d g⟫ =
      BrownianSharp.Latest.fractionalIntegrationValue
        (fun i => (m i : ℝ) + 1) g x := by
  let a : Fin d → ℝ := fun i => (m i : ℝ) + 1
  have ha : ∀ i, 1/2 < a i := by
    intro i
    dsimp [a]
    have h : (0 : ℝ) ≤ (m i : ℝ) := Nat.cast_nonneg _
    linarith
  rw [integrateSheetFeatureField_naturalTensor, naturalTensorFeature_eq_fractionalKernel]
  calc
    ⟪unitCubeZeroExtendCLM d
        (AlignmentFractionalTensorOperator.tensorKernelFamily a ha x),
      unitCubeZeroExtendCLM d g⟫ =
      ⟪AlignmentFractionalTensorOperator.tensorKernelFamily a ha x, g⟫ :=
        unitCubeZeroExtendCLM_inner _ _
    _ = AlignmentFractionalTensorOperator.fractionalTensorRL a ha g x := rfl
    _ = BrownianSharp.Latest.fractionalIntegrationValue a g x :=
      AlignmentFractionalTensorOperator.fractionalTensorRL_apply a ha g x

/-- The Volterra composition identity for an arbitrary integrable one-dimensional
source. This is the one-coordinate Fubini step behind integer RL order. -/
theorem volterra_integral_succ {t : ℝ}
    {f : ℝ → ℝ} (hf : IntegrableOn f (Set.Ioc (0 : ℝ) t) volume) :
    (∫ s in Set.Ioc (0 : ℝ) t,
      ∫ u in Set.Ioc (0 : ℝ) s, f u ∂volume ∂volume) =
    ∫ u in Set.Ioc (0 : ℝ) t, (t - u) * f u ∂volume := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) t)
  have hμ : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hfμ : Integrable f μ := by
    exact hf
  have hinner : ∀ s ∈ Set.Ioc (0 : ℝ) t,
      (∫ u, (if u ≤ s then f u else 0) ∂μ) =
        ∫ u in Set.Ioc (0 : ℝ) s, f u ∂volume := by
    intro s hs
    have hio : MeasurableSet (Set.Iic s) := measurableSet_Iic
    have hsets : Set.Iic s ∩ Set.Ioc (0 : ℝ) t = Set.Ioc (0 : ℝ) s := by
      ext u
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc]
      constructor
      · rintro ⟨hus, hu0, hut⟩
        exact ⟨hu0, hus⟩
      · rintro ⟨hu0, hus⟩
        exact ⟨hus, hu0, le_trans hus hs.2⟩
    calc
      _ = ∫ u, (Set.Iic s).indicator f u ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun u => by
          simp [Set.indicator_apply])
      _ = ∫ u, f u ∂(μ.restrict (Set.Iic s)) := by
        rw [integral_indicator hio]
      _ = ∫ u, f u ∂(volume.restrict (Set.Ioc (0 : ℝ) s)) := by
        rw [show μ.restrict (Set.Iic s) =
          volume.restrict (Set.Ioc (0 : ℝ) s) by
            dsimp [μ]
            rw [Measure.restrict_restrict hio, hsets]
            ]
  have hswap := volterraTriangle_integral_swap hfμ
  calc
    (∫ s in Set.Ioc (0 : ℝ) t,
      ∫ u in Set.Ioc (0 : ℝ) s, f u ∂volume ∂volume) =
        ∫ s, ∫ u, (if u ≤ s then f u else 0) ∂μ ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          have hs' : s ∈ Set.Ioc (0 : ℝ) t := hs
          rw [hinner s hs']
    _ = ∫ u, ∫ s, (if u ≤ s then f u else 0) ∂μ ∂μ := hswap
    _ = ∫ u in Set.Ioc (0 : ℝ) t, (t - u) * f u ∂volume := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
          exact volterraTriangle_inner_integral hu.1 hu.2

/-- Integer-order Gamma kernels are exactly the factorial-normalized
truncated-power tensor kernels generated by repeated ordinary integration. -/
theorem fractionalTensorKernel_natSucc_eq_power {d : ℕ}
    (m : Fin d → ℕ) (t : BrownianCubeAnchor d) (u : Fin d → ℝ) :
    BrownianSharp.Latest.fractionalTensorKernel (fun i => (m i : ℝ) + 1) t u =
      ∏ i, if u i < t.val i then
        ((m i).factorial : ℝ)⁻¹ * (t.val i - u i) ^ (m i) else 0 := by
  unfold BrownianSharp.Latest.fractionalTensorKernel
  apply Finset.prod_congr rfl
  intro i hi
  have hγ : Real.Gamma ((m i : ℝ) + 1) = (m i).factorial :=
    Real.Gamma_nat_eq_factorial (m i)
  by_cases hu : u i < t.val i
  · simp [hu, hγ]
  · simp [hu]

/-- Pairing a Bochner-integrated feature field against a fixed source vector
commutes with the corresponding path integration operator. -/
theorem inner_integrateCoordinateFeature_eq_path {d : ℕ}
    (i : Fin d) (g : brownianCubeBoxSpan d)
    (f : C(BrownianCubeAnchor d, brownianCubeBoxSpan d))
    (x : BrownianCubeAnchor d) :
    ⟪g, integrateCoordinateFeature i f x⟫ =
      BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath i
        ⟨fun z => ⟪g, f z⟫, continuous_const.inner f.continuous⟩ x := by
  rw [integrateCoordinateFeature_apply,
    BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath_apply]
  let F : ℝ → brownianCubeBoxSpan d := fun v =>
    x.val i • f (brownianCubeClamp d (Function.update x.val i (x.val i * v)))
  have hF : Integrable F (volume.restrict (Set.Icc (0 : ℝ) 1)) := by
    have hc : Continuous F := by
      dsimp [F]
      exact (continuous_const : Continuous (fun _ : ℝ => x.val i)).smul
        (f.continuous.comp ((continuous_brownianCubeClamp d).comp (by fun_prop)))
    exact hc.continuousOn.integrableOn_compact
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hpair :
      (fun v => ⟪g, F v⟫) =
        fun v => x.val i * ⟪g,
          f (brownianCubeClamp d (Function.update x.val i (x.val i * v)))⟫ := by
    funext v
    simp [F, real_inner_smul_right]
  calc
    ⟪g, ∫ v in Set.Icc (0 : ℝ) 1, F v ∂volume⟫ =
        ∫ v in Set.Icc (0 : ℝ) 1, ⟪g, F v⟫ ∂volume := by
          exact (integral_inner hF g).symm
    _ = ∫ v in Set.Icc (0 : ℝ) 1,
        x.val i * ⟪g,
          f (brownianCubeClamp d
            (Function.update x.val i (x.val i * v)))⟫ ∂volume := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun v => congrFun hpair v)
    _ = BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath i
        ⟨fun z => ⟪g, f z⟫, continuous_const.inner f.continuous⟩ x := rfl

/-- Iterated feature integration pairs with the same number of scalar path
integrations, for every vector in the feature Hilbert space. -/
theorem inner_iterateCoordinateFeature_eq_path {d : ℕ}
    (i : Fin d) (g : brownianCubeBoxSpan d) :
    ∀ n (f : C(BrownianCubeAnchor d, brownianCubeBoxSpan d))
      (x : BrownianCubeAnchor d),
      ⟪g, iterateCoordinateFeature i n f x⟫ =
        BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath i n
          ⟨fun z => ⟪g, f z⟫, continuous_const.inner f.continuous⟩ x := by
  intro n
  induction n with
  | zero =>
      intro f x
      rfl
  | succ n ih =>
      intro f x
      change ⟪g, integrateCoordinateFeature i (iterateCoordinateFeature i n f) x⟫ = _
      rw [inner_integrateCoordinateFeature_eq_path]
      have hpath :
          (⟨fun z => ⟪g, iterateCoordinateFeature i n f z⟫,
            continuous_const.inner (iterateCoordinateFeature i n f).continuous⟩ :
              C(BrownianCubeAnchor d, ℝ)) =
          BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath i n
            ⟨fun z => ⟪g, f z⟫, continuous_const.inner f.continuous⟩ := by
        ext z
        exact ih f z
      rw [hpath]
      rfl

/-- For every integer multi-order, the deterministic feature paired against a
source vector is its repeated path integral. This identifies the integrated
feature field as the representer of the integrated evaluation functional. -/
theorem integratedFeatureField_pairing_eq_path {d : ℕ}
    (m : Fin d → ℕ) (g : brownianCubeBoxSpan d)
    (x : BrownianCubeAnchor d) :
    ⟪g, integratedFeatureField m x⟫ =
      BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (featurePath g) x := by
  classical
  unfold integratedFeatureField integrateSheetFeatureField
  have hfold : ∀ (l : List (Fin d))
      (f : C(BrownianCubeAnchor d, brownianCubeBoxSpan d)),
      ⟪g, l.foldl (fun f i => iterateCoordinateFeature i (m i) f) f x⟫ =
        l.foldl (fun f i => BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath i
          (m i) f)
          ⟨fun z => ⟪g, f z⟫, continuous_const.inner f.continuous⟩ x := by
    intro l
    induction l with
    | nil =>
        intro f
        rfl
    | cons i l ih =>
        intro f
        simp only [List.foldl_cons]
        rw [ih (iterateCoordinateFeature i (m i) f)]
        have hpath :
            (⟨fun z => ⟪g, iterateCoordinateFeature i (m i) f z⟫,
              continuous_const.inner (iterateCoordinateFeature i (m i) f).continuous⟩ :
                C(BrownianCubeAnchor d, ℝ)) =
            BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath i (m i)
              ⟨fun z => ⟪g, f z⟫, continuous_const.inner f.continuous⟩ := by
          ext z
          exact inner_iterateCoordinateFeature_eq_path i g (m i) f z
        rw [hpath]
  have hbase :
      (⟨fun z => ⟪g, (featureVector z : brownianCubeBoxSpan d)⟫,
        continuous_const.inner (featureVector_continuous d)⟩ :
          C(BrownianCubeAnchor d, ℝ)) = featurePath g := by
    rfl
  rw [← hbase]
  simpa [BrownianSharp.AlignmentGaussianRates.integrateSheetPath] using
    hfold (Finset.univ.toList) ⟨featureVector, featureVector_continuous d⟩

/-- Ambient-source version of the deterministic bridge: the integrated
feature is the actual `L²` representer of repeated RL integration applied to
the anchored integration path of any ambient source. -/
theorem integratedFeatureField_ambient_pairing_eq_path {d : ℕ}
    (m : Fin d → ℕ) (g : CameronMartin.AmbientL2 d)
    (x : BrownianCubeAnchor d) :
    ⟪brownianCubeSpanEmbedding d (integratedFeatureField m x), g⟫ =
      BrownianSharp.AlignmentGaussianRates.integrateSheetPath m
        (CameronMartin.anchoredIntegrationPath g) x := by
  let p : brownianCubeBoxSpan d :=
    (brownianCubeBoxSpan d).orthogonalProjectionOnto g
  have hp : CameronMartin.anchoredIntegrationPath g = featurePath p := by
    ext z
    exact CameronMartin.anchoredIntegrationPath_projected g z
  have hproj := (brownianCubeBoxSpan d).inner_orthogonalProjectionOnto_eq_of_mem_right
    (u := integratedFeatureField m x) (v := g)
  calc
    ⟪brownianCubeSpanEmbedding d (integratedFeatureField m x), g⟫ =
        ⟪g, brownianCubeSpanEmbedding d (integratedFeatureField m x)⟫ :=
          real_inner_comm _ _
    _ =
        ⟪p, integratedFeatureField m x⟫ := by
          exact hproj.symm
    _ = BrownianSharp.AlignmentGaussianRates.integrateSheetPath m
          (featurePath p) x := by
            simpa only [real_inner_comm] using
              integratedFeatureField_pairing_eq_path m p x
    _ = BrownianSharp.AlignmentGaussianRates.integrateSheetPath m
          (CameronMartin.anchoredIntegrationPath g) x := by
            rw [← hp]

theorem integrateSheetPath_unitCube_eq_fractionalIntegrationValue {d : ℕ}
    (m : Fin d → ℕ) (g : CameronMartin.UnitCubeL2 d)
    (x : BrownianCubeAnchor d) :
    BrownianSharp.AlignmentGaussianRates.integrateSheetPath m
        (CameronMartin.unitCubeIntegrationPath g) x =
      BrownianSharp.Latest.fractionalIntegrationValue
        (fun i => (m i : ℝ) + 1) g x := by
  calc
    BrownianSharp.AlignmentGaussianRates.integrateSheetPath m
        (CameronMartin.unitCubeIntegrationPath g) x =
      ⟪brownianCubeSpanEmbedding d (integratedFeatureField m x),
        unitCubeZeroExtendCLM d g⟫ := by
          simpa [CameronMartin.unitCubeIntegrationPath, unitCubeZeroExtendCLM] using
            (integratedFeatureField_ambient_pairing_eq_path m
              (CameronMartin.unitCubeZeroExtend g) x).symm
    _ = BrownianSharp.Latest.fractionalIntegrationValue
        (fun i => (m i : ℝ) + 1) g x :=
      integratedFeatureField_fractionalIntegrationValue m g x

/-- A reusable normalized Gaussian feature field: a measurable random
continuous path represented pointwise in `L²` by one fixed isonormal map. -/
structure ContinuousIsonormalField {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P) where
  path : Ω → C(BrownianCubeAnchor d, ℝ)
  feature : C(BrownianCubeAnchor d, brownianCubeBoxSpan d)
  measurable_path : Measurable path
  eval_ae : ∀ x, (fun ω => path ω x) =ᵐ[P]
    fun ω => T (feature x) ω
  feature_norm_le_one : ∀ x, ‖feature x‖ ≤ 1

theorem ContinuousIsonormalField.integrateCoordinate_eval_ae {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P}
    (X : ContinuousIsonormalField P T) (i : Fin d)
    (x : BrownianCubeAnchor d)
    (hmoment : ∀ z, ∫ ω, ‖X.path ω z‖ ∂P ≤ 1) :
    (fun ω => BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath i
        (X.path ω) x) =ᵐ[P]
      fun ω => T (integrateCoordinateFeature i X.feature x) ω := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let φ : ℝ → Lp ℝ 2 P := fun v =>
    x.val i • T (X.feature (integratedSheetAnchor i x v))
  have hφcont : Continuous φ := by
    exact (continuous_const : Continuous (fun _ : ℝ => x.val i)).smul
      ((T.continuous).comp (X.feature.continuous.comp
        (continuous_integratedSheetAnchor i x)))
  have hφint : Integrable φ μ :=
    hφcont.continuousOn.integrableOn_compact
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hfeature :
      T (integrateCoordinateFeature i X.feature x) = ∫ v, φ v ∂μ := by
    change T (∫ v in Set.Icc (0 : ℝ) 1,
        x.val i • X.feature (integratedSheetAnchor i x v) ∂volume) = _
    rw [← T.integral_comp_comm (μ := μ)
      (fun v => x.val i • X.feature (integratedSheetAnchor i x v))]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    change T (x.val i • X.feature (integratedSheetAnchor i x v)) = φ v
    simp [map_smul, φ]
  let F : ℝ × Ω → ℝ := fun p =>
    x.val i * X.path p.2 (integratedSheetAnchor i x p.1)
  have hFmeas : Measurable F := by
    let hpair : ℝ × Ω → C(BrownianCubeAnchor d, ℝ) × BrownianCubeAnchor d :=
      fun p => (X.path p.2, integratedSheetAnchor i x p.1)
    have hp : Measurable hpair := by
      apply Measurable.prodMk
      · exact X.measurable_path.comp measurable_snd
      · exact (continuous_integratedSheetAnchor i x).measurable.comp measurable_fst
    have heval := ContinuousEval.continuous_eval.measurable.comp hp
    change Measurable (fun p : ℝ × Ω => x.val i *
      X.path p.2 (integratedSheetAnchor i x p.1))
    exact measurable_const.mul heval
  have hFsm : StronglyMeasurable F := hFmeas.stronglyMeasurable
  have hnormsm : StronglyMeasurable (fun p => ‖F p‖) := hFsm.norm
  have hinner : StronglyMeasurable (fun v => ∫ ω, ‖F (v, ω)‖ ∂P) :=
    hnormsm.integral_prod_right'
  have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by
    exact integrableOn_const (by rw [Real.volume_Icc]; norm_num)
  have hsecond : Integrable (fun v => ∫ ω, ‖F (v, ω)‖ ∂P) μ := by
    apply hconst.mono hinner.aestronglyMeasurable
    filter_upwards with v
    have hv := hmoment (integratedSheetAnchor i x v)
    have hnonneg : 0 ≤ ∫ ω, ‖X.path ω (integratedSheetAnchor i x v)‖ ∂P :=
      integral_nonneg fun ω => norm_nonneg _
    have hxi := (x.property i).1
    have hxiabs : |x.val i| ≤ 1 := by
      rw [abs_of_nonneg hxi]
      exact (x.property i).2
    have hbound : |x.val i| *
        ∫ ω, ‖X.path ω (integratedSheetAnchor i x v)‖ ∂P ≤ 1 := by
      nlinarith [hv, hnonneg]
    have hval : ∫ ω, ‖x.val i * X.path ω (integratedSheetAnchor i x v)‖ ∂P ≤ 1 := by
      calc
        ∫ ω, ‖x.val i * X.path ω (integratedSheetAnchor i x v)‖ ∂P =
            |x.val i| * ∫ ω, ‖X.path ω (integratedSheetAnchor i x v)‖ ∂P := by
          rw [show (fun ω => ‖x.val i * X.path ω (integratedSheetAnchor i x v)‖) =
              (fun ω => |x.val i| * ‖X.path ω (integratedSheetAnchor i x v)‖) from by
                funext ω
                rw [norm_mul, Real.norm_eq_abs]]
          rw [integral_const_mul]
        _ ≤ 1 := hbound
    have hvalF : ∫ ω, ‖F (v, ω)‖ ∂P ≤ 1 := by
      simpa [F, norm_mul, Real.norm_eq_abs] using hval
    have hnonnegF : 0 ≤ ∫ ω, ‖F (v, ω)‖ ∂P :=
      integral_nonneg (fun ω => norm_nonneg (F (v, ω)))
    rw [Real.norm_eq_abs, abs_of_nonneg hnonnegF]
    norm_num
    exact hvalF
  have hfirst : ∀ᵐ v ∂μ, Integrable
      (fun ω => F (v, ω)) P := by
    filter_upwards with v
    have hmem : MemLp (fun ω => X.path ω (integratedSheetAnchor i x v)) 2 P :=
      (Lp.memLp (T (X.feature (integratedSheetAnchor i x v)))).ae_eq
        (X.eval_ae (integratedSheetAnchor i x v)).symm
    exact (hmem.const_mul (x.val i)).integrable (by norm_num)
  have hFint : Integrable F (μ.prod P) :=
    (integrable_prod_iff hFsm.aestronglyMeasurable).2 ⟨hfirst, hsecond⟩
  have hpathInt : Integrable
      (fun ω => BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath i
        (X.path ω) x) P := by
    have hswap : Integrable (Function.uncurry (fun ω v => F (v, ω))) (P.prod μ) :=
      hFint.swap
    have hint := hswap.integral_prod_left
    have heq : (fun ω => BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath i
        (X.path ω) x) = fun ω => ∫ v, F (v, ω) ∂μ := by
      funext ω
      rw [BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath_apply]
      rfl
    rw [heq]
    exact hint
  have hnormalInt : Integrable (fun ω => T (integrateCoordinateFeature i X.feature x) ω) P :=
    (Lp.memLp _).integrable (by norm_num)
  have hsets : ∀ A : Set Ω, MeasurableSet A → P A < ⊤ →
      ∫ ω in A, BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath i
          (X.path ω) x ∂P =
        ∫ ω in A, T (integrateCoordinateFeature i X.feature x) ω ∂P := by
    intro A hA hAfinite
    have hFA : Integrable F (μ.prod (P.restrict A)) :=
      hFint.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    have hswap :
        Integrable (Function.uncurry (fun ω v => F (v, ω)))
          ((P.restrict A).prod μ) := by
      change Integrable (F ∘ Prod.swap) ((P.restrict A).prod μ)
      exact hFA.swap
    have hleft :
        ∫ ω in A, BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath i
            (X.path ω) x ∂P =
          ∫ v, ∫ ω in A, F (v, ω) ∂P ∂μ := by
      have heq : (fun ω => BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath i
          (X.path ω) x) = fun ω => ∫ v, F (v, ω) ∂μ := by
        funext ω
        rw [BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath_apply]
        rfl
      change ∫ ω, _ ∂(P.restrict A) = _
      rw [heq]
      rw [integral_integral_swap hswap]
    let g : Lp ℝ 2 P := indicatorConstLp 2 hA hAfinite.ne 1
    let L : Lp ℝ 2 P →L[ℝ] ℝ := innerSL ℝ g
    have hL_eval (z : BrownianCubeAnchor d) :
        L (T (X.feature z)) = ∫ ω in A, X.path ω z ∂P := by
      change ⟪g, T (X.feature z)⟫ = _
      rw [L2.inner_indicatorConstLp_one hA hAfinite.ne]
      apply setIntegral_congr_ae hA
      filter_upwards [X.eval_ae z] with ω hω hωA
      exact hω.symm
    have hLfeature :
        L (T (integrateCoordinateFeature i X.feature x)) =
          ∫ ω in A, T (integrateCoordinateFeature i X.feature x) ω ∂P := by
      change ⟪g, T (integrateCoordinateFeature i X.feature x)⟫ = _
      exact L2.inner_indicatorConstLp_one hA hAfinite.ne _
    have hright :
        ∫ ω in A, T (integrateCoordinateFeature i X.feature x) ω ∂P =
          ∫ v, ∫ ω in A, F (v, ω) ∂P ∂μ := by
      rw [← hLfeature, hfeature, ← L.integral_comp_comm hφint]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      change L (x.val i • T (X.feature (integratedSheetAnchor i x v))) = _
      rw [map_smul, hL_eval]
      simp [F, integral_const_mul]
    exact hleft.trans hright.symm
  exact Integrable.ae_eq_of_forall_setIntegral_eq _ _ hpathInt hnormalInt hsets

private theorem integral_norm_le_one_of_second_moment {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : MemLp f 2 P)
    (hsq : ∫ ω, f ω ^ 2 ∂P ≤ 1) :
    ∫ ω, ‖f ω‖ ∂P ≤ 1 := by
  have hnormint : Integrable (fun ω => ‖f ω‖) P :=
    hf.norm.integrable (by norm_num)
  have hsqint : Integrable (fun ω => f ω ^ 2) P := by
    convert hf.integrable_mul hf using 1
    ext ω
    simp [pow_two]
  have hmajor : ∀ ω, ‖f ω‖ ≤ (1 + f ω ^ 2) / 2 := by
    intro ω
    rw [Real.norm_eq_abs]
    by_cases h : 0 ≤ f ω
    · rw [abs_of_nonneg h]
      nlinarith [sq_nonneg (f ω - 1)]
    · rw [abs_of_nonpos (le_of_not_ge h)]
      nlinarith [sq_nonneg (f ω + 1)]
  have hright : Integrable (fun ω => (1 + f ω ^ 2) / 2) P := by
    have heq : (fun ω => (1 + f ω ^ 2) / 2) =
        (fun _ : Ω => (1 / 2 : ℝ)) + (fun ω => (1 / 2 : ℝ) * f ω ^ 2) := by
      ext ω
      simp
      ring
    rw [heq]
    exact (integrable_const (1 / 2 : ℝ)).add
      (hsqint.const_mul (1 / 2 : ℝ))
  calc
    ∫ ω, ‖f ω‖ ∂P ≤ ∫ ω, (1 + f ω ^ 2) / 2 ∂P :=
      integral_mono_ae hnormint hright (Filter.Eventually.of_forall hmajor)
    _ = (1 + ∫ ω, f ω ^ 2 ∂P) / 2 := by
      calc
        _ = ∫ ω, (1 / 2 : ℝ) + (1 / 2) * f ω ^ 2 ∂P := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall (fun ω => by ring)
        _ = (∫ _ω, (1 / 2 : ℝ) ∂P) +
            ∫ ω, (1 / 2 : ℝ) * f ω ^ 2 ∂P :=
          integral_add (integrable_const (1 / 2 : ℝ))
            (hsqint.const_mul (1 / 2 : ℝ))
        _ = (1 + ∫ ω, f ω ^ 2 ∂P) / 2 := by
          rw [integral_const, integral_const_mul]
          simp
          ring
    _ ≤ 1 := by linarith

theorem ContinuousIsonormalField.eval_memLp {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P}
    (X : ContinuousIsonormalField P T) (x : BrownianCubeAnchor d) :
    MemLp (fun ω => X.path ω x) 2 P := by
  have hTmem : MemLp (fun ω => T (X.feature x) ω) 2 P :=
    Lp.memLp (T (X.feature x))
  exact hTmem.ae_eq (X.eval_ae x).symm

theorem ContinuousIsonormalField.eval_integral_sq_le_one {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P}
    (X : ContinuousIsonormalField P T) (x : BrownianCubeAnchor d) :
    ∫ ω, (X.path ω x) ^ 2 ∂P ≤ 1 := by
  let hmem := X.eval_memLp x
  let f : Lp ℝ 2 P := hmem.toLp (fun ω => X.path ω x)
  have hrep : (fun ω => f ω) =ᵐ[P] fun ω => X.path ω x := hmem.coeFn_toLp
  have hclass : f = T (X.feature x) := by
    apply Lp.ext
    exact hrep.trans (X.eval_ae x)
  have hsqint : Integrable (fun ω => (X.path ω x) ^ 2) P := by
    convert hmem.integrable_mul hmem using 1
    ext ω
    simp [pow_two]
  have hsq : ∫ ω, (X.path ω x) ^ 2 ∂P = ‖f‖ ^ 2 := by
    calc
      ∫ ω, (X.path ω x) ^ 2 ∂P = ∫ ω, (f ω) ^ 2 ∂P := by
        apply integral_congr_ae
        filter_upwards [hrep] with ω hω
        simp [hω]
      _ = ⟪f, f⟫ := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards with ω
        change (f ω) ^ 2 = (f ω) * (f ω)
        ring
      _ = ‖f‖ ^ 2 := real_inner_self_eq_norm_sq f
  have hnorm : ‖f‖ ≤ 1 := by
    calc
      ‖f‖ = ‖T (X.feature x)‖ := congrArg norm hclass
      _ = ‖X.feature x‖ := T.norm_map _
      _ ≤ 1 := X.feature_norm_le_one x
  rw [hsq]
  nlinarith [norm_nonneg f]

theorem ContinuousIsonormalField.eval_integral_norm_le_one {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P}
    (X : ContinuousIsonormalField P T) (x : BrownianCubeAnchor d) :
    ∫ ω, ‖X.path ω x‖ ∂P ≤ 1 := by
  exact integral_norm_le_one_of_second_moment (fun ω => X.path ω x)
    (X.eval_memLp x) (X.eval_integral_sq_le_one x)

/-- Apply the actual sample-path and deterministic-feature coordinate
integrals to a continuously varying isonormal field. -/
noncomputable def ContinuousIsonormalField.integrateCoordinate {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P}
    (X : ContinuousIsonormalField P T) (i : Fin d) :
    ContinuousIsonormalField P T := by
  refine ⟨(fun ω => BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath
      i (X.path ω)), integrateCoordinateFeature i X.feature, ?_, ?_, ?_⟩
  · exact (BrownianSharp.AlignmentGaussianRates.integrateCoordinatePath_continuous i).measurable.comp
      X.measurable_path
  · intro x
    exact X.integrateCoordinate_eval_ae i x X.eval_integral_norm_le_one
  · intro x
    let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
    let f : ℝ → brownianCubeBoxSpan d := fun v =>
      x.val i • X.feature (integratedSheetAnchor i x v)
    have hf : Integrable f μ := by
      have hc : Continuous f := by
        exact (continuous_const : Continuous (fun _ : ℝ => x.val i)).smul
          (X.feature.continuous.comp (continuous_integratedSheetAnchor i x))
      exact hc.continuousOn.integrableOn_compact
        (isCompact_Icc (a := (0 : ℝ)) (b := 1))
    have hconst : Integrable (fun _ : ℝ => (1 : ℝ)) μ := by
      exact integrableOn_const (by rw [Real.volume_Icc]; norm_num)
    have hbound : ∀ᵐ v ∂μ, ‖f v‖ ≤ 1 := by
      filter_upwards with v
      dsimp [f]
      rw [norm_smul]
      have hxi := (x.property i).1
      have hxiabs : |x.val i| ≤ 1 := by
        rw [abs_of_nonneg hxi]
        exact (x.property i).2
      rw [Real.norm_eq_abs]
      calc
        |x.val i| * ‖X.feature (integratedSheetAnchor i x v)‖ ≤
            |x.val i| * 1 :=
          mul_le_mul_of_nonneg_left
            (X.feature_norm_le_one (integratedSheetAnchor i x v))
            (abs_nonneg _)
        _ ≤ 1 := by nlinarith
    change ‖∫ v, f v ∂μ‖ ≤ 1
    calc
      ‖∫ v, f v ∂μ‖ ≤ ∫ v, ‖f v‖ ∂μ := norm_integral_le_integral_norm f
      _ ≤ ∫ v, (1 : ℝ) ∂μ := integral_mono_ae hf.norm hconst hbound
      _ = 1 := by simp [μ]

def iterateCoordinateIsonormalField {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P} (i : Fin d) :
    ℕ → ContinuousIsonormalField P T → ContinuousIsonormalField P T
  | 0, X => X
  | n + 1, X => (iterateCoordinateIsonormalField i n X).integrateCoordinate i

def integrateSheetIsonormalField {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P}
    (m : Fin d → ℕ) (X : ContinuousIsonormalField P T) :
    ContinuousIsonormalField P T :=
  (Finset.univ.toList : List (Fin d)).foldl
    (fun Y i => iterateCoordinateIsonormalField i (m i) Y) X

theorem iterateCoordinateIsonormalField_path {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P}
    (i : Fin d) (n : ℕ) (X : ContinuousIsonormalField P T) :
    (iterateCoordinateIsonormalField i n X).path =
      fun ω => BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath i n (X.path ω) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      ext ω
      simp [iterateCoordinateIsonormalField, ContinuousIsonormalField.integrateCoordinate,
        ih, BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath]

theorem iterateCoordinateIsonormalField_feature {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P}
    (i : Fin d) (n : ℕ) (X : ContinuousIsonormalField P T) :
    (iterateCoordinateIsonormalField i n X).feature =
      iterateCoordinateFeature i n X.feature := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [iterateCoordinateIsonormalField, ContinuousIsonormalField.integrateCoordinate,
        ih, iterateCoordinateFeature]

theorem integrateSheetIsonormalField_path {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P}
    (m : Fin d → ℕ) (X : ContinuousIsonormalField P T) :
    (integrateSheetIsonormalField m X).path =
      fun ω => BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (X.path ω) := by
  classical
  have hfold : ∀ l : List (Fin d), ∀ Y : ContinuousIsonormalField P T,
      (l.foldl (fun Z j => iterateCoordinateIsonormalField j (m j) Z) Y).path =
        fun ω => l.foldl (fun f j => BrownianSharp.AlignmentGaussianRates.iterateCoordinatePath
          j (m j) f) (Y.path ω) := by
    intro l
    induction l with
    | nil => intro Y; rfl
    | cons j l ih =>
        intro Y
        simp only [List.foldl_cons]
        rw [ih]
        funext ω
        rw [iterateCoordinateIsonormalField_path]
  change ((Finset.univ.toList : List (Fin d)).foldl
      (fun Y j => iterateCoordinateIsonormalField j (m j) Y) X).path = _
  rw [hfold]
  rfl

theorem integrateSheetIsonormalField_feature {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P}
    (m : Fin d → ℕ) (X : ContinuousIsonormalField P T) :
    (integrateSheetIsonormalField m X).feature = integrateSheetFeatureField m X.feature := by
  classical
  have hfold : ∀ l : List (Fin d), ∀ Y : ContinuousIsonormalField P T,
      (l.foldl (fun Z j => iterateCoordinateIsonormalField j (m j) Z) Y).feature =
        l.foldl (fun f j => iterateCoordinateFeature j (m j) f) Y.feature := by
    intro l
    induction l with
    | nil => intro Y; rfl
    | cons j l ih =>
        intro Y
        simp only [List.foldl_cons]
        rw [ih]
        rw [iterateCoordinateIsonormalField_feature]
  change ((Finset.univ.toList : List (Fin d)).foldl
      (fun Y j => iterateCoordinateIsonormalField j (m j) Y) X).feature = _
  rw [hfold]
  rfl

@[simp] theorem integratedFeatureField_zero {d : ℕ} :
    integratedFeatureField (fun _ : Fin d => 0) =
      ⟨featureVector, featureVector_continuous d⟩ := by
  simp [integratedFeatureField, integrateSheetFeatureField, iterateCoordinateFeature]

theorem integratedFeatureField_isGaussian {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ) :
    ∃ T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P,
      IsGaussianProcess
        (fun x ω => T (integratedFeatureField m x) ω) P := by
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Unit) B
  have hTprocess : IsGaussianProcess (fun z : brownianCubeBoxSpan d =>
      fun ω => T z ω) P := by
    refine ⟨fun I => ?_⟩
    obtain ⟨W', hW'⟩ :=
      brownianSheetCube_isonormal_of_covariance_isometry (ι := ↥I) B T hT
    have hLaw := W'.jointlyGaussian (fun z : ↥I => z.1)
    have hae : (fun ω (z : ↥I) => W'.eval z.1 ω) =ᵐ[P]
        (fun ω z => T z.1 ω) := by
      have hall := ae_all_iff.mpr (fun z : ↥I => hW' z.1)
      filter_upwards [hall] with ω hω
      funext z
      exact hω z
    exact hLaw.congr hae
  exact ⟨T, hTprocess.comp_right (fun x => integratedFeatureField m x)⟩

/-- The actual iterated Riemann--Liouville image of a Brownian sheet is a
Gaussian process for every coordinatewise order `m`. The proof iterates the
samplewise/L² identification, preserving one common isonormal map throughout. -/
theorem integratedSheetPath_isGaussianProcess {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ) :
    IsGaussianProcess
      (fun x ω =>
        BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x) P := by
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Unit) B
  have hT_eval (z : BrownianCubeAnchor d) :
      brownianEvalToLp B z = T (featureVector z) := by
    rw [brownianEvalToLp_eq, ← hT z]
    apply congrArg T
    apply Subtype.ext
    rfl
  let X₀ : ContinuousIsonormalField P T := {
    path := B.path
    feature := ⟨featureVector, featureVector_continuous d⟩
    measurable_path := B.measurable_path
    eval_ae := by
      intro z
      have hmem : MemLp (B.eval z) 2 P := (B.eval_gaussian z).memLp_two
      have hrep : (fun ω => brownianEvalToLp B z ω) =ᵐ[P] B.eval z := by
        simpa [brownianEvalToLp] using hmem.coeFn_toLp
      have hclass : (fun ω => brownianEvalToLp B z ω) =ᵐ[P]
          fun ω => T (featureVector z) ω := by
        filter_upwards with ω
        exact congrArg (fun f : Lp ℝ 2 P => f ω) (hT_eval z)
      exact hrep.symm.trans hclass
    feature_norm_le_one := featureVector_norm_le_one
  }
  let X := integrateSheetIsonormalField m X₀
  have hTprocess : IsGaussianProcess
      (fun z : brownianCubeBoxSpan d => fun ω => T z ω) P := by
    refine ⟨fun I => ?_⟩
    obtain ⟨W', hW'⟩ :=
      brownianSheetCube_isonormal_of_covariance_isometry (ι := ↥I) B T hT
    have hLaw := W'.jointlyGaussian (fun z : ↥I => z.1)
    have hae : (fun ω (z : ↥I) => W'.eval z.1 ω) =ᵐ[P]
        (fun ω z => T z.1 ω) := by
      have hall := ae_all_iff.mpr (fun z : ↥I => hW' z.1)
      filter_upwards [hall] with ω hω
      funext z
      exact hω z
    exact hLaw.congr hae
  have hfeatures := hTprocess.comp_right (fun x => X.feature x)
  have hpathAE : ∀ x : BrownianCubeAnchor d,
      (fun ω => T (X.feature x) ω) =ᵐ[P]
        (fun ω => BrownianSharp.AlignmentGaussianRates.integrateSheetPath m
          (B.path ω) x) := by
    intro x
    have h := X.eval_ae x
    rw [integrateSheetIsonormalField_path] at h
    simpa [X, X₀] using h.symm
  exact hfeatures.congr hpathAE

/-- The actual arbitrary-order integrated sheet has the same evaluation
classes as the deterministic integrated features under one common isonormal
map. -/
theorem integratedSheetPath_ae_eq_isonormal {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ) :
    ∃ T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∃ W : IsonormalGaussianFamily (brownianCubeBoxSpan d) Ω Unit P,
        (∀ z, W.eval z =ᵐ[P] fun ω => T z ω) ∧
        ∀ x, (fun ω =>
          BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x) =ᵐ[P]
          fun ω => T (integratedFeatureField m x) ω := by
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Unit) B
  have hT_eval (z : BrownianCubeAnchor d) :
      brownianEvalToLp B z = T (featureVector z) := by
    rw [brownianEvalToLp_eq, ← hT z]
    apply congrArg T
    apply Subtype.ext
    rfl
  let X₀ : ContinuousIsonormalField P T := {
    path := B.path
    feature := ⟨featureVector, featureVector_continuous d⟩
    measurable_path := B.measurable_path
    eval_ae := by
      intro z
      have hmem : MemLp (B.eval z) 2 P := (B.eval_gaussian z).memLp_two
      have hrep : (fun ω => brownianEvalToLp B z ω) =ᵐ[P] B.eval z := by
        simpa [brownianEvalToLp] using hmem.coeFn_toLp
      have hclass : (fun ω => brownianEvalToLp B z ω) =ᵐ[P]
          fun ω => T (featureVector z) ω := by
        filter_upwards with ω
        exact congrArg (fun f : Lp ℝ 2 P => f ω) (hT_eval z)
      exact hrep.symm.trans hclass
    feature_norm_le_one := featureVector_norm_le_one
  }
  let X := integrateSheetIsonormalField m X₀
  refine ⟨T, W, hW, ?_⟩
  intro x
  have h := X.eval_ae x
  rw [integrateSheetIsonormalField_path] at h
  rw [integrateSheetIsonormalField_feature] at h
  simpa [X, X₀, integratedFeatureField, integrateSheetFeatureField] using h

/-- Covariance of actual arbitrary-order integrated path evaluations is the
inner product of their integrated deterministic features. -/
theorem integratedSheetPath_covariance {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ)
    (x y : BrownianCubeAnchor d) :
    cov[fun ω => BrownianSharp.AlignmentGaussianRates.integrateSheetPath
          m (B.path ω) x,
        fun ω => BrownianSharp.AlignmentGaussianRates.integrateSheetPath
          m (B.path ω) y; P] =
      ⟪integratedFeatureField m x, integratedFeatureField m y⟫ := by
  obtain ⟨T, W, hW, hAE⟩ := integratedSheetPath_ae_eq_isonormal B m
  let fx := integratedFeatureField m x
  let fy := integratedFeatureField m y
  have hpathX := hAE x
  have hpathY := hAE y
  have hfx : MemLp (fun ω => T fx ω) 2 P := Lp.memLp (T fx)
  have hfy : MemLp (fun ω => T fy ω) 2 P := Lp.memLp (T fy)
  have hX : MemLp (fun ω =>
      BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x) 2 P :=
    hfx.ae_eq hpathX.symm
  have hY : MemLp (fun ω =>
      BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) y) 2 P :=
    hfy.ae_eq hpathY.symm
  have hWfxLaw : HasGaussianLaw (W.eval fx) P := by
    have h := (W.jointlyGaussian (fun _ : Unit => fx)).eval ()
    simpa using h
  have hWfyLaw : HasGaussianLaw (W.eval fy) P := by
    have h := (W.jointlyGaussian (fun _ : Unit => fy)).eval ()
    simpa using h
  have hWfxMem : MemLp (W.eval fx) 2 P := hWfxLaw.memLp_two
  have hWfyMem : MemLp (W.eval fy) 2 P := hWfyLaw.memLp_two
  have hmeanX : ∫ ω, BrownianSharp.AlignmentGaussianRates.integrateSheetPath
      m (B.path ω) x ∂P = 0 := by
    calc
      _ = ∫ ω, T fx ω ∂P := integral_congr_ae hpathX
      _ = ∫ ω, W.eval fx ω ∂P := integral_congr_ae (hW fx).symm
      _ = 0 := W.mean_zero fx
  have hmeanY : ∫ ω, BrownianSharp.AlignmentGaussianRates.integrateSheetPath
      m (B.path ω) y ∂P = 0 := by
    calc
      _ = ∫ ω, T fy ω ∂P := integral_congr_ae hpathY
      _ = ∫ ω, W.eval fy ω ∂P := integral_congr_ae (hW fy).symm
      _ = 0 := W.mean_zero fy
  have hTmeanX : ∫ ω, T fx ω ∂P = 0 := by
    calc
      _ = ∫ ω, W.eval fx ω ∂P := integral_congr_ae (hW fx).symm
      _ = 0 := W.mean_zero fx
  have hTmeanY : ∫ ω, T fy ω ∂P = 0 := by
    calc
      _ = ∫ ω, W.eval fy ω ∂P := integral_congr_ae (hW fy).symm
      _ = 0 := W.mean_zero fy
  have hprod :
      (fun ω => BrownianSharp.AlignmentGaussianRates.integrateSheetPath
          m (B.path ω) x *
        BrownianSharp.AlignmentGaussianRates.integrateSheetPath
          m (B.path ω) y) =ᵐ[P]
      (fun ω => T fx ω * T fy ω) := hpathX.mul hpathY
  have hTprod : (fun ω => T fx ω * T fy ω) =ᵐ[P]
      (fun ω => W.eval fx ω * W.eval fy ω) := (hW fx).symm.mul (hW fy).symm
  have hWmeanX : ∫ ω, W.eval fx ω ∂P = 0 := W.mean_zero fx
  have hWmeanY : ∫ ω, W.eval fy ω ∂P = 0 := W.mean_zero fy
  have hcovT : cov[fun ω => T fx ω, fun ω => T fy ω; P] =
      cov[fun ω => W.eval fx ω, fun ω => W.eval fy ω; P] := by
    calc
      cov[fun ω => T fx ω, fun ω => T fy ω; P] =
          ∫ ω, T fx ω * T fy ω ∂P := by
            rw [covariance_eq_sub hfx hfy]
            simp [hTmeanX, hTmeanY]
      _ = ∫ ω, W.eval fx ω * W.eval fy ω ∂P := integral_congr_ae hTprod
      _ = cov[fun ω => W.eval fx ω, fun ω => W.eval fy ω; P] := by
            rw [covariance_eq_sub hWfxMem hWfyMem]
            simp [hWmeanX, hWmeanY]
  calc
    cov[fun ω => BrownianSharp.AlignmentGaussianRates.integrateSheetPath
          m (B.path ω) x,
        fun ω => BrownianSharp.AlignmentGaussianRates.integrateSheetPath
          m (B.path ω) y; P] =
        ∫ ω, BrownianSharp.AlignmentGaussianRates.integrateSheetPath
          m (B.path ω) x *
          BrownianSharp.AlignmentGaussianRates.integrateSheetPath
            m (B.path ω) y ∂P := by
          rw [covariance_eq_sub hX hY]
          simp [hmeanX, hmeanY]
    _ = ∫ ω, T fx ω * T fy ω ∂P := integral_congr_ae hprod
    _ = cov[fun ω => T fx ω, fun ω => T fy ω; P] := by
          rw [covariance_eq_sub hfx hfy]
          simp [hTmeanX, hTmeanY]
    _ = cov[fun ω => W.eval fx ω, fun ω => W.eval fy ω; P] := hcovT
    _ = ⟪fx, fy⟫ := W.covariance_eq_inner fx fy

theorem integratedSheetFeature_eq_isonormal_integral {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P)
    (i : Fin d) (x : BrownianCubeAnchor d) :
    ∃ T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∃ W : IsonormalGaussianFamily (brownianCubeBoxSpan d) Ω Unit P,
        (∀ z, W.eval z =ᵐ[P] fun ω => T z ω) ∧
        T (integratedSheetFeature i x) =
          ∫ v in Set.Icc (0 : ℝ) 1,
            x.val i • T (scaledSheetFeature i x v) ∂volume := by
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Unit) B
  refine ⟨T, W, hW, ?_⟩
  have hc : Continuous (fun v : ℝ => x.val i • scaledSheetFeature i x v) :=
    (continuous_const : Continuous (fun _ : ℝ => x.val i)).smul
      (continuous_scaledSheetFeature i x)
  have hint : IntegrableOn (fun v : ℝ => x.val i • scaledSheetFeature i x v)
      (Set.Icc (0 : ℝ) 1) volume :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  change T (∫ v in Set.Icc (0 : ℝ) 1,
      x.val i • scaledSheetFeature i x v ∂volume) = _
  rw [← T.integral_comp_comm (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
    (fun v => x.val i • scaledSheetFeature i x v)]
  simp only [T.map_smul]

theorem integratedFeature_l2_integral_eq {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (i : Fin d)
    (x : BrownianCubeAnchor d) :
    ∃ T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P,
      T (integratedSheetFeature i x) =
        ∫ v in Set.Icc (0 : ℝ) 1,
          x.val i • brownianEvalToLp B
            (brownianCubeClamp d (Function.update x.val i (x.val i * v))) ∂volume := by
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Unit) B
  refine ⟨T, ?_⟩
  have hc : Continuous (fun v : ℝ => x.val i • scaledSheetFeature i x v) :=
    (continuous_const : Continuous (fun _ : ℝ => x.val i)).smul
      (continuous_scaledSheetFeature i x)
  have hint : IntegrableOn (fun v : ℝ => x.val i • scaledSheetFeature i x v)
      (Set.Icc (0 : ℝ) 1) volume :=
    hc.continuousOn.integrableOn_compact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  change T (∫ v in Set.Icc (0 : ℝ) 1,
      x.val i • scaledSheetFeature i x v ∂volume) = _
  rw [← T.integral_comp_comm (μ := volume.restrict (Set.Icc (0 : ℝ) 1))
    (fun v => x.val i • scaledSheetFeature i x v)]
  simp only [T.map_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  change x.val i • T ⟨brownianSheetBoxIndicatorLp
      (brownianCubeClamp d (Function.update x.val i (x.val i * v))).val,
      brownianCubeBoxIndicator_mem (brownianCubeClamp d
        (Function.update x.val i (x.val i * v)))⟩ = _
  rw [hT (brownianCubeClamp d (Function.update x.val i (x.val i * v)))]
  simp [brownianEvalToLp]

/-- A positive-order integrated feature gives a centered Gaussian random
variable in `L²(P)`.  This is derived from the Brownian sheet's isonormal
realization and linearity of Bochner integration. -/
theorem integratedFeature_hasGaussianLaw {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (i : Fin d)
    (x : BrownianCubeAnchor d) :
    ∃ T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∃ W : IsonormalGaussianFamily (brownianCubeBoxSpan d) Ω Unit P,
        (∀ z, W.eval z =ᵐ[P] fun ω => T z ω) ∧
        HasGaussianLaw
          (fun ω => T (integratedSheetFeature i x) ω) P := by
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Unit) B
  have hcoord : HasGaussianLaw (fun ω => W.eval (integratedSheetFeature i x) ω) P := by
    have h := (W.jointlyGaussian (fun _ : Unit => integratedSheetFeature i x)).eval ()
    simpa using h
  exact ⟨T, W, hW, hcoord.congr (hW (integratedSheetFeature i x))⟩

/-- Covariance of the positive-order integrated Gaussian coordinates is the
inner product of their integrated deterministic features.  This is a useful
kernel representation even before expanding the inner product into scalar
iterated integrals. -/
theorem integratedFeature_covariance {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (i : Fin d)
    (x y : BrownianCubeAnchor d) :
    ∃ T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∃ W : IsonormalGaussianFamily (brownianCubeBoxSpan d) Ω Unit P,
        (∀ z, W.eval z =ᵐ[P] fun ω => T z ω) ∧
        cov[fun ω => T (integratedSheetFeature i x) ω,
            fun ω => T (integratedSheetFeature i y) ω; P] =
          ⟪integratedSheetFeature i x, integratedSheetFeature i y⟫ := by
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Unit) B
  let fx := integratedSheetFeature i x
  let fy := integratedSheetFeature i y
  have hfxMean : ∫ ω, T fx ω ∂P = 0 := by
    calc
      ∫ ω, T fx ω ∂P = ∫ ω, W.eval fx ω ∂P :=
        integral_congr_ae (hW fx).symm
      _ = 0 := W.mean_zero fx
  have hfyMean : ∫ ω, T fy ω ∂P = 0 := by
    calc
      ∫ ω, T fy ω ∂P = ∫ ω, W.eval fy ω ∂P :=
        integral_congr_ae (hW fy).symm
      _ = 0 := W.mean_zero fy
  have hfxMem : MemLp (fun ω => T fx ω) 2 P := Lp.memLp (T fx)
  have hfyMem : MemLp (fun ω => T fy ω) 2 P := Lp.memLp (T fy)
  have hWfxLaw : HasGaussianLaw (W.eval fx) P := by
    have h := (W.jointlyGaussian (fun _ : Unit => fx)).eval ()
    simpa using h
  have hWfyLaw : HasGaussianLaw (W.eval fy) P := by
    have h := (W.jointlyGaussian (fun _ : Unit => fy)).eval ()
    simpa using h
  have hWfxMem : MemLp (W.eval fx) 2 P := hWfxLaw.memLp_two
  have hWfyMem : MemLp (W.eval fy) 2 P := hWfyLaw.memLp_two
  have hprod : (fun ω => T fx ω * T fy ω) =ᵐ[P]
      (fun ω => W.eval fx ω * W.eval fy ω) :=
    (hW fx).symm.mul (hW fy).symm
  have hWfxMean : ∫ ω, W.eval fx ω ∂P = 0 := W.mean_zero fx
  have hWfyMean : ∫ ω, W.eval fy ω ∂P = 0 := W.mean_zero fy
  refine ⟨T, W, hW, ?_⟩
  calc
    cov[fun ω => T fx ω, fun ω => T fy ω; P] =
        ∫ ω, T fx ω * T fy ω ∂P := by
          rw [covariance_eq_sub hfxMem hfyMem]
          simp [hfxMean, hfyMean]
    _ = ∫ ω, W.eval fx ω * W.eval fy ω ∂P := integral_congr_ae hprod
    _ = cov[fun ω => W.eval fx ω, fun ω => W.eval fy ω; P] := by
      rw [covariance_eq_sub hWfxMem hWfyMem]
      simp [hWfxMean, hWfyMean]
    _ = ⟪fx, fy⟫ := W.covariance_eq_inner fx fy

/-- The integrated covariance kernel expands as the iterated integral of the
original Brownian feature inner products. This is the feature-space analogue
of the usual covariance Fubini formula for an integrated sheet. -/
theorem integratedSheetFeature_inner_eq_iterated {d : ℕ}
    (i j : Fin d) (x y : BrownianCubeAnchor d) :
    ⟪integratedSheetFeature i x, integratedSheetFeature j y⟫ =
      ∫ v in Set.Icc (0 : ℝ) 1, ∫ w in Set.Icc (0 : ℝ) 1,
        ⟪x.val i • scaledSheetFeature i x v,
          y.val j • scaledSheetFeature j y w⟫ ∂volume ∂volume := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)
  let F : ℝ → brownianCubeBoxSpan d := fun v =>
    x.val i • scaledSheetFeature i x v
  let G : ℝ → brownianCubeBoxSpan d := fun w =>
    y.val j • scaledSheetFeature j y w
  have hF : Integrable F μ := by
    have hc : Continuous F := by
      dsimp [F]
      exact (continuous_const : Continuous (fun _ : ℝ => x.val i)).smul
        (continuous_scaledSheetFeature i x)
    exact hc.continuousOn.integrableOn_compact
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  have hG : Integrable G μ := by
    have hc : Continuous G := by
      dsimp [G]
      exact (continuous_const : Continuous (fun _ : ℝ => y.val j)).smul
        (continuous_scaledSheetFeature j y)
    exact hc.continuousOn.integrableOn_compact
      (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  change ⟪∫ v, F v ∂μ, ∫ w, G w ∂μ⟫ = _
  calc
    ⟪∫ v, F v ∂μ, ∫ w, G w ∂μ⟫ =
        ∫ v, ⟪F v, ∫ w, G w ∂μ⟫ ∂μ := by
          calc
            _ = ⟪∫ w, G w ∂μ, ∫ v, F v ∂μ⟫ := real_inner_comm _ _
            _ = ∫ v, ⟪∫ w, G w ∂μ, F v⟫ ∂μ :=
              (integral_inner hF (∫ w, G w ∂μ)).symm
            _ = ∫ v, ⟪F v, ∫ w, G w ∂μ⟫ ∂μ := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall (fun v => real_inner_comm _ _)
    _ = ∫ v, ∫ w, ⟪F v, G w⟫ ∂μ ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall
            (fun v => (integral_inner hG (F v)).symm)

theorem featureVector_inner {d : ℕ} (x y : BrownianCubeAnchor d) :
    ⟪featureVector x, featureVector y⟫ =
      ∏ k, min (x.val k) (y.val k) := by
  change ⟪brownianSheetBoxIndicatorLp x.val,
    brownianSheetBoxIndicatorLp y.val⟫ = _
  exact brownianSheetBoxIndicatorLp_inner x.val y.val
    (fun k => (x.property k).1) (fun k => (y.property k).1)

theorem scaledSheetFeature_inner {d : ℕ} (i j : Fin d)
    (x y : BrownianCubeAnchor d) (v w : ℝ) :
    ⟪x.val i • scaledSheetFeature i x v,
      y.val j • scaledSheetFeature j y w⟫ =
      x.val i * y.val j *
        ∏ k, min
          ((brownianCubeClamp d (Function.update x.val i (x.val i * v))).val k)
          ((brownianCubeClamp d (Function.update y.val j (y.val j * w))).val k) := by
  let a := brownianCubeClamp d (Function.update x.val i (x.val i * v))
  let b := brownianCubeClamp d (Function.update y.val j (y.val j * w))
  calc
    ⟪x.val i • scaledSheetFeature i x v,
        y.val j • scaledSheetFeature j y w⟫ =
        x.val i * (y.val j *
          ⟪scaledSheetFeature i x v, scaledSheetFeature j y w⟫) := by
            calc
              _ = x.val i * ⟪scaledSheetFeature i x v,
                  y.val j • scaledSheetFeature j y w⟫ := by
                    exact real_inner_smul_left
                      (x := scaledSheetFeature i x v)
                      (y := y.val j • scaledSheetFeature j y w)
                      (r := x.val i)
              _ = x.val i * (y.val j *
                  ⟪scaledSheetFeature i x v, scaledSheetFeature j y w⟫) := by
                    rw [real_inner_smul_right
                      (x := scaledSheetFeature i x v)
                      (y := scaledSheetFeature j y w)
                      (r := y.val j)]
    _ = x.val i * y.val j *
        ⟪featureVector a, featureVector b⟫ := by
          simp [a, b, scaledSheetFeature]
          ring
    _ = _ := by
          rw [featureVector_inner]

theorem integratedSheetFeature_inner_eq_scalarKernel {d : ℕ}
    (i j : Fin d) (x y : BrownianCubeAnchor d) :
    ⟪integratedSheetFeature i x, integratedSheetFeature j y⟫ =
      ∫ v in Set.Icc (0 : ℝ) 1, ∫ w in Set.Icc (0 : ℝ) 1,
        x.val i * y.val j *
          ∏ k, min
            ((brownianCubeClamp d (Function.update x.val i (x.val i * v))).val k)
            ((brownianCubeClamp d (Function.update y.val j (y.val j * w))).val k)
          ∂volume ∂volume := by
  rw [integratedSheetFeature_inner_eq_iterated]
  apply integral_congr_ae
  filter_upwards with v
  apply integral_congr_ae
  filter_upwards with w
  exact scaledSheetFeature_inner i j x y v w

/-- The actual continuous sample path obtained by applying the iterated
Riemann--Liouville path operator to a Brownian sheet sample. -/
noncomputable def integratedSheetPath {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ) (ω : Ω) :
    C(BrownianCubeAnchor d, ℝ) :=
  BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω)

/-- The integrated continuous path is a measurable random element. This uses
the actual path operator, not an assumed integrated-process realization. -/
theorem measurable_integratedSheetPath {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ) :
    Measurable (integratedSheetPath B m) := by
  exact (BrownianSharp.AlignmentGaussianRates.integrateSheetPath_continuous m).measurable.comp
    B.measurable_path

/-- Evaluation of the actual integrated sample path is measurable. -/
theorem measurable_integratedSheetPath_eval {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ)
    (x : BrownianCubeAnchor d) :
    Measurable (fun ω => integratedSheetPath B m ω x) := by
  exact (ContinuousMap.measurable_eval x).comp
    (measurable_integratedSheetPath B m)

/-- Any finite-index collection of positive-order integrated sheet
coordinates is jointly Gaussian. The coordinates are built from deterministic
feature integrals, so Gaussianity follows from the isonormal realization and
does not assume an integrated process. -/
theorem integratedFeatureProcess_isGaussian {d : ℕ} {Ω ι : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [Fintype ι] (B : BrownianSheetOnCube d Ω P)
    (axis : ι → Fin d) (x : ι → BrownianCubeAnchor d) :
    ∃ T : brownianCubeBoxSpan d →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∃ W : IsonormalGaussianFamily (brownianCubeBoxSpan d) Ω Unit P,
        (∀ z, W.eval z =ᵐ[P] fun ω => T z ω) ∧
        IsGaussianProcess
          (fun k ω => T (integratedSheetFeature (axis k) (x k)) ω) P := by
  obtain ⟨T, W, hT, hW⟩ :=
    brownianSheetCube_exists_isonormal (ι := Unit) B
  have hTprocess : IsGaussianProcess (fun z : brownianCubeBoxSpan d =>
      fun ω => T z ω) P := by
    refine ⟨fun I => ?_⟩
    obtain ⟨W', hW'⟩ :=
      brownianSheetCube_isonormal_of_covariance_isometry (ι := I) B T hT
    let f : I → brownianCubeBoxSpan d := fun z => z.1
    have hLaw := W'.jointlyGaussian f
    have hae : (fun ω z => W'.eval (f z) ω) =ᵐ[P]
        (fun ω z => T (f z) ω) := by
      have hall := ae_all_iff.mpr (fun z => hW' (f z))
      filter_upwards [hall] with ω hω
      funext z
      exact hω z
    exact hLaw.congr hae
  have hIntegrated := hTprocess.comp_right
    (fun k => integratedSheetFeature (axis k) (x k))
  exact ⟨T, W, hW, hIntegrated⟩

end
end BrownianSharp.AlignmentGaussianBochner
