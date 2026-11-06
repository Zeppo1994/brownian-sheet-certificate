import BrownianSharp.AlignmentCompactFeatureBall
import BrownianSharp.CovarianceSpanIsometry
import BrownianSharp.ContinuousMapFiniteLaw
import BrownianSharp.AlignmentPaperMatern
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-! Generic covariance-feature bridges for continuous Gaussian fields.

The first result realizes the closed linear span of any continuous Hilbert
feature family isometrically inside the `L²` space of any centered process
with the same covariance Gram kernel. The second is the path-law endpoint:
once finite evaluation laws agree, the laws on continuous paths agree. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperGaussianFeatureBridge

open BrownianSharp.AlignmentCompactFeatureBall

/-- The evaluation random variable, viewed as an element of `L²(P)`. -/
def evaluationL2 {α Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (X : α → Ω → ℝ) (hX : ∀ x, MemLp (X x) 2 P) (x : α) : Lp ℝ 2 P :=
  (hX x).toLp (X x)

/-- A centered process whose covariance is the Gram kernel of a continuous
Hilbert feature family induces an isometry from the feature span into its
evaluation span in `L²(P)`. This is the reusable Gaussian-feature/CM bridge;
it does not assume any entropy or small-deviation estimate. -/
theorem exists_feature_covariance_isometry
    {α Ω H : Type*} [TopologicalSpace α] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (K : C(α, H)) (X : α → Ω → ℝ)
    (hX : ∀ x, MemLp (X x) 2 P)
    (hmean : ∀ x, ∫ ω, X x ω ∂P = 0)
    (hcov : ∀ x y, cov[X x, X y; P] = inner ℝ (K x) (K y)) :
    ∃ T : (Submodule.span ℝ (Set.range fun x : α => K x)).topologicalClosure
          →ₗᵢ[ℝ] Lp ℝ 2 P,
      ∀ x, T ⟨K x,
        (Submodule.span ℝ (Set.range fun x : α => K x)).le_topologicalClosure
          (Submodule.subset_span (Set.mem_range_self x))⟩ =
        evaluationL2 X hX x := by
  let v : α → H := fun x => K x
  let w : α → Lp ℝ 2 P := fun x => evaluationL2 X hX x
  have hGram (x y : α) : inner ℝ (w x) (w y) = inner ℝ (v x) (v y) := by
    rw [L2.inner_def]
    calc
      (∫ ω, inner ℝ (w x ω) (w y ω) ∂P) =
          ∫ ω, X x ω * X y ω ∂P := by
        apply integral_congr_ae
        filter_upwards [(hX x).coeFn_toLp, (hX y).coeFn_toLp] with ω hx hy
        simp [w, evaluationL2, hx, hy, mul_comm]
      _ = cov[X x, X y; P] := by
        rw [covariance_eq_sub (hX x) (hX y), hmean x, hmean y]
        simp
      _ = inner ℝ (v x) (v y) := hcov x y
  obtain ⟨T, hT⟩ := HaarQuarter.exists_closedSpan_isometry_of_gram v w hGram
  refine ⟨T, ?_⟩
  intro x
  simpa [v, w, evaluationL2] using hT x

/-- The covariance isometry is onto the closed span of the evaluation random
variables. Thus the intrinsic source for the Gaussian covariance shift map is
exactly isometric to the closed feature span, rather than merely embedded in
it. -/
theorem exists_feature_covariance_isometry_onto
    {α Ω H : Type*} [TopologicalSpace α] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (K : C(α, H)) (X : α → Ω → ℝ)
    (hX : ∀ x, MemLp (X x) 2 P)
    (hmean : ∀ x, ∫ ω, X x ω ∂P = 0)
    (hcov : ∀ x y, cov[X x, X y; P] = inner ℝ (K x) (K y)) :
    ∃ T : (Submodule.span ℝ (Set.range fun x : α => K x)).topologicalClosure
          →ₗᵢ[ℝ] Lp ℝ 2 P,
      (∀ x, T ⟨K x,
        (Submodule.span ℝ (Set.range fun x : α => K x)).le_topologicalClosure
          (Submodule.subset_span (Set.mem_range_self x))⟩ =
        evaluationL2 X hX x) ∧
      (∀ s, T s ∈ (Submodule.span ℝ (Set.range fun x : α => evaluationL2 X hX x)).topologicalClosure) ∧
      (∀ z : (Submodule.span ℝ (Set.range fun x : α => evaluationL2 X hX x)).topologicalClosure,
        ∃ s, T s = z) := by
  classical
  let V : Submodule ℝ H := Submodule.span ℝ (Set.range fun x : α => K x)
  let S := V.topologicalClosure
  let w : α → Lp ℝ 2 P := fun x => evaluationL2 X hX x
  let W : Submodule ℝ (Lp ℝ 2 P) := Submodule.span ℝ (Set.range w)
  let U := W.topologicalClosure
  obtain ⟨T, hT⟩ := exists_feature_covariance_isometry K X hX hmean hcov
  have himage (s : S) : T s ∈ U :=
    HaarQuarter.closedSpan_isometry_image_mem (fun x : α => K x) w T hT s
  have hclosed : IsClosed (Set.range (T : S → Lp ℝ 2 P)) :=
    T.isometry.isClosedEmbedding.isClosed_range
  have hWle : W ≤ LinearMap.range T.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro z ⟨x, rfl⟩
    refine ⟨⟨K x, V.le_topologicalClosure
      (Submodule.subset_span (Set.mem_range_self x))⟩, ?_⟩
    exact hT x
  have hUle : U ≤ LinearMap.range T.toLinearMap :=
    Submodule.topologicalClosure_minimal W hWle hclosed
  refine ⟨T, hT, himage, ?_⟩
  intro z
  obtain ⟨s, hs⟩ := hUle z.property
  exact ⟨s, hs⟩

/-- Intrinsic Gaussian Cameron--Martin unit ball: the image of the unit ball
in the closed `L²(P)` span of evaluations under the covariance shift map
`z ↦ (x ↦ ⟪z, X(x)⟫₂)`. -/
def intrinsicGaussianCMUnitBall
    {α Ω : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : α → Ω → ℝ) (hX : ∀ x, MemLp (X x) 2 P) : Set C(α, ℝ) :=
  {f | ∃ z : Lp ℝ 2 P,
    z ∈ (Submodule.span ℝ (Set.range fun x => evaluationL2 X hX x)).topologicalClosure ∧
    ‖z‖ ≤ 1 ∧ ∀ x, f x = inner ℝ z (evaluationL2 X hX x)}

/-- For a covariance feature representation, the intrinsic Cameron--Martin
unit ball defined from the actual evaluation variables is exactly the Hilbert
feature unit ball. The closed evaluation span and feature span are identified
by the onto isometry above. -/
theorem intrinsicGaussianCMUnitBall_eq_featureBall
    {α Ω H : Type*} [MetricSpace α] [CompactSpace α] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (K : C(α, H)) (X : α → Ω → ℝ)
    (hX : ∀ x, MemLp (X x) 2 P)
    (hmean : ∀ x, ∫ ω, X x ω ∂P = 0)
    (hcov : ∀ x y, cov[X x, X y; P] = inner ℝ (K x) (K y)) :
    intrinsicGaussianCMUnitBall X hX = featureBall K := by
  classical
  let V : Submodule ℝ H := Submodule.span ℝ (Set.range fun x => K x)
  let S := V.topologicalClosure
  let w : α → Lp ℝ 2 P := fun x => evaluationL2 X hX x
  let W : Submodule ℝ (Lp ℝ 2 P) := Submodule.span ℝ (Set.range w)
  let U := W.topologicalClosure
  obtain ⟨T, hT, himage, honto⟩ :=
    exists_feature_covariance_isometry_onto K X hX hmean hcov
  ext f
  constructor
  · rintro ⟨z, hz, hznorm, hf⟩
    obtain ⟨s, hs⟩ := honto ⟨z, hz⟩
    refine ⟨s, ?_, ?_⟩
    · calc
        ‖s‖ = ‖T s‖ := (T.norm_map s).symm
        _ = ‖z‖ := by rw [hs]
        _ ≤ 1 := hznorm
    · ext x
      let hxK : S := ⟨K x, V.le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self x))⟩
      have hxT : T hxK = evaluationL2 X hX x := by
        simpa [V, S, hxK] using hT x
      calc
        featurePath K (s : H) x = inner ℝ (s : H) (K x) := rfl
        _ = inner ℝ s hxK := by
          change inner ℝ (s : H) (K x) = inner ℝ (s : H) (K x)
          rfl
        _ = inner ℝ (T s) (T hxK) := (T.inner_map_map s hxK).symm
        _ = inner ℝ z (evaluationL2 X hX x) := by
          rw [hs]
          rw [hxT]
        _ = f x := (hf x).symm
  · rintro ⟨g, hg, hgf⟩
    let gS : S := S.orthogonalProjectionOnto g
    let z : Lp ℝ 2 P := T gS
    refine ⟨z, himage gS, ?_, ?_⟩
    · calc
        ‖z‖ = ‖gS‖ := T.norm_map gS
        _ ≤ ‖g‖ := S.norm_orthogonalProjectionOnto_apply_le g
        _ ≤ 1 := hg
    · intro x
      let hxK : S := ⟨K x, V.le_topologicalClosure
        (Submodule.subset_span (Set.mem_range_self x))⟩
      have hxT : T hxK = evaluationL2 X hX x := by
        simpa [V, S, hxK] using hT x
      calc
        f x = featurePath K g x :=
          (congrArg (fun q : C(α, ℝ) => q x) hgf).symm
        _ = inner ℝ g (K x) := rfl
        _ = inner ℝ (gS : H) (K x) := by
          have hp := S.inner_orthogonalProjectionOnto_eq_of_mem_right hxK g
          simpa only [Submodule.coe_inner, gS] using hp.symm
        _ = inner ℝ gS hxK := by
          change inner ℝ (gS : H) (K x) = inner ℝ (gS : H) (K x)
          rfl
        _ = inner ℝ (T gS) (T hxK) := (T.inner_map_map gS hxK).symm
        _ = inner ℝ (T gS) (evaluationL2 X hX x) := by
          rw [hxT]

/-- Actual Cameron--Martin identification for any centered continuous field
with the raw tensor Matérn spectral covariance: its intrinsic covariance
shift unit ball in the closed evaluation-variable span equals the unit ball
of the concrete real spectral feature family. -/
theorem maternRawSpectral_intrinsicCM_ball_eq_featureBall
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h)
    (X : HaarQuarter.BrownianCubeAnchor d → Ω → ℝ)
    (hX : ∀ x, MemLp (X x) 2 P)
    (hmean : ∀ x, ∫ ω, X x ω ∂P = 0)
    (hcov : ∀ x y,
      cov[X x, X y; P] =
        ∏ i, c i * AlignmentMaternSpectralFeature.stationaryCovariance
          (κ i) h (x.val i) (y.val i)) :
    intrinsicGaussianCMUnitBall X hX =
      AlignmentCompactFeatureBall.featureBall
        (AlignmentPaperMatern.maternSheetFeatureWithSpectralAmplitude
          κ c h hκ hc hh) := by
  let K := AlignmentPaperMatern.maternSheetFeatureWithSpectralAmplitude
    κ c h hκ hc hh
  have hgram (x y : HaarQuarter.BrownianCubeAnchor d) :
      cov[X x, X y; P] = inner ℝ (K x) (K y) := by
    rw [AlignmentPaperMatern.maternSheetFeatureWithSpectralAmplitude_gram]
    exact hcov x y
  exact intrinsicGaussianCMUnitBall_eq_featureBall K X hX hmean hgram

/-- The feature-ball definition and the RKHS feature-operator image use the
same Hilbert unit ball. -/
theorem featureBall_eq_featureOperator_image
    {α H : Type*} [MetricSpace α] [CompactSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : C(α, H)) :
    featureBall K = AlignmentFractionalSheetRKHS.featureOperator K ''
      Metric.closedBall (0 : H) 1 := by
  ext f
  constructor
  · rintro ⟨g, hg, hgf⟩
    have hg' : g ∈ Metric.closedBall (0 : H) 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hg
    refine ⟨g, hg', ?_⟩
    ext x
    rw [AlignmentFractionalSheetRKHS.featureOperator_apply, real_inner_comm]
    simpa [featurePath] using
      congrArg (fun q : C(α, ℝ) => q x) hgf
  · rintro ⟨g, hg, hgf⟩
    have hg' : ‖g‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hg
    refine ⟨g, hg', ?_⟩
    ext x
    simpa [featurePath, AlignmentFractionalSheetRKHS.featureOperator_apply,
      real_inner_comm] using
      congrArg (fun q : C(α, ℝ) => q x) hgf

/-- Raw Matérn entropy lower bound transferred to the intrinsic
Cameron--Martin ball of any centered Gaussian realization with the same
covariance kernel. -/
theorem maternRawSpectral_intrinsicCM_entropy_lower {d : ℕ}
    (hd : 2 ≤ d) (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (X : HaarQuarter.BrownianCubeAnchor d → Ω → ℝ)
    (hX : ∀ x, MemLp (X x) 2 P)
    (hmean : ∀ x, ∫ ω, X x ω ∂P = 0)
    (hcov : ∀ x y,
      cov[X x, X y; P] =
        ∏ i, c i * AlignmentMaternSpectralFeature.stationaryCovariance
          (κ i) h (x.val i) (y.val i)) :
    ∃ cE : ℝ, 0 < cE ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal
        (cE * BrownianSharp.logarithmicIndexRate (h + 1/2)
          ((h + 1/2) * (d - 1 : ℕ) + 1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k (intrinsicGaussianCMUnitBall X hX) := by
  obtain ⟨cE, hcE, k₀, hk₀, hbound⟩ :=
    AlignmentPaperMatern.maternSheetRawSpectralFeature_entropy_lower
      hd κ c h hκ hc hh
  refine ⟨cE, hcE, k₀, hk₀, ?_⟩
  intro k hk
  have hball := maternRawSpectral_intrinsicCM_ball_eq_featureBall
    κ c h hκ hc hh X hX hmean hcov
  have himage := featureBall_eq_featureOperator_image
    (AlignmentPaperMatern.maternSheetFeatureWithSpectralAmplitude
      κ c h hκ hc hh)
  simpa [hball, himage] using hbound k hk

/-- Two centered Gaussian coordinate vectors with the same covariance matrix
have the same law, even when they are realized on different probability
spaces. -/
private def finitePiToEuclidean (I : Type*) [Fintype I] :
    (I → ℝ) →L[ℝ] EuclideanSpace ℝ I :=
  (EuclideanSpace.equiv I ℝ).symm.toContinuousLinearMap

/-- Two centered Gaussian coordinate vectors with the same covariance matrix
have the same law, even when they are realized on different probability
spaces. -/
theorem finite_centered_gaussian_law_eq
    {α Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {P : Measure Ω} {Q : Measure Ψ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (I : Finset α) (X : α → Ω → ℝ) (Y : α → Ψ → ℝ)
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y Q)
    (hmeanX : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hmeanY : ∀ i, ∫ ω, Y i ω ∂Q = 0)
    (hcov : ∀ i j, cov[X i, X j; P] = cov[Y i, Y j; Q]) :
    P.map (fun ω => finitePiToEuclidean I (I.restrict (X · ω))) =
      Q.map (fun ω => finitePiToEuclidean I (I.restrict (Y · ω))) := by
  classical
  let μX : Measure (EuclideanSpace ℝ I) :=
    P.map (fun ω => finitePiToEuclidean I (I.restrict (X · ω)))
  let μY : Measure (EuclideanSpace ℝ I) :=
    Q.map (fun ω => finitePiToEuclidean I (I.restrict (Y · ω)))
  have hXpi : HasGaussianLaw (fun ω => fun i : I => X i.1 ω) P := by
    change HasGaussianLaw (fun ω => I.restrict (X · ω)) P
    exact hX.hasGaussianLaw I
  have hYpi : HasGaussianLaw (fun ω => fun i : I => Y i.1 ω) Q := by
    change HasGaussianLaw (fun ω => I.restrict (Y · ω)) Q
    exact hY.hasGaussianLaw I
  have hXlaw := hXpi.map (finitePiToEuclidean I)
  have hYlaw := hYpi.map (finitePiToEuclidean I)
  have hXcoord : ∀ i : I, MemLp (fun ω => X i.1 ω) 2 P :=
    fun i => (hX.hasGaussianLaw_eval i.1).memLp_two
  have hYcoord : ∀ i : I, MemLp (fun ω => Y i.1 ω) 2 Q :=
    fun i => (hY.hasGaussianLaw_eval i.1).memLp_two
  have hμX : IsGaussian μX := hXlaw.isGaussian_map
  have hμY : IsGaussian μY := hYlaw.isGaussian_map
  have hcovBilin : covarianceBilin μX = covarianceBilin μY := by
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun I ℝ).toBasis
      fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply,
      ContinuousLinearMap.toBilinForm_apply]
    change covarianceBilin
        (Measure.map (fun ω => WithLp.toLp 2 (fun i : I => X i.1 ω)) P) _ _ =
      covarianceBilin
        (Measure.map (fun ω => WithLp.toLp 2 (fun i : I => Y i.1 ω)) Q) _ _
    rw [covarianceBilin_apply_pi hXcoord, covarianceBilin_apply_pi hYcoord]
    simp_rw [hcov]
  have hIntXpi : Integrable (fun ω => fun i : I => X i.1 ω) P :=
    integrable_pi_iff.mpr fun i => (hXcoord i).integrable (by norm_num)
  have hIntYpi : Integrable (fun ω => fun i : I => Y i.1 ω) Q :=
    integrable_pi_iff.mpr fun i => (hYcoord i).integrable (by norm_num)
  have hIntEquivX : Integrable (fun ω =>
      (EuclideanSpace.equiv I ℝ) (WithLp.toLp 2 (fun i : I => X i.1 ω))) P := by
    apply integrable_pi_iff.mpr
    intro i
    simpa using (hXcoord i).integrable (by norm_num)
  have hIntEquivY : Integrable (fun ω =>
      (EuclideanSpace.equiv I ℝ) (WithLp.toLp 2 (fun i : I => Y i.1 ω))) Q := by
    apply integrable_pi_iff.mpr
    intro i
    simpa using (hYcoord i).integrable (by norm_num)
  have hmeanμX : ∫ z : EuclideanSpace ℝ I, z ∂μX = 0 := by
    apply (EuclideanSpace.equiv I ℝ).injective
    have hcomp := (EuclideanSpace.equiv I ℝ).toContinuousLinearMap.integral_comp_comm
      (IsGaussian.integrable_id (μ := μX))
    calc
      (EuclideanSpace.equiv I ℝ) (∫ z, z ∂μX) =
          ∫ z, (EuclideanSpace.equiv I ℝ) z ∂μX := hcomp.symm
      _ = ∫ ω, (EuclideanSpace.equiv I ℝ)
          (finitePiToEuclidean I (fun i : I => X i.1 ω)) ∂P :=
        integral_map hXlaw.aemeasurable (by fun_prop)
      _ = 0 := by
        ext i
        let q : (I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
        have hproj := q.integral_comp_comm hIntEquivX
        calc
          (∫ ω, (EuclideanSpace.equiv I ℝ)
              (finitePiToEuclidean I (fun j : I => X j.1 ω)) ∂P) i =
              q (∫ ω, (EuclideanSpace.equiv I ℝ)
                (finitePiToEuclidean I (fun j : I => X j.1 ω)) ∂P) := rfl
          _ = ∫ ω, q ((EuclideanSpace.equiv I ℝ)
                (finitePiToEuclidean I (fun j : I => X j.1 ω))) ∂P := hproj.symm
          _ = ∫ ω, X i.1 ω ∂P := by
            congr 1
          _ = 0 := hmeanX i.1
  have hmeanμY : ∫ z : EuclideanSpace ℝ I, z ∂μY = 0 := by
    apply (EuclideanSpace.equiv I ℝ).injective
    have hcomp := (EuclideanSpace.equiv I ℝ).toContinuousLinearMap.integral_comp_comm
      (IsGaussian.integrable_id (μ := μY))
    calc
      (EuclideanSpace.equiv I ℝ) (∫ z, z ∂μY) =
          ∫ z, (EuclideanSpace.equiv I ℝ) z ∂μY := hcomp.symm
      _ = ∫ ω, (EuclideanSpace.equiv I ℝ)
          (finitePiToEuclidean I (fun i : I => Y i.1 ω)) ∂Q :=
        integral_map hYlaw.aemeasurable (by fun_prop)
      _ = 0 := by
        ext i
        let q : (I → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
        have hproj := q.integral_comp_comm hIntEquivY
        calc
          (∫ ω, (EuclideanSpace.equiv I ℝ)
              (finitePiToEuclidean I (fun j : I => Y j.1 ω)) ∂Q) i =
              q (∫ ω, (EuclideanSpace.equiv I ℝ)
                (finitePiToEuclidean I (fun j : I => Y j.1 ω)) ∂Q) := rfl
          _ = ∫ ω, q ((EuclideanSpace.equiv I ℝ)
                (finitePiToEuclidean I (fun j : I => Y j.1 ω))) ∂Q := hproj.symm
          _ = ∫ ω, Y i.1 ω ∂Q := by
            congr 1
          _ = 0 := hmeanY i.1
  have hmeanEq : μX[id] = μY[id] := by
    simpa using hmeanμX.trans hmeanμY.symm
  have hμeq : μX = μY := IsGaussian.ext (ν := μY) hmeanEq hcovBilin
  exact hμeq

/-- The finite Gaussian law equality, expressed in the ordinary function
space used by continuous-path evaluation maps. -/
theorem finite_centered_gaussian_restrict_law_eq
    {α Ω Ψ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {P : Measure Ω} {Q : Measure Ψ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (I : Finset α) (X : α → Ω → ℝ) (Y : α → Ψ → ℝ)
    (hX : IsGaussianProcess X P) (hY : IsGaussianProcess Y Q)
    (hmeasX : ∀ i, Measurable (X i))
    (hmeasY : ∀ i, Measurable (Y i))
    (hmeanX : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hmeanY : ∀ i, ∫ ω, Y i ω ∂Q = 0)
    (hcov : ∀ i j, cov[X i, X j; P] = cov[Y i, Y j; Q]) :
    P.map (fun ω => I.restrict (X · ω)) =
      Q.map (fun ω => I.restrict (Y · ω)) := by
  have h := finite_centered_gaussian_law_eq I X Y hX hY hmeanX hmeanY hcov
  have h' := congrArg
    (fun μ : Measure (EuclideanSpace ℝ (↑I)) =>
      μ.map (EuclideanSpace.equiv (↑I) ℝ)) h
  have hXlaw := hX.hasGaussianLaw I
  have hYlaw := hY.hasGaussianLaw I
  have hXeuclid := hXlaw.map (finitePiToEuclidean (↑I))
  have hYeuclid := hYlaw.map (finitePiToEuclidean (↑I))
  have hXfinite : Measurable (fun ω => I.restrict (X · ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact hmeasX i.1
  have hYfinite : Measurable (fun ω => I.restrict (Y · ω)) := by
    apply measurable_pi_iff.mpr
    intro i
    exact hmeasY i.1
  have hXcomp : Measurable (fun ω => finitePiToEuclidean (↑I)
      (I.restrict (X · ω))) := (finitePiToEuclidean (↑I)).measurable.comp hXfinite
  have hYcomp : Measurable (fun ω => finitePiToEuclidean (↑I)
      (I.restrict (Y · ω))) := (finitePiToEuclidean (↑I)).measurable.comp hYfinite
  rw [Measure.map_map (by fun_prop) hXcomp,
    Measure.map_map (by fun_prop) hYcomp] at h'
  have hfunX : (fun ω => (EuclideanSpace.equiv (↑I) ℝ)
      (finitePiToEuclidean (↑I) (I.restrict (X · ω)))) =
      (fun ω => I.restrict (X · ω)) := by
    funext ω
    ext i
    rfl
  have hfunY : (fun ω => (EuclideanSpace.equiv (↑I) ℝ)
      (finitePiToEuclidean (↑I) (I.restrict (Y · ω)))) =
      (fun ω => I.restrict (Y · ω)) := by
    funext ω
    ext i
    rfl
  have hfunX' : (EuclideanSpace.equiv (↑I) ℝ) ∘
      (fun ω => finitePiToEuclidean (↑I) (I.restrict (X · ω))) =
      (fun ω => I.restrict (X · ω)) := by
    funext ω
    exact congrFun hfunX ω
  have hfunY' : (EuclideanSpace.equiv (↑I) ℝ) ∘
      (fun ω => finitePiToEuclidean (↑I) (I.restrict (Y · ω))) =
      (fun ω => I.restrict (Y · ω)) := by
    funext ω
    exact congrFun hfunY ω
  rw [hfunX', hfunY'] at h'
  exact h'

/-- The finite-evaluation criterion for continuous-function laws with
different sample spaces and probability measures. -/
theorem continuousMap_map_eq_of_finite_evaluations_cross
    {K Ω Ψ : Type*} [TopologicalSpace K] [SecondCountableTopology K]
    [LocallyCompactSpace K] [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {P : Measure Ω} {Q : Measure Ψ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Ω → C(K, ℝ)) (G : Ψ → C(K, ℝ))
    (hF : Measurable F) (hG : Measurable G)
    (hfinite : ∀ I : Finset K,
      P.map (fun ω => I.restrict (fun x => F ω x)) =
        Q.map (fun ω => I.restrict (fun x => G ω x))) :
    P.map F = Q.map G := by
  let R := P.prod Q
  let F' : Ω × Ψ → C(K, ℝ) := fun z => F z.1
  let G' : Ω × Ψ → C(K, ℝ) := fun z => G z.2
  have hfinite' : ∀ I : Finset K,
      R.map (fun z => I.restrict (fun x => F' z x)) =
        R.map (fun z => I.restrict (fun x => G' z x)) := by
    intro I
    have hFX : Measurable (fun ω => I.restrict (fun x => F ω x)) := by
      apply measurable_pi_iff.mpr
      intro x
      exact (ContinuousMap.measurable_eval x.1).comp hF
    have hGY : Measurable (fun ω => I.restrict (fun x => G ω x)) := by
      apply measurable_pi_iff.mpr
      intro x
      exact (ContinuousMap.measurable_eval x.1).comp hG
    calc
      R.map (fun z => I.restrict (fun x => F' z x)) =
          P.map (fun ω => I.restrict (fun x => F ω x)) := by
            change R.map ((fun ω => I.restrict (fun x => F ω x)) ∘ Prod.fst) = _
            rw [← Measure.map_map hFX measurable_fst]
            simp [R]
      _ = Q.map (fun ω => I.restrict (fun x => G ω x)) := hfinite I
      _ = R.map (fun z => I.restrict (fun x => G' z x)) := by
            symm
            change R.map ((fun ω => I.restrict (fun x => G ω x)) ∘ Prod.snd) = _
            rw [← Measure.map_map hGY measurable_snd]
            simp [R]
  have hpath := HaarQuarter.continuousMap_map_eq_of_finite_evaluations
    R F' G' (hF.comp measurable_fst) (hG.comp measurable_snd) hfinite'
  calc
    P.map F = R.map F' := by
      symm
      change R.map (F ∘ Prod.fst) = P.map F
      rw [← Measure.map_map hF measurable_fst]
      simp [R]
    _ = R.map G' := hpath
    _ = Q.map G := by
      change R.map (G ∘ Prod.snd) = Q.map G
      rw [← Measure.map_map hG measurable_snd]
      simp [R]

/-- Centered Gaussian continuous fields on possibly different probability
spaces have the same law on continuous paths whenever their covariance
kernels agree. The proof derives every finite law from Gaussianity and the
covariance matrix, then applies the continuous-path determination theorem. -/
theorem continuous_path_law_eq_of_same_covariance
    {α Ω Ψ : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [LocallyCompactSpace α] [MeasurableSpace Ω] [MeasurableSpace Ψ]
    {P : Measure Ω} {Q : Measure Ψ}
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Ω → C(α, ℝ)) (G : Ψ → C(α, ℝ))
    (hF : Measurable F) (hG : Measurable G)
    (hXF : IsGaussianProcess (fun x ω => F ω x) P)
    (hYG : IsGaussianProcess (fun x ω => G ω x) Q)
    (hmeanF : ∀ x, ∫ ω, F ω x ∂P = 0)
    (hmeanG : ∀ x, ∫ ω, G ω x ∂Q = 0)
    (hcov : ∀ x y, cov[fun ω => F ω x, fun ω => F ω y; P] =
      cov[fun ω => G ω x, fun ω => G ω y; Q]) :
    P.map F = Q.map G := by
  apply continuousMap_map_eq_of_finite_evaluations_cross F G hF hG
  intro I
  apply finite_centered_gaussian_restrict_law_eq I
    (fun x ω => F ω x) (fun x ω => G ω x) hXF hYG
  · intro x
    exact (ContinuousMap.measurable_eval x).comp hF
  · intro x
    exact (ContinuousMap.measurable_eval x).comp hG
  · exact hmeanF
  · exact hmeanG
  · exact hcov

end BrownianSharp.AlignmentPaperGaussianFeatureBridge
