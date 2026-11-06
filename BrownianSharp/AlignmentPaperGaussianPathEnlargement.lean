import BrownianSharp.AlignmentPaperGaussianDilationLimit
import BrownianSharp.AlignmentPaperQuadraticGaussianMoment
import BrownianSharp.AlignmentPaperMaternSmallBall
import BrownianSharp.AlignmentPaperCompactTubes
import BrownianSharp.AlignmentPaperGaussianEmpiricalAssembly
import BrownianSharp.AlignmentPaperQuantizationUpperRates
import BrownianSharp.AlignmentPaperEmpiricalRateBudget
import BrownianSharp.AlignmentPaperContinuousGaussianFernique
import BrownianSharp.AlignmentPaperEmpiricalBudgetConversion
import BrownianSharp.AlignmentPaperQuantizationRates
import BrownianSharp.AlignmentGaussianBochner
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-!
# Continuous-path Gaussian dilation

Finite-dimensional evaluation-law and compactness ingredients for passing a
Gaussian enlargement estimate from finite grids to a compact path feature ball.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology RealInnerProductSpace ENNReal NNReal

namespace BrownianSharp.AlignmentPaperGaussianPathEnlargement

open BrownianSharp.AlignmentPaperQuadraticGaussianMoment

/-- A nonzero finite Gaussian feature coordinate makes every finite cube
strictly smaller than the whole Gaussian space. This is the open-complement
fact used to keep the limiting path-ball mass below one. -/
theorem stdGaussian_featureCube_real_lt_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {I : Type*} [Fintype I] (v : I → E) (hv : ∃ i, v i ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    (ProbabilityTheory.stdGaussian E).real
      {g | ∀ i, |inner ℝ g (v i)| ≤ ε} < 1 := by
  classical
  let μ : Measure E := ProbabilityTheory.stdGaussian E
  let A : Set E := {g | ∀ i, |inner ℝ g (v i)| ≤ ε}
  obtain ⟨i₀, hi₀⟩ := hv
  have hdim : 0 < Module.finrank ℝ E := by
    apply (Module.finrank_pos_iff_exists_ne_zero (R := ℝ) (M := E)).2
    exact ⟨v i₀, hi₀⟩
  letI : Nonempty (Fin (Module.finrank ℝ E)) := Fin.pos_iff_nonempty.mp hdim
  let b : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ E := stdOrthonormalBasis ℝ E
  have hevalCont : Continuous (fun g : E => fun i => inner ℝ g (v i)) := by
    refine continuous_pi fun i => ?_
    simpa [real_inner_comm] using (innerSL ℝ (v i)).continuous
  have hAmeas : MeasurableSet A := by
    have hc : IsClosed A := by
      rw [show A = ⋂ i : I, {g : E | |inner ℝ g (v i)| ≤ ε} by
        ext g
        simp [A]]
      exact isClosed_iInter fun i =>
        isClosed_Iic.preimage (continuous_abs.comp
          ((continuous_apply i).comp hevalCont))
    exact hc.measurableSet
  let z : E := v i₀
  let c : ℝ := (ε + 1) / ‖v i₀‖ ^ 2
  let g₀ : E := c • z
  have hvnorm : 0 < ‖v i₀‖ := norm_pos_iff.mpr hi₀
  have hlarge : ε < inner ℝ g₀ (v i₀) := by
    dsimp [g₀, c, z]
    rw [inner_smul_left]
    simp only [real_inner_self_eq_norm_sq]
    have hsq : ‖v i₀‖ ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hvnorm)
    have hc : ‖v i₀‖ ^ 2 * ((ε + 1) / ‖v i₀‖ ^ 2) = ε + 1 := by
      field_simp
    simp only [starRingEnd_apply, star_trivial]
    change ε < ((ε + 1) / ‖v i₀‖ ^ 2) * ‖v i₀‖ ^ 2
    nlinarith [hc]
  let O : Set E := {g | ε < inner ℝ g (v i₀)}
  have hOopen : IsOpen O := isOpen_Ioi.preimage
    ((continuous_apply i₀).comp hevalCont)
  have hOsub : O ⊆ Aᶜ := by
    intro g hg hA
    have h := abs_le.mp (hA i₀)
    change ε < inner ℝ g (v i₀) at hg
    linarith
  have hstdOpen := finiteHilbertStdGaussian_isOpenPosMeasure b
  letI : μ.IsOpenPosMeasure := hstdOpen
  have hOpos : 0 < μ O := hOopen.measure_pos μ ⟨g₀, hlarge⟩
  have hAcpos : 0 < μ Aᶜ := lt_of_lt_of_le hOpos (measure_mono hOsub)
  have hsum := MeasureTheory.measureReal_add_measureReal_compl (μ := μ) (s := A) hAmeas
  have htotal : μ.real Set.univ = 1 := by simp [μ]
  rw [htotal] at hsum
  have hAcomp : 0 < μ.real Aᶜ :=
    ENNReal.toReal_pos hAcpos.ne' (measure_ne_top μ _)
  linarith

/-- A nonzero covariance feature makes the actual centered path law assign
strictly less than one to every finite-radius uniform ball. The proof uses a
single evaluation and the finite Gaussian evaluation-law identity. -/
theorem actual_path_ball_real_lt_one
    {T Ω H : Type*} [MetricSpace T] [CompactSpace T] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(T, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun y ω => F ω y) P)
    (hmean : ∀ y, ∫ ω, F ω y ∂P = 0)
    (K : C(T, H)) (a : T) (hKa : K a ≠ 0)
    (hcov : ∀ y z, cov[fun ω => F ω y, fun ω => F ω z; P] =
      inner ℝ (K y) (K z)) {ε : ℝ} (hε : 0 < ε) :
    (P.map F).real (Metric.closedBall (0 : C(T, ℝ)) ε) < 1 := by
  classical
  let N : ℕ := 1
  let x : Fin N → T := fun _ => a
  let E : Submodule ℝ H := Submodule.span ℝ ({K a} : Set H)
  let v : Fin N → E := fun _ => ⟨K a, Submodule.subset_span (by simp)⟩
  let J := ↥(Finset.univ : Finset (Fin N))
  let vJ : J → E := fun i => v i.1
  letI : FiniteDimensional ℝ E :=
    (Submodule.fg_iff_finiteDimensional E).mp (Submodule.fg_span (Set.finite_singleton (K a)))
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let rF : Ω → (J → ℝ) := fun ω i => F ω (x i.1)
  let rE : E → (J → ℝ) := fun g i => inner ℝ g (vJ i)
  let C : Set (J → ℝ) := {z | ∀ i, |z i| ≤ ε}
  let μ : Measure C(T, ℝ) := P.map F
  have hmean' : ∀ i, ∫ ω, F ω (x i) ∂P = 0 := by intro i; exact hmean _
  have hcov' : ∀ i j, cov[fun ω => F ω (x i), fun ω => F ω (x j); P] =
      inner ℝ (v i) (v j) := by
    intro i j
    simpa [v, x] using hcov (x i) (x j)
  have hfinite := BrownianSharp.AlignmentPaperGaussianDilationLimit.finite_feature_evaluation_law_eq
    v F x hF hX hmean' hcov'
  have hrF : Measurable rF := by
    apply measurable_pi_iff.mpr
    intro i
    exact (continuous_eval_const (x i.1)).measurable.comp hF
  have hrE : Measurable rE := by
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun g : E => inner ℝ g (vJ i))
    simpa [real_inner_comm] using (innerSL ℝ (vJ i)).continuous.measurable
  have hC : MeasurableSet C := by
    have hc : IsClosed C := by
      rw [show C = ⋂ i : J, {z : J → ℝ | |z i| ≤ ε} by
        ext z
        simp [C]]
      exact isClosed_iInter fun i => isClosed_Iic.preimage
        (continuous_abs.comp (continuous_apply i))
    exact hc.measurableSet
  have hmap := congrArg (fun ν : Measure (J → ℝ) => ν C) hfinite
  have hleft : μ {f : C(T, ℝ) | ∀ i : J, |f (x i.1)| ≤ ε} =
      (μ.map (fun f i => f (x i.1))) C := by
    rw [Measure.map_apply (by
      apply measurable_pi_iff.mpr
      intro i
      exact (continuous_eval_const (x i.1)).measurable) hC]
    congr 1
  have hmap' : (μ.map (fun f i => f (x i.1))) C =
      (ProbabilityTheory.stdGaussian E).map rE C := by
    change (Measure.map (fun f i => f (x i.1)) (Measure.map F P)) C = _
    rw [Measure.map_map]
    · exact hmap
    · exact measurable_pi_iff.mpr (fun i => (continuous_eval_const (x i.1)).measurable)
    · exact hF
  have hpre : rE ⁻¹' C = {g : E | ∀ i, |inner ℝ g (vJ i)| ≤ ε} := by
    ext g
    simp [C, rE]
  have hright : (ProbabilityTheory.stdGaussian E).map rE C =
      ProbabilityTheory.stdGaussian E {g : E | ∀ i, |inner ℝ g (vJ i)| ≤ ε} := by
    rw [Measure.map_apply hrE hC, hpre]
  have hcube : (ProbabilityTheory.stdGaussian E).real
      {g : E | ∀ i, |inner ℝ g (vJ i)| ≤ ε} < 1 :=
    stdGaussian_featureCube_real_lt_one vJ ⟨⟨0, Finset.mem_univ _⟩, by simpa [vJ, v] using hKa⟩ hε
  have hslab : μ.real {f : C(T, ℝ) | ∀ i : J, |f (x i.1)| ≤ ε} < 1 := by
    have hreal := congrArg ENNReal.toReal (hleft.trans (hmap'.trans hright))
    simpa [Measure.real] using hreal ▸ hcube
  have hballSub : Metric.closedBall (0 : C(T, ℝ)) ε ⊆
      {f : C(T, ℝ) | ∀ i : J, |f (x i.1)| ≤ ε} := by
    intro f hf y
    have hnorm : ‖f‖ ≤ ε := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hf
    exact le_trans (by simpa using (f.norm_coe_le_norm (x y.1))) hnorm
  have hmono : μ.real (Metric.closedBall (0 : C(T, ℝ)) ε) ≤
      μ.real {f : C(T, ℝ) | ∀ i : J, |f (x i.1)| ≤ ε} := MeasureTheory.measureReal_mono hballSub
  exact lt_of_le_of_lt hmono hslab

/-- In finite dimension, the coordinate tube around the image of a Hilbert
unit ball is closed. This is the measurable-set fact needed to transfer a
finite-grid law equality to its tube event. -/
theorem finiteFeatureEvaluationTube_isClosed
    {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype J] [TopologicalSpace J] [DiscreteTopology J]
    (v : J → E) (t ε : ℝ) :
    IsClosed {y : J → ℝ | ∃ z ∈ Metric.closedBall (0 : E) 1, ∀ i,
      |y i - t * inner ℝ z (v i)| ≤ ε} := by
  classical
  let Q : Set (J → ℝ) := Set.univ.pi (fun _ => Set.Icc (-ε) ε)
  let G : E × (J → ℝ) → (J → ℝ) :=
    fun p i => t * inner ℝ p.1 (v i) + p.2 i
  have hball : IsCompact (Metric.closedBall (0 : E) 1) := isCompact_closedBall _ _
  have hQ : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  have hGcont : Continuous G := by
    refine continuous_pi fun i => ?_
    have hc : Continuous (fun p : E × (J → ℝ) =>
        t * inner ℝ p.1 (v i)) := by
      exact continuous_const.mul <|
        continuous_inner.comp (continuous_fst.prodMk continuous_const)
    convert hc.add ((continuous_apply i).comp continuous_snd) using 1 <;> ext p <;> rfl
  have hcompact : IsCompact (G '' (Metric.closedBall (0 : E) 1 ×ˢ Q)) :=
    (hball.prod hQ).image hGcont
  have hclosed : IsClosed (G '' (Metric.closedBall (0 : E) 1 ×ˢ Q)) :=
    hcompact.isClosed
  have heq : {y : J → ℝ | ∃ z ∈ Metric.closedBall (0 : E) 1, ∀ i,
      |y i - t * inner ℝ z (v i)| ≤ ε} =
      G '' (Metric.closedBall (0 : E) 1 ×ˢ Q) := by
    ext y
    constructor
    · rintro ⟨z, hz, hy⟩
      let q : J → ℝ := fun i => y i - t * inner ℝ z (v i)
      have hq : q ∈ Q := by
        intro i _
        exact abs_le.mp (hy i)
      refine ⟨(z, q), Set.mk_mem_prod hz hq, ?_⟩
      funext i
      dsimp [G, q]
      ring
    · rintro ⟨p, hp, hEq⟩
      rcases Set.mem_prod.mp hp with ⟨hpball, hpQ⟩
      refine ⟨p.1, hpball, ?_⟩
      intro i
      have hqi : p.2 i ∈ Set.Icc (-ε) ε := (Set.mem_pi.mp hpQ) i (Set.mem_univ i)
      have hi := congrFun hEq i
      dsimp [G] at hi
      have : y i - t * inner ℝ p.1 (v i) = p.2 i := by linarith
      rw [this]
      exact abs_le.mpr hqi
  rw [heq]
  exact hclosed

/-- The grid image of the intrinsic Hilbert feature ball is exactly the image
of the unit ball in the finite span of the observed feature vectors. -/
theorem featureBall_grid_projection_eq
    {T H : Type*} [MetricSpace T] [CompactSpace T]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {N : ℕ} (K : C(T, H)) (x : Fin N → T) :
    let S : Submodule ℝ H := Submodule.span ℝ (Set.range (fun i => K (x i)))
    let v : Fin N → S := fun i => ⟨K (x i), Submodule.subset_span ⟨i, rfl⟩⟩
    (fun (f : C(T, ℝ)) (i : Fin N) => f (x i)) ''
      AlignmentCompactFeatureBall.featureBall K =
    (fun (g : S) (i : Fin N) => inner ℝ g (v i)) ''
      Metric.closedBall (0 : S) 1 := by
  classical
  let S : Submodule ℝ H := Submodule.span ℝ (Set.range (fun i : Fin N => K (x i)))
  let v : Fin N → S := fun i => ⟨K (x i), Submodule.subset_span ⟨i, rfl⟩⟩
  let rK : C(T, ℝ) → (Fin N → ℝ) := fun f i => f (x i)
  let rH : H → (Fin N → ℝ) :=
    fun g i => inner ℝ g (K (x i))
  let rS : S → (Fin N → ℝ) := fun g i => inner ℝ g (v i)
  have hleft : rK '' AlignmentCompactFeatureBall.featureBall K =
      rH '' Metric.closedBall (0 : H) 1 := by
    ext y
    constructor
    · rintro ⟨f, hf, rfl⟩
      rcases hf with ⟨g, hg, rfl⟩
      refine ⟨g, ?_, ?_⟩
      · simpa [Metric.mem_closedBall, dist_zero_right] using hg
      · funext i
        simp [rK, rH, AlignmentCompactFeatureBall.featurePath]
    · rintro ⟨g, hg, rfl⟩
      refine ⟨AlignmentCompactFeatureBall.featurePath K g, ⟨g, ?_, rfl⟩, ?_⟩
      · simpa [Metric.mem_closedBall, dist_zero_right] using hg
      · funext i
        simp [rK, rH, AlignmentCompactFeatureBall.featurePath]
  have hproj :=
    BrownianSharp.AlignmentPaperQuadraticGaussianMoment.finiteFeatureEvaluation_unitBall_image_eq
      (fun i : Fin N => K (x i))
  have hfunH : (fun g : H => finiteFeatureEval (fun i : Fin N => K (x i)) g) = rH := by
    funext g i
    rfl
  have hfunS : (fun g : S => finiteFeatureEval (fun i : Fin N => K (x i)) (g : H)) = rS := by
    funext g i
    rfl
  have hproj' : rH '' Metric.closedBall (0 : H) 1 =
      rS '' Metric.closedBall (0 : S) 1 := by
    simpa only [← hfunH, ← hfunS] using hproj
  exact hleft.trans hproj'

/-- Actual finite-grid path-law enlargement. The finite-dimensional Gaussian
law equality is derived from the process hypotheses; the only geometric input
is the exact equality between the grid image of the path feature set and the
projected Hilbert unit ball. -/
theorem actual_finiteGrid_featureTube_enlargement
    {T Ω E : Type*} [MetricSpace T] [CompactSpace T] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (F : Ω → C(T, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun y ω => F ω y) P)
    (x : Fin N → T) (v : Fin N → E)
    (hmean : ∀ i, ∫ ω, F ω (x i) ∂P = 0)
    (hcov : ∀ i j, cov[fun ω => F ω (x i), fun ω => F ω (x j); P] =
      inner ℝ (v i) (v j))
    (K : Set C(T, ℝ)) (hK : IsCompact K)
    (hprojection : (fun (f : C(T, ℝ)) (i : ↥(Finset.univ : Finset (Fin N)) ) =>
        f (x i.1)) '' K =
      (fun (g : E) (i : ↥(Finset.univ : Finset (Fin N)) ) =>
        inner ℝ g (v i.1)) '' Metric.closedBall (0 : E) 1)
    (hv : ∃ i, v i ≠ 0) {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    let μ := P.map F
    Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile
        (μ.real {f | ∀ i : Fin N, |f (x i)| ≤ ε}) + t) ≤
      μ.real {f | ∃ g ∈ K, ∀ i : Fin N,
        |f (x i) - t * g (x i)| ≤ ε} := by
  classical
  let J := ↥(Finset.univ : Finset (Fin N))
  let rK : C(T, ℝ) → (J → ℝ) := fun f i => f (x i.1)
  let rE : E → (J → ℝ) := fun g i => inner ℝ g (v i.1)
  let Acoord : Set (J → ℝ) := {y | ∀ i, |y i| ≤ ε}
  let Dcoord : Set (J → ℝ) := {y | ∃ z ∈ Metric.closedBall (0 : E) 1,
    ∀ i, |y i - t * inner ℝ z (v i.1)| ≤ ε}
  let Apath : Set C(T, ℝ) := {f | ∀ i : Fin N, |f (x i)| ≤ ε}
  let Dpath : Set C(T, ℝ) := {f | ∃ g ∈ K, ∀ i : Fin N,
    |f (x i) - t * g (x i)| ≤ ε}
  let AE : Set E := {g | ∀ i : Fin N, |inner ℝ g (v i)| ≤ ε}
  let DE : Set E := {g | ∃ z ∈ Metric.closedBall (0 : E) 1,
    ∀ i : Fin N, |inner ℝ g (v i) - t * inner ℝ z (v i)| ≤ ε}
  let μ : Measure C(T, ℝ) := P.map F
  have hAcoord : MeasurableSet Acoord := by
    have hclosed : IsClosed Acoord := by
      rw [show Acoord = ⋂ i : J, {y : J → ℝ | |y i| ≤ ε} by
        ext y
        simp [Acoord]]
      exact isClosed_iInter fun i =>
        isClosed_Iic.preimage (continuous_abs.comp (continuous_apply i))
    exact hclosed.measurableSet
  have hDcoord : MeasurableSet Dcoord :=
    (finiteFeatureEvaluationTube_isClosed (fun i : J => v i.1) t ε).measurableSet
  have hrK : Measurable rK := by
    apply measurable_pi_iff.mpr
    intro i
    exact (continuous_eval_const (x i.1)).measurable
  have hrE : Measurable rE := by
    apply measurable_pi_iff.mpr
    intro i
    change Measurable (fun g : E => inner ℝ g (v i.1))
    simpa [real_inner_comm] using (innerSL ℝ (v i.1)).continuous.measurable
  have hfinite := BrownianSharp.AlignmentPaperGaussianDilationLimit.finite_feature_evaluation_law_eq
    v F x hF hX hmean hcov
  have hAmapENN : μ Apath = ProbabilityTheory.stdGaussian E AE := by
    have hmap := congrArg (fun ν : Measure (J → ℝ) => ν Acoord) hfinite
    have hleft : μ Apath = (μ.map rK) Acoord := by
      rw [Measure.map_apply hrK hAcoord]
      congr 1
      ext f
      simp [Apath, Acoord, rK, J]
    have hpre : rE ⁻¹' Acoord = AE := by
      ext g
      simp [AE, Acoord, rE, J]
    have hrightENN : (ProbabilityTheory.stdGaussian E).map rE Acoord =
        ProbabilityTheory.stdGaussian E AE := by
      rw [Measure.map_apply hrE hAcoord, hpre]
    have hright : ((ProbabilityTheory.stdGaussian E).map rE).real Acoord =
        (ProbabilityTheory.stdGaussian E).real AE := by
      change ((ProbabilityTheory.stdGaussian E).map rE Acoord).toReal =
        (ProbabilityTheory.stdGaussian E AE).toReal
      exact congrArg ENNReal.toReal hrightENN
    have hmap' : μ.map rK Acoord = (ProbabilityTheory.stdGaussian E).map rE Acoord := by
      change (Measure.map rK (Measure.map F P)) Acoord = _
      rw [Measure.map_map hrK hF]
      exact hmap
    calc
      μ Apath = μ.map rK Acoord := hleft
      _ = (ProbabilityTheory.stdGaussian E).map rE Acoord := hmap'
      _ = ProbabilityTheory.stdGaussian E AE := hrightENN
  have hAmap : μ.real Apath = (ProbabilityTheory.stdGaussian E).real AE := by
    simpa [Measure.real] using congrArg ENNReal.toReal hAmapENN
  have hDmapENN : μ Dpath = ProbabilityTheory.stdGaussian E DE := by
    have hmap := congrArg (fun ν : Measure (J → ℝ) => ν Dcoord) hfinite
    have hleft : μ Dpath = (μ.map rK) Dcoord := by
      rw [Measure.map_apply hrK hDcoord]
      congr 1
      change Dpath = rK ⁻¹' Dcoord
      ext f
      constructor
      · rintro ⟨g, hgK, hg⟩
        have hproj : rK g ∈ rE '' Metric.closedBall (0 : E) 1 := by
          rw [← hprojection]
          exact ⟨g, hgK, rfl⟩
        obtain ⟨z, hz, heval⟩ := hproj
        refine ⟨z, hz, ?_⟩
        intro i
        have hi := hg i.1
        have hcoord := congrFun heval i
        have hcoord' : inner ℝ z (v i.1) = g (x i.1) := by
          simpa [rK, rE] using hcoord
        rw [hcoord']
        simpa [rK] using hi
      · rintro ⟨z, hz, hf⟩
        have hproj : rE z ∈ (fun f : C(T, ℝ) => rK f) '' K := by
          rw [hprojection]
          exact ⟨z, hz, rfl⟩
        obtain ⟨g, hgK, heval⟩ := hproj
        refine ⟨g, hgK, ?_⟩
        intro i
        have hi := hf ⟨i, Finset.mem_univ i⟩
        have hcoord := congrFun heval ⟨i, Finset.mem_univ i⟩
        have hcoord' : g (x i) = inner ℝ z (v i) := by
          simpa [rK, rE] using hcoord
        rw [← hcoord'] at hi
        simpa [rK] using hi
    have hpre : rE ⁻¹' Dcoord = DE := by
      ext g
      simp [DE, Dcoord, rE, J]
    have hrightENN : (ProbabilityTheory.stdGaussian E).map rE Dcoord =
        ProbabilityTheory.stdGaussian E DE := by
      rw [Measure.map_apply hrE hDcoord, hpre]
    have hright : ((ProbabilityTheory.stdGaussian E).map rE).real Dcoord =
        (ProbabilityTheory.stdGaussian E).real DE := by
      change ((ProbabilityTheory.stdGaussian E).map rE Dcoord).toReal =
        (ProbabilityTheory.stdGaussian E DE).toReal
      exact congrArg ENNReal.toReal hrightENN
    have hmap' : μ.map rK Dcoord = (ProbabilityTheory.stdGaussian E).map rE Dcoord := by
      change (Measure.map rK (Measure.map F P)) Dcoord = _
      rw [Measure.map_map hrK hF]
      exact hmap
    calc
      μ Dpath = μ.map rK Dcoord := hleft
      _ = (ProbabilityTheory.stdGaussian E).map rE Dcoord := hmap'
      _ = ProbabilityTheory.stdGaussian E DE := hrightENN
  have hDmap : μ.real Dpath = (ProbabilityTheory.stdGaussian E).real DE := by
    simpa [Measure.real] using congrArg ENNReal.toReal hDmapENN
  have hstd := finiteFeatureSpan_stdGaussian_cube_enlargement v hv hε ht
  have hstd' : Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile
        ((ProbabilityTheory.stdGaussian E).real AE) + t) ≤
      (ProbabilityTheory.stdGaussian E).real DE := by
    simpa [AE, DE, finiteFeatureEval] using hstd
  rw [← hAmap, ← hDmap] at hstd'
  simpa [Apath, Dpath, μ] using hstd'

/-- Actual continuous-path Gaussian enlargement by the compact intrinsic
feature ball. The finite-grid inequalities are instantiated from covariance
features on each finite span; the two decreasing limits are identified with
the uniform closed ball and uniform feature-ball tube. -/
theorem actual_featureBall_uniform_enlargement
    {T Ω H : Type*} [MetricSpace T] [CompactSpace T] [T2Space T]
    [SecondCountableTopology T] [LocallyCompactSpace T] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(T, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun y ω => F ω y) P)
    (hmean : ∀ y, ∫ ω, F ω y ∂P = 0)
    (K : C(T, H))
    (hcov : ∀ y z, cov[fun ω => F ω y, fun ω => F ω z; P] =
      inner ℝ (K y) (K z))
    (a : T) (ha : K a ≠ 0)
    (x : ℕ → T) (hx : DenseRange x) (hx0 : x 0 = a)
    {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) :
    Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile
        ((P.map F).real (Metric.closedBall (0 : C(T, ℝ)) ε)) + t) ≤
      (P.map F).real {f : C(T, ℝ) | ∃ g ∈ AlignmentCompactFeatureBall.featureBall K,
        ∀ y, |f y - t * g y| ≤ ε} := by
  classical
  let μ : Measure C(T, ℝ) := P.map F
  let A : ℕ → Set C(T, ℝ) := fun n =>
    {f | ∀ j ≤ n, |f (x j)| ≤ ε}
  let D : ℕ → Set C(T, ℝ) := fun n =>
    {f | ∃ g ∈ AlignmentCompactFeatureBall.featureBall K,
      ∀ j ≤ n, |f (x j) - t * g (x j)| ≤ ε}
  have hAmeas : ∀ n, NullMeasurableSet (A n) μ := by
    intro n
    let N := n + 1
    let xN : Fin N → T := fun i => x i.1
    have hclosed := BrownianSharp.AlignmentPaperGaussianDilationLimit.finiteGridTubeSet_isClosed
      xN ({0} : Set C(T, ℝ)) isCompact_singleton 0 ε
    have heq : A n = {f | ∃ g ∈ ({0} : Set C(T, ℝ)), ∀ i : Fin N,
        |f (xN i) - 0 * g (xN i)| ≤ ε} := by
      ext f
      constructor
      · intro hf
        refine ⟨0, by simp, ?_⟩
        intro i
        simpa [xN] using hf i.1 (by omega)
      · rintro ⟨g, hg, h⟩ j hj
        simpa [xN] using h (⟨j, by omega⟩ : Fin N)
    rw [heq]
    exact hclosed.measurableSet.nullMeasurableSet
  have hDmeas : ∀ n, NullMeasurableSet (D n) μ := by
    intro n
    let N := n + 1
    let xN : Fin N → T := fun i => x i.1
    have hclosed := BrownianSharp.AlignmentPaperGaussianDilationLimit.finiteGridTubeSet_isClosed
      xN (AlignmentCompactFeatureBall.featureBall K)
      (AlignmentCompactFeatureBall.featureBall_isCompact K) t ε
    have heq : D n = {f | ∃ g ∈ AlignmentCompactFeatureBall.featureBall K,
        ∀ i : Fin N, |f (xN i) - t * g (xN i)| ≤ ε} := by
      ext f
      constructor
      · rintro ⟨g, hg, h⟩
        refine ⟨g, hg, ?_⟩
        intro i
        exact h i.1 (by omega)
      · rintro ⟨g, hg, h⟩
        refine ⟨g, hg, ?_⟩
        intro j hj
        simpa [xN] using h (⟨j, by omega⟩ : Fin N)
    rw [heq]
    exact hclosed.measurableSet.nullMeasurableSet
  have hAanti : Antitone A := by
    intro n m hnm f hf j hj
    exact hf j (le_trans hj hnm)
  have hDanti : Antitone D := by
    intro n m hnm f hf
    rcases hf with ⟨g, hg, hineq⟩
    exact ⟨g, hg, fun j hj => hineq j (le_trans hj hnm)⟩
  have hbound : ∀ n, Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile (μ.real (A n)) + t) ≤ μ.real (D n) := by
    intro n
    let N := n + 1
    let xN : Fin N → T := fun i => x i.1
    let S : Submodule ℝ H := Submodule.span ℝ (Set.range (fun i : Fin N => K (xN i)))
    letI : FiniteDimensional ℝ S :=
      (Submodule.fg_iff_finiteDimensional S).mp
        (Submodule.fg_span (Set.finite_range fun i : Fin N => K (xN i)))
    letI : MeasurableSpace S := borel S
    letI : BorelSpace S := ⟨rfl⟩
    let v : Fin N → S := fun i => ⟨K (xN i), Submodule.subset_span ⟨i, rfl⟩⟩
    let J := ↥(Finset.univ : Finset (Fin N))
    have hv : ∃ i, v i ≠ 0 := by
      refine ⟨⟨0, by omega⟩, ?_⟩
      intro hz
      have : K a = 0 := by simpa [v, xN, hx0] using congrArg Subtype.val hz
      exact ha this
    have hprojFull := featureBall_grid_projection_eq K xN
    let restrict : (Fin N → ℝ) → (J → ℝ) := fun z i => z i.1
    have hprojection : (fun (f : C(T, ℝ)) (i : J) => f (xN i.1)) ''
        AlignmentCompactFeatureBall.featureBall K =
      (fun (g : S) (i : J) => inner ℝ g (v i.1)) '' Metric.closedBall (0 : S) 1 := by
      have h := congrArg (fun Z : Set (Fin N → ℝ) => restrict '' Z) hprojFull
      simpa [restrict, Set.image_image, v] using h
    have hmeanN : ∀ i, ∫ ω, F ω (xN i) ∂P = 0 := fun i => hmean _
    have hcovN : ∀ i j, cov[fun ω => F ω (xN i), fun ω => F ω (xN j); P] =
        inner ℝ (v i) (v j) := by
      intro i j
      simpa [v] using hcov (xN i) (xN j)
    have hfinite := actual_finiteGrid_featureTube_enlargement
      F hF hX xN v hmeanN hcovN (AlignmentCompactFeatureBall.featureBall K)
      (AlignmentCompactFeatureBall.featureBall_isCompact K) hprojection hv hε ht
    have hAeq : A n = {f | ∀ i : Fin N, |f (xN i)| ≤ ε} := by
      ext f
      constructor
      · intro hf i
        exact hf i.1 (by omega)
      · intro hf j hj
        simpa [xN] using hf (⟨j, by omega⟩ : Fin N)
    have hDeq : D n = {f | ∃ g ∈ AlignmentCompactFeatureBall.featureBall K,
        ∀ i : Fin N, |f (xN i) - t * g (xN i)| ≤ ε} := by
      ext f
      constructor
      · rintro ⟨g, hg, h⟩
        exact ⟨g, hg, fun i => h i.1 (by omega)⟩
      · rintro ⟨g, hg, h⟩
        exact ⟨g, hg, fun j hj => h ⟨j, by omega⟩⟩
    rw [hAeq, hDeq]
    simpa [μ] using hfinite
  have hAinter : ⋂ n, A n = Metric.closedBall (0 : C(T, ℝ)) ε := by
    ext f
    rw [Set.mem_iInter]
    constructor
    · intro hf
      apply (ContinuousMap.norm_le f hε.le).2
      intro y
      have hgrid : ∀ j, |f (x j)| ≤ ε := by
        intro j
        exact hf j j le_rfl
      have hclosed : IsClosed {y : T | |f y| ≤ ε} := by
        exact isClosed_Iic.preimage (continuous_abs.comp f.continuous)
      have hsub : Set.range x ⊆ {y : T | |f y| ≤ ε} := by
        rintro z ⟨j, rfl⟩
        exact hgrid j
      have hall := closure_minimal hsub hclosed
      have hrange : closure (Set.range x) = Set.univ := hx.closure_eq
      have hy := hall (by rw [hrange]; exact Set.mem_univ y)
      change |f y| ≤ ε at hy
      simpa [Real.norm_eq_abs] using hy
    · intro hf n
      change ‖f‖ ≤ ε at hf
      intro j hj
      have hn : ‖f‖ ≤ ε := hf
      exact le_trans (by simpa using f.norm_coe_le_norm (x j)) hn
  have hDinter : ⋂ n, D n =
      {f : C(T, ℝ) | ∃ g ∈ AlignmentCompactFeatureBall.featureBall K,
        ∀ y, |f y - t * g y| ≤ ε} := by
    ext f
    rw [Set.mem_iInter]
    exact BrownianSharp.AlignmentPaperGaussianDilationLimit.finiteGridTube_iff_uniformTube
      hx (AlignmentCompactFeatureBall.featureBall K)
      (AlignmentCompactFeatureBall.featureBall_isCompact K) f
  have hA0 : 0 < μ.real (⋂ n, A n) := by
    rw [hAinter]
    exact AlignmentPaperMaternSmallBall.centered_path_closedBall_pos F hF hX hmean ε hε
  have hA1 : μ.real (⋂ n, A n) < 1 := by
    rw [hAinter]
    exact actual_path_ball_real_lt_one F hF hX hmean K a ha hcov hε
  have hlimit := BrownianSharp.AlignmentPaperGaussianDilationLimit.gaussianCDF_enlargement_of_decreasing_limits
    μ A D hAmeas hDmeas hAanti hDanti ht hbound hA0 hA1
  rw [hAinter, hDinter] at hlimit
  simpa [μ] using hlimit

/-- Convenience form of the path enlargement theorem: the anchored dense grid
is constructed internally, and the conclusion is stated for the compact
closed tube around the scaled feature ball. -/
theorem actual_featureBall_closedTube_enlargement
    {T Ω H : Type*} [MetricSpace T] [CompactSpace T] [T2Space T]
    [SecondCountableTopology T] [LocallyCompactSpace T] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [Nonempty T] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(T, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun y ω => F ω y) P)
    (hmean : ∀ y, ∫ ω, F ω y ∂P = 0)
    (K : C(T, H)) (hcov : ∀ y z, cov[fun ω => F ω y, fun ω => F ω z; P] =
      inner ℝ (K y) (K z))
    (a : T) (ha : K a ≠ 0) {ε R : ℝ} (hε : 0 < ε) (hR : 0 < R) :
    Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile
        ((P.map F).real (Metric.closedBall (0 : C(T, ℝ)) ε)) + R) ≤
      (P.map F).real
        (AlignmentPaperCompactTubes.closedTube
          ((fun f : C(T, ℝ) => R • f) '' AlignmentCompactFeatureBall.featureBall K) ε) := by
  classical
  let d : ℕ → T := TopologicalSpace.denseSeq T
  let x : ℕ → T := fun n => if n = 0 then a else d (n - 1)
  have hx0 : x 0 = a := by simp [x]
  have hx : DenseRange x := by
    intro y
    have hsub : Set.range d ⊆ Set.range x := by
      rintro z ⟨n, rfl⟩
      refine ⟨n + 1, ?_⟩
      simp [x]
    have hd : closure (Set.range d) = Set.univ :=
      TopologicalSpace.denseRange_denseSeq T |>.closure_eq
    have hy : y ∈ closure (Set.range d) := by rw [hd]; simp
    exact closure_mono hsub hy
  have hdil := actual_featureBall_uniform_enlargement
    F hF hX hmean K hcov a ha x hx hx0 hε hR
  have hset : {f : C(T, ℝ) | ∃ g ∈ AlignmentCompactFeatureBall.featureBall K,
      ∀ y, |f y - R * g y| ≤ ε} =
      AlignmentPaperCompactTubes.closedTube
        ((fun f : C(T, ℝ) => R • f) '' AlignmentCompactFeatureBall.featureBall K) ε := by
    ext f
    constructor
    · rintro ⟨g, hg, hpoint⟩
      refine ⟨R • g, ⟨g, hg, rfl⟩, ?_⟩
      rw [dist_eq_norm]
      apply (ContinuousMap.norm_le (f - R • g) hε.le).2
      intro y
      simpa [ContinuousMap.sub_apply, ContinuousMap.smul_apply, Real.norm_eq_abs] using hpoint y
    · rintro ⟨g, hg, hdist⟩
      rcases hg with ⟨g, hg, rfl⟩
      refine ⟨g, hg, ?_⟩
      have hn : ‖f - R • g‖ ≤ ε := by simpa [dist_eq_norm] using hdist
      intro y
      have hy := (ContinuousMap.norm_le (f - R • g) hε.le).1 hn y
      simpa [ContinuousMap.sub_apply, ContinuousMap.smul_apply, Real.norm_eq_abs] using hy
  rw [hset] at hdil
  exact hdil

/-- Unconditional actual-law empirical Wasserstein bound. The only
quantitative premises left visible are the logarithmic small-ball estimate,
the Gaussian enlargement scale relation, and the fourth-moment bound; the
base-ball positivity, strict upper mass bound, and tube probability all come
from the actual path-law providers above. -/
theorem expected_empirical_bound_actual_feature_tube
    {T Ω H : Type*} [MetricSpace T] [CompactSpace T] [Nonempty T]
    [SecondCountableTopology T] [LocallyCompactSpace T] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(T, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
    (K : C(T, H)) (a : T) (ha : K a ≠ 0)
    (hcov : ∀ x y, cov[fun ω => F ω x, fun ω => F ω y; P] =
      inner ℝ (K x) (K y))
    (R : ℝ) (hR : 0 < R) (ε : ℝ≥0) (hε : 0 < ε)
    (φ s : ℝ) (hφ : 0 ≤ φ) (hs : 0 ≤ s)
    (hRlarge : Real.sqrt (2 * φ) + s ≤ R)
    (hlog : -Real.log ((P.map F).real
      (Metric.closedBall (0 : C(T, ℝ)) (ε : ℝ))) ≤ φ)
    (M4 : ℝ≥0∞)
    (hM4 : (∫⁻ f : C(T, ℝ), edist f 0 ^ 4 ∂P.map F) ≤ M4) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp (R ^ 2 / 2 + φ) + 1 ∧
      ∀ m : ℕ, ∀ hm : 0 < m,
        AlignmentPaperEmpiricalWasserstein.expectedEmpiricalWassersteinTwo
          (P.map F) m hm ≤
        ennrealSqrt
          (3 * ((2 : ℝ≥0∞) *
            ((ENNReal.ofReal (3 * (ε : ℝ))) ^ 2 +
              ennrealSqrt M4 *
                ennrealSqrt
                  (ENNReal.ofReal (Real.exp (-s ^ 2 / 2)))) +
            (ENNReal.ofReal (2 * R * ‖K‖)) ^ 2 *
              ENNReal.ofReal ((1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / m)))) := by
  have hp1 : (P.map F).real (Metric.closedBall (0 : C(T, ℝ)) (ε : ℝ)) < 1 :=
    actual_path_ball_real_lt_one F hF hX hmean K a ha hcov (show 0 < (ε : ℝ) by exact_mod_cast hε)
  have hmass := actual_featureBall_closedTube_enlargement
    F hF hX hmean K hcov a ha (show 0 < (ε : ℝ) by exact_mod_cast hε) hR
  simpa [AlignmentPaperEmpiricalWasserstein.expectedEmpiricalWassersteinTwo] using
    (AlignmentPaperGaussianEmpiricalAssembly.expected_empirical_bound_of_feature_tube_mass
      F hF hX hmean K a ha hcov R hR ε hε φ s hφ hs hRlarge hp1 hlog hmass M4 hM4)

/-- Generic sharp power-log empirical Wasserstein upper rate from the actual
small-ball upper estimate. Fernique supplies the finite fourth moment, path
enlargement supplies the actual tube mass, and the empirical budget closes
the rate without assuming either probability conclusion from a caller. -/
theorem expected_empirical_powerlog_rate_of_smallBall
    {T Ω H : Type*} [MetricSpace T] [CompactSpace T] [Nonempty T]
    [SecondCountableTopology T] [LocallyCompactSpace T] [MeasurableSpace Ω]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(T, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
    (K : C(T, H)) (a : T) (ha : K a ≠ 0)
    (hcov : ∀ x y, cov[fun ω => F ω x, fun ω => F ω y; P] =
      inner ℝ (K x) (K y))
    {α β Csb ε₀ : ℝ} (hα : 0 < α) (hβ : 0 ≤ β)
    (hCsb : 0 < Csb) (hε₀ : 0 < ε₀)
    (hsb : ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      -Real.log ((P.map F).real (Metric.closedBall (0 : C(T, ℝ)) ε)) ≤
        Csb * Latest.smallBallRate α β ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, 0 < m₀ ∧ ∀ m : ℕ, m₀ ≤ m →
      ∀ hm : 0 < m,
      AlignmentPaperEmpiricalWasserstein.expectedEmpiricalWassersteinTwo
        (P.map F) m hm ≤
        ENNReal.ofReal (C * (Real.log (m : ℝ)) ^ (-(1 / α)) *
          (Real.log (Real.log (m : ℝ))) ^ (β / α)) := by
  classical
  obtain ⟨M4, hM4finite, hM4⟩ :=
    AlignmentPaperContinuousGaussianFernique.centeredGaussian_path_fourth_lintegral_finite
      F hF hX hmean
  obtain ⟨c, hc, hrate⟩ :=
    AlignmentPaperQuantizationUpperRates.exists_eventual_powerlog_upper_budget
      hα hβ hCsb (by norm_num : (0 : ℝ) < 1 / 64)
  have hwindow : ∀ᶠ x : ℝ in atTop,
      BrownianSharp.canonicalPowerlogRadius α β c x ≤ ε₀ := by
    have hlim := BrownianSharp.tendsto_powerlog_radius_zero hα hβ hc
    filter_upwards [hlim.eventually (Iio_mem_nhds hε₀)] with x hx
    exact hx.le
  have hbudget' := AlignmentPaperEmpiricalRateBudget.eventually_empirical_budget_le_radius
    (M := M4.toReal) (K := ‖K‖) hα hβ hc ENNReal.toReal_nonneg
  have hgood : ∀ᶠ x : ℝ in atTop,
      1 < x ∧
      Csb * Latest.smallBallRate α β
        (BrownianSharp.canonicalPowerlogRadius α β c x) ≤ x / 64 ∧
      BrownianSharp.canonicalPowerlogRadius α β c x ≤ ε₀ ∧
      (∀ N : ℝ, 0 ≤ N → N ≤ Real.exp (9 * x / 64) + 1 →
        Real.sqrt (3 * (2 * ((3 * BrownianSharp.canonicalPowerlogRadius α β c x) ^ 2 +
          Real.sqrt M4.toReal * Real.exp (-x / 64)) +
          (x * ‖K‖ ^ 2) * (1 / 2) * Real.sqrt (N / Real.exp x))) ≤
          8 * BrownianSharp.canonicalPowerlogRadius α β c x) := by
    filter_upwards [hrate, hwindow, hbudget', eventually_gt_atTop 1] with x hxrate hxwin hxbudget hxone
    refine ⟨hxone, ?_, hxwin, ?_⟩
    · nlinarith [hxrate]
    · simpa using hxbudget
  have hgoodNat : ∀ᶠ m : ℕ in atTop,
      (1 < Real.log (m : ℝ)) ∧
      Csb * Latest.smallBallRate α β
        (BrownianSharp.canonicalPowerlogRadius α β c (Real.log (m : ℝ))) ≤
          Real.log (m : ℝ) / 64 ∧
      BrownianSharp.canonicalPowerlogRadius α β c (Real.log (m : ℝ)) ≤ ε₀ ∧
      (∀ N : ℝ, 0 ≤ N → N ≤ Real.exp (9 * Real.log (m : ℝ) / 64) + 1 →
        Real.sqrt (3 * (2 * ((3 * BrownianSharp.canonicalPowerlogRadius α β c
          (Real.log (m : ℝ))) ^ 2 + Real.sqrt M4.toReal *
            Real.exp (-Real.log (m : ℝ) / 64)) +
          (Real.log (m : ℝ) * ‖K‖ ^ 2) * (1 / 2) *
            Real.sqrt (N / Real.exp (Real.log (m : ℝ))))) ≤
          8 * BrownianSharp.canonicalPowerlogRadius α β c
            (Real.log (m : ℝ))) := by
    exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hgood
  obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.1 hgoodNat
  refine ⟨8 * c, by positivity, m₀ + 1, by omega, ?_⟩
  intro m hmm
  intro hm
  have hmm0 : m₀ ≤ m := by omega
  have hmNat' : 0 < m := by omega
  have ⟨hx, hrateM, hwindowM, hbudgetM⟩ := hm₀ m hmm0
  have hmpos : 0 < (m : ℝ) := by
    by_contra hnot
    have hle : (m : ℝ) ≤ 0 := le_of_not_gt hnot
    have hm0 : m = 0 := by
      have hcast : (m : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg m)
      exact_mod_cast hcast
    subst m
    norm_num at hx
  let x := Real.log (m : ℝ)
  let εr := BrownianSharp.canonicalPowerlogRadius α β c x
  have hεr : 0 < εr := by
    dsimp [εr, BrownianSharp.canonicalPowerlogRadius]
    have hx0 : 0 < x := by dsimp [x]; linarith
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  have hεrwin : εr ≤ ε₀ := by simpa [εr, x] using hwindowM
  have hlog : -Real.log ((P.map F).real (Metric.closedBall 0 εr)) ≤ x / 64 := by
    calc
      _ ≤ Csb * Latest.smallBallRate α β εr := hsb εr hεr hεrwin
      _ ≤ x / 64 := by simpa [εr, x] using hrateM
  let εn : ℝ≥0 := ⟨εr, hεr.le⟩
  let R : ℝ := Real.sqrt x / 2
  let s : ℝ := Real.sqrt x / 4
  let φ : ℝ := x / 64
  have hx0 : 0 ≤ x := by dsimp [x]; linarith
  have hR : 0 < R := by dsimp [R]; positivity
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hφ : 0 ≤ φ := by dsimp [φ]; positivity
  have hRlarge : Real.sqrt (2 * φ) + s ≤ R := by
    dsimp [R, s, φ]
    have hsqrt : Real.sqrt (x / 32) ≤ Real.sqrt x / 4 := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · nlinarith [Real.sq_sqrt hx0]
    have hroot : Real.sqrt (2 * (x / 64)) = Real.sqrt (x / 32) := by congr 1 <;> ring
    rw [hroot]
    linarith
  have hlogm : Real.exp x = (m : ℝ) := by
    dsimp [x]
    exact Real.exp_log hmpos
  obtain ⟨N, hN, hcard, hEmp⟩ := expected_empirical_bound_actual_feature_tube
    F hF hX hmean K a ha hcov R hR εn (by exact_mod_cast hεr) φ s hφ hs hRlarge hlog M4 hM4
  have hcard' : (N : ℝ) ≤ Real.exp (9 * x / 64) + 1 := by
    have hscale : R ^ 2 / 2 + φ = 9 * x / 64 := by
      dsimp [R, φ]
      nlinarith [Real.sq_sqrt hx0]
    calc
      (N : ℝ) ≤ Real.exp (R ^ 2 / 2 + φ) + 1 := hcard
      _ = Real.exp (9 * x / 64) + 1 := by rw [hscale]
  have hbudgetN := hbudgetM (N : ℝ) (by positivity) hcard'
  have hbudgetEq := AlignmentPaperEmpiricalBudgetConversion.assembly_empirical_budget_eq_ofReal
    εn R s ‖K‖ ((N : ℝ) / (m : ℝ)) M4 hM4finite (le_of_lt hR) (norm_nonneg K)
      (by positivity)
  have hqeq : (N : ℝ) / (m : ℝ) = (N : ℝ) / Real.exp x := by rw [hlogm]
  have hrealbudget : Real.sqrt (3 * (2 * ((3 * εr) ^ 2 +
      Real.sqrt M4.toReal * Real.exp (-s ^ 2 / 4)) +
      (2 * R * ‖K‖) ^ 2 * (1 / 2) * Real.sqrt ((N : ℝ) / (m : ℝ)))) ≤ 8 * εr := by
    have hbase' : Real.sqrt (3 * (2 * ((3 * εr) ^ 2 + Real.sqrt M4.toReal *
        Real.exp (-x / 64)) + (x * ‖K‖ ^ 2) * (1 / 2) *
        Real.sqrt ((N : ℝ) / Real.exp x))) ≤ 8 * εr := by
      simpa [x, εr, BrownianSharp.canonicalPowerlogRadius] using hbudgetN
    apply le_trans ?_ hbase'
    apply Real.sqrt_le_sqrt
    rw [hqeq]
    have htail : Real.exp (-s ^ 2 / 4) = Real.exp (-x / 64) := by
      congr 1
      dsimp [s]
      nlinarith [Real.sq_sqrt hx0]
    have hroot : (2 * R) ^ 2 = x := by
      dsimp [R]
      nlinarith [Real.sq_sqrt hx0]
    have hcoef : (2 * R * ‖K‖) ^ 2 = x * ‖K‖ ^ 2 := by
      calc
        (2 * R * ‖K‖) ^ 2 = (2 * R) ^ 2 * ‖K‖ ^ 2 := by ring
        _ = x * ‖K‖ ^ 2 := by rw [hroot]
    rw [hcoef]
    rw [htail]
  have hEmp' := hEmp m hmNat'
  let Bemp : ℝ≥0∞ := ennrealSqrt (3 * ((2 : ℝ≥0∞) *
      ((ENNReal.ofReal (3 * (εn : ℝ))) ^ 2 +
        ennrealSqrt M4 * ennrealSqrt (ENNReal.ofReal (Real.exp (-s ^ 2 / 2)))) +
      (ENNReal.ofReal (2 * R * ‖K‖)) ^ 2 *
        ENNReal.ofReal ((1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / (m : ℝ)))))
  have hEmpBound : AlignmentPaperEmpiricalWasserstein.expectedEmpiricalWassersteinTwo
      (P.map F) m hmNat' ≤ Bemp := by
    simpa [Bemp, εn] using hEmp'
  -- The conversion lemma identifies the empirical budget with `ofReal` of the
  -- real square root bounded by `hrealbudget`.
  calc
    _ ≤ Bemp := hEmpBound
    _ = ENNReal.ofReal (Real.sqrt (3 * (2 * ((3 * εr) ^ 2 +
        Real.sqrt M4.toReal * Real.exp (-s ^ 2 / 4)) +
        (2 * R * ‖K‖) ^ 2 * (1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / (m : ℝ))))) := hbudgetEq
    _ ≤ ENNReal.ofReal (8 * εr) := ENNReal.ofReal_le_ofReal hrealbudget
    _ = ENNReal.ofReal (8 * c * (Real.log (m : ℝ)) ^ (-(1 / α)) *
        (Real.log (Real.log (m : ℝ))) ^ (β / α)) := by
      congr 1
      dsimp [εr, x, BrownianSharp.canonicalPowerlogRadius]
      ring

end BrownianSharp.AlignmentPaperGaussianPathEnlargement
