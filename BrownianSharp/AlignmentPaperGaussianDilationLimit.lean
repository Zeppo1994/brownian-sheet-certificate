import BrownianSharp.AlignmentCompactFeatureBall
import BrownianSharp.GaussianCDFCalculus
import BrownianSharp.AlignmentPaperGaussianFeatureBridge
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.Tactic

/-!
# Compact limit for finite-grid tubes

A deterministic compactness lemma used when passing finite-dimensional Gaussian
Ehrhard inequalities to continuous paths. It makes no probabilistic claim.
-/

noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open scoped Topology

namespace BrownianSharp.AlignmentPaperGaussianDilationLimit

/-- A finite vector of linear evaluations of a finite-dimensional standard
Gaussian is itself a centered Gaussian process with Gram covariance. -/
theorem stdGaussian_featureEvaluation_process
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {N : ℕ} (v : Fin N → E) :
    IsGaussianProcess (fun i (ω : E) => inner ℝ ω (v i))
      (ProbabilityTheory.stdGaussian E) := by
  classical
  refine ⟨?_⟩
  intro I
  let L : E →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi fun i => innerSL ℝ (v i)
  have hbase : HasGaussianLaw (id : E → E) (ProbabilityTheory.stdGaussian E) :=
    ProbabilityTheory.IsGaussian.hasGaussianLaw_id
  have hmap := hbase.map L
  have heq : (fun ω : E => I.restrict (fun i => inner ℝ ω (v i))) = L := by
    funext ω i
    simp [L, innerSL_apply_apply, real_inner_comm]
  rw [heq]
  exact hmap

/-- The mean and covariance of the standard-Gaussian feature evaluations. -/
theorem stdGaussian_featureEvaluation_mean_covariance
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {N : ℕ} (v : Fin N → E) :
    (∀ i, ∫ ω : E, inner ℝ ω (v i) ∂ProbabilityTheory.stdGaussian E = 0) ∧
    (∀ i j, cov[fun ω : E => inner ℝ ω (v i),
      fun ω : E => inner ℝ ω (v j); ProbabilityTheory.stdGaussian E] =
        inner ℝ (v i) (v j)) := by
  constructor
  · intro i
    simpa [real_inner_comm] using
      (ProbabilityTheory.integral_strongDual_stdGaussian (innerSL ℝ (v i)))
  · intro i j
    have hid : MemLp (id : E → E) 2 (ProbabilityTheory.stdGaussian E) :=
      (ProbabilityTheory.IsGaussian.hasGaussianLaw_id
        (μ := ProbabilityTheory.stdGaussian E)).memLp_two
    have hcov := ProbabilityTheory.covarianceBilin_apply_eq_cov hid (v i) (v j)
    rw [ProbabilityTheory.covarianceBilin_stdGaussian] at hcov
    rw [innerSL_apply_apply] at hcov
    simpa [real_inner_comm] using hcov.symm

/-- The actual finite evaluation vector of a centered Gaussian path is equal
in law to the corresponding evaluations of a standard Gaussian on the span of
its covariance features. This is an application of finite Gaussian-law
uniqueness, not an assumption about the projected law. -/
theorem finite_feature_evaluation_law_eq
    {T Ω E : Type*} [MetricSpace T] [CompactSpace T] [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} (v : Fin N → E) (F : Ω → C(T, ℝ)) (x : Fin N → T)
    (hF : Measurable F)
    (hX : IsGaussianProcess (fun y ω => F ω y) P)
    (hmean : ∀ i, ∫ ω, F ω (x i) ∂P = 0)
    (hcov : ∀ i j, cov[fun ω => F ω (x i), fun ω => F ω (x j); P] =
      inner ℝ (v i) (v j)) :
    P.map (fun ω => (Finset.univ : Finset (Fin N)).restrict
      (fun i => F ω (x i))) =
      (ProbabilityTheory.stdGaussian E).map (fun g =>
        (Finset.univ : Finset (Fin N)).restrict (fun i => inner ℝ g (v i))) := by
  classical
  let X : Fin N → Ω → ℝ := fun i ω => F ω (x i)
  let Y : Fin N → E → ℝ := fun i g => inner ℝ g (v i)
  have hXgrid : IsGaussianProcess X P := by
    change IsGaussianProcess (fun i ω => F ω (x i)) P
    exact hX.comp_right x
  have hY : IsGaussianProcess Y (ProbabilityTheory.stdGaussian E) := by
    simpa [Y] using stdGaussian_featureEvaluation_process v
  have hmeasX : ∀ i, Measurable (X i) := by
    intro i
    exact (continuous_eval_const (x i)).measurable.comp hF
  have hmeasY : ∀ i, Measurable (Y i) := by
    intro i
    simpa [Y, real_inner_comm] using (innerSL ℝ (v i)).continuous.measurable
  have hmeanX : ∀ i, ∫ ω, X i ω ∂P = 0 := hmean
  have hmeanY : ∀ i, ∫ g, Y i g ∂ProbabilityTheory.stdGaussian E = 0 :=
    (stdGaussian_featureEvaluation_mean_covariance v).1
  have hcovXY : ∀ i j, cov[X i, X j; P] = cov[Y i, Y j;
      ProbabilityTheory.stdGaussian E] := by
    intro i j
    rw [hcov i j]
    rw [(stdGaussian_featureEvaluation_mean_covariance v).2 i j]
  have hfinite := AlignmentPaperGaussianFeatureBridge.finite_centered_gaussian_restrict_law_eq
    (Finset.univ : Finset (Fin N)) X Y hXgrid hY hmeasX hmeasY
    hmeanX hmeanY hcovXY
  simpa [X, Y] using hfinite

/-- Continuity from above for real masses of a decreasing sequence of
measurable events under a probability measure. -/
theorem tendsto_measureReal_iInter
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (S : ℕ → Set Ω) (hS : ∀ n, NullMeasurableSet (S n) μ)
    (hanti : Antitone S) :
    Tendsto (fun n => μ.real (S n)) atTop (𝓝 (μ.real (⋂ n, S n))) := by
  have hENN : Tendsto (fun n => μ (S n)) atTop (𝓝 (μ (⋂ n, S n))) :=
    MeasureTheory.tendsto_measure_iInter_atTop hS hanti ⟨0, measure_ne_top μ _⟩
  have hfinite : μ (⋂ n, S n) ≠ ⊤ := measure_ne_top μ _
  have hreal := (ENNReal.tendsto_toReal hfinite).comp hENN
  convert hreal using 1 <;> rfl

/-- Passage of finite-grid CDF enlargement bounds to decreasing measurable
limits. The interior-mass hypothesis is exactly what licenses quantile
continuity. -/
theorem gaussianCDF_enlargement_of_decreasing_limits
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A D : ℕ → Set Ω) (hA : ∀ n, NullMeasurableSet (A n) μ)
    (hD : ∀ n, NullMeasurableSet (D n) μ)
    (hAanti : Antitone A) (hDanti : Antitone D)
    {t : ℝ} (ht : 0 < t)
    (hbound : ∀ n, Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile (μ.real (A n)) + t) ≤ μ.real (D n))
    (hA0 : 0 < μ.real (⋂ n, A n)) (hA1 : μ.real (⋂ n, A n) < 1) :
    Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile (μ.real (⋂ n, A n)) + t) ≤
        μ.real (⋂ n, D n) := by
  let a : ℝ := μ.real (⋂ n, A n)
  have hAtend : Tendsto (fun n => μ.real (A n)) atTop (𝓝 a) := by
    simpa [a] using tendsto_measureReal_iInter μ A hA hAanti
  have hDtend : Tendsto (fun n => μ.real (D n)) atTop
      (𝓝 (μ.real (⋂ n, D n))) := tendsto_measureReal_iInter μ D hD hDanti
  have hqcont := BrownianSharp.standardGaussianQuantile_continuousAt hA0 hA1
  have hq : Tendsto (fun n => Concentration.standardGaussianQuantile (μ.real (A n)))
      atTop (𝓝 (Concentration.standardGaussianQuantile a)) := hqcont.tendsto.comp hAtend
  have hcdf : ContinuousAt Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile a + t) :=
    (BrownianSharp.hasDerivAt_standardGaussianCDF _).continuousAt
  have hleft : Tendsto (fun n => Concentration.standardGaussianCDF
      (Concentration.standardGaussianQuantile (μ.real (A n)) + t)) atTop
      (𝓝 (Concentration.standardGaussianCDF
        (Concentration.standardGaussianQuantile a + t))) := by
    exact hcdf.tendsto.comp (hq.add_const t)
  exact le_of_tendsto_of_tendsto hleft hDtend (Filter.Eventually.of_forall hbound)

/-- On a compact feature set of continuous functions, satisfying every finite
initial segment of a dense evaluation grid is equivalent to satisfying the
uniform tube constraint. -/
theorem finiteGridTube_iff_uniformTube
    {T : Type*} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    {x : ℕ → T} (hx : DenseRange x)
    (K : Set C(T, ℝ)) (hK : IsCompact K)
    (z : C(T, ℝ)) {t ε : ℝ} :
    (∀ n : ℕ, ∃ h ∈ K, ∀ j ≤ n,
      |z (x j) - t * h (x j)| ≤ ε) ↔
    ∃ h ∈ K, ∀ y : T, |z y - t * h y| ≤ ε := by
  constructor
  · intro hfinite
    let F : ℕ → Set C(T, ℝ) := fun n =>
      {h | h ∈ K ∧ ∀ j ≤ n, |z (x j) - t * h (x j)| ≤ ε}
    have hclosed : ∀ n, IsClosed (F n) := by
      intro n
      have hconstraints : IsClosed {h : C(T, ℝ) | ∀ j ≤ n,
          |z (x j) - t * h (x j)| ≤ ε} := by
        rw [show {h : C(T, ℝ) | ∀ j ≤ n,
            |z (x j) - t * h (x j)| ≤ ε} =
          ⋂ j : ℕ, {h : C(T, ℝ) |
            if j ≤ n then |z (x j) - t * h (x j)| ≤ ε else True} by
          ext h
          simp]
        exact isClosed_iInter fun j => by
          split_ifs
          · have hc : Continuous (fun h : C(T, ℝ) =>
                z (x j) - t * h (x j)) :=
                continuous_const.sub (continuous_const.mul (continuous_eval_const (x j)))
            exact isClosed_Iic.preimage (continuous_abs.comp hc)
          · exact isClosed_univ
      change IsClosed (K ∩ {h : C(T, ℝ) | ∀ j ≤ n,
        |z (x j) - t * h (x j)| ≤ ε})
      exact hK.isClosed.inter hconstraints
    have hnonempty : ∀ n, (F n).Nonempty := by
      intro n
      obtain ⟨h, hhK, hh⟩ := hfinite n
      exact ⟨h, hhK, hh⟩
    have hdecr : ∀ n, F (n + 1) ⊆ F n := by
      intro n h hh
      exact ⟨hh.1, fun j hj => hh.2 j (Nat.le_trans hj (Nat.le_succ n))⟩
    obtain ⟨h, hh⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      F hdecr hnonempty
      (hK.of_isClosed_subset (hclosed 0) (by intro y hy; exact hy.1)) hclosed
    have hhK : h ∈ K := (mem_iInter.mp hh 0).1
    have hhgrid : ∀ j, |z (x j) - t * h (x j)| ≤ ε := by
      intro j
      exact (mem_iInter.mp hh j).2 j le_rfl
    have hclosedTube : IsClosed {y : T | |z y - t * h y| ≤ ε} := by
      have hc : Continuous (fun y : T => z y - t * h y) :=
        z.continuous.sub (continuous_const.mul h.continuous)
      change IsClosed ((fun y : T => |z y - t * h y|) ⁻¹' Set.Iic ε)
      exact isClosed_Iic.preimage (continuous_abs.comp hc)
    have hgridSub : Set.range x ⊆ {y : T | |z y - t * h y| ≤ ε} := by
      rintro y ⟨j, rfl⟩
      exact hhgrid j
    have hwhole := closure_minimal hgridSub hclosedTube
    have hrangeDense : closure (Set.range x) = Set.univ := hx.closure_eq
    refine ⟨h, hhK, ?_⟩
    intro y
    have hycl : y ∈ closure (Set.range x) := by rw [hrangeDense]; exact mem_univ y
    exact hwhole hycl
  · rintro ⟨h, hhK, hh⟩ n
    exact ⟨h, hhK, fun j _ => hh (x j)⟩

/-- The event that a path lies within `ε` on a finite grid of a scaled compact
set of paths is closed. This supplies the measurability needed for continuity
from above in the path-level dilation argument. -/
theorem finiteGridTubeSet_isClosed
    {T : Type*} [TopologicalSpace T] {N : ℕ}
    (x : Fin N → T) (K : Set C(T, ℝ)) (hK : IsCompact K)
    (t ε : ℝ) :
    IsClosed {f : C(T, ℝ) | ∃ h ∈ K, ∀ i,
      |f (x i) - t * h (x i)| ≤ ε} := by
  classical
  let Q : Set (Fin N → ℝ) := Set.univ.pi (fun _ => Set.Icc (-ε) ε)
  let G : C(T, ℝ) × (Fin N → ℝ) → (Fin N → ℝ) :=
    fun p i => t * p.1 (x i) + p.2 i
  have hQ : IsCompact Q := by
    exact isCompact_univ_pi fun _ => isCompact_Icc
  have hGcont : Continuous G := by
    refine continuous_pi fun i => ?_
    have hc : Continuous (fun p : C(T, ℝ) × (Fin N → ℝ) =>
        t * p.1 (x i)) :=
      continuous_const.mul ((continuous_eval_const (x i)).comp continuous_fst)
    convert hc.add ((continuous_apply i).comp continuous_snd) using 1 <;> ext p <;> rfl
  have hImage : IsCompact (G '' (K ×ˢ Q)) := (hK.prod hQ).image hGcont
  have hclosedImage : IsClosed (G '' (K ×ˢ Q)) := hImage.isClosed
  let ev : C(T, ℝ) → (Fin N → ℝ) := fun f i => f (x i)
  have hevCont : Continuous ev := by
    exact continuous_pi fun i => continuous_eval_const (x i)
  have heq : {f : C(T, ℝ) | ∃ h ∈ K, ∀ i,
      |f (x i) - t * h (x i)| ≤ ε} = ev ⁻¹' (G '' (K ×ˢ Q)) := by
    ext f
    constructor
    · rintro ⟨h, hhK, hh⟩
      let q : Fin N → ℝ := fun i => f (x i) - t * h (x i)
      have hq : q ∈ Q := by
        intro i _
        have := abs_le.mp (hh i)
        exact ⟨this.1, this.2⟩
      refine ⟨(h, q), ?_, ?_⟩
      · exact Set.mk_mem_prod hhK hq
      · funext i
        dsimp [G, ev, q]
        ring
    · rintro ⟨p, hp, hEq⟩
      rcases Set.mem_prod.mp hp with ⟨hpK, hpQ⟩
      refine ⟨p.1, hpK, ?_⟩
      intro i
      have hqi : p.2 i ∈ Set.Icc (-ε) ε := (Set.mem_pi.mp hpQ) i (Set.mem_univ i)
      have hEval : f (x i) - t * p.1 (x i) = p.2 i := by
        have hi := congrFun hEq.symm i
        change ev f i = G p i at hi
        dsimp [ev, G] at hi
        linarith
      rw [hEval]
      exact abs_le.mpr hqi
      /-
      have hEval : G p i - t * p.1 (x i) = p.2 i := by
        simp [G]
        ring
      rw [show ev (G p) i = G p i by rfl, hEval]
      exact abs_le.mpr hqi
      -/
  rw [heq]
  exact hclosedImage.preimage hevCont

end BrownianSharp.AlignmentPaperGaussianDilationLimit
