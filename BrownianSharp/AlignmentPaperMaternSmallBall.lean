import BrownianSharp.AlignmentPaperGaussianFeatureBridge
import BrownianSharp.AlignmentGaussianFeatureShift
import BrownianSharp.AlignmentGaussianGridLimit
import BrownianSharp.AlignmentGaussianEntropySmallBall
import BrownianSharp.AlignmentPaperQuantization
import BrownianSharp.BrownianSheetOnCube
import BrownianSharp.AlignmentMaternScalarFeature
import BrownianSharp.AlignmentMaternContinuousFeature
import BrownianSharp.AlignmentMaternSpectralFeature
import BrownianSharp.AlignmentMaternTensorFeature
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! Actual-realization Matérn small-ball lower bound.

The shift inequality is proved on finite evaluation grids from the Gaussian
Gram matrix and then passed to the uniform path norm.  The entropy input is
the raw spectral Matérn feature entropy bound transferred to the intrinsic
closed span of the evaluation variables.
-/

noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperMaternSmallBall

open BrownianSharp.AlignmentCompactFeatureBall
open BrownianSharp.AlignmentGaussianFeatureShift
open BrownianSharp.AlignmentGaussianGridLimit
open BrownianSharp.AlignmentGaussianEntropySmallBall
open BrownianSharp.AlignmentPaperGaussianFeatureBridge
open BrownianSharp.AlignmentPaperMatern
open BrownianSharp.AlignmentMaternTensorFeature
open BrownianSharp
open BrownianSharp.AlignmentMaternSpectralFeature
open BrownianSharp.AlignmentMaternContinuousFeature
open HaarQuarter

private def cubeCorner (d : ℕ) : BrownianCubeAnchor d :=
  ⟨fun _ => 1, fun _ => ⟨by norm_num, by norm_num⟩⟩

private def finiteGridEquiv {J : Type*} [Fintype J] :
    (↥(Finset.univ : Finset J)) ≃ J :=
  { toFun := fun i => i.1
    invFun := fun j => ⟨j, Finset.mem_univ j⟩
    left_inv := by intro i; apply Subtype.ext; rfl
    right_inv := by intro j; rfl }

private theorem gaussian_grid_law
    {α Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : α → Ω → ℝ) (hX : IsGaussianProcess X P)
    (x : J → α) : HasGaussianLaw (fun ω j => X (x j) ω) P := by
  let hp := hX.comp_right x
  have hr := hp.hasGaussianLaw Finset.univ
  let R : ((↥(Finset.univ : Finset J)) → ℝ) ≃L[ℝ] (J → ℝ) :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : J => ℝ) finiteGridEquiv
  have heq : (fun ω j => X (x j) ω) =
      (fun ω => R (fun i => X (x i.1) ω)) := by
    funext ω j
    rfl
  rw [heq]
  exact hr.map_equiv R

/-- A continuous centered Gaussian path with a continuous Hilbert feature
Gram kernel satisfies the actual Cameron--Martin translation inequality.
The finite-dimensional step uses its genuine Gaussian evaluation vectors;
compactness then closes the inequality for the sup norm.
-/
theorem featurePathLaw_ball_shift_lower
    {α Ω H : Type*} [MetricSpace α] [CompactSpace α] [Nonempty α]
    [SecondCountableTopology α] [LocallyCompactSpace α]
    [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
    (K : C(α, H)) (a : α) (ha : K a ≠ 0)
    (hcov : ∀ x y, cov[fun ω => F ω x, fun ω => F ω y; P] = inner ℝ (K x) (K y))
    (R ε : ℝ) (hR : 0 < R) (hε : 0 < ε)
    (f : C(α, ℝ)) (hf : f ∈ featureBall K) :
    ENNReal.ofReal (Real.exp (-(R^2)/2)) *
        (P.map F) (Metric.closedBall 0 ε) ≤
      (P.map F) (Metric.closedBall (R • f) ε) := by
  classical
  rcases hf with ⟨g, hg, hfg⟩
  have hnorm : ‖R • g‖ ^ 2 ≤ R ^ 2 := by
    have hgn : ‖g‖ ≤ 1 := hg
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    nlinarith [sq_nonneg (R * (1 - ‖g‖)), norm_nonneg g]
  have hfactor : ENNReal.ofReal (Real.exp (-(R^2)/2)) ≤
      ENNReal.ofReal (Real.exp (-‖R • g‖^2/2)) := by
    apply ENNReal.ofReal_le_ofReal
    exact Real.exp_le_exp.mpr (by nlinarith [hnorm])
  let points : ℕ → α := TopologicalSpace.denseSeq α
  have hdense : DenseRange points := TopologicalSpace.denseRange_denseSeq α
  have hcoord : ∀ t, Measurable (fun ω => F ω t) :=
    fun t => (ContinuousMap.measurable_eval t).comp hF
  have hfinite : ∀ S : Finset α,
      ENNReal.ofReal (Real.exp (-(R^2)/2)) *
        P {ω | ∀ t ∈ S, |F ω t| ≤ ε} ≤
      P {ω | ∀ t ∈ S, |F ω t - (R • f) t| ≤ ε} := by
    intro S
    let J := {t : α // t ∈ S}
    let Y : Ω → J → ℝ := fun ω t => F ω t.1
    let w : J → H := fun t => K t.1
    let e' : Fin 1 → H := fun _ => ‖K a‖⁻¹ • K a
    have he' : ∀ i j, ⟪e' i, e' j⟫ = if i = j then 1 else 0 := by
      intro i j
      have hij : i = j := Subsingleton.elim _ _
      subst j
      have hn : ‖K a‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr ha)
      have hnorm : ‖e' 0‖ = 1 := by
        change ‖‖K a‖⁻¹ • K a‖ = 1
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr ha))]
        field_simp [hn]
      have hii : i = 0 := Subsingleton.elim _ _
      subst i
      rw [if_pos rfl, real_inner_self_eq_norm_sq, hnorm]
      norm_num
    have hY : HasGaussianLaw (fun ω t => Y ω t) P :=
      gaussian_grid_law (fun x ω => F ω x) hX Subtype.val
    have hmy : ∀ t, ∫ ω, Y ω t ∂P = 0 := fun t => hmean t.1
    have hcy : ∀ s t, covariance (fun ω => Y ω s) (fun ω => Y ω t) P = ⟪w s, w t⟫ := by
      intro s t
      simpa [Y, w] using hcov s.1 t.1
    have hlocal := finiteGaussian_gram_shift_lower Y e' w hY hmy hcy he' (R • g) ε
    have hlocalShift : ∀ t : J, ⟪w t, R • g⟫ = (R • f) t.1 := by
      intro t
      rw [inner_smul_right]
      change R * ⟪K t.1, g⟫ = R * f t.1
      have hp := congrArg (fun q : C(α, ℝ) => q t.1) hfg
      simpa [featurePath, real_inner_comm] using congrArg (fun z : ℝ => R * z) hp
    have hlocalNorm : ‖R • g‖ ^ 2 ≤ R ^ 2 := hnorm
    have hlocalFactor : ENNReal.ofReal (Real.exp (-(R^2)/2)) ≤
        ENNReal.ofReal (Real.exp (-‖R • g‖^2/2)) := hfactor
    have heq0 : {ω | ∀ t : J, |Y ω t| ≤ ε} = {ω | ∀ t ∈ S, |F ω t| ≤ ε} := by
      ext ω
      constructor
      · intro h t ht
        exact h ⟨t, ht⟩
      · intro h t
        exact h t.1 t.2
    have heq1 : {ω | ∀ t : J, |Y ω t - ⟪w t, R • g⟫| ≤ ε} =
        {ω | ∀ t ∈ S, |F ω t - (R • f) t| ≤ ε} := by
      ext ω
      constructor
      · intro h t ht
        simpa [Y, hlocalShift] using h ⟨t, ht⟩
      · intro h t
        simpa [Y, hlocalShift] using h t.1 t.2
    rw [heq0, heq1] at hlocal
    calc
      ENNReal.ofReal (Real.exp (-(R^2)/2)) *
          P {ω | ∀ t ∈ S, |F ω t| ≤ ε} ≤
        ENNReal.ofReal (Real.exp (-‖R • g‖^2/2)) *
          P {ω | ∀ t ∈ S, |F ω t| ≤ ε} :=
        mul_le_mul_of_nonneg_right hlocalFactor (by positivity)
      _ ≤ P {ω | ∀ t ∈ S, |F ω t - (R • f) t| ≤ ε} := hlocal
  have hgridAll := finite_grid_mass_lower_to_uniform_mass_lower P points hdense
    F hcoord (R • f) ε hε.le (ENNReal.ofReal (Real.exp (-(R^2)/2))) hfinite
  have hmass0 : P {ω | ‖F ω‖ ≤ ε} = (P.map F) (Metric.closedBall 0 ε) := by
    symm
    rw [Measure.map_apply hF measurableSet_closedBall]
    congr 1
  have hmassx : P {ω | ‖F ω - (R • f)‖ ≤ ε} =
      (P.map F) (Metric.closedBall (R • f) ε) := by
    symm
    rw [Measure.map_apply hF measurableSet_closedBall]
    congr 1
    ext ω
    simp [Metric.mem_closedBall, dist_eq_norm]
  simpa only [hmass0, hmassx] using hgridAll

/-- Every centered Gaussian path law has positive mass in each centered
closed ball. A support point gives positive mass to a nearby ball, and the
independent-copy difference inequality transfers this to a centered ball. -/
theorem centered_path_closedBall_pos
    {α Ω : Type*} [TopologicalSpace α] [CompactSpace α]
    [SecondCountableTopology α] [LocallyCompactSpace α]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
    (ε : ℝ) (hε : 0 < ε) :
    0 < (P.map F).real (Metric.closedBall 0 ε) := by
  let μ := P.map F
  have hμne : μ ≠ 0 := by
    intro hz
    have := congrArg (fun ν : Measure C(α, ℝ) => ν Set.univ) hz
    simp [μ] at this
  obtain ⟨a, ha⟩ := μ.nonempty_support hμne
  let t := ε / (2 * Real.sqrt 2)
  have ht : 0 < t := by dsimp [t]; positivity
  have hnear : 0 < μ (Metric.ball a t) := by
    apply (Measure.mem_support_iff_forall a).mp ha (Metric.ball a t)
    exact Metric.ball_mem_nhds _ ht
  have hclosed : 0 < μ (Metric.closedBall a t) :=
    lt_of_lt_of_le hnear (measure_mono Metric.ball_subset_closedBall)
  have hsym := centered_gaussian_translated_ball_mass_sq_le F hF hX hmean a t ht.le
  have hsqrt : Real.sqrt 2 * t ≤ ε := by
    dsimp [t]
    have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    field_simp
    nlinarith [Real.sq_sqrt (show 0 ≤ (2:ℝ) by norm_num)]
  have hpow : 0 < μ (Metric.closedBall a t) ^ 2 := by
    rw [pow_two]
    exact ENNReal.mul_pos hclosed.ne' hclosed.ne'
  have hposSmall : 0 < μ (Metric.closedBall 0 (Real.sqrt 2 * t)) :=
    lt_of_lt_of_le hpow hsym
  have hsubset : Metric.closedBall (0 : C(α, ℝ)) (Real.sqrt 2 * t) ⊆
      Metric.closedBall 0 ε := Metric.closedBall_subset_closedBall hsqrt
  have hmono : μ (Metric.closedBall 0 (Real.sqrt 2 * t)) ≤
      μ (Metric.closedBall 0 ε) := measure_mono hsubset
  have hpos : 0 < μ (Metric.closedBall 0 ε) := lt_of_lt_of_le hposSmall hmono
  change 0 < ((P.map F) (Metric.closedBall 0 ε)).toReal
  exact ENNReal.toReal_pos hpos.ne' (measure_ne_top (P.map F) _)

/-- The raw tensor Matérn covariance has the paper's small-ball lower rate
for every centered continuous Gaussian realization with that covariance.
The exponent simplifies to `d - 1 + d/(2h)`. -/
theorem maternRawSpectral_actual_path_smallBall_lowerLog
    {d : ℕ} (hd : 2 ≤ d) (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(BrownianCubeAnchor d, ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
    (hcov : ∀ x y, cov[fun ω => F ω x, fun ω => F ω y; P] =
      ∏ i, c i * BrownianSharp.AlignmentMaternSpectralFeature.stationaryCovariance
        (κ i) h (x.val i) (y.val i)) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
        C * Latest.smallBallRate (h⁻¹) (d - 1 + (d : ℝ) / (2*h)) ε ≤
          -Real.log ((P.map F).real (Metric.closedBall 0 ε)) := by
  let X : BrownianCubeAnchor d → Ω → ℝ := fun x ω => F ω x
  let K := maternSheetFeatureWithSpectralAmplitude κ c h hκ hc hh
  have hmem : ∀ x, MemLp (X x) 2 P := fun x => (hX.hasGaussianLaw_eval x).memLp_two
  have hgram : ∀ x y, cov[X x, X y; P] = inner ℝ (K x) (K y) := by
    intro x y
    rw [maternSheetFeatureWithSpectralAmplitude_gram]
    exact hcov x y
  have hcorner : K (cubeCorner d) ≠ 0 := by
    intro hz
    have hnorm := congrArg norm hz
    have hfeature := maternSheetFeature_norm κ h (by assumption) hh (cubeCorner d)
    have hP : 0 < ∏ i : Fin d, c i * BrownianSharp.AlignmentMaternContinuousFeature.spectralMass (κ i) h :=
      Finset.prod_pos (fun i _ => mul_pos (hc i)
        (BrownianSharp.AlignmentMaternContinuousFeature.spectralMass_pos
          (κ i) h (hκ i) hh))
    have hscale : ‖K (cubeCorner d)‖ = Real.sqrt
        (∏ i : Fin d, c i * BrownianSharp.AlignmentMaternContinuousFeature.spectralMass (κ i) h) := by
      simp [K, maternSheetFeatureWithSpectralAmplitude, norm_smul,
        Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hP), hfeature]
    rw [hscale] at hnorm
    have hzero : Real.sqrt
        (∏ i : Fin d, c i * BrownianSharp.AlignmentMaternContinuousFeature.spectralMass (κ i) h) = 0 :=
      by simpa using hnorm
    exact (ne_of_gt (Real.sqrt_pos.mpr hP)) hzero
  have hball : intrinsicGaussianCMUnitBall X hmem = featureBall K :=
    maternRawSpectral_intrinsicCM_ball_eq_featureBall κ c h hκ hc hh X hmem hmean hcov
  have hshift : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      ∀ f ∈ intrinsicGaussianCMUnitBall X hmem,
        ENNReal.ofReal (Real.exp (-(R^2)/2)) *
          (P.map F) (Metric.closedBall 0 ε) ≤
          (P.map F) (Metric.closedBall (R • f) ε) := by
    intro R hR ε hε f hf
    have hf' : f ∈ featureBall K := by simpa [hball] using hf
    exact featurePathLaw_ball_shift_lower F hF hX hmean K (cubeCorner d) hcorner
      hgram R ε hR hε f hf'
  have hEntropy := maternRawSpectral_intrinsicCM_entropy_lower hd κ c h hκ hc hh
    X hmem hmean hcov
  have hr : 1/2 < h + 1/2 := by linarith
  have ha : 0 ≤ (h + 1/2) * (d - 1 : ℕ) + 1/2 := by positivity
  have hpositive : ∀ ε : ℝ, 0 < ε →
      0 < (P.map F).real (Metric.closedBall 0 ε) :=
    centered_path_closedBall_pos F hF hX hmean
  rcases hEntropy with ⟨cE, hcE, k₀, hk₀, hE⟩
  have hEntropy' : ∃ cE : ℝ, 0 < cE ∧ ∃ n₀ : ℕ, ∀ k, n₀ ≤ k →
      ENNReal.ofReal (cE * BrownianSharp.logarithmicIndexRate (h + 1/2)
        ((h + 1/2) * (d - 1 : ℕ) + 1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k (intrinsicGaussianCMUnitBall X hmem) :=
    ⟨cE, hcE, k₀, fun k hk => hE k hk⟩
  have hresult := smallBall_lowerLog_of_entropy_lower (P.map F)
    (intrinsicGaussianCMUnitBall X hmem) (h + 1/2)
    ((h + 1/2) * (d - 1 : ℕ) + 1/2) hr ha hEntropy' hshift hpositive
  rcases hresult with ⟨C, ε₀, hC, hε₀, hε₀', hbound⟩
  refine ⟨C, ε₀, hC, hε₀, hε₀', ?_⟩
  intro ε hε hsmall
  have hb := hbound ε hε hsmall
  have hexp : (h + 1/2 - 1/2)⁻¹ = h⁻¹ := by congr 1 <;> ring
  have hlog : (((h + 1/2) * (d - 1 : ℕ) + 1/2) / h) =
      d - 1 + (d : ℝ) / (2*h) := by
    have hdreal : (d : ℝ) = (d - 1 : ℕ) + 1 := by
      have hn : d - 1 + 1 = d := Nat.sub_add_cancel (by omega : 1 ≤ d)
      exact_mod_cast hn.symm
    change (((h + 1/2) * (d - 1 : ℕ) + 1/2) / h) =
      (d : ℝ) - 1 + (d : ℝ) / (2*h)
    rw [hdreal]
    field_simp
    ring
  rw [Latest.smallBallRate] at hb ⊢
  rw [hexp] at hb
  rw [show h + 1/2 - 1/2 = h by ring] at hb
  rw [hlog] at hb
  exact hb

end BrownianSharp.AlignmentPaperMaternSmallBall
