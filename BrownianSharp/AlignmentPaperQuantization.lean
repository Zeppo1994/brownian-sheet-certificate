import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Integral.MeanInequalities
import BrownianSharp.AlignmentPaperGaussianFeatureBridge
import BrownianSharp.AlignmentGaussianRates
import BrownianSharp.AlignmentGaussianBrownianReverse
import BrownianSharp.AlignmentGaussianBochner
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

/-!
# Functional quantization primitives and lower-tail bounds

This file formalizes finite-codebook distortion and transport costs for laws on
measurable metric spaces. It does not by itself establish the empirical
Wasserstein upper theorem or any sheet-specific rate.
-/

open MeasureTheory
open ProbabilityTheory
open scoped NNReal ENNReal

namespace BrownianSharp

/-- Order-theoretic nonnegative square root on extended nonnegative reals. -/
noncomputable def ennrealSqrt (x : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.rpow x (1 / 2 : ℝ)

/-- A coupling of two measures on one measurable space, represented by a
measure on the product with the prescribed marginals. -/
structure TransportCoupling {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) where
  measure : Measure (X × X)
  fst_map : Measure.map Prod.fst measure = μ
  snd_map : Measure.map Prod.snd measure = ν

/-- The empirical probability measure of a nonempty finite sample. -/
noncomputable def empiricalMeasure {X : Type*} [MeasurableSpace X]
    (m : ℕ) (hm : 0 < m) (x : Fin m → X) : Measure X :=
  Measure.sum (fun i : Fin m => ((m : ℝ≥0)⁻¹) • Measure.dirac (x i))

/-- The empirical measure has total mass one. -/
theorem empiricalMeasure_isProbability {X : Type*} [MeasurableSpace X]
    (m : ℕ) (hm : 0 < m) (x : Fin m → X) :
    IsProbabilityMeasure (empiricalMeasure m hm x) := by
  constructor
  have hmcast : (m : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp [empiricalMeasure, Measure.sum_apply, Measure.smul_apply]
  exact_mod_cast (mul_inv_cancel₀ hmcast)

/-- Every empirical measure is supported on the range of its sample. -/
theorem empiricalMeasure_supported {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X] [MeasurableSingletonClass X]
    (m : ℕ) (hm : 0 < m) (x : Fin m → X) :
    empiricalMeasure m hm x {y | y ∉ Set.range x} = 0 := by
  have hrange : MeasurableSet (Set.range x)ᶜ :=
    (Set.Finite.measurableSet (Set.finite_range x)).compl
  simp [empiricalMeasure, Measure.sum_apply, Measure.smul_apply,
    Set.mem_range, hrange]

/-- The quadratic transport cost of a coupling. -/
noncomputable def couplingCostTwo {X : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace X] {μ ν : Measure X} (γ : TransportCoupling μ ν) : ℝ≥0∞ :=
  ennrealSqrt (∫⁻ z, edist z.1 z.2 ^ 2 ∂γ.measure)

/-- Wasserstein-two distance, defined as the infimum of quadratic costs over
all couplings. -/
noncomputable def wassersteinTwo {X : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace X] (μ ν : Measure X) : ℝ≥0∞ :=
  ⨅ γ : TransportCoupling μ ν, couplingCostTwo γ

/-- Distance from a point to a finite nonempty codebook, as an attained finite
infimum in extended nonnegative reals. -/
noncomputable def finiteCodebookDistortion {X : Type*} [PseudoEMetricSpace X]
    {m : ℕ} (hm : 0 < m) (c : Fin m → X) (x : X) : ℝ≥0∞ :=
  (Finset.univ : Finset (Fin m)).inf' (by
    exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
    (fun i => edist x (c i))

/-- First-order optimal finite-codebook quantization cost. The codebook has
`m` deterministic representatives. -/
noncomputable def quantizationQ1 {X : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace X] (μ : Measure X) (m : ℕ) (hm : 0 < m) : ℝ≥0∞ :=
  ⨅ c : Fin m → X, ∫⁻ x, finiteCodebookDistortion hm c x ∂μ

/-- Second-order optimal finite-codebook quantization cost. -/
noncomputable def quantizationQ2 {X : Type*} [MeasurableSpace X]
    [PseudoEMetricSpace X] (μ : Measure X) (m : ℕ) (hm : 0 < m) : ℝ≥0∞ :=
  ⨅ c : Fin m → X,
    ennrealSqrt (∫⁻ x, finiteCodebookDistortion hm c x ^ 2 ∂μ)

/-- For a probability law, the first-order codebook cost is bounded above
by the second-order codebook cost. -/
theorem quantizationQ1_le_Q2
    {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (hmeas : ∀ c : Fin m → X, Measurable (fun x => finiteCodebookDistortion hm c x)) :
    quantizationQ1 μ m hm ≤ quantizationQ2 μ m hm := by
  unfold quantizationQ1 quantizationQ2
  apply iInf_mono
  intro c
  have h := ENNReal.lintegral_mul_rpow_le_lintegral_rpow_mul_lintegral_rpow
    (μ := μ) Real.HolderConjugate.two_two (hmeas c).aemeasurable
    (measurable_const : Measurable (fun _ : X => (1 : ℝ≥0∞))).aemeasurable
  simpa [ennrealSqrt, ENNReal.rpow_one] using h

/-- If the second marginal of a transport coupling is supported on a finite
codebook, nearest-codebook distortion is bounded by that coupling's distance
cost. This is the coupling direction needed for empirical measures. -/
theorem codebookCost_le_couplingCostTwo
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [PseudoMetricSpace X]
    [MeasurableSingletonClass X]
    {μ ν : Measure X} (γ : TransportCoupling μ ν)
    (m : ℕ) (hm : 0 < m) (c : Fin m → X)
    (hsupp : ν {y | y ∉ Set.range c} = 0)
    (hD : Measurable (fun x => finiteCodebookDistortion hm c x)) :
    ennrealSqrt (∫⁻ x, finiteCodebookDistortion hm c x ^ 2 ∂μ) ≤
      couplingCostTwo γ := by
  let S : Set (X × X) := {z | z.2 ∉ Set.range c}
  have hRangeCompl : MeasurableSet (Set.range c)ᶜ :=
    (Set.Finite.measurableSet (Set.finite_range c)).compl
  have hS : MeasurableSet S := by
    exact measurable_snd hRangeCompl
  have hSzero : γ.measure S = 0 := by
    change γ.measure (Prod.snd ⁻¹' (Set.range c)ᶜ) = 0
    have htemp : (Measure.map Prod.snd γ.measure) (Set.range c)ᶜ =
        ν (Set.range c)ᶜ := by rw [γ.snd_map]
    rw [Measure.map_apply measurable_snd hRangeCompl] at htemp
    rw [htemp]
    exact hsupp
  have hgood : ∀ᵐ z ∂γ.measure, z.2 ∈ Set.range c := by
    rw [ae_iff]
    simpa [S] using hSzero
  have hpoint : ∀ᵐ z ∂γ.measure,
      finiteCodebookDistortion hm c z.1 ^ 2 ≤ edist z.1 z.2 ^ 2 := by
    filter_upwards [hgood] with z hz
    obtain ⟨i, hEq⟩ := hz
    have hle : finiteCodebookDistortion hm c z.1 ≤ edist z.1 (c i) := by
      simp only [finiteCodebookDistortion]
      exact Finset.inf'_le _ (Finset.mem_univ i)
    calc
      finiteCodebookDistortion hm c z.1 ^ 2 ≤ edist z.1 (c i) ^ 2 :=
        pow_le_pow_left₀ bot_le hle 2
      _ = edist z.1 z.2 ^ 2 := by rw [hEq]
  have hcost : (∫⁻ x, finiteCodebookDistortion hm c x ^ 2 ∂μ) ≤
      ∫⁻ z, edist z.1 z.2 ^ 2 ∂γ.measure := by
    calc
      (∫⁻ x, finiteCodebookDistortion hm c x ^ 2 ∂μ) =
          ∫⁻ x, finiteCodebookDistortion hm c x ^ 2 ∂Measure.map Prod.fst γ.measure := by
        rw [γ.fst_map]
      _ = ∫⁻ z, finiteCodebookDistortion hm c z.1 ^ 2 ∂γ.measure :=
        lintegral_map (hD.pow_const 2) measurable_fst
      _ ≤ ∫⁻ z, edist z.1 z.2 ^ 2 ∂γ.measure := lintegral_mono_ae hpoint
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : 0 < (1 / 2 : ℝ))).2
  simpa [couplingCostTwo, ennrealSqrt] using hcost

/-- Quantization by `m` points never exceeds transport to a law supported on
those points. In particular this gives qₘ,₂ ≤ W₂(μ, empiricalMeasure). -/
theorem quantizationQ2_le_wassersteinTwo_of_supported
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X] [PseudoMetricSpace X]
    [MeasurableSingletonClass X]
    (μ ν : Measure X) (m : ℕ) (hm : 0 < m) (c : Fin m → X)
    (hsupp : ν {y | y ∉ Set.range c} = 0)
    (hmeas : Measurable (fun x => finiteCodebookDistortion hm c x)) :
    quantizationQ2 μ m hm ≤ wassersteinTwo μ ν := by
  unfold wassersteinTwo
  apply le_iInf
  intro γ
  calc
    quantizationQ2 μ m hm ≤
        ennrealSqrt (∫⁻ x, finiteCodebookDistortion hm c x ^ 2 ∂μ) :=
      iInf_le _ c
    _ ≤ couplingCostTwo γ := codebookCost_le_couplingCostTwo γ m hm c hsupp hmeas

/-- The paper's deterministic-to-empirical comparison: first-order optimal
quantization is bounded by second-order quantization, which is bounded by
transport to the empirical measure of any `m`-sample. -/
theorem quantizationQ1_le_Q2_le_empiricalWassersteinTwo
    {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [BorelSpace X]
    [PseudoMetricSpace X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (x : Fin m → X)
    (hmeas : ∀ c : Fin m → X, Measurable (fun y => finiteCodebookDistortion hm c y)) :
    quantizationQ1 μ m hm ≤ quantizationQ2 μ m hm ∧
      quantizationQ2 μ m hm ≤ wassersteinTwo μ (empiricalMeasure m hm x) := by
  constructor
  · exact quantizationQ1_le_Q2 μ m hm hmeas
  · exact quantizationQ2_le_wassersteinTwo_of_supported μ
      (empiricalMeasure m hm x) m hm x (empiricalMeasure_supported m hm x) (hmeas x)

/-- Independent-copy symmetrization: if the normalized difference of two
independent samples has the original law, then every translated ball has mass
squared bounded by the centred ball at radius `√2` times as large. -/
theorem translatedBall_mass_sq_le_of_normalized_difference_law
    {X : Type*} [MeasurableSpace X] [NormedAddCommGroup X] [NormedSpace ℝ X]
    [SecondCountableTopology X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hdiff : Measure.map
      (fun z : X × X => (Real.sqrt 2)⁻¹ • (z.1 - z.2)) (μ.prod μ) = μ)
    (c : X) (t : ℝ) (ht : 0 ≤ t) :
    μ (Metric.closedBall c t) ^ 2 ≤
      μ (Metric.closedBall 0 (Real.sqrt 2 * t)) := by
  let A : Set X := Metric.closedBall c t
  let T : Set X := Metric.closedBall 0 (Real.sqrt 2 * t)
  let δ : X × X → X := fun z => (Real.sqrt 2)⁻¹ • (z.1 - z.2)
  have hA : MeasurableSet A := Metric.isClosed_closedBall.measurableSet
  have hT : MeasurableSet T := Metric.isClosed_closedBall.measurableSet
  have hδ : Measurable δ := by
    have hδc : Continuous δ := by
      change Continuous (fun z : X × X => (Real.sqrt 2)⁻¹ • (z.1 - z.2))
      exact continuous_const.smul (continuous_fst.sub continuous_snd)
    exact hδc.measurable
  have hsubset : A ×ˢ A ⊆ δ ⁻¹' T := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hxy : dist x y ≤ 2 * t := by
      calc
        dist x y ≤ dist x c + dist c y := dist_triangle x c y
        _ ≤ t + t := add_le_add hx (by simpa [A, Metric.mem_closedBall, dist_comm] using hy)
        _ = 2 * t := by ring
    have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hrootSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hfac : (Real.sqrt 2)⁻¹ * 2 = Real.sqrt 2 := by
      field_simp [ne_of_gt hroot]
      nlinarith [hrootSq]
    have hnorm : dist (δ (x, y)) 0 ≤ Real.sqrt 2 * t := by
      change dist ((Real.sqrt 2)⁻¹ • (x - y)) 0 ≤ Real.sqrt 2 * t
      rw [dist_eq_norm, sub_zero]
      change ‖(Real.sqrt 2)⁻¹ • (x - y)‖ ≤ Real.sqrt 2 * t
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hroot)]
      have hdistNorm : ‖x - y‖ = dist x y := by rw [dist_eq_norm, norm_sub_rev]
      rw [hdistNorm]
      calc
        (Real.sqrt 2)⁻¹ * dist x y ≤ (Real.sqrt 2)⁻¹ * (2 * t) :=
          mul_le_mul_of_nonneg_left hxy (by positivity)
        _ = Real.sqrt 2 * t := by rw [← mul_assoc, hfac]
    simpa [T, Metric.mem_closedBall, dist_comm] using hnorm
  have hmap : μ T = (μ.prod μ) (δ ⁻¹' T) := by
    calc
      μ T = (Measure.map (fun z : X × X => (Real.sqrt 2)⁻¹ • (z.1 - z.2))
          (μ.prod μ)) T := by rw [hdiff]
      _ = (μ.prod μ) (δ ⁻¹' T) := by
        rw [Measure.map_apply hδ hT]
  calc
    μ A ^ 2 = (μ.prod μ) (A ×ˢ A) := by
      rw [MeasureTheory.Measure.prod_prod A A]
      simp [pow_two]
    _ ≤ (μ.prod μ) (δ ⁻¹' T) := measure_mono hsubset
    _ = μ T := hmap.symm

/-- The normalized difference of two independent copies of a centered
Gaussian continuous field has the original path law. The finite-dimensional
Gaussianity is proved from independence of the two coordinate copies; the
path-law equality then follows from covariance uniqueness. -/
theorem normalized_copy_difference_path_law
    {α Ω : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [LocallyCompactSpace α] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α, ℝ)) (hF : Measurable F)
    (hX : ProbabilityTheory.IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0) :
    Measure.map (fun z : C(α, ℝ) × C(α, ℝ) =>
      (Real.sqrt 2)⁻¹ • (z.1 - z.2)) ((P.map F).prod (P.map F)) = P.map F := by
  let R : Measure (Ω × Ω) := P.prod P
  let G : Ω × Ω → C(α, ℝ) := fun z =>
    (Real.sqrt 2)⁻¹ • (F z.1 - F z.2)
  have hR : IsProbabilityMeasure R := by
    constructor
    simp [R]
  have hGmeas : Measurable G := by
    fun_prop
  have hGproc : ProbabilityTheory.IsGaussianProcess (fun x z => G z x) R := by
    constructor
    intro I
    let V := I → ℝ
    let A : Ω → V := fun ω i => F ω i.1
    have hAmeas : Measurable A := by
      apply measurable_pi_iff.mpr
      intro i
      exact (ContinuousMap.measurable_eval i.1).comp hF
    have hA : HasGaussianLaw (fun z : Ω × Ω => A z.1) R := by
      refine ⟨by fun_prop, ?_⟩
      have hmap : R.map (fun z : Ω × Ω => A z.1) = P.map A := by
        dsimp [R]
        change R.map (A ∘ Prod.fst) = P.map A
        rw [← Measure.map_map hAmeas measurable_fst, Measure.map_fst_prod,
          measure_univ, one_smul]
      rw [hmap]
      exact (hX.hasGaussianLaw I).isGaussian_map
    have hB : HasGaussianLaw (fun z : Ω × Ω => A z.2) R := by
      refine ⟨by fun_prop, ?_⟩
      have hmap : R.map (fun z : Ω × Ω => A z.2) = P.map A := by
        dsimp [R]
        change R.map (A ∘ Prod.snd) = P.map A
        rw [← Measure.map_map hAmeas measurable_snd, Measure.map_snd_prod,
          measure_univ, one_smul]
      rw [hmap]
      exact (hX.hasGaussianLaw I).isGaussian_map
    have hAB : ProbabilityTheory.IndepFun (fun z : Ω × Ω => A z.1)
        (fun z : Ω × Ω => A z.2) R := by
      exact ProbabilityTheory.indepFun_prod hAmeas hAmeas
    have hsub := (hAB.hasGaussianLaw hA hB).fun_sub
    have hscaled := hsub.fun_smul ((Real.sqrt 2)⁻¹)
    change HasGaussianLaw
      (fun z : Ω × Ω => I.restrict (fun x => G z x)) R
    convert hscaled using 1 <;> ext i <;> simp [G, A, V, Finset.restrict_def]
  have hfst : R.map Prod.fst = P := by simp [R]
  have hsnd : R.map Prod.snd = P := by simp [R]
  have hmeanG : ∀ x, ∫ z, G z x ∂R = 0 := by
    intro x
    have hfx : Measurable (fun ω => F ω x) :=
      (ContinuousMap.measurable_eval x).comp hF
    have hfirst : Integrable (fun z : Ω × Ω => F z.1 x) R := by
      have := (hX.hasGaussianLaw_eval x).memLp_two
      exact (this.comp_fst P).integrable (by norm_num)
    have hsecond : Integrable (fun z : Ω × Ω => F z.2 x) R := by
      have := (hX.hasGaussianLaw_eval x).memLp_two
      exact (this.comp_snd P).integrable (by norm_num)
    have hfirstMean : ∫ z : Ω × Ω, F z.1 x ∂R = ∫ ω, F ω x ∂P := by
      calc
        ∫ z : Ω × Ω, F z.1 x ∂R = ∫ ω, F ω x ∂R.map Prod.fst := by
          simpa using (integral_map measurable_fst.aemeasurable
            (by simpa [R] using hfx.aestronglyMeasurable)).symm
        _ = ∫ ω, F ω x ∂P := by rw [hfst]
    have hsecondMean : ∫ z : Ω × Ω, F z.2 x ∂R = ∫ ω, F ω x ∂P := by
      calc
        ∫ z : Ω × Ω, F z.2 x ∂R = ∫ ω, F ω x ∂R.map Prod.snd := by
          simpa using (integral_map measurable_snd.aemeasurable
            (by simpa [R] using hfx.aestronglyMeasurable)).symm
        _ = ∫ ω, F ω x ∂P := by rw [hsnd]
    simp only [G, ContinuousMap.smul_apply, ContinuousMap.sub_apply]
    rw [integral_smul, integral_sub hfirst hsecond, hfirstMean, hsecondMean, hmean x]
    simp
  have hcovG : ∀ x y, cov[fun z => G z x, fun z => G z y; R] =
      cov[fun ω => F ω x, fun ω => F ω y; P] := by
    intro x y
    have hx : MemLp (fun ω => F ω x) 2 P := (hX.hasGaussianLaw_eval x).memLp_two
    have hy : MemLp (fun ω => F ω y) 2 P := (hX.hasGaussianLaw_eval y).memLp_two
    have hxf : MemLp (fun z : Ω × Ω => F z.1 x) 2 R := hx.comp_fst P
    have hyf : MemLp (fun z : Ω × Ω => F z.1 y) 2 R := hy.comp_fst P
    have hxs : MemLp (fun z : Ω × Ω => F z.2 x) 2 R := hx.comp_snd P
    have hys : MemLp (fun z : Ω × Ω => F z.2 y) 2 R := hy.comp_snd P
    have hdiag : cov[fun z : Ω × Ω => F z.1 x, fun z => F z.1 y; R] =
        cov[fun ω => F ω x, fun ω => F ω y; P] := by
      calc
        _ = cov[fun ω => F ω x, fun ω => F ω y; (P.prod P).map Prod.fst] :=
          (covariance_map (by simpa [R] using hx.aestronglyMeasurable)
            (by simpa [R] using hy.aestronglyMeasurable) measurable_fst.aemeasurable).symm
        _ = _ := by simp
    have hcross₁ : cov[fun z : Ω × Ω => F z.1 x,
        fun z => F z.2 y; R] = 0 := covariance_fst_snd_prod hx hy
    have hcross₂ : cov[fun z : Ω × Ω => F z.2 x,
        fun z => F z.1 y; R] = 0 := by
      rw [covariance_comm]
      exact covariance_fst_snd_prod hy hx
    have hdiag₂ : cov[fun z : Ω × Ω => F z.2 x, fun z => F z.2 y; R] =
        cov[fun ω => F ω x, fun ω => F ω y; P] := by
      calc
        _ = cov[fun ω => F ω x, fun ω => F ω y; (P.prod P).map Prod.snd] :=
          (covariance_map (by simpa [R] using hx.aestronglyMeasurable)
            (by simpa [R] using hy.aestronglyMeasurable) measurable_snd.aemeasurable).symm
        _ = _ := by simp
    change cov[(Real.sqrt 2)⁻¹ • (fun z : Ω × Ω => F z.1 x - F z.2 x),
      (Real.sqrt 2)⁻¹ • (fun z : Ω × Ω => F z.1 y - F z.2 y); R] = _
    rw [covariance_smul_left, covariance_smul_right,
      covariance_fun_sub_fun_sub hxf hxs hyf hys]
    rw [hdiag, hcross₁, hcross₂, hdiag₂]
    have hr : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
      have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have hsquare : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
      field_simp
      nlinarith
    rw [← mul_assoc, hr]
    ring
  have hpath := AlignmentPaperGaussianFeatureBridge.continuous_path_law_eq_of_same_covariance
    F G hF hGmeas hX hGproc hmean hmeanG (fun x y => (hcovG x y).symm)
  have hpush : Measure.map G R =
      Measure.map (fun z : C(α, ℝ) × C(α, ℝ) =>
        (Real.sqrt 2)⁻¹ • (z.1 - z.2)) ((P.map F).prod (P.map F)) := by
    let H : Ω × Ω → C(α, ℝ) × C(α, ℝ) := fun z => (F z.1, F z.2)
    let δ : C(α, ℝ) × C(α, ℝ) → C(α, ℝ) := fun z =>
      (Real.sqrt 2)⁻¹ • (z.1 - z.2)
    have hH : Measurable H := by fun_prop
    have hδ : Measurable δ := by fun_prop
    calc
      Measure.map G R = Measure.map (δ ∘ H) (P.prod P) := by
        congr 1
      _ = Measure.map δ (Measure.map H (P.prod P)) := by
        rw [Measure.map_map hδ hH]
      _ = Measure.map δ ((P.map F).prod (P.map F)) := by
        change Measure.map δ (Measure.map (Prod.map F F) (P.prod P)) = _
        rw [Measure.map_prod_map P P hF hF]
  exact hpush.symm.trans hpath.symm

/-- Centered Gaussian path laws satisfy the uniform translated-ball estimate
used in finite-codebook quantization bounds. -/
theorem centered_gaussian_translated_ball_mass_sq_le
    {α Ω : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [LocallyCompactSpace α] [CompactSpace α] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α, ℝ)) (hF : Measurable F)
    (hX : ProbabilityTheory.IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
    (c : C(α, ℝ)) (t : ℝ) (ht : 0 ≤ t) :
    (P.map F) (Metric.closedBall c t) ^ 2 ≤
      (P.map F) (Metric.closedBall 0 (Real.sqrt 2 * t)) := by
  have hdiff := normalized_copy_difference_path_law F hF hX hmean
  exact translatedBall_mass_sq_le_of_normalized_difference_law
    (P.map F) hdiff c t ht

/-- A lower bound on the mass above level `t` gives the corresponding lower
bound on the extended expectation of a nonnegative distortion. This form
needs no integrability assumption and can be applied to nearest-codepoint
distortion once its tail mass has been bounded. -/
theorem lintegral_distortion_ge_level_mul_tail
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℝ≥0∞) (hD : Measurable D) (t : ℝ≥0∞)
    (htail : (1 / 2 : ℝ≥0∞) ≤ P {ω | t < D ω}) :
    t / 2 ≤ ∫⁻ ω, D ω ∂P := by
  let A : Set Ω := {ω | t < D ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hD
  have hpoint : ∀ ω, (Set.indicator A (fun _ : Ω => t)) ω ≤ D ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp [Set.indicator, A, hω]
      exact le_of_lt (by simpa [A] using hω)
    · simp [Set.indicator, A, hω]
  have hmono := lintegral_mono (μ := P) hpoint
  have hindicator : (∫⁻ ω, Set.indicator A (fun _ : Ω => t) ω ∂P) = t * P A := by
    rw [lintegral_indicator hA]
    simp
  calc
    t / 2 = t * (1 / 2 : ℝ≥0∞) := by simp [ENNReal.div_eq_inv_mul, mul_comm]
    _ ≤ t * P A := mul_le_mul_of_nonneg_left htail ((show 0 ≤ t from bot_le))
    _ = ∫⁻ ω, Set.indicator A (fun _ : Ω => t) ω ∂P := hindicator.symm
    _ ≤ ∫⁻ ω, D ω ∂P := hmono

/-- The nearest-codebook sublevel event is contained in the union of the
radius-`t` balls about its finitely many deterministic representatives. -/
theorem finiteCodebook_sublevel_subset_balls
    {X : Type*} [PseudoEMetricSpace X] {m : ℕ} (hm : 0 < m)
    (c : Fin m → X) (t : ℝ≥0∞) :
    {x | finiteCodebookDistortion hm c x ≤ t} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin m)), {x | edist x (c i) ≤ t} := by
  intro x hx
  obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_inf'
    (s := (Finset.univ : Finset (Fin m)))
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
    (fun i => edist x (c i))
  have hdist : edist x (c i) ≤ t := by
    have hcode : (Finset.univ : Finset (Fin m)).inf'
        (by exact Finset.univ_nonempty_iff.mpr ⟨⟨0, hm⟩⟩)
        (fun j => edist x (c j)) ≤ t := by
      simpa [finiteCodebookDistortion] using hx
    rw [← heq]
    exact hcode
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi, hdist⟩⟩

/-- Uniform centre-ball bounds of size `1/(2m)` imply that any fixed
`m`-point codebook captures at most one half the law inside its radius-`t`
nearest-neighbour region. -/
theorem finiteCodebook_sublevel_mass_le
    {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X]
    (μ : Measure X) {m : ℕ} (hm : 0 < m) (t : ℝ≥0∞)
    (b : ℝ≥0∞) (hball : ∀ z : X, μ {x | edist x z ≤ t} ≤ b)
    (hbudget : (m : ℝ≥0∞) * b ≤ 1 / 2) (c : Fin m → X) :
    μ {x | finiteCodebookDistortion hm c x ≤ t} ≤ 1 / 2 := by
  calc
    μ {x | finiteCodebookDistortion hm c x ≤ t} ≤
        μ (⋃ i ∈ (Finset.univ : Finset (Fin m)), {x | edist x (c i) ≤ t}) :=
      measure_mono (finiteCodebook_sublevel_subset_balls hm c t)
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin m)),
        μ {x | edist x (c i) ≤ t} := measure_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ (Finset.univ : Finset (Fin m)), b := by
      apply Finset.sum_le_sum
      intro i hi
      exact hball (c i)
    _ = (m : ℝ≥0∞) * b := by simp
    _ ≤ 1 / 2 := hbudget

/-- Under a probability measure, a sublevel set of mass at most one half
leaves at least one half of the mass strictly above the threshold. -/
theorem probability_tail_ge_half_of_sublevel
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : Ω → ℝ≥0∞) (hD : Measurable D) (t : ℝ≥0∞)
    (hsub : P {ω | D ω ≤ t} ≤ 1 / 2) :
    (1 / 2 : ℝ) ≤ P.real {ω | t < D ω} := by
  let A : Set Ω := {ω | t < D ω}
  have hA : MeasurableSet A := measurableSet_lt measurable_const hD
  have hsum := measureReal_add_measureReal_compl (μ := P) hA
  simp only [probReal_univ] at hsum
  have hcomp : Aᶜ = {ω | D ω ≤ t} := by
    ext ω
    simp only [A, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt]
  have hsubR : P.real Aᶜ ≤ (1 / 2 : ℝ) := by
    rw [hcomp]
    have hle := (ENNReal.toReal_le_toReal (measure_ne_top P _) (by norm_num)).2 hsub
    rw [measureReal_def]
    simpa using hle
  rw [← hsum]
  linarith

/-- The usual sublevel-probability form of the finite-codebook lower bound. -/
theorem quantizationQ1_ge_of_uniform_sublevel
    {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m) (t : ℝ≥0∞)
    (hmeas : ∀ c : Fin m → X, Measurable (fun x => finiteCodebookDistortion hm c x))
    (hsub : ∀ c : Fin m → X,
      μ {x | finiteCodebookDistortion hm c x ≤ t} ≤ 1 / 2) :
    t / 2 ≤ quantizationQ1 μ m hm := by
  unfold quantizationQ1
  apply le_iInf
  intro c
  have htailR := probability_tail_ge_half_of_sublevel μ
    (fun x => finiteCodebookDistortion hm c x) (hmeas c) t (hsub c)
  have htail : (1 / 2 : ℝ≥0∞) ≤
      μ {x | t < finiteCodebookDistortion hm c x} := by
    have htailReal : (1 / 2 : ℝ≥0∞).toReal ≤
        (μ {x | t < finiteCodebookDistortion hm c x}).toReal := by
      have hhalf : (1 / 2 : ℝ≥0∞).toReal = (1 / 2 : ℝ) := by norm_num
      rw [hhalf]
      simpa only [measureReal_def] using htailR
    apply (ENNReal.toReal_le_toReal (by norm_num) (measure_ne_top μ _)).mp
    exact htailReal
  exact lintegral_distortion_ge_level_mul_tail μ
    (fun x => finiteCodebookDistortion hm c x) (hmeas c) t htail

/-- Uniform translated-ball bounds with total mass budget one half imply a
lower bound for the first-order optimal finite-codebook quantization error. -/
theorem quantizationQ1_ge_of_uniform_ball_mass
    {X : Type*} [MeasurableSpace X] [PseudoEMetricSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (t b : ℝ≥0∞)
    (hmeas : ∀ c : Fin m → X, Measurable (fun x => finiteCodebookDistortion hm c x))
    (hball : ∀ z : X, μ {x | edist x z ≤ t} ≤ b)
    (hbudget : (m : ℝ≥0∞) * b ≤ 1 / 2) :
    t / 2 ≤ quantizationQ1 μ m hm := by
  apply quantizationQ1_ge_of_uniform_sublevel μ m hm t hmeas
  intro c
  exact finiteCodebook_sublevel_mass_le μ hm t b hball hbudget c

/-- Centered Gaussian small-ball control at `√2 t` gives a first-order
finite-codebook lower bound. The squared small-ball budget is the precise
input needed by independent-copy symmetrization. -/
theorem centered_gaussian_quantizationQ1_lower
    {α Ω : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [LocallyCompactSpace α] [CompactSpace α] [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α, ℝ)) (hF : Measurable F)
    (hX : ProbabilityTheory.IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
    (m : ℕ) (hm : 0 < m) (t b : ℝ)
    (ht : 0 ≤ t) (hb : 0 ≤ b)
    (hmeas : ∀ c : Fin m → C(α, ℝ),
      Measurable (fun x => finiteCodebookDistortion hm c x))
    (hcenter : (P.map F) (Metric.closedBall 0 (Real.sqrt 2 * t)) ≤
      ENNReal.ofReal b ^ 2)
    (hbudget : (m : ℝ≥0∞) * ENNReal.ofReal b ≤ 1 / 2) :
    ENNReal.ofReal t / 2 ≤ quantizationQ1 (P.map F) m hm := by
  have hballs : ∀ c : C(α, ℝ),
      (P.map F) {x | edist x c ≤ ENNReal.ofReal t} ≤ ENNReal.ofReal b := by
    intro c
    have hsym := centered_gaussian_translated_ball_mass_sq_le F hF hX hmean c t ht
    have hball : (P.map F) (Metric.closedBall c t) ^ 2 ≤ ENNReal.ofReal b ^ 2 :=
      hsym.trans hcenter
    have hprob : (P.map F) (Metric.closedBall c t) ≤ 1 := by
      calc
        _ ≤ (P.map F) Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have hmassTop : (P.map F) (Metric.closedBall c t) ≠ ∞ := by
      exact ne_of_lt (lt_of_le_of_lt hprob ENNReal.one_lt_top)
    have hbtop : ENNReal.ofReal b ≠ ∞ := by simp
    have hmassSqTop : ((P.map F) (Metric.closedBall c t)) ^ 2 ≠ ∞ := by
      simp [hmassTop]
    have hbSqTop : (ENNReal.ofReal b) ^ 2 ≠ ∞ := by simp
    have hrealSq := (ENNReal.toReal_le_toReal hmassSqTop hbSqTop).2 hball
    have hreal : ((P.map F) (Metric.closedBall c t)).toReal ≤ b := by
      have hrealSq' : ((P.map F) (Metric.closedBall c t)).toReal ^ 2 ≤ b ^ 2 := by
        simpa [ENNReal.toReal_pow, ENNReal.toReal_ofReal hb] using hrealSq
      nlinarith [sq_nonneg (((P.map F) (Metric.closedBall c t)).toReal - b)]
    have hle := (ENNReal.toReal_le_toReal hmassTop hbtop).1
      (by simpa [ENNReal.toReal_ofReal hb] using hreal)
    simpa [Metric.closedBall, Metric.mem_closedBall, edist_dist,
      ENNReal.ofReal_le_ofReal_iff ht] using hle
  exact quantizationQ1_ge_of_uniform_ball_mass (P.map F) m hm
    (ENNReal.ofReal t) (ENNReal.ofReal b) hmeas hballs hbudget

end BrownianSharp
