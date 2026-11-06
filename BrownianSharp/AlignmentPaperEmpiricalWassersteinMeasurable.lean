import BrownianSharp.AlignmentPaperEmpiricalPerturbation

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace BrownianSharp.AlignmentPaperEmpiricalWassersteinMeasurable

open BrownianSharp
open BrownianSharp.AlignmentPaperEmpiricalIntegrals
open BrownianSharp.AlignmentPaperEmpiricalWasserstein
open BrownianSharp.AlignmentPaperEmpiricalPerturbation
open BrownianSharp.AlignmentPaperEmpiricalCellLift

/-- A finite second moment about one point makes every empirical W₂ value
finite. The one-point codebook gives a genuine finite-cost coupling bound. -/
theorem wassersteinTwo_empirical_ne_top {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (x₀ : X)
    (hM : (∫⁻ y, edist y x₀ ^ 2 ∂μ) ≠ ⊤)
    (m : ℕ) (hm : 0 < m) (x : Fin m → X) :
    wassersteinTwo μ (empiricalMeasure m hm x) ≠ ⊤ := by
  let c : Fin 1 → X := fun _ => x₀
  have hμcost :
      (∫⁻ y, finiteCodebookDistortion (by omega : 0 < 1) c y ^ 2 ∂μ) ≠ ⊤ := by
    have heq : (fun y => finiteCodebookDistortion (by omega : 0 < 1) c y ^ 2) =
        fun y => edist y x₀ ^ 2 := by
      funext y
      simp [finiteCodebookDistortion, c]
    rw [show (∫⁻ y, finiteCodebookDistortion (by omega : 0 < 1) c y ^ 2 ∂μ) =
        ∫⁻ y, edist y x₀ ^ 2 ∂μ by rw [heq]]
    exact hM
  have hνcost :
      (∫⁻ y, finiteCodebookDistortion (by omega : 0 < 1) c y ^ 2
        ∂empiricalMeasure m hm x) ≠ ⊤ := by
    rw [lintegral_empiricalMeasure m hm x _
      ((AlignmentPaperQuantizationAtomicBridge.finiteCodebookDistortion_measurable
        (by omega : 0 < 1) c).pow_const 2)]
    rw [tsum_fintype]
    apply ENNReal.sum_ne_top.mpr
    intro i hi
    apply ENNReal.mul_ne_top
    · simp
    · exact ne_of_lt (ENNReal.pow_lt_top (edist_lt_top (x i) x₀))
  have hdiam : ∀ i j : Fin 1, edist (c i) (c j) ^ 2 ≤ (0 : ℝ≥0∞) ^ 2 := by
    intro i j
    simp [c]
  have hbound := wassersteinTwo_le_codebook_empirical μ m hm 1 (by omega) c 0 hdiam x
  have hfinite : (ennrealSqrt (3 * ((∫⁻ y,
      finiteCodebookDistortion (by omega : 0 < 1) c y ^ 2 ∂μ) +
      (0 : ℝ≥0∞) ^ 2 * ENNReal.ofReal (commonResidualCellMass
        (nearestCellRealWeight (by omega : 0 < 1) c μ)
        (nearestCellRealWeight (by omega : 0 < 1) c
          (empiricalMeasure m hm x))) +
      (∫⁻ y, finiteCodebookDistortion (by omega : 0 < 1) c y ^ 2
        ∂empiricalMeasure m hm x)))) ≠ ⊤ := by
    unfold ennrealSqrt
    apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
    apply ENNReal.mul_ne_top (by norm_num)
    simp [hμcost, hνcost]
  exact ne_top_of_le_ne_top hfinite hbound

/-- The ordinary real-valued empirical W₂ map. -/
noncomputable def empiricalWassersteinReal {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSingletonClass X]
    (μ : Measure X) {m : ℕ} (hm : 0 < m) (x : Fin m → X) : ℝ :=
  (wassersteinTwo μ (empiricalMeasure m hm x)).toReal

/-- Finite second moment upgrades the extended perturbation estimate to a
one-Lipschitz estimate for the ordinary real-valued Wasserstein map. -/
theorem empiricalWassersteinReal_lipschitz {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (x₀ : X)
    (hM : (∫⁻ y, edist y x₀ ^ 2 ∂μ) ≠ ⊤)
    {m : ℕ} (hm : 0 < m) :
    LipschitzWith 1 (empiricalWassersteinReal μ hm) := by
  classical
  apply LipschitzWith.of_le_add
  intro x x'
  let δ := empiricalSampleDisplacement x x'
  have hδeq : δ = edist x x' := by
    dsimp [δ, empiricalSampleDisplacement]
    rw [← Finset.sup_univ_eq_iSup, edist_pi_def]
  have hW (z : Fin m → X) :
      wassersteinTwo μ (empiricalMeasure m hm z) ≠ ⊤ :=
    wassersteinTwo_empirical_ne_top μ x₀ hM m hm z
  have hδ : δ ≠ ⊤ := by
    rw [hδeq]
    exact edist_ne_top _ _
  have hforward0 := wassersteinTwo_empirical_perturb_le (μ := μ) (m := m) hm x' x
  have hforward : wassersteinTwo μ (empiricalMeasure m hm x) ≤
      wassersteinTwo μ (empiricalMeasure m hm x') + δ := by
    simpa [δ, empiricalSampleDisplacement, edist_comm] using hforward0
  have hsum : wassersteinTwo μ (empiricalMeasure m hm x') + δ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hW x', hδ⟩
  have hforwardReal :
      empiricalWassersteinReal μ hm x ≤
        empiricalWassersteinReal μ hm x' + δ.toReal := by
    change (wassersteinTwo μ (empiricalMeasure m hm x)).toReal ≤ _
    calc
      (wassersteinTwo μ (empiricalMeasure m hm x)).toReal ≤
          (wassersteinTwo μ (empiricalMeasure m hm x') + δ).toReal :=
        ENNReal.toReal_mono hsum hforward
      _ = empiricalWassersteinReal μ hm x' + δ.toReal := by
        rw [ENNReal.toReal_add (hW x') hδ]
        rfl
  have hδreal : δ.toReal = dist x x' := by
    rw [hδeq, dist_edist]
  rw [hδreal] at hforwardReal
  exact hforwardReal

/-- Measurability of the real empirical Wasserstein map follows from its
one-Lipschitz dependence on the finite sample. -/
theorem empiricalWassersteinReal_measurable {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (x₀ : X)
    (hM : (∫⁻ y, edist y x₀ ^ 2 ∂μ) ≠ ⊤)
    {m : ℕ} (hm : 0 < m) :
    Measurable (empiricalWassersteinReal μ hm) :=
  (empiricalWassersteinReal_lipschitz μ x₀ hM hm).continuous.measurable

/-- The extended-valued W₂ map itself is measurable when the source law has
finite second moment. -/
theorem wassersteinTwo_empirical_measurable {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (x₀ : X)
    (hM : (∫⁻ y, edist y x₀ ^ 2 ∂μ) ≠ ⊤)
    {m : ℕ} (hm : 0 < m) :
    Measurable (fun x : Fin m → X =>
      wassersteinTwo μ (empiricalMeasure m hm x)) := by
  have hreal := empiricalWassersteinReal_measurable μ x₀ hM hm
  have hEq : (fun x : Fin m → X =>
      wassersteinTwo μ (empiricalMeasure m hm x)) =
      fun x => ENNReal.ofReal (empiricalWassersteinReal μ hm x) := by
    funext x
    exact (ENNReal.ofReal_toReal (wassersteinTwo_empirical_ne_top μ x₀ hM m hm x)).symm
  rw [hEq]
  fun_prop

/-- Under the second-moment hypothesis, the ordinary expectation of empirical
W₂ is integrable and equals the real-valued form of its extended integral. -/
theorem integral_empiricalWassersteinReal_eq_toReal_lintegral
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [MeasurableSingletonClass X]
    (μ : Measure X) [IsProbabilityMeasure μ] (x₀ : X)
    (hM : (∫⁻ y, edist y x₀ ^ 2 ∂μ) ≠ ⊤)
    {m : ℕ} (hm : 0 < m) :
    (∫ x : Fin m → X, empiricalWassersteinReal μ hm x ∂iidSampleLaw μ m) =
      (∫⁻ x : Fin m → X,
        wassersteinTwo μ (empiricalMeasure m hm x) ∂iidSampleLaw μ m).toReal := by
  let P := iidSampleLaw μ m
  let f : (Fin m → X) → ℝ≥0∞ := fun x =>
    wassersteinTwo μ (empiricalMeasure m hm x)
  have hmeas : Measurable f := wassersteinTwo_empirical_measurable μ x₀ hM hm
  have hfinite : (∫⁻ x, f x ∂P) ≠ ⊤ := by
    let c : Fin 1 → X := fun _ => x₀
    have hA :
        (∫⁻ y, finiteCodebookDistortion (by omega : 0 < 1) c y ^ 2 ∂μ) =
          ∫⁻ y, edist y x₀ ^ 2 ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [] with y
      simp [finiteCodebookDistortion, c]
    have hdiam : ∀ i j : Fin 1, edist (c i) (c j) ^ 2 ≤ (0 : ℝ≥0∞) ^ 2 := by
      intro i j
      simp [c]
    have hbound := expected_wassersteinTwo_le_codebook μ m hm 1 (by omega) c 0 hdiam
    have hsqrt : ennrealSqrt (3 * ((2 : ℝ≥0∞) *
        (∫⁻ y, finiteCodebookDistortion (by omega : 0 < 1) c y ^ 2 ∂μ))) ≠ ⊤ := by
      rw [hA]
      unfold ennrealSqrt
      apply ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      apply ENNReal.mul_ne_top (by norm_num)
      exact ENNReal.mul_ne_top (by norm_num) hM
    have hupper : (∫⁻ x : Fin m → X, f x ∂P) ≤
        ennrealSqrt (3 * ((2 : ℝ≥0∞) *
          (∫⁻ y, finiteCodebookDistortion (by omega : 0 < 1) c y ^ 2 ∂μ))) := by
      simpa [P, f, zero_mul, add_zero] using hbound
    exact ne_top_of_le_ne_top hsqrt hupper
  have hpoint : ∀ᵐ x ∂P, f x < ⊤ :=
    ae_of_all P (fun x => lt_top_iff_ne_top.mpr
      (wassersteinTwo_empirical_ne_top μ x₀ hM m hm x))
  change (∫ x, (f x).toReal ∂P) = (∫⁻ x, f x ∂P).toReal
  exact integral_toReal hmeas.aemeasurable hpoint

end BrownianSharp.AlignmentPaperEmpiricalWassersteinMeasurable
