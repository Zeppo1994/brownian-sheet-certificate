import BrownianSharp.AlignmentPaperEmpiricalCellLift

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace BrownianSharp.AlignmentPaperEmpiricalIntegrals

open BrownianSharp
open BrownianSharp.AlignmentPaperEmpiricalWasserstein
open BrownianSharp.AlignmentPaperEmpiricalCellLift

theorem lintegral_empiricalMeasure {Y : Type*} [MeasurableSpace Y]
    (m : ℕ) (hm : 0 < m) (x : Fin m → Y) (f : Y → ℝ≥0∞)
    (hf : Measurable f) :
    (∫⁻ y, f y ∂empiricalMeasure m hm x) =
      ∑' i : Fin m, ((m : ℝ≥0)⁻¹) • f (x i) := by
  rw [empiricalMeasure, lintegral_sum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hf]

theorem iidCoordinate_lintegral {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (m : ℕ) (i : Fin m)
    (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Fin m → Y, f (x i) ∂iidSampleLaw μ m) = ∫⁻ y, f y ∂μ := by
  have hmap : Measure.map (fun x : Fin m → Y => x i) (iidSampleLaw μ m) = μ := by
    dsimp [iidSampleLaw]
    rw [Measure.pi_map_eval]
    simp
  rw [← lintegral_map hf (measurable_pi_apply i), hmap]

theorem expected_empirical_integral_eq {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (m : ℕ) (hm : 0 < m)
    (f : Y → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x : Fin m → Y,
      (∫⁻ y, f y ∂empiricalMeasure m hm x) ∂iidSampleLaw μ m) =
      ∫⁻ y, f y ∂μ := by
  have hfun : (fun x : Fin m → Y =>
      ∫⁻ y, f y ∂empiricalMeasure m hm x) =
        fun x => ∑ i : Fin m, ((m : ℝ≥0)⁻¹) • f (x i) := by
    funext x
    simpa only [tsum_fintype] using lintegral_empiricalMeasure m hm x f hf
  rw [hfun]
  rw [lintegral_finsetSum]
  · calc
      (∑ i : Fin m, ∫⁻ x : Fin m → Y,
          ((m : ℝ≥0)⁻¹) • f (x i) ∂iidSampleLaw μ m) =
        ∑ i : Fin m, ((m : ℝ≥0) : ℝ≥0∞)⁻¹ * (∫⁻ y, f y ∂μ) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hpoint : (fun x : Fin m → Y => ((m : ℝ≥0)⁻¹) • f (x i)) =
              fun x => ((m : ℝ≥0) : ℝ≥0∞)⁻¹ * f (x i) := by
            funext x
            have hmnn : (m : ℝ≥0) ≠ 0 := by exact_mod_cast hm.ne'
            rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv hmnn]
          rw [hpoint]
          calc
            (∫⁻ x : Fin m → Y,
                ((m : ℝ≥0) : ℝ≥0∞)⁻¹ * f (x i) ∂iidSampleLaw μ m) =
              ((m : ℝ≥0) : ℝ≥0∞)⁻¹ *
                (∫⁻ x : Fin m → Y, f (x i) ∂iidSampleLaw μ m) := by
                  exact lintegral_const_mul _ (f := fun x : Fin m → Y => f (x i))
                    (hf.comp (measurable_pi_apply i))
            _ = ((m : ℝ≥0) : ℝ≥0∞)⁻¹ * (∫⁻ y, f y ∂μ) := by
                  rw [iidCoordinate_lintegral μ m i f hf]
      _ = ∫⁻ y, f y ∂μ := by
          rw [← Finset.mul_sum]
          have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast hm.ne'
          have hmT : (m : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top m
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, ENNReal.coe_inv, ENNReal.coe_natCast]
          rw [← mul_assoc, ENNReal.inv_mul_cancel hm0 hmT, one_mul]
  · intro i hi
    exact (measurable_const.mul (hf.comp (measurable_pi_apply i)))

theorem empiricalCodebookDistortion_measurable {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N) (c : Fin N → X) :
    Measurable (fun x : Fin m → X =>
      ∫⁻ y, finiteCodebookDistortion hN c y ^ 2 ∂empiricalMeasure m hm x) := by
  have hd : Measurable (fun y : X => finiteCodebookDistortion hN c y ^ 2) := by
    exact (AlignmentPaperQuantizationAtomicBridge.finiteCodebookDistortion_measurable
      hN c).pow_const 2
  have hfun : (fun x : Fin m → X =>
      ∫⁻ y, finiteCodebookDistortion hN c y ^ 2 ∂empiricalMeasure m hm x) =
      fun x => ∑ i : Fin m, ((m : ℝ≥0)⁻¹) •
        finiteCodebookDistortion hN c (x i) ^ 2 := by
    funext x
    simpa only [tsum_fintype] using
      lintegral_empiricalMeasure m hm x _ hd
  rw [hfun]
  apply Finset.measurable_sum Finset.univ
  intro i hi
  exact measurable_const.smul (hd.comp (measurable_pi_apply i))

theorem empiricalMeasure_real_singleton_eq_frequency {N m : ℕ}
    (hm : 0 < m) (x : Fin m → Fin N) (i : Fin N) :
    (empiricalMeasure m hm x).real {i} =
      AlignmentPaperFiniteEmpiricalCoupling.empiricalCategoryFrequency hm x i := by
  let p : Fin N → ℝ :=
    AlignmentPaperFiniteEmpiricalCoupling.empiricalCategoryFrequency hm x
  have hp : ∀ j, 0 ≤ p j := by
    intro j
    exact (AlignmentPaperFiniteEmpiricalCoupling.empiricalCategoryFrequency_mem_Icc hm x j).1
  have hpone : ∑ j : Fin N, p j = 1 := by
    simpa [p] using
      AlignmentPaperFiniteEmpiricalCoupling.sum_empiricalCategoryFrequency_eq_one hm x
  have heq : empiricalMeasure m hm x = AlignmentPaperFiniteEmpiricalCoupling.finiteCategoryLaw p := by
    rw [AlignmentPaperFiniteEmpiricalCoupling.empiricalMeasure_eq_finiteFrequencyMeasure]
    unfold AlignmentPaperFiniteEmpiricalCoupling.finiteCategoryLaw
      AlignmentPaperFiniteEmpiricalCoupling.finiteAtomicMeasure
    congr 1
    funext j
    rw [AlignmentPaperFiniteEmpiricalCoupling.empiricalCategoryWeight_eq_ofReal_frequency]
  rw [heq]
  exact AlignmentPaperFiniteEmpiricalCoupling.finiteCategoryLaw_real_singleton p hp hpone i

theorem map_empiricalMeasure {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y]
    (m : ℕ) (hm : 0 < m) (x : Fin m → X) (g : X → Y) (hg : Measurable g) :
    Measure.map g (empiricalMeasure m hm x) =
      empiricalMeasure m hm (fun i => g (x i)) := by
  rw [empiricalMeasure, Measure.map_sum hg.aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul _ hg.aemeasurable]
  simp [Measure.map_dirac' hg]

theorem nearestCellRealWeight_empirical_eq_frequency {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N) (c : Fin N → X)
    (x : Fin m → X) (i : Fin N) :
    nearestCellRealWeight hN c (empiricalMeasure m hm x) i =
      AlignmentPaperFiniteEmpiricalCoupling.empiricalCategoryFrequency hm
        (nearestCategorySample hN c x) i := by
  let g := AlignmentPaperQuantizationAtomicBridge.nearestIndex hN c
  let ν := empiricalMeasure m hm x
  have hg : Measurable g := AlignmentPaperQuantizationAtomicBridge.nearestIndex_measurable hN c
  have hmap := map_empiricalMeasure m hm x g hg
  have hmass : ν (nearestCell hN c i) =
      (empiricalMeasure m hm (nearestCategorySample hN c x)) {i} := by
    change ν (g ⁻¹' ({i} : Set (Fin N))) = _
    rw [← Measure.map_apply hg (measurableSet_singleton i), hmap]
    rfl
  unfold nearestCellRealWeight nearestCellWeight
  rw [hmass]
  exact empiricalMeasure_real_singleton_eq_frequency hm
    (nearestCategorySample hN c x) i

theorem nearestCellResidual_eq_empiricalFrequency {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N) (c : Fin N → X)
    (μ : Measure X) [IsProbabilityMeasure μ] (x : Fin m → X) :
    commonResidualCellMass (nearestCellRealWeight hN c μ)
      (nearestCellRealWeight hN c (empiricalMeasure m hm x)) =
    AlignmentPaperFiniteEmpiricalCoupling.empiricalFrequencyResidual hm
      (Measure.map (AlignmentPaperQuantizationAtomicBridge.nearestIndex hN c) μ)
      (nearestCategorySample hN c x) := by
  letI : IsProbabilityMeasure (empiricalMeasure m hm x) :=
    empiricalMeasure_isProbability m hm x
  let ρ := Measure.map (AlignmentPaperQuantizationAtomicBridge.nearestIndex hN c) μ
  let p := nearestCellRealWeight hN c μ
  let q := nearestCellRealWeight hN c (empiricalMeasure m hm x)
  have hpone : ∑ i : Fin N, p i = 1 := by
    simpa [p] using nearestCellRealWeight_sum_eq_one hN c μ
  have hqone : ∑ i : Fin N, q i = 1 := by
    simpa [q] using nearestCellRealWeight_sum_eq_one hN c (empiricalMeasure m hm x)
  have hsrc (i : Fin N) : p i = ρ.real {i} := by
    dsimp [p, ρ, nearestCellRealWeight, nearestCellWeight]
    rw [Measure.real, Measure.map_apply
      (AlignmentPaperQuantizationAtomicBridge.nearestIndex_measurable hN c)
      (measurableSet_singleton i)]
    rfl
  have htgt (i : Fin N) :
      q i = AlignmentPaperFiniteEmpiricalCoupling.empiricalCategoryFrequency hm
        (nearestCategorySample hN c x) i := by
    exact nearestCellRealWeight_empirical_eq_frequency m hm N hN c x i
  have hhalf := AlignmentPaperFiniteEmpiricalCoupling.commonMassResidual_eq_half_l1 p q
    hpone hqone
  unfold commonResidualCellMass
  rw [hhalf]
  unfold AlignmentPaperFiniteEmpiricalCoupling.empiricalFrequencyResidual
  simp_rw [hsrc, htgt, abs_sub_comm]
  rfl

theorem expected_nearestCellResidual_le {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N) (c : Fin N → X)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    (∫⁻ x : Fin m → X,
      ENNReal.ofReal (commonResidualCellMass (nearestCellRealWeight hN c μ)
        (nearestCellRealWeight hN c (empiricalMeasure m hm x)))
      ∂iidSampleLaw μ m) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / m)) := by
  have hfun : (fun x : Fin m → X =>
      ENNReal.ofReal (commonResidualCellMass (nearestCellRealWeight hN c μ)
        (nearestCellRealWeight hN c (empiricalMeasure m hm x)))) =
      fun x => ENNReal.ofReal
        (AlignmentPaperFiniteEmpiricalCoupling.empiricalFrequencyResidual hm
          (Measure.map (AlignmentPaperQuantizationAtomicBridge.nearestIndex hN c) μ)
          (nearestCategorySample hN c x)) := by
    funext x
    rw [nearestCellResidual_eq_empiricalFrequency]
  rw [hfun]
  exact nearestCategory_empiricalResidual_lintegral_le hN hm c μ

theorem nearestCellResidual_measurable {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N) (c : Fin N → X)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    Measurable (fun x : Fin m → X => ENNReal.ofReal
      (commonResidualCellMass (nearestCellRealWeight hN c μ)
        (nearestCellRealWeight hN c (empiricalMeasure m hm x)))) := by
  have hfun : (fun x : Fin m → X => ENNReal.ofReal
      (commonResidualCellMass (nearestCellRealWeight hN c μ)
        (nearestCellRealWeight hN c (empiricalMeasure m hm x)))) =
      fun x => ENNReal.ofReal
        (AlignmentPaperFiniteEmpiricalCoupling.empiricalFrequencyResidual hm
          (Measure.map (AlignmentPaperQuantizationAtomicBridge.nearestIndex hN c) μ)
          (nearestCategorySample hN c x)) := by
    funext x
    rw [nearestCellResidual_eq_empiricalFrequency]
  rw [hfun]
  have hcat : Measurable (nearestCategorySample (n := m) hN c) := by
    apply measurable_pi_iff.mpr
    intro k
    exact (AlignmentPaperQuantizationAtomicBridge.nearestIndex_measurable hN c).comp
      (measurable_pi_apply k)
  exact (by fun_prop : Measurable (fun y : Fin m → Fin N =>
      ENNReal.ofReal (AlignmentPaperFiniteEmpiricalCoupling.empiricalFrequencyResidual hm
        (Measure.map (AlignmentPaperQuantizationAtomicBridge.nearestIndex hN c) μ) y))).comp hcat

theorem wassersteinTwo_le_codebook_empirical {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N)
    (c : Fin N → X) (D : ℝ≥0∞)
    (hdiam : ∀ i j, edist (c i) (c j) ^ 2 ≤ D ^ 2)
    (x : Fin m → X) :
    wassersteinTwo μ (empiricalMeasure m hm x) ≤
      ennrealSqrt (3 * ((∫⁻ y, finiteCodebookDistortion hN c y ^ 2 ∂μ) +
        D ^ 2 * ENNReal.ofReal (commonResidualCellMass
          (nearestCellRealWeight hN c μ)
          (nearestCellRealWeight hN c (empiricalMeasure m hm x))) +
        (∫⁻ y, finiteCodebookDistortion hN c y ^ 2
          ∂empiricalMeasure m hm x))) := by
  let ν : Measure X := empiricalMeasure m hm x
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    exact empiricalMeasure_isProbability m hm x
  have hbase := wassersteinTwo_le_threeLeg_of_nearestCells hN c μ ν D hdiam
  dsimp at hbase
  have hleft := nearestCellRealWeightedDistortion_eq hN c μ
  have hright := nearestCellRealWeightedDistortion_eq hN c ν
  have hrightRev :
      (∑ i : Fin N, ENNReal.ofReal (nearestCellRealWeight hN c ν i) *
        (∫⁻ y, edist (c i) y ^ 2 ∂nearestCellLaw hN c ν i)) =
        ∫⁻ y, finiteCodebookDistortion hN c y ^ 2 ∂ν := by
    calc
      (∑ i : Fin N, ENNReal.ofReal (nearestCellRealWeight hN c ν i) *
          (∫⁻ y, edist (c i) y ^ 2 ∂nearestCellLaw hN c ν i)) =
        ∑ i : Fin N, ENNReal.ofReal (nearestCellRealWeight hN c ν i) *
          (∫⁻ y, edist y (c i) ^ 2 ∂nearestCellLaw hN c ν i) := by
            apply Finset.sum_congr rfl
            intro i hi
            congr 1
            rw [lintegral_congr_ae]
            filter_upwards [] with y
            rw [edist_comm]
      _ = ∫⁻ y, finiteCodebookDistortion hN c y ^ 2 ∂ν := hright
  have hbase' : wassersteinTwo μ (empiricalMeasure m hm x) ≤ ennrealSqrt (3 *
      ((∑ i : Fin N, ENNReal.ofReal (nearestCellRealWeight hN c μ i) *
          ∫⁻ y, edist y (c i) ^ 2 ∂nearestCellLaw hN c μ i) +
        D ^ 2 * ENNReal.ofReal (commonResidualCellMass
          (nearestCellRealWeight hN c μ) (nearestCellRealWeight hN c ν)) +
        (∑ i : Fin N, ENNReal.ofReal (nearestCellRealWeight hN c ν i) *
          ∫⁻ y, edist (c i) y ^ 2 ∂nearestCellLaw hN c ν i))) := by
    simpa [ν, edist_comm] using hbase
  rw [← hleft, ← hrightRev]
  simpa [ν] using hbase'

theorem expected_wassersteinTwo_le_codebook {X : Type*} [MetricSpace X]
    [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (m : ℕ) (hm : 0 < m) (N : ℕ) (hN : 0 < N)
    (c : Fin N → X) (D : ℝ≥0∞)
    (hdiam : ∀ i j, edist (c i) (c j) ^ 2 ≤ D ^ 2) :
    (∫⁻ x : Fin m → X,
      wassersteinTwo μ (empiricalMeasure m hm x) ∂iidSampleLaw μ m) ≤
      ennrealSqrt (3 * ((2 : ℝ≥0∞) *
        (∫⁻ y, finiteCodebookDistortion hN c y ^ 2 ∂μ) +
        D ^ 2 * ENNReal.ofReal ((1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / m)))) := by
  let P := iidSampleLaw μ m
  let A : ℝ≥0∞ := ∫⁻ y, finiteCodebookDistortion hN c y ^ 2 ∂μ
  let R : (Fin m → X) → ℝ≥0∞ := fun x => ENNReal.ofReal
    (commonResidualCellMass (nearestCellRealWeight hN c μ)
      (nearestCellRealWeight hN c (empiricalMeasure m hm x)))
  let B : (Fin m → X) → ℝ≥0∞ := fun x =>
    ∫⁻ y, finiteCodebookDistortion hN c y ^ 2 ∂empiricalMeasure m hm x
  let F : (Fin m → X) → ℝ≥0∞ := fun x => 3 * (A + (D ^ 2 * R x + B x))
  letI : IsProbabilityMeasure P := by
    dsimp [P, iidSampleLaw]
    infer_instance
  have hRmeas : Measurable R := by
    exact nearestCellResidual_measurable m hm N hN c μ
  have hBmeas : Measurable (fun x : Fin m → X =>
      ∫⁻ y, finiteCodebookDistortion hN c y ^ 2 ∂empiricalMeasure m hm x) := by
    exact empiricalCodebookDistortion_measurable m hm N hN c
  have hDRmeas : Measurable (fun x : Fin m → X => D ^ 2 * R x) :=
    measurable_const.mul hRmeas
  have hAmeas : Measurable (fun _ : Fin m → X => A) := measurable_const
  have hsummeas : Measurable (fun x : Fin m → X => A + (D ^ 2 * R x + B x)) := by
    change Measurable (fun x : Fin m → X => A +
      (D ^ 2 * R x + (fun x =>
        ∫⁻ y, finiteCodebookDistortion hN c y ^ 2 ∂empiricalMeasure m hm x) x))
    exact hAmeas.add (hDRmeas.add hBmeas)
  have hthreeMeas : Measurable (fun _ : Fin m → X => (3 : ℝ≥0∞)) := measurable_const
  have hFmeas : Measurable F := by
    dsimp [F]
    exact hthreeMeas.mul hsummeas
  have hpoint : ∀ x : Fin m → X,
      wassersteinTwo μ (empiricalMeasure m hm x) ≤ ennrealSqrt (F x) := by
    intro x
    simpa [F, A, R, B, add_assoc] using
      wassersteinTwo_le_codebook_empirical μ m hm N hN c D hdiam x
  have hFint : (∫⁻ x : Fin m → X, F x ∂P) =
      3 * (A + (D ^ 2 * (∫⁻ x : Fin m → X, R x ∂P) + A)) := by
    dsimp [F]
    rw [lintegral_const_mul 3 hsummeas]
    rw [lintegral_add_left measurable_const (fun x => D ^ 2 * R x + B x)]
    rw [lintegral_add_left hDRmeas B]
    rw [lintegral_const, measure_univ]
    rw [lintegral_const_mul (D ^ 2) hRmeas]
    rw [expected_empirical_integral_eq μ m hm
      (fun y => finiteCodebookDistortion hN c y ^ 2)
      (by exact (AlignmentPaperQuantizationAtomicBridge.finiteCodebookDistortion_measurable
        hN c).pow_const 2)]
    simp [A, add_assoc, add_comm, add_left_comm]
  have hres := expected_nearestCellResidual_le m hm N hN c μ
  have hupper : (∫⁻ x : Fin m → X, F x ∂P) ≤
      3 * ((2 : ℝ≥0∞) * A + D ^ 2 *
        ENNReal.ofReal ((1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / m))) := by
    rw [hFint]
    calc
      3 * (A + (D ^ 2 * (∫⁻ x : Fin m → X, R x ∂P) + A)) ≤
          3 * (A + (D ^ 2 * ENNReal.ofReal
            ((1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / m)) + A)) := by
              gcongr
      _ = 3 * ((2 : ℝ≥0∞) * A + D ^ 2 *
          ENNReal.ofReal ((1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / m))) := by
            congr 1
            simp [two_mul, add_assoc, add_comm, add_left_comm]
  calc
    (∫⁻ x : Fin m → X,
      wassersteinTwo μ (empiricalMeasure m hm x) ∂P) ≤
        ∫⁻ x : Fin m → X, ennrealSqrt (F x) ∂P :=
      lintegral_mono_ae (ae_of_all P hpoint)
    _ ≤ ennrealSqrt (∫⁻ x : Fin m → X, F x ∂P) :=
      lintegral_ennrealSqrt_le_sqrt_lintegral P F hFmeas.aemeasurable
    _ ≤ ennrealSqrt (3 * ((2 : ℝ≥0∞) * A + D ^ 2 *
        ENNReal.ofReal ((1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / m)))) := by
          unfold ennrealSqrt
          apply ENNReal.rpow_le_rpow
          · exact hupper
          · norm_num

end BrownianSharp.AlignmentPaperEmpiricalIntegrals
