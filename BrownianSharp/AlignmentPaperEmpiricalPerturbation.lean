import BrownianSharp.AlignmentPaperEmpiricalIntegrals
import BrownianSharp.AlignmentPaperFiniteFiber
import BrownianSharp.AlignmentPaperFiniteFiberMeasure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace BrownianSharp.AlignmentPaperEmpiricalPerturbation

open BrownianSharp

/-- Number of occurrences of the `i`th point in a finite sample. -/
def sampleMultiplicityAt {X : Type*} (m : ℕ) (x : Fin m → X) (y : X) : ℕ :=
  by
    classical
    exact (Finset.univ.filter fun j : Fin m => x j = y).card

def sampleMultiplicity {X : Type*} [DecidableEq X] (m : ℕ) (x : Fin m → X)
    (i : Fin m) : ℕ :=
  BrownianSharp.AlignmentPaperFiniteFiber.multiplicity x (x i)

/-- A transport measure obtained by splitting the mass over a repeated sample
point equally among its labels, then moving each label to its perturbed point. -/
def splitEmpiricalTransportMeasure {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X] {μ : Measure X} {m : ℕ} (hm : 0 < m)
    (x x' : Fin m → X)
    (γ : TransportCoupling μ (empiricalMeasure m hm x)) : Measure (X × X) :=
  Measure.sum fun i : Fin m =>
    ((sampleMultiplicity m x i : ℝ≥0∞)⁻¹) •
      Measure.map (fun z : X × X => (z.1, x' i))
        (γ.measure.restrict {z | z.2 = x i})

theorem empiricalMeasure_singleton_eq_count {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] {m : ℕ} (hm : 0 < m) (x : Fin m → X) (y : X) :
    empiricalMeasure m hm x {y} =
      (sampleMultiplicityAt m x y : ℝ≥0∞) * ↑((m : ℝ≥0)⁻¹) := by
  classical
  change (Measure.sum fun i : Fin m =>
    ((m : ℝ≥0)⁻¹) • Measure.dirac (x i)) {y} = _
  rw [Measure.sum_apply _ (measurableSet_singleton y)]
  simp only [tsum_fintype, Measure.smul_apply, Measure.dirac_apply,
    Set.indicator_apply, Set.mem_singleton_iff, ENNReal.smul_def, smul_eq_mul,
    Function.const_apply, one_apply, Pi.one_apply, zero_apply, Pi.zero_apply]
  simp only [mul_ite, mul_one, mul_zero]
  calc
    (∑ i : Fin m, if x i = y then ↑((m : ℝ≥0)⁻¹) else 0) =
        ∑ i ∈ (Finset.univ.filter fun i : Fin m => x i = y),
          ↑((m : ℝ≥0)⁻¹) := (Finset.sum_filter _ _).symm
    _ = (sampleMultiplicityAt m x y : ℝ≥0∞) * ↑((m : ℝ≥0)⁻¹) := by
      simp [sampleMultiplicityAt, nsmul_eq_mul]

theorem splitEmpiricalTransportMeasure_snd {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X] {μ : Measure X} {m : ℕ} (hm : 0 < m)
    (x x' : Fin m → X)
    (γ : TransportCoupling μ (empiricalMeasure m hm x)) :
    Measure.map Prod.snd (splitEmpiricalTransportMeasure hm x x' γ) =
      empiricalMeasure m hm x' := by
  classical
  -- The sum is evaluated on arbitrary measurable target sets; each summand
  -- is a point mass at the corresponding perturbed sample label.
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_snd hA]
  rw [splitEmpiricalTransportMeasure]
  rw [Measure.sum_apply _ (measurable_snd hA)]
  have hx' : empiricalMeasure m hm x' =
      Measure.sum (fun i : Fin m => ((m : ℝ≥0)⁻¹) • Measure.dirac (x' i)) := rfl
  rw [hx']
  rw [Measure.sum_apply _ hA]
  simp only [tsum_fintype]
  apply Finset.sum_congr rfl
  intro i hi
  let F : Set (X × X) := {z | z.2 = x i}
  have hmass : γ.measure F = empiricalMeasure m hm x {x i} := by
    have hs := congrArg (fun ν : Measure X => ν {x i}) γ.snd_map
    rw [Measure.map_apply measurable_snd (measurableSet_singleton (x i))] at hs
    simpa [F, Set.preimage, Set.mem_preimage, Set.mem_singleton_iff] using hs
  have hmass' : γ.measure F =
      (sampleMultiplicityAt m x (x i) : ℝ≥0∞) * ↑((m : ℝ≥0)⁻¹) := by
    rw [hmass, empiricalMeasure_singleton_eq_count hm]
  have hcount : sampleMultiplicity m x i ≠ 0 := by
    change BrownianSharp.AlignmentPaperFiniteFiber.multiplicity x (x i) ≠ 0
    unfold BrownianSharp.AlignmentPaperFiniteFiber.multiplicity
    apply Finset.card_ne_zero.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  have hterm :
      ((sampleMultiplicity m x i : ℝ≥0∞)⁻¹) •
        (Measure.map (fun z : X × X => (z.1, x' i))
          (γ.measure.restrict F)) (Prod.snd ⁻¹' A) =
        ((m : ℝ≥0)⁻¹) • (Measure.dirac (x' i)) A := by
    have hmap :
        (Measure.map (fun z : X × X => (z.1, x' i))
          (γ.measure.restrict F)) (Prod.snd ⁻¹' A) =
          if x' i ∈ A then γ.measure F else 0 := by
      rw [Measure.map_apply (measurable_fst.prodMk measurable_const)
        (measurable_snd hA)]
      by_cases hx : x' i ∈ A
      · have hpre : (fun z : X × X => (z.1, x' i)) ⁻¹' (Prod.snd ⁻¹' A) =
            Set.univ := by ext z; simp [hx]
        rw [hpre, Measure.restrict_apply_univ]
        simp [hx]
      · have hpre : (fun z : X × X => (z.1, x' i)) ⁻¹' (Prod.snd ⁻¹' A) =
            ∅ := by ext z; simp [hx]
        rw [hpre]
        simp [hx]
    rw [Measure.dirac_apply]
    rw [hmap]
    by_cases hx : x' i ∈ A
    · simp only [hx, if_pos, hmass', Set.indicator_apply,
        ENNReal.smul_def, smul_eq_mul, one_apply, Pi.one_apply]
      have hcancel :
          (sampleMultiplicity m x i : ℝ≥0∞)⁻¹ *
              (sampleMultiplicity m x i : ℝ≥0∞) = 1 := by
        rw [mul_comm]
        exact ENNReal.mul_inv_cancel (by exact_mod_cast hcount) (by simp)
      have hmult : sampleMultiplicityAt m x (x i) = sampleMultiplicity m x i := by
        unfold sampleMultiplicityAt sampleMultiplicity
        unfold BrownianSharp.AlignmentPaperFiniteFiber.multiplicity
        congr 1
        ext j
        simp
      rw [hmult]
      calc
        (sampleMultiplicity m x i : ℝ≥0∞)⁻¹ *
            ((sampleMultiplicity m x i : ℝ≥0∞) * ↑((m : ℝ≥0)⁻¹)) =
            ((sampleMultiplicity m x i : ℝ≥0∞)⁻¹ *
              (sampleMultiplicity m x i : ℝ≥0∞)) * ↑((m : ℝ≥0)⁻¹) := by rw [mul_assoc]
        _ = ↑((m : ℝ≥0)⁻¹) * 1 := by rw [hcancel]; simp
    · simp [hx, ENNReal.smul_def, smul_eq_mul]
  simpa [splitEmpiricalTransportMeasure, F, Measure.smul_apply] using hterm

theorem splitEmpiricalTransportMeasure_fst {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X] {μ : Measure X} {m : ℕ}
    (hm : 0 < m) (x x' : Fin m → X)
    (γ : TransportCoupling μ (empiricalMeasure m hm x)) :
    Measure.map Prod.fst (splitEmpiricalTransportMeasure hm x x' γ) = μ := by
  classical
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_fst hA]
  rw [splitEmpiricalTransportMeasure, Measure.sum_apply _ (measurable_fst hA)]
  simp only [tsum_fintype, Measure.smul_apply]
  let S : Set (X × X) := Prod.fst ⁻¹' A
  have hS : MeasurableSet S := measurable_fst hA
  have hfiber (i : Fin m) : MeasurableSet {z : X × X | z.2 = x i} :=
    measurable_snd (measurableSet_singleton (x i))
  have hterm (i : Fin m) :
      (Measure.map (fun z : X × X => (z.1, x' i))
        (γ.measure.restrict {z | z.2 = x i})) (Prod.fst ⁻¹' A) =
        ∫⁻ z in {z | z.2 = x i}, S.indicator (fun _ => (1 : ℝ≥0∞)) z ∂γ.measure := by
    rw [Measure.map_apply (measurable_fst.prodMk measurable_const) hS]
    have hpre : (fun z : X × X => (z.1, x' i)) ⁻¹' (Prod.fst ⁻¹' A) = S := by
      ext z
      simp [S]
    rw [hpre, Measure.restrict_apply hS]
    have hintegral :
        (∫⁻ z in {z | z.2 = x i}, S.indicator (fun _ => (1 : ℝ≥0∞)) z ∂γ.measure) =
          γ.measure (S ∩ {z | z.2 = x i}) := by
      rw [← lintegral_indicator (hfiber i) (S.indicator (fun _ => (1 : ℝ≥0∞)))]
      rw [Set.indicator_indicator]
      rw [lintegral_indicator ((hfiber i).inter hS)]
      simp [Measure.restrict_apply_univ, Set.inter_comm]
    rw [hintegral]
  have hhelper := AlignmentPaperFiniteFiberMeasure.lintegral_inverse_fiber_partition
    γ.measure x Prod.snd measurable_snd
    (by
      have hsupp : empiricalMeasure m hm x {y | y ∉ Set.range x} = 0 := by
        classical
        have hrange : MeasurableSet (Set.range x)ᶜ :=
          (Set.Finite.measurableSet (Set.finite_range x)).compl
        simp [empiricalMeasure, Measure.sum_apply, Measure.smul_apply,
          Measure.dirac_apply, hrange]
      have hmap := congrArg (fun ν : Measure X => ν ((Set.range x)ᶜ)) γ.snd_map
      rw [Measure.map_apply measurable_snd
        ((Set.Finite.measurableSet (Set.finite_range x)).compl)] at hmap
      have hzero : γ.measure (Prod.snd ⁻¹' (Set.range x)ᶜ) = 0 :=
        hmap.trans hsupp
      rw [ae_iff]
      simpa [Set.preimage, Set.mem_preimage] using hzero)
    (S.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hS)
  calc
    (∑ i : Fin m, (sampleMultiplicity m x i : ℝ≥0∞)⁻¹ *
        (Measure.map (fun z : X × X => (z.1, x' i))
          (γ.measure.restrict {z | z.2 = x i})) (Prod.fst ⁻¹' A)) =
      ∑ i : Fin m, (sampleMultiplicity m x i : ℝ≥0∞)⁻¹ *
        (∫⁻ z in {z | z.2 = x i}, S.indicator (fun _ => (1 : ℝ≥0∞)) z ∂γ.measure) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hterm]
    _ = ∫⁻ z, S.indicator (fun _ => (1 : ℝ≥0∞)) z ∂γ.measure := by
      exact hhelper
    _ = γ.measure S := by
      rw [lintegral_indicator hS]
      simp [S, Measure.restrict_apply_univ]
    _ = μ A := by
      have h := congrArg (fun ν : Measure X => ν A) γ.fst_map
      rw [Measure.map_apply measurable_fst hA] at h
      exact h

noncomputable def splitEmpiricalTransportCoupling {X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] [DecidableEq X] {μ : Measure X} {m : ℕ}
    (hm : 0 < m) (x x' : Fin m → X)
    (γ : TransportCoupling μ (empiricalMeasure m hm x)) :
    TransportCoupling μ (empiricalMeasure m hm x') :=
  ⟨splitEmpiricalTransportMeasure hm x x' γ,
    splitEmpiricalTransportMeasure_fst hm x x' γ,
    splitEmpiricalTransportMeasure_snd hm x x' γ⟩

def empiricalSampleDisplacement {X : Type*} [PseudoEMetricSpace X]
    {m : ℕ} (x x' : Fin m → X) : ℝ≥0∞ :=
  ⨆ i : Fin m, edist (x i) (x' i)

theorem splitEmpiricalTransportCoupling_cost_le {X : Type*}
    [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X]
    [SecondCountableTopology X] [MeasurableSingletonClass X] [DecidableEq X]
    {μ : Measure X} [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m)
    (x x' : Fin m → X)
    (γ : TransportCoupling μ (empiricalMeasure m hm x)) :
    couplingCostTwo (splitEmpiricalTransportCoupling hm x x' γ) ≤
      couplingCostTwo γ + empiricalSampleDisplacement x x' := by
  classical
  let γ' := splitEmpiricalTransportCoupling hm x x' γ
  let δ := empiricalSampleDisplacement x x'
  let f : X × X → ℝ≥0∞ := fun z => edist z.1 z.2
  let g : X × X → ℝ≥0∞ := fun _ => δ
  have hf : Measurable f := measurable_edist
  have hg : Measurable g := measurable_const
  have hmass : γ.measure Set.univ = 1 := by
    have h := congrArg (fun ν : Measure X => ν Set.univ) γ.fst_map
    rw [Measure.map_apply measurable_fst MeasurableSet.univ] at h
    simpa using h
  have hnew :
      (∫⁻ z, edist z.1 z.2 ^ 2 ∂γ'.measure) ≤
        ∑ i : Fin m, (sampleMultiplicity m x i : ℝ≥0∞)⁻¹ *
          (∫⁻ z in {z | z.2 = x i}, (f z + g z) ^ 2 ∂γ.measure) := by
    change (∫⁻ z, edist z.1 z.2 ^ 2 ∂
      splitEmpiricalTransportMeasure hm x x' γ) ≤ _
    rw [splitEmpiricalTransportMeasure, lintegral_sum_measure]
    simp only [tsum_fintype, lintegral_smul_measure]
    simp only [ENNReal.smul_def, smul_eq_mul]
    apply Finset.sum_le_sum
    intro i hi
    let F : Set (X × X) := {z | z.2 = x i}
    have hmap :
        (∫⁻ z, edist z.1 z.2 ^ 2 ∂
          Measure.map (fun z : X × X => (z.1, x' i)) (γ.measure.restrict F)) =
        ∫⁻ z in F, edist z.1 (x' i) ^ 2 ∂γ.measure := by
      rw [lintegral_map (measurable_edist.pow_const 2)
        (measurable_fst.prodMk measurable_const)]
    rw [hmap]
    have hI :
        (∫⁻ z in F, edist z.1 (x' i) ^ 2 ∂γ.measure) ≤
          ∫⁻ z in F, (f z + g z) ^ 2 ∂γ.measure := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurable_snd (measurableSet_singleton (x i)))] with z hz
      have hzx : z.2 = x i := by simpa [F] using hz
      have htri : edist z.1 (x' i) ≤ edist z.1 z.2 + δ := by
        calc
          edist z.1 (x' i) ≤ edist z.1 z.2 + edist z.2 (x' i) := edist_triangle _ _ _
          _ = edist z.1 z.2 + edist (x i) (x' i) := by rw [hzx]
          _ ≤ edist z.1 z.2 + δ := by
            gcongr
            exact le_iSup_of_le i le_rfl
      have hpow := pow_le_pow_left₀ bot_le htri 2
      simpa [f, g] using hpow
    calc
      (sampleMultiplicity m x i : ℝ≥0∞)⁻¹ *
          (∫⁻ z in F, edist z.1 (x' i) ^ 2 ∂γ.measure) =
          (∫⁻ z in F, edist z.1 (x' i) ^ 2 ∂γ.measure) *
            (sampleMultiplicity m x i : ℝ≥0∞)⁻¹ := mul_comm _ _
      _ ≤ (∫⁻ z in F, (f z + g z) ^ 2 ∂γ.measure) *
            (sampleMultiplicity m x i : ℝ≥0∞)⁻¹ := mul_le_mul_left hI _
      _ = (sampleMultiplicity m x i : ℝ≥0∞)⁻¹ *
            (∫⁻ z in F, (f z + g z) ^ 2 ∂γ.measure) := mul_comm _ _
  have hpartition := AlignmentPaperFiniteFiberMeasure.lintegral_inverse_fiber_partition
    γ.measure x Prod.snd measurable_snd
    (by
      have hsupp : empiricalMeasure m hm x {y | y ∉ Set.range x} = 0 := by
        have hrange : MeasurableSet (Set.range x)ᶜ :=
          (Set.Finite.measurableSet (Set.finite_range x)).compl
        simp [empiricalMeasure, Measure.dirac_apply, hrange]
      have hmap := congrArg (fun ν : Measure X => ν ((Set.range x)ᶜ)) γ.snd_map
      rw [Measure.map_apply measurable_snd
        ((Set.Finite.measurableSet (Set.finite_range x)).compl)] at hmap
      have hzero : γ.measure (Prod.snd ⁻¹' (Set.range x)ᶜ) = 0 := hmap.trans hsupp
      rw [ae_iff]
      simpa [Set.preimage, Set.mem_preimage] using hzero)
    (fun z => (f z + g z) ^ 2) ((hf.add hg).pow_const 2)
  have hnew' :
      (∫⁻ z, edist z.1 z.2 ^ 2 ∂γ'.measure) ≤
        ∫⁻ z, (f z + g z) ^ 2 ∂γ.measure := by
    calc
      _ ≤ ∑ i : Fin m, (sampleMultiplicity m x i : ℝ≥0∞)⁻¹ *
          (∫⁻ z in {z | z.2 = x i}, (f z + g z) ^ 2 ∂γ.measure) := hnew
      _ = ∫⁻ z, (f z + g z) ^ 2 ∂γ.measure := hpartition
  have hminkowski := ENNReal.lintegral_Lp_add_le (μ := γ.measure)
    hf.aemeasurable hg.aemeasurable
    (by norm_num : (1 : ℝ) ≤ 2)
  have hcostroot : ennrealSqrt (∫⁻ z, edist z.1 z.2 ^ 2 ∂γ'.measure) ≤
      ennrealSqrt (∫⁻ z, (f z + g z) ^ 2 ∂γ.measure) := by
    apply ENNReal.rpow_le_rpow hnew' (by norm_num)
  have hminkowski' : ennrealSqrt (∫⁻ z, (f z + g z) ^ 2 ∂γ.measure) ≤
      ennrealSqrt (∫⁻ z, f z ^ 2 ∂γ.measure) + δ := by
    calc
      ennrealSqrt (∫⁻ z, (f z + g z) ^ 2 ∂γ.measure) ≤
          ennrealSqrt (∫⁻ z, f z ^ 2 ∂γ.measure) + ennrealSqrt (δ ^ 2) := by
        simpa [ennrealSqrt, ENNReal.rpow_natCast, f, g, hmass] using hminkowski
      _ = ennrealSqrt (∫⁻ z, f z ^ 2 ∂γ.measure) + δ := by
        congr 1
        unfold ennrealSqrt
        convert ENNReal.rpow_rpow_inv (by norm_num : (2 : ℝ) ≠ 0) δ using 1 <;> norm_num
  unfold couplingCostTwo ennrealSqrt at *
  simpa [γ', δ] using le_trans hcostroot hminkowski'

/-- Perturbing the labelled empirical atoms by at most `δ` changes the
Wasserstein-two cost by at most `δ`. The proof transports each arbitrary
coupling by splitting repeated atoms equally among their labels. -/
theorem wassersteinTwo_empirical_perturb_le {X : Type*}
    [MeasurableSpace X] [PseudoMetricSpace X] [BorelSpace X]
    [SecondCountableTopology X] [MeasurableSingletonClass X] [DecidableEq X]
    {μ : Measure X} [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m)
    (x x' : Fin m → X) :
    wassersteinTwo μ (empiricalMeasure m hm x') ≤
      wassersteinTwo μ (empiricalMeasure m hm x) + empiricalSampleDisplacement x x' := by
  classical
  let δ := empiricalSampleDisplacement x x'
  calc
    wassersteinTwo μ (empiricalMeasure m hm x') ≤
        ⨅ γ : TransportCoupling μ (empiricalMeasure m hm x),
          couplingCostTwo γ + δ := by
      apply le_iInf
      intro γ
      calc
        wassersteinTwo μ (empiricalMeasure m hm x') ≤
            couplingCostTwo (splitEmpiricalTransportCoupling hm x x' γ) :=
          iInf_le _ (splitEmpiricalTransportCoupling hm x x' γ)
        _ ≤ couplingCostTwo γ + δ := by
          simpa [δ] using splitEmpiricalTransportCoupling_cost_le hm x x' γ
    _ = wassersteinTwo μ (empiricalMeasure m hm x) + δ := by
      simp [wassersteinTwo, ENNReal.iInf_add, δ]

end BrownianSharp.AlignmentPaperEmpiricalPerturbation
