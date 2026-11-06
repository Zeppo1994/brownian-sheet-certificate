import BrownianSharp.AlignmentPaperFiniteEmpiricalCoupling
import BrownianSharp.AlignmentPaperEmpiricalWasserstein
import BrownianSharp.AlignmentPaperQuantizationAtomicBridge

open MeasureTheory
open scoped ENNReal NNReal

namespace BrownianSharp.AlignmentPaperEmpiricalCellLift

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X]

/-- The measurable nearest-codepoint cells for an enumerated finite codebook. -/
def nearestCell {m : ℕ} (hm : 0 < m) (c : Fin m → X) (i : Fin m) : Set X :=
  (AlignmentPaperQuantizationAtomicBridge.nearestIndex hm c) ⁻¹' {i}

theorem nearestCell_measurable {m : ℕ} (hm : 0 < m) (c : Fin m → X)
    (i : Fin m) : MeasurableSet (nearestCell hm c i) := by
  exact (AlignmentPaperQuantizationAtomicBridge.nearestIndex_measurable hm c)
    (MeasurableSet.singleton i)

/-- Probability measure conditioned on a nearest-codepoint cell. Empty cells
use the corresponding codepoint as a harmless probability fallback. -/
noncomputable def nearestCellLaw {m : ℕ} (hm : 0 < m) (c : Fin m → X)
    (μ : Measure X) (i : Fin m) : Measure X :=
  if h : μ (nearestCell hm c i) = 0 then Measure.dirac (c i)
  else (μ (nearestCell hm c i))⁻¹ • μ.restrict (nearestCell hm c i)

/-- Cell masses used by the nearest-cell mixture representation. -/
def nearestCellWeight {m : ℕ} (hm : 0 < m) (c : Fin m → X)
    (μ : Measure X) (i : Fin m) : ℝ≥0∞ := μ (nearestCell hm c i)

theorem nearestCellLaw_isProbability {m : ℕ} (hm : 0 < m) (c : Fin m → X)
    (μ : Measure X) [IsProbabilityMeasure μ] (i : Fin m) :
    IsProbabilityMeasure (nearestCellLaw hm c μ i) := by
  classical
  constructor
  by_cases h : μ (nearestCell hm c i) = 0
  · simp [nearestCellLaw, h]
  · have hne : μ (nearestCell hm c i) ≠ 0 := h
    have hmass : μ.restrict (nearestCell hm c i) Set.univ =
        μ (nearestCell hm c i) := by
      rw [Measure.restrict_apply_univ]
    have hle : μ (nearestCell hm c i) ≤ 1 := by
      calc
        μ (nearestCell hm c i) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have htop : μ (nearestCell hm c i) ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
    simp only [nearestCellLaw, dif_neg h]
    rw [Measure.smul_apply, hmass]
    rw [smul_eq_mul, ENNReal.inv_mul_cancel hne htop]

theorem nearestCell_weightedLaw_eq_restrict {m : ℕ} (hm : 0 < m)
    (c : Fin m → X) (μ : Measure X) [IsProbabilityMeasure μ] (i : Fin m) :
    μ (nearestCell hm c i) • nearestCellLaw hm c μ i =
      μ.restrict (nearestCell hm c i) := by
  classical
  by_cases h : μ (nearestCell hm c i) = 0
  · simp [nearestCellLaw, h, Measure.restrict_zero_set h]
  · have hne : μ (nearestCell hm c i) ≠ 0 := h
    have hle : μ (nearestCell hm c i) ≤ 1 := by
      calc
        μ (nearestCell hm c i) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    have htop : μ (nearestCell hm c i) ≠ ∞ :=
      ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
    simp only [nearestCellLaw, dif_neg h]
    rw [← smul_assoc]
    change (μ (nearestCell hm c i) * (μ (nearestCell hm c i))⁻¹) •
      μ.restrict (nearestCell hm c i) = _
    rw [ENNReal.mul_inv_cancel hne htop, one_smul]

theorem nearestCell_mixture_eq {m : ℕ} (hm : 0 < m) (c : Fin m → X)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    Measure.sum (fun i : Fin m => μ (nearestCell hm c i) •
      nearestCellLaw hm c μ i) = μ := by
  classical
  have hdisj : Pairwise fun i j => Disjoint (nearestCell hm c i) (nearestCell hm c j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change AlignmentPaperQuantizationAtomicBridge.nearestIndex hm c x = i at hxi
    change AlignmentPaperQuantizationAtomicBridge.nearestIndex hm c x = j at hxj
    exact hij (hxi.symm.trans hxj)
  have hcover : (⋃ i : Fin m, nearestCell hm c i) = Set.univ := by
    ext x
    simp [nearestCell]
  calc
    Measure.sum (fun i : Fin m => μ (nearestCell hm c i) •
        nearestCellLaw hm c μ i) =
      Measure.sum (fun i : Fin m => μ.restrict (nearestCell hm c i)) := by
        congr 1
        funext i
        exact nearestCell_weightedLaw_eq_restrict hm c μ i
    _ = μ := by
      rw [← Measure.restrict_iUnion hdisj (nearestCell_measurable hm c)]
      rw [hcover, Measure.restrict_univ]

/-- The cell-weighted conditional second moment is exactly the ordinary
nearest-codebook distortion integral. -/
theorem nearestCellWeightedDistortion_eq {m : ℕ} (hm : 0 < m)
    (c : Fin m → X) (μ : Measure X) [IsProbabilityMeasure μ] :
    (∑ i : Fin m, nearestCellWeight hm c μ i *
      (∫⁻ x, edist x (c i) ^ 2 ∂nearestCellLaw hm c μ i)) =
      ∫⁻ x, finiteCodebookDistortion hm c x ^ 2 ∂μ := by
  classical
  have hdecomp : Measure.sum (fun i : Fin m => μ.restrict (nearestCell hm c i)) = μ := by
    calc
      Measure.sum (fun i : Fin m => μ.restrict (nearestCell hm c i)) =
          Measure.sum (fun i : Fin m =>
            nearestCellWeight hm c μ i • nearestCellLaw hm c μ i) := by
              congr 1
              funext i
              exact (nearestCell_weightedLaw_eq_restrict hm c μ i).symm
      _ = μ := nearestCell_mixture_eq hm c μ
  have hcell (i : Fin m) : ∀ᵐ x ∂μ.restrict (nearestCell hm c i),
      edist x (c i) ^ 2 = finiteCodebookDistortion hm c x ^ 2 := by
    filter_upwards [ae_restrict_mem (nearestCell_measurable hm c i)] with x hx
    change AlignmentPaperQuantizationAtomicBridge.nearestIndex hm c x = i at hx
    have hproj :
        AlignmentPaperQuantizationAtomicBridge.codebookProjection hm c x = c i := by
      simp [AlignmentPaperQuantizationAtomicBridge.codebookProjection, hx]
    rw [← hproj, AlignmentPaperQuantizationAtomicBridge.codebookProjection_edist_eq]
  have hterm (i : Fin m) :
      nearestCellWeight hm c μ i *
        (∫⁻ x, edist x (c i) ^ 2 ∂nearestCellLaw hm c μ i) =
      ∫⁻ x, finiteCodebookDistortion hm c x ^ 2
        ∂μ.restrict (nearestCell hm c i) := by
    calc
      nearestCellWeight hm c μ i *
          (∫⁻ x, edist x (c i) ^ 2 ∂nearestCellLaw hm c μ i) =
          ∫⁻ x, edist x (c i) ^ 2 ∂
            (nearestCellWeight hm c μ i • nearestCellLaw hm c μ i) := by
              rw [lintegral_smul_measure]
              simp [ENNReal.smul_def]
      _ = ∫⁻ x, finiteCodebookDistortion hm c x ^ 2
          ∂μ.restrict (nearestCell hm c i) := by
              have hmeasure : nearestCellWeight hm c μ i •
                  nearestCellLaw hm c μ i = μ.restrict (nearestCell hm c i) := by
                simpa [nearestCellWeight] using
                  nearestCell_weightedLaw_eq_restrict hm c μ i
              rw [hmeasure]
              exact lintegral_congr_ae (hcell i)
  calc
    (∑ i : Fin m, nearestCellWeight hm c μ i *
        (∫⁻ x, edist x (c i) ^ 2 ∂nearestCellLaw hm c μ i)) =
      ∑ i : Fin m, ∫⁻ x, finiteCodebookDistortion hm c x ^ 2
        ∂μ.restrict (nearestCell hm c i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hterm i
    _ = ∫⁻ x, finiteCodebookDistortion hm c x ^ 2
        ∂Measure.sum (fun i : Fin m => μ.restrict (nearestCell hm c i)) := by
          rw [lintegral_sum_measure]
          simp
    _ = ∫⁻ x, finiteCodebookDistortion hm c x ^ 2 ∂μ := by
          rw [hdecomp]

/-- Lift any finite coupling matrix between the nearest-cell mass vectors to an
actual coupling of the original probability measures. -/
noncomputable def nearestCellTransportCoupling {m : ℕ} (hm : 0 < m)
    (c : Fin m → X) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (w : Fin m → Fin m → ℝ≥0∞)
    (hrow : ∀ i, ∑ j : Fin m, w i j = nearestCellWeight hm c μ i)
    (hcol : ∀ j, ∑ i : Fin m, w i j = nearestCellWeight hm c ν j) :
    TransportCoupling μ ν := by
  exact AlignmentPaperFiniteEmpiricalCoupling.finiteMixtureTransportCoupling μ ν
    (nearestCellLaw hm c μ) (nearestCellLaw hm c ν)
    (nearestCellWeight hm c μ) (nearestCellWeight hm c ν) w
    (nearestCellLaw_isProbability hm c μ)
    (nearestCellLaw_isProbability hm c ν)
    (by simpa [nearestCellWeight] using (nearestCell_mixture_eq hm c μ).symm)
    (by simpa [nearestCellWeight] using (nearestCell_mixture_eq hm c ν).symm)
    hrow hcol

/-- Componentwise cost bound for the actual nearest-cell coupling. -/
theorem nearestCellTransportCoupling_cost_le {m : ℕ} (hm : 0 < m)
    (c : Fin m → X) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (w : Fin m → Fin m → ℝ≥0∞)
    (hrow : ∀ i, ∑ j : Fin m, w i j = nearestCellWeight hm c μ i)
    (hcol : ∀ j, ∑ i : Fin m, w i j = nearestCellWeight hm c ν j)
    (C : Fin m → Fin m → ℝ≥0∞)
    (hcomponent : ∀ i j,
      (∫⁻ z : X × X, edist z.1 z.2 ^ 2 ∂
        (nearestCellLaw hm c μ i).prod (nearestCellLaw hm c ν j)) ≤ C i j) :
    (∫⁻ z : X × X, edist z.1 z.2 ^ 2 ∂
      (nearestCellTransportCoupling hm c μ ν w hrow hcol).measure) ≤
        ∑ i : Fin m, ∑ j : Fin m, w i j * C i j := by
  exact AlignmentPaperFiniteEmpiricalCoupling.finiteMixtureTransportCoupling_cost_le μ ν
    (nearestCellLaw hm c μ) (nearestCellLaw hm c ν)
    (nearestCellWeight hm c μ) (nearestCellWeight hm c ν) w
    (nearestCellLaw_isProbability hm c μ)
    (nearestCellLaw_isProbability hm c ν)
    (by simpa [nearestCellWeight] using (nearestCell_mixture_eq hm c μ).symm)
    (by simpa [nearestCellWeight] using (nearestCell_mixture_eq hm c ν).symm)
    hrow hcol C hcomponent

/-- Coordinatewise common-mass matching gives an explicit balanced matrix for
any two real probability vectors. -/
noncomputable def commonResidualCellWeight {m : ℕ} (p q : Fin m → ℝ) :
    Fin m → Fin m → ℝ≥0∞ :=
  let c : Fin m → ℝ := fun i => min (p i) (q i)
  let a : Fin m → ℝ := fun i => p i - c i
  let b : Fin m → ℝ := fun i => q i - c i
  let r : ℝ := ∑ i : Fin m, a i
  AlignmentPaperFiniteEmpiricalCoupling.commonResidualTransportWeight c a b r

def commonResidualCellMass {m : ℕ} (p q : Fin m → ℝ) : ℝ :=
  ∑ i : Fin m, (p i - min (p i) (q i))

theorem commonResidualCellWeight_offDiagonalMass_le {m : ℕ} (p q : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpone : ∑ i : Fin m, p i = 1) (hqone : ∑ i : Fin m, q i = 1) :
    AlignmentPaperFiniteEmpiricalCoupling.offDiagonalMatrixMass
      (commonResidualCellWeight p q) ≤
        ENNReal.ofReal (commonResidualCellMass p q) := by
  classical
  let c : Fin m → ℝ := fun i => min (p i) (q i)
  let a : Fin m → ℝ := fun i => p i - c i
  let b : Fin m → ℝ := fun i => q i - c i
  let r : ℝ := ∑ i : Fin m, a i
  have hc : ∀ i, 0 ≤ c i := fun i => le_min (hp i) (hq i)
  have ha : ∀ i, 0 ≤ a i := fun i => sub_nonneg.mpr (min_le_left _ _)
  have hb : ∀ i, 0 ≤ b i := fun i => sub_nonneg.mpr (min_le_right _ _)
  have hasum : ∑ i : Fin m, a i = r := rfl
  have hbsum : ∑ i : Fin m, b i = r := by
    dsimp [r, a, b, c]
    calc
      (∑ i : Fin m, (q i - min (p i) (q i))) =
          (1 / 2 : ℝ) * ∑ i : Fin m, |p i - q i| := by
            have h := AlignmentPaperFiniteEmpiricalCoupling.commonMassResidual_eq_half_l1
              q p hqone hpone
            simpa [min_comm, abs_sub_comm] using h
      _ = ∑ i : Fin m, (p i - min (p i) (q i)) := by
            symm
            exact AlignmentPaperFiniteEmpiricalCoupling.commonMassResidual_eq_half_l1
              p q hpone hqone
  have hr : 0 ≤ r := by
    dsimp [r]
    exact Finset.sum_nonneg fun i hi => ha i
  have hmass := AlignmentPaperFiniteEmpiricalCoupling.commonResidualTransportWeight_offDiagonalMass_le
    c a b r hr hasum hbsum hc ha hb
  change AlignmentPaperFiniteEmpiricalCoupling.offDiagonalMatrixMass
      (AlignmentPaperFiniteEmpiricalCoupling.commonResidualTransportWeight c a b r) ≤
    ENNReal.ofReal r
  exact hmass

theorem commonResidualWeight_marginals {m : ℕ} (p q : Fin m → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpone : ∑ i : Fin m, p i = 1) (hqone : ∑ i : Fin m, q i = 1) :
      (∀ i, ∑ j : Fin m, commonResidualCellWeight p q i j = ENNReal.ofReal (p i)) ∧
      (∀ j, ∑ i : Fin m, commonResidualCellWeight p q i j = ENNReal.ofReal (q j)) := by
  classical
  let c : Fin m → ℝ := fun i => min (p i) (q i)
  let a : Fin m → ℝ := fun i => p i - c i
  let b : Fin m → ℝ := fun i => q i - c i
  let r : ℝ := ∑ i : Fin m, a i
  have hc : ∀ i, 0 ≤ c i := fun i => le_min (hp i) (hq i)
  have ha : ∀ i, 0 ≤ a i := fun i => sub_nonneg.mpr (min_le_left _ _)
  have hb : ∀ i, 0 ≤ b i := fun i => sub_nonneg.mpr (min_le_right _ _)
  have hasum : ∑ i : Fin m, a i = r := rfl
  have hbsum : ∑ i : Fin m, b i = r := by
    dsimp [r, a, b, c]
    calc
      (∑ i : Fin m, (q i - min (p i) (q i))) =
          (1 / 2 : ℝ) * ∑ i : Fin m, |p i - q i| := by
            have h := AlignmentPaperFiniteEmpiricalCoupling.commonMassResidual_eq_half_l1
              q p hqone hpone
            simpa [min_comm, abs_sub_comm] using h
      _ = ∑ i : Fin m, (p i - min (p i) (q i)) := by
            symm
            exact AlignmentPaperFiniteEmpiricalCoupling.commonMassResidual_eq_half_l1
              p q hpone hqone
  have hr : 0 ≤ r := by
    dsimp [r]
    exact Finset.sum_nonneg fun i hi => ha i
  let M := AlignmentPaperFiniteEmpiricalCoupling.commonResidualMatrix c a b r
  have hMnonneg : ∀ i j, 0 ≤ M i j := by
    intro i j
    by_cases hr0 : r = 0
    · have hazero : ∀ i, a i = 0 := by
        intro i
        have hsum : ∑ k : Fin m, a k = 0 := by rw [hasum, hr0]
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => ha k)).1 hsum i
          (Finset.mem_univ i)
      have hbzero : ∀ j, b j = 0 := by
        intro j
        have hsum : ∑ k : Fin m, b k = 0 := by rw [hbsum, hr0]
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => hb k)).1 hsum j
          (Finset.mem_univ j)
      rw [show M = AlignmentPaperFiniteEmpiricalCoupling.commonResidualMatrix c a b r by rfl,
        AlignmentPaperFiniteEmpiricalCoupling.commonResidualMatrix, hazero i, hbzero j]
      by_cases hij : i = j
      · subst j
        simp
        exact hc i
      · simp [hij]
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      exact AlignmentPaperFiniteEmpiricalCoupling.commonResidualMatrix_nonneg
        c a b r hrpos hc ha hb i j
  have hmatrix :
      (∀ i, (∑ j : Fin m, M i j) = c i + a i) ∧
      (∀ j, (∑ i : Fin m, M i j) = c j + b j) := by
    by_cases hr0 : r = 0
    · have hasum0 : ∑ i : Fin m, a i = 0 := by rw [hasum, hr0]
      have hbsum0 : ∑ i : Fin m, b i = 0 := by rw [hbsum, hr0]
      have h := AlignmentPaperFiniteEmpiricalCoupling.commonResidualMatrix_zero_marginals
        c a b hasum0 hbsum0 ha hb
      exact ⟨by simpa [M, hr0] using h.1, by simpa [M, hr0] using h.2⟩
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have h := AlignmentPaperFiniteEmpiricalCoupling.commonResidualMatrix_marginals
        c a b r hrpos hasum hbsum
      exact ⟨by simpa [M] using h.1, by simpa [M] using h.2⟩
  change (∀ i, ∑ j : Fin m,
      AlignmentPaperFiniteEmpiricalCoupling.commonResidualTransportWeight c a b r i j =
        ENNReal.ofReal (p i)) ∧
    (∀ j, ∑ i : Fin m,
      AlignmentPaperFiniteEmpiricalCoupling.commonResidualTransportWeight c a b r i j =
        ENNReal.ofReal (q j))
  constructor
  · intro i
    rw [show (∑ j : Fin m,
        AlignmentPaperFiniteEmpiricalCoupling.commonResidualTransportWeight c a b r i j) =
        ENNReal.ofReal (∑ j : Fin m, M i j) by
      dsimp [AlignmentPaperFiniteEmpiricalCoupling.commonResidualTransportWeight, M]
      rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun j => AlignmentPaperFiniteEmpiricalCoupling.commonResidualMatrix c a b r i j)
        (fun j hj => hMnonneg i j)]]
    rw [hmatrix.1 i]
    simp [a, c]
  · intro j
    rw [show (∑ i : Fin m,
        AlignmentPaperFiniteEmpiricalCoupling.commonResidualTransportWeight c a b r i j) =
        ENNReal.ofReal (∑ i : Fin m, M i j) by
      dsimp [AlignmentPaperFiniteEmpiricalCoupling.commonResidualTransportWeight, M]
      rw [ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
        (f := fun i => AlignmentPaperFiniteEmpiricalCoupling.commonResidualMatrix c a b r i j)
        (fun i hi => hMnonneg i j)]]
    rw [hmatrix.2 j]
    simp [b, c]

/-- Center-to-center transport cost of the canonical matrix is controlled by
the codebook diameter squared times its common-mass residual. -/
theorem commonResidualCellWeight_centerCost_le {N : ℕ}
    (p q : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hpone : ∑ i : Fin N, p i = 1) (hqone : ∑ i : Fin N, q i = 1)
    (c : Fin N → X) (D : ℝ≥0∞)
    (hdiam : ∀ i j, edist (c i) (c j) ^ 2 ≤ D ^ 2) :
    (∑ i : Fin N, ∑ j : Fin N,
      commonResidualCellWeight p q i j * edist (c i) (c j) ^ 2) ≤
      D ^ 2 * ENNReal.ofReal (commonResidualCellMass p q) := by
  have hres := commonResidualCellWeight_offDiagonalMass_le p q hp hq hpone hqone
  have hcost := AlignmentPaperFiniteEmpiricalCoupling.finiteCouplingMeasure_cost_le_of_offDiagonalMass
    (commonResidualCellWeight p q) c D (ENNReal.ofReal (commonResidualCellMass p q))
    hdiam hres
  calc
    (∑ i : Fin N, ∑ j : Fin N,
      commonResidualCellWeight p q i j * edist (c i) (c j) ^ 2) =
        (∫⁻ z : X × X, edist z.1 z.2 ^ 2 ∂
          AlignmentPaperFiniteEmpiricalCoupling.finiteCouplingMeasure
            (commonResidualCellWeight p q) c) := by
      symm
      exact AlignmentPaperFiniteEmpiricalCoupling.finiteCouplingMeasure_lintegral_edist_sq
        (commonResidualCellWeight p q) c
    _ ≤ D ^ 2 * ENNReal.ofReal (commonResidualCellMass p q) := hcost

/-- Rearranging the lifted coupling cost separates the source and target
within-cell errors from the center-to-center matrix cost. -/
theorem commonResidualCell_weightedCost_expand {N : ℕ}
    (p q : Fin N → ℝ) (w : Fin N → Fin N → ℝ≥0∞)
    (hrow : ∀ i, ∑ j : Fin N, w i j = ENNReal.ofReal (p i))
    (hcol : ∀ j, ∑ i : Fin N, w i j = ENNReal.ofReal (q j))
    (A B : Fin N → ℝ≥0∞) (C : Fin N → Fin N → ℝ≥0∞) :
    (∑ i : Fin N, ∑ j : Fin N, w i j * (A i + C i j + B j)) =
      (∑ i : Fin N, ENNReal.ofReal (p i) * A i) +
      (∑ i : Fin N, ∑ j : Fin N, w i j * C i j) +
      (∑ j : Fin N, ENNReal.ofReal (q j) * B j) := by
  have hsplit :
      (∑ i : Fin N, ∑ j : Fin N, w i j * (A i + C i j + B j)) =
      (∑ i : Fin N, ∑ j : Fin N, w i j * A i) +
      (∑ i : Fin N, ∑ j : Fin N, w i j * C i j) +
      (∑ i : Fin N, ∑ j : Fin N, w i j * B j) := by
    simp_rw [mul_add, Finset.sum_add_distrib]
  have hsource :
      (∑ i : Fin N, ∑ j : Fin N, w i j * A i) =
      ∑ i : Fin N, (∑ j : Fin N, w i j) * A i := by
    congr 1
    funext i
    rw [Finset.sum_mul]
  have htarget :
      (∑ i : Fin N, ∑ j : Fin N, w i j * B j) =
      ∑ j : Fin N, (∑ i : Fin N, w i j) * B j := by
    rw [Finset.sum_comm]
    congr 1
    funext j
    rw [Finset.sum_mul]
  calc
    (∑ i : Fin N, ∑ j : Fin N, w i j * (A i + C i j + B j)) =
        (∑ i : Fin N, ∑ j : Fin N, w i j * A i) +
          (∑ i : Fin N, ∑ j : Fin N, w i j * C i j) +
          (∑ i : Fin N, ∑ j : Fin N, w i j * B j) := hsplit
    _ = (∑ i : Fin N, (∑ j : Fin N, w i j) * A i) +
          (∑ i : Fin N, ∑ j : Fin N, w i j * C i j) +
          (∑ j : Fin N, (∑ i : Fin N, w i j) * B j) := by rw [hsource, htarget]
    _ = (∑ i : Fin N, ENNReal.ofReal (p i) * A i) +
          (∑ i : Fin N, ∑ j : Fin N, w i j * C i j) +
          (∑ j : Fin N, ENNReal.ofReal (q j) * B j) := by simp_rw [hrow, hcol]

/-- Real-valued cell probabilities, obtained from the actual measurable cell
masses. -/
def nearestCellRealWeight {m : ℕ} (hm : 0 < m) (c : Fin m → X)
    (μ : Measure X) (i : Fin m) : ℝ := (nearestCellWeight hm c μ i).toReal

theorem nearestCellRealWeightedDistortion_eq {m : ℕ} (hm : 0 < m)
    (c : Fin m → X) (μ : Measure X) [IsProbabilityMeasure μ] :
    (∑ i : Fin m, ENNReal.ofReal (nearestCellRealWeight hm c μ i) *
      (∫⁻ x, edist x (c i) ^ 2 ∂nearestCellLaw hm c μ i)) =
      ∫⁻ x, finiteCodebookDistortion hm c x ^ 2 ∂μ := by
  calc
    (∑ i : Fin m, ENNReal.ofReal (nearestCellRealWeight hm c μ i) *
        (∫⁻ x, edist x (c i) ^ 2 ∂nearestCellLaw hm c μ i)) =
      ∑ i : Fin m, nearestCellWeight hm c μ i *
        (∫⁻ x, edist x (c i) ^ 2 ∂nearestCellLaw hm c μ i) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hfinite : nearestCellWeight hm c μ i ≠ ∞ := by
            have hle : nearestCellWeight hm c μ i ≤ 1 := by
              calc
                nearestCellWeight hm c μ i ≤ μ Set.univ := measure_mono (Set.subset_univ _)
                _ = 1 := measure_univ
            exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
          simp [nearestCellRealWeight, ENNReal.ofReal_toReal hfinite]
    _ = ∫⁻ x, finiteCodebookDistortion hm c x ^ 2 ∂μ :=
      nearestCellWeightedDistortion_eq hm c μ

noncomputable def nearestCellCouplingWeight {m : ℕ} (hm : 0 < m)
    (c : Fin m → X) (μ ν : Measure X) : Fin m → Fin m → ℝ≥0∞ :=
  commonResidualCellWeight (nearestCellRealWeight hm c μ)
    (nearestCellRealWeight hm c ν)

theorem nearestCellRealWeight_sum_eq_one {m : ℕ} (hm : 0 < m)
    (c : Fin m → X) (μ : Measure X) [IsProbabilityMeasure μ] :
    ∑ i : Fin m, nearestCellRealWeight hm c μ i = 1 := by
  classical
  have hdisj : Pairwise fun i j => Disjoint (nearestCell hm c i) (nearestCell hm c j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    change AlignmentPaperQuantizationAtomicBridge.nearestIndex hm c x = i at hxi
    change AlignmentPaperQuantizationAtomicBridge.nearestIndex hm c x = j at hxj
    exact hij (hxi.symm.trans hxj)
  have hcover : (⋃ i : Fin m, nearestCell hm c i) = Set.univ := by
    ext x
    simp [nearestCell]
  have hsum : ∑ i : Fin m, nearestCellWeight hm c μ i = 1 := by
    have hdecomp : Measure.sum (fun i : Fin m => μ.restrict (nearestCell hm c i)) = μ := by
      rw [← Measure.restrict_iUnion hdisj (nearestCell_measurable hm c), hcover,
        Measure.restrict_univ]
    have h := congrArg (fun ρ : Measure X => ρ Set.univ) hdecomp
    simpa [nearestCellWeight, Measure.sum_apply] using h
  have hfinite : ∀ i : Fin m, nearestCellWeight hm c μ i ≠ ∞ := by
    intro i
    have hle : nearestCellWeight hm c μ i ≤ 1 := by
      calc
        nearestCellWeight hm c μ i ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  rw [show (∑ i : Fin m, nearestCellRealWeight hm c μ i) =
      (∑ i : Fin m, nearestCellWeight hm c μ i).toReal by
        unfold nearestCellRealWeight
        rw [ENNReal.toReal_sum (fun i hi => hfinite i)]]
  rw [hsum]
  simp

theorem nearestCellCouplingWeight_balanced {m : ℕ} (hm : 0 < m) (c : Fin m → X)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∀ i, ∑ j : Fin m, nearestCellCouplingWeight hm c μ ν i j =
      nearestCellWeight hm c μ i) ∧
    (∀ j, ∑ i : Fin m, nearestCellCouplingWeight hm c μ ν i j =
      nearestCellWeight hm c ν j) := by
  let p := nearestCellRealWeight hm c μ
  let q := nearestCellRealWeight hm c ν
  have hp : ∀ i, 0 ≤ p i := fun _ => ENNReal.toReal_nonneg
  have hq : ∀ i, 0 ≤ q i := fun _ => ENNReal.toReal_nonneg
  have hpone : ∑ i : Fin m, p i = 1 := by
    simpa [p] using nearestCellRealWeight_sum_eq_one hm c μ
  have hqone : ∑ i : Fin m, q i = 1 := by
    simpa [q] using nearestCellRealWeight_sum_eq_one hm c ν
  have hmarg := commonResidualWeight_marginals p q hp hq hpone hqone
  have hfiniteμ : ∀ i, nearestCellWeight hm c μ i ≠ ∞ := by
    intro i
    have hle : nearestCellWeight hm c μ i ≤ 1 := by
      calc
        nearestCellWeight hm c μ i ≤ μ Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  have hfiniteν : ∀ i, nearestCellWeight hm c ν i ≠ ∞ := by
    intro i
    have hle : nearestCellWeight hm c ν i ≤ 1 := by
      calc
        nearestCellWeight hm c ν i ≤ ν Set.univ := measure_mono (Set.subset_univ _)
        _ = 1 := measure_univ
    exact ne_of_lt (lt_of_le_of_lt hle ENNReal.one_lt_top)
  constructor
  · intro i
    change (∑ j : Fin m, commonResidualCellWeight p q i j) =
      nearestCellWeight hm c μ i
    rw [hmarg.1 i]
    unfold p nearestCellRealWeight
    rw [ENNReal.ofReal_toReal (hfiniteμ i)]
  · intro j
    change (∑ i : Fin m, commonResidualCellWeight p q i j) =
      nearestCellWeight hm c ν j
    rw [hmarg.2 j]
    unfold q nearestCellRealWeight
    rw [ENNReal.ofReal_toReal (hfiniteν j)]

/-- The nearest-cell category of each member of the actual iid sample. -/
noncomputable def nearestCategorySample {N n : ℕ} (hN : 0 < N)
    (c : Fin N → X) (x : Fin n → X) : Fin n → Fin N :=
  fun k => AlignmentPaperQuantizationAtomicBridge.nearestIndex hN c (x k)

theorem nearestCategorySample_map_iid {N n : ℕ} (hN : 0 < N)
    (c : Fin N → X) (μ : Measure X) [IsProbabilityMeasure μ] :
    Measure.map (nearestCategorySample hN c)
      (AlignmentPaperEmpiricalWasserstein.iidSampleLaw μ n) =
      AlignmentPaperFiniteEmpiricalCoupling.finiteIidSampleLaw
        (Measure.map (AlignmentPaperQuantizationAtomicBridge.nearestIndex hN c) μ) := by
  let g := AlignmentPaperQuantizationAtomicBridge.nearestIndex hN c
  have hg : Measurable g := AlignmentPaperQuantizationAtomicBridge.nearestIndex_measurable hN c
  letI : IsProbabilityMeasure (Measure.map g μ) := by
    dsimp [g]
    infer_instance
  change Measure.map (fun x k => g (x k))
      (Measure.pi fun _ : Fin n => μ) =
    Measure.pi (fun _ : Fin n => Measure.map g μ)
  exact Measure.pi_map_pi (μ := fun _ : Fin n => μ)
    (f := fun _ : Fin n => g) (fun _ => hg.aemeasurable)

/-- The finite-category frequency residual estimate transfers to the labels
of the actual iid samples from any probability measure. -/
theorem nearestCategory_empiricalResidual_lintegral_le {N n : ℕ}
    (hN : 0 < N) (hn : 0 < n) (c : Fin N → X)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    (∫⁻ x : Fin n → X,
      ENNReal.ofReal (AlignmentPaperFiniteEmpiricalCoupling.empiricalFrequencyResidual
        hn (Measure.map (AlignmentPaperQuantizationAtomicBridge.nearestIndex hN c) μ)
        (nearestCategorySample hN c x))
      ∂AlignmentPaperEmpiricalWasserstein.iidSampleLaw μ n) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / n)) := by
  classical
  let ν : Measure (Fin N) :=
    Measure.map (AlignmentPaperQuantizationAtomicBridge.nearestIndex hN c) μ
  let P := AlignmentPaperFiniteEmpiricalCoupling.finiteIidSampleLaw (m := n) ν
  let r : (Fin n → Fin N) → ℝ :=
    AlignmentPaperFiniteEmpiricalCoupling.empiricalFrequencyResidual hn ν
  letI : IsProbabilityMeasure ν := by
    dsimp [ν]
    infer_instance
  letI : IsProbabilityMeasure P := by
    dsimp [P, AlignmentPaperFiniteEmpiricalCoupling.finiteIidSampleLaw]
    infer_instance
  have hnonneg : ∀ y : Fin n → Fin N, 0 ≤ r y := by
    intro y
    dsimp [r, AlignmentPaperFiniteEmpiricalCoupling.empiricalFrequencyResidual]
    positivity
  have hleone : ∀ y : Fin n → Fin N, r y ≤ 1 := by
    intro y
    dsimp [r, AlignmentPaperFiniteEmpiricalCoupling.empiricalFrequencyResidual]
    have hfreqsum := AlignmentPaperFiniteEmpiricalCoupling.sum_empiricalCategoryFrequency_eq_one hn y
    have hmasssum := AlignmentPaperFiniteEmpiricalCoupling.sum_singleton_masses_eq_one ν
    have hmassnonneg : ∀ i : Fin N, 0 ≤ ν.real {i} := fun _ => measureReal_nonneg
    have hmassle : ∀ i : Fin N, ν.real {i} ≤ 1 := fun _ => measureReal_le_one
    have hpoint : ∀ i : Fin N,
        |AlignmentPaperFiniteEmpiricalCoupling.empiricalCategoryFrequency hn y i -
          ν.real {i}| ≤
        AlignmentPaperFiniteEmpiricalCoupling.empiricalCategoryFrequency hn y i +
          ν.real {i} := by
      intro i
      have hq := AlignmentPaperFiniteEmpiricalCoupling.empiricalCategoryFrequency_mem_Icc
        hn y i
      rw [abs_le]
      constructor <;> linarith [hq.1, hq.2, hmassnonneg i, hmassle i]
    have hsum := calc
      (∑ i : Fin N,
          |AlignmentPaperFiniteEmpiricalCoupling.empiricalCategoryFrequency hn y i -
            ν.real {i}|) ≤
          ∑ i : Fin N,
            (AlignmentPaperFiniteEmpiricalCoupling.empiricalCategoryFrequency hn y i +
              ν.real {i}) := Finset.sum_le_sum fun i hi => hpoint i
      _ = 2 := by rw [Finset.sum_add_distrib, hfreqsum, hmasssum]; norm_num
    nlinarith
  have hrmeas : Measurable r := by fun_prop
  have hcatmeas : Measurable (nearestCategorySample (n := n) hN c) := by
    apply measurable_pi_iff.mpr
    intro k
    exact (AlignmentPaperQuantizationAtomicBridge.nearestIndex_measurable hN c).comp
      (measurable_pi_apply k)
  have hrint : Integrable r P := by
    have hbound : ∀ᵐ y ∂P, r y ∈ Set.Icc (0 : ℝ) 1 :=
      ae_of_all P fun y => ⟨hnonneg y, hleone y⟩
    exact (memLp_of_bounded hbound (by fun_prop) 2).integrable one_le_two
  have hmap := nearestCategorySample_map_iid (N := N) (n := n) hN c μ
  have hpush :
      (∫⁻ x : Fin n → X, ENNReal.ofReal (r (nearestCategorySample hN c x))
        ∂AlignmentPaperEmpiricalWasserstein.iidSampleLaw μ n) =
      ∫⁻ y : Fin n → Fin N, ENNReal.ofReal (r y) ∂P := by
    change (∫⁻ x : Fin n → X, ENNReal.ofReal
      (r (nearestCategorySample hN c x))
      ∂AlignmentPaperEmpiricalWasserstein.iidSampleLaw μ n) =
      ∫⁻ y : Fin n → Fin N, ENNReal.ofReal (r y)
        ∂AlignmentPaperFiniteEmpiricalCoupling.finiteIidSampleLaw (m := n) ν
    rw [← hmap]
    rw [lintegral_map (by fun_prop) hcatmeas]
  have hreal := AlignmentPaperFiniteEmpiricalCoupling.empiricalFrequencyResidual_integral_le
    hn ν
  have hconvert :
      (∫⁻ y : Fin n → Fin N, ENNReal.ofReal (r y) ∂P) =
      ENNReal.ofReal (∫ y : Fin n → Fin N, r y ∂P) := by
    symm
    rw [ofReal_integral_eq_lintegral_ofReal hrint (ae_of_all P hnonneg)]
  calc
    (∫⁻ x : Fin n → X, ENNReal.ofReal
      (AlignmentPaperFiniteEmpiricalCoupling.empiricalFrequencyResidual hn ν
        (nearestCategorySample hN c x))
      ∂AlignmentPaperEmpiricalWasserstein.iidSampleLaw μ n) =
        ∫⁻ x : Fin n → X, ENNReal.ofReal (r (nearestCategorySample hN c x))
          ∂AlignmentPaperEmpiricalWasserstein.iidSampleLaw μ n := by rfl
    _ = ∫⁻ y : Fin n → Fin N, ENNReal.ofReal (r y) ∂P := hpush
    _ = ENNReal.ofReal (∫ y : Fin n → Fin N, r y ∂P) := hconvert
    _ ≤ ENNReal.ofReal ((1 / 2 : ℝ) * Real.sqrt ((N : ℝ) / n)) :=
      ENNReal.ofReal_le_ofReal hreal

/-- Three-leg transport bound: source to its cell center, between cell
centers, and from the target center to the empirical sample. -/
theorem edist_sq_le_three_leg {x y a b : X} :
    edist x y ^ 2 ≤ 3 * (edist x a ^ 2 + edist a b ^ 2 + edist b y ^ 2) := by
  have htri : dist x y ≤ dist x a + dist a b + dist b y := by
    calc
      dist x y ≤ dist x a + dist a y := dist_triangle x a y
      _ ≤ dist x a + (dist a b + dist b y) := by
        gcongr
        exact dist_triangle a b y
      _ = dist x a + dist a b + dist b y := by ring
  have hreal : (dist x y) ^ 2 ≤
      3 * ((dist x a) ^ 2 + (dist a b) ^ 2 + (dist b y) ^ 2) := by
    calc
      (dist x y) ^ 2 ≤ (dist x a + dist a b + dist b y) ^ 2 := by
        have hxy : 0 ≤ dist x y := dist_nonneg
        have hxa : 0 ≤ dist x a := dist_nonneg
        have hab : 0 ≤ dist a b := dist_nonneg
        have hby : 0 ≤ dist b y := dist_nonneg
        nlinarith [htri, hxy, hxa, hab, hby]
      _ ≤ 3 * ((dist x a) ^ 2 + (dist a b) ^ 2 + (dist b y) ^ 2) := by
        nlinarith [sq_nonneg (dist x a - dist a b),
          sq_nonneg (dist x a - dist b y), sq_nonneg (dist a b - dist b y)]
  have hnxy : 0 ≤ dist x y := dist_nonneg
  have hnxa : 0 ≤ dist x a := dist_nonneg
  have hnab : 0 ≤ dist a b := dist_nonneg
  have hnby : 0 ≤ dist b y := dist_nonneg
  rw [edist_dist, edist_dist, edist_dist, edist_dist]
  rw [← ENNReal.ofReal_pow hnxy, ← ENNReal.ofReal_pow hnxa,
    ← ENNReal.ofReal_pow hnab, ← ENNReal.ofReal_pow hnby]
  calc
    ENNReal.ofReal (dist x y ^ 2) ≤
        ENNReal.ofReal (3 * (dist x a ^ 2 + dist a b ^ 2 + dist b y ^ 2)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = 3 * ENNReal.ofReal
          (dist x a ^ 2 + dist a b ^ 2 + dist b y ^ 2) := by
        rw [ENNReal.ofReal_mul]
        norm_num
        all_goals norm_num
    _ ≤ 3 * (ENNReal.ofReal (dist x a ^ 2) +
          ENNReal.ofReal (dist a b ^ 2) + ENNReal.ofReal (dist b y ^ 2)) := by
        gcongr
        calc
          ENNReal.ofReal (dist x a ^ 2 + dist a b ^ 2 + dist b y ^ 2) ≤
              ENNReal.ofReal (dist x a ^ 2 + dist a b ^ 2) +
                ENNReal.ofReal (dist b y ^ 2) := ENNReal.ofReal_add_le
          _ ≤ (ENNReal.ofReal (dist x a ^ 2) + ENNReal.ofReal (dist a b ^ 2)) +
                ENNReal.ofReal (dist b y ^ 2) := by
              gcongr
              exact ENNReal.ofReal_add_le

/-- Integrating the three-leg estimate against a product of conditional cell
laws reduces the component cost to the two within-cell distortions and the
distance between cell centers. -/
theorem nearestCell_productCost_le_threeLeg {N : ℕ}
    (c : Fin N → X) (κ η : Measure X)
    [IsProbabilityMeasure κ] [IsProbabilityMeasure η] (i j : Fin N) :
    (∫⁻ z : X × X, edist z.1 z.2 ^ 2 ∂κ.prod η) ≤
      3 * ((∫⁻ x, edist x (c i) ^ 2 ∂κ) + edist (c i) (c j) ^ 2 +
        (∫⁻ y, edist (c j) y ^ 2 ∂η)) := by
  let f : X × X → ℝ≥0∞ := fun z => edist z.1 (c i) ^ 2
  let g : X × X → ℝ≥0∞ := fun _ => edist (c i) (c j) ^ 2
  let h : X × X → ℝ≥0∞ := fun z => edist (c j) z.2 ^ 2
  have hpoint : ∀ z : X × X,
      edist z.1 z.2 ^ 2 ≤ 3 * (f z + g z + h z) := by
    intro z
    simpa [f, g, h] using edist_sq_le_three_leg (x := z.1) (y := z.2)
      (a := c i) (b := c j)
  have hsrc : ∫⁻ z : X × X, f z ∂κ.prod η = ∫⁻ x, edist x (c i) ^ 2 ∂κ := by
    rw [lintegral_prod f (by fun_prop)]
    simp [f]
  have hmid : ∫⁻ z : X × X, g z ∂κ.prod η = edist (c i) (c j) ^ 2 := by
    simp [g]
  have htgt : ∫⁻ z : X × X, h z ∂κ.prod η = ∫⁻ y, edist (c j) y ^ 2 ∂η := by
    rw [lintegral_prod h (by fun_prop)]
    simp [h]
  calc
    (∫⁻ z : X × X, edist z.1 z.2 ^ 2 ∂κ.prod η) ≤
        ∫⁻ z : X × X, 3 * (f z + g z + h z) ∂κ.prod η :=
      lintegral_mono fun z => hpoint z
    _ = 3 * ((∫⁻ z : X × X, f z ∂κ.prod η) +
          (∫⁻ z : X × X, g z ∂κ.prod η) +
          (∫⁻ z : X × X, h z ∂κ.prod η)) := by
      rw [lintegral_const_mul 3 (by fun_prop)]
      rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop)]
    _ = 3 * ((∫⁻ x, edist x (c i) ^ 2 ∂κ) + edist (c i) (c j) ^ 2 +
          (∫⁻ y, edist (c j) y ^ 2 ∂η)) := by rw [hsrc, hmid, htgt]

/-- The actual lifted cell coupling has cost bounded by the weighted sum of
source distortion, center displacement, and empirical distortion terms. -/
theorem nearestCellTransportCoupling_cost_le_threeLeg {N : ℕ} (hN : 0 < N)
    (c : Fin N → X) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (w : Fin N → Fin N → ℝ≥0∞)
    (hrow : ∀ i, ∑ j : Fin N, w i j = nearestCellWeight hN c μ i)
    (hcol : ∀ j, ∑ i : Fin N, w i j = nearestCellWeight hN c ν j) :
    (∫⁻ z : X × X, edist z.1 z.2 ^ 2 ∂
      (nearestCellTransportCoupling hN c μ ν w hrow hcol).measure) ≤
      ∑ i : Fin N, ∑ j : Fin N, w i j *
        (3 * ((∫⁻ x, edist x (c i) ^ 2 ∂nearestCellLaw hN c μ i) +
          edist (c i) (c j) ^ 2 +
          (∫⁻ y, edist (c j) y ^ 2 ∂nearestCellLaw hN c ν j))) := by
  apply nearestCellTransportCoupling_cost_le hN c μ ν w hrow hcol
  intro i j
  letI : IsProbabilityMeasure (nearestCellLaw hN c μ i) :=
    nearestCellLaw_isProbability hN c μ i
  letI : IsProbabilityMeasure (nearestCellLaw hN c ν j) :=
    nearestCellLaw_isProbability hN c ν j
  exact nearestCell_productCost_le_threeLeg c
    (nearestCellLaw hN c μ i) (nearestCellLaw hN c ν j) i j

/-- Direct finite-cell coupling bound for two actual probability laws. The
first and third terms are the two within-cell quadratic distortions; the middle
term is controlled by the diameter and the common-mass residual. -/
theorem wassersteinTwo_le_threeLeg_of_nearestCells {N : ℕ} (hN : 0 < N)
    (c : Fin N → X) (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (D : ℝ≥0∞)
    (hdiam : ∀ i j, edist (c i) (c j) ^ 2 ≤ D ^ 2) :
    let p := nearestCellRealWeight hN c μ
    let q := nearestCellRealWeight hN c ν
    let A : Fin N → ℝ≥0∞ := fun i =>
      ∫⁻ x, edist x (c i) ^ 2 ∂nearestCellLaw hN c μ i
    let B : Fin N → ℝ≥0∞ := fun j =>
      ∫⁻ y, edist (c j) y ^ 2 ∂nearestCellLaw hN c ν j
    wassersteinTwo μ ν ≤ ennrealSqrt (3 *
      ((∑ i : Fin N, ENNReal.ofReal (p i) * A i) +
        D ^ 2 * ENNReal.ofReal (commonResidualCellMass p q) +
        (∑ j : Fin N, ENNReal.ofReal (q j) * B j))) := by
  dsimp
  let p := nearestCellRealWeight hN c μ
  let q := nearestCellRealWeight hN c ν
  let A : Fin N → ℝ≥0∞ := fun i =>
    ∫⁻ x, edist x (c i) ^ 2 ∂nearestCellLaw hN c μ i
  let B : Fin N → ℝ≥0∞ :=
    fun j => ∫⁻ y, edist (c j) y ^ 2 ∂nearestCellLaw hN c ν j
  let w := nearestCellCouplingWeight hN c μ ν
  have hbal := nearestCellCouplingWeight_balanced hN c μ ν
  have hrow := hbal.1
  have hcol := hbal.2
  let γ := nearestCellTransportCoupling hN c μ ν w hrow hcol
  have hcellcost := nearestCellTransportCoupling_cost_le_threeLeg
    hN c μ ν w hrow hcol
  have hpone : ∑ i : Fin N, p i = 1 := by
    simpa [p] using nearestCellRealWeight_sum_eq_one hN c μ
  have hqone : ∑ i : Fin N, q i = 1 := by
    simpa [q] using nearestCellRealWeight_sum_eq_one hN c ν
  have hmat := commonResidualWeight_marginals p q
    (fun i => ENNReal.toReal_nonneg) (fun i => ENNReal.toReal_nonneg) hpone hqone
  have hexpand := commonResidualCell_weightedCost_expand p q w hmat.1 hmat.2 A B
    (fun i j => edist (c i) (c j) ^ 2)
  have hcenters := commonResidualCellWeight_centerCost_le p q
    (fun i => ENNReal.toReal_nonneg) (fun i => ENNReal.toReal_nonneg)
    hpone hqone c D hdiam
  have hcenterBound :
      (∑ i : Fin N, ∑ j : Fin N, w i j * edist (c i) (c j) ^ 2) ≤
        D ^ 2 * ENNReal.ofReal (commonResidualCellMass p q) := by
    simpa [w, nearestCellCouplingWeight, p, q] using hcenters
  have hcost :
      (∫⁻ z : X × X, edist z.1 z.2 ^ 2 ∂γ.measure) ≤
        3 * ((∑ i : Fin N, ENNReal.ofReal (p i) * A i) +
          D ^ 2 * ENNReal.ofReal (commonResidualCellMass p q) +
          (∑ j : Fin N, ENNReal.ofReal (q j) * B j)) := by
    calc
      (∫⁻ z : X × X, edist z.1 z.2 ^ 2 ∂γ.measure) ≤
          ∑ i : Fin N, ∑ j : Fin N, w i j *
            (3 * (A i + edist (c i) (c j) ^ 2 + B j)) := by
              simpa [γ, A, B] using hcellcost
      _ = 3 * (∑ i : Fin N, ∑ j : Fin N,
            w i j * (A i + edist (c i) (c j) ^ 2 + B j)) := by
              calc
                (∑ i : Fin N, ∑ j : Fin N, w i j *
                    (3 * (A i + edist (c i) (c j) ^ 2 + B j))) =
                    ∑ i : Fin N, ∑ j : Fin N,
                      3 * (w i j * (A i + edist (c i) (c j) ^ 2 + B j)) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        apply Finset.sum_congr rfl
                        intro j hj
                        ring
                _ = 3 * (∑ i : Fin N, ∑ j : Fin N,
                    w i j * (A i + edist (c i) (c j) ^ 2 + B j)) := by
                      symm
                      calc
                        3 * (∑ i : Fin N, ∑ j : Fin N,
                            w i j * (A i + edist (c i) (c j) ^ 2 + B j)) =
                            ∑ i : Fin N, 3 * (∑ j : Fin N,
                              w i j * (A i + edist (c i) (c j) ^ 2 + B j)) := by
                                rw [← Finset.mul_sum]
                        _ = ∑ i : Fin N, ∑ j : Fin N,
                              3 * (w i j * (A i + edist (c i) (c j) ^ 2 + B j)) := by
                                apply Finset.sum_congr rfl
                                intro i hi
                                rw [← Finset.mul_sum]
      _ = 3 * ((∑ i : Fin N, ENNReal.ofReal (p i) * A i) +
            (∑ i : Fin N, ∑ j : Fin N, w i j * edist (c i) (c j) ^ 2) +
            (∑ j : Fin N, ENNReal.ofReal (q j) * B j)) := by
              rw [hexpand]
      _ ≤ 3 * ((∑ i : Fin N, ENNReal.ofReal (p i) * A i) +
            D ^ 2 * ENNReal.ofReal (commonResidualCellMass p q) +
            (∑ j : Fin N, ENNReal.ofReal (q j) * B j)) := by
              gcongr
  have hroot : couplingCostTwo γ ≤ ennrealSqrt
      (3 * ((∑ i : Fin N, ENNReal.ofReal (p i) * A i) +
        D ^ 2 * ENNReal.ofReal (commonResidualCellMass p q) +
        (∑ j : Fin N, ENNReal.ofReal (q j) * B j))) := by
    unfold couplingCostTwo ennrealSqrt
    apply ENNReal.rpow_le_rpow
    · exact hcost
    · norm_num
  unfold wassersteinTwo
  exact (iInf_le _ γ).trans hroot

end BrownianSharp.AlignmentPaperEmpiricalCellLift
