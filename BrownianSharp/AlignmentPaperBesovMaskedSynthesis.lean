import BrownianSharp.AlignmentPeriodicFourierReconstruction
import BrownianSharp.AlignmentPeriodicReconstruction
import BrownianSharp.AlignmentPeriodicL1Fourier
import BrownianSharp.AlignmentPeriodicCutoffYoung
import BrownianSharp.AlignmentCountableFiniteOverlapRpow
import BrownianSharp.AtomicBlockKernelL2
import BrownianSharp.SmoothResolution

/-! Real-valued reconstructions of masked subseries of the canonical smooth
Fourier blocks. Complementary masks split an actual periodic function. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperBesovMaskedSynthesis

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AlignmentPeriodicFourierReconstruction
open BrownianSharp.AlignmentPeriodicReconstruction
open BrownianSharp.AlignmentPeriodicL1Fourier
open BrownianSharp.AlignmentPeriodicCutoffYoung
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicCutoffClasses
open BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel
open BrownianSharp.AtomicBlockKernelL2
open UnitAddTorus
open Classical
open scoped ComplexConjugate

private theorem continuousMap_eLpNorm_coe {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (g : C(X, ℂ)) (p : ℝ≥0∞) (μ : Measure X) :
    eLpNorm (⇑g) p μ = eLpNorm (fun x => g x) p μ := rfl

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance (d : ℕ) : Measure.IsAddHaarMeasure
    (volume : Measure (UnitAddTorus (Fin d))) := by
  change Measure.IsAddHaarMeasure
    (Measure.pi (fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle)))
  infer_instance

/-- The complex continuous function represented by the selected canonical
blocks of `f`. -/
def maskedBlockSeries {d : ℕ} (S : Set (Fin d → ℕ)) (f : RealPeriodic d) :
    C(UnitAddTorus (Fin d), ℂ) := by
  classical
  exact ∑' s : Fin d → ℕ, if s ∈ S then block s f else 0

theorem maskedBlockSeries_summable {d : ℕ} {r : ℝ} (hr : 1/2 < r)
    (f : RealPeriodic d) (hf : NikolskyUnitBall 2 r f)
    (S : Set (Fin d → ℕ)) :
    Summable (fun s : Fin d → ℕ => if s ∈ S then block s f else 0) := by
  classical
  have hq0 : 0 ≤ (2 : ℝ) ^ (1 / 2 - r) :=
    Real.rpow_nonneg (by norm_num) _
  have hq1 : (2 : ℝ) ^ (1 / 2 - r) < 1 := by
    rw [Real.rpow_lt_one_iff_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact Or.inl ⟨by norm_num, by linarith⟩
  have hmajor :=
    (summable_shape_geometric d hq0 hq1).mul_left (Real.sqrt ((5 : ℝ) ^ d)
  )
  apply Summable.of_norm_bounded hmajor
  intro s
  by_cases hs : s ∈ S
  · simpa [hs] using nikolsky_two_block_sup_bound s f r hf
  · simp [hs]
    positivity

/-- Fourier coefficients commute with the masked block series.  This is the
coefficient-level bridge needed to analyze a masked realization: the
coefficient functional is a bounded continuous linear map, so it preserves
the absolutely summable block series. -/
theorem maskedBlockSeries_fourierCoefficient {d : ℕ} {r : ℝ}
    (hr : 1/2 < r) (f : RealPeriodic d) (hf : NikolskyUnitBall 2 r f)
    (S : Set (Fin d → ℕ)) (k : Fin d → ℤ) :
    mFourierCoeff (maskedBlockSeries S f) k =
      ∑' s : Fin d → ℕ,
        if s ∈ S then (tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k
        else 0 := by
  classical
  have hsum := (fourierCoefficientCLM k).hasSum
    (maskedBlockSeries_summable hr f hf S).hasSum
  have hsum' : HasSum
      (fun s : Fin d → ℕ =>
        if s ∈ S then (tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k
        else 0)
      (mFourierCoeff (maskedBlockSeries S f) k) := by
    convert hsum using 1
    · funext s
      by_cases hs : s ∈ S
      · simp [hs, fourierCoefficientCLM_apply, block_coefficient]
      · simp [hs, fourierCoefficientCLM_apply, UnitAddTorus.mFourierCoeff]
    · simp only [maskedBlockSeries, fourierCoefficientCLM_apply]
  exact hsum'.tsum_eq.symm

/-- Fourier coefficients of the real part of a continuous complex function. -/
theorem mFourierCoeff_realPart {d : ℕ}
    (g : UnitAddTorus (Fin d) → ℂ)
    (hg : Integrable g (volume : Measure (UnitAddTorus (Fin d))))
    (k : Fin d → ℤ) :
    mFourierCoeff (fun x => ((g x).re : ℂ)) k =
      (mFourierCoeff g k + conj (mFourierCoeff g (-k))) / 2 := by
  have hreal : Integrable (fun x => ((g x).re : ℂ))
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact Complex.ofRealCLM.integrable_comp
      ((@RCLike.reCLM ℂ _).integrable_comp hg)
  have h1 : Integrable (fun x => mFourier (-k) x * g x)
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact hg.bdd_smul 1 (mFourier (-k)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        calc
          ‖mFourier (-k) x‖ ≤ ‖mFourier (-k)‖ := (mFourier (-k)).norm_coe_le_norm x
          _ = 1 := mFourier_norm)
  have h2 : Integrable (fun x => mFourier k x * g x)
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact hg.bdd_smul 1 (mFourier k).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        calc
          ‖mFourier k x‖ ≤ ‖mFourier k‖ := (mFourier k).norm_coe_le_norm x
          _ = 1 := mFourier_norm)
  have h2c : Integrable (fun x => conj (mFourier k x * g x))
      (volume : Measure (UnitAddTorus (Fin d))) := by
    exact h2.congr'_enorm
      (Complex.continuous_conj.comp_aestronglyMeasurable h2.1)
      (Filter.Eventually.of_forall fun x => by simp)
  have hrealFormula (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
    apply Complex.ext <;> simp <;> ring
  have hp : (fun x => mFourier (-k) x • ((g x).re : ℂ)) =
      fun x => (mFourier (-k) x * g x + conj (mFourier k x * g x)) / 2 := by
    funext x
    simp only [smul_eq_mul]
    rw [hrealFormula]
    simp only [map_mul, mFourier_neg]
    ring
  calc
    mFourierCoeff (fun x => ((g x).re : ℂ)) k =
        ∫ x, (mFourier (-k) x * g x + conj (mFourier k x * g x)) / 2 ∂
          (volume : Measure (UnitAddTorus (Fin d))) := by
      unfold mFourierCoeff
      rw [integral_congr_ae (Filter.Eventually.of_forall (congrFun hp))]
    _ = (mFourierCoeff g k + conj (mFourierCoeff g (-k))) / 2 := by
      simp_rw [div_eq_mul_inv]
      rw [integral_mul_const, integral_add h1 h2c, integral_conj]
      simp only [mFourierCoeff, smul_eq_mul, neg_neg, div_eq_mul_inv]

/-- Real-valued periodic inputs have conjugate-symmetric Fourier
coefficients. -/
theorem realPeriodicFourierCoeff_neg {d : ℕ} (f : RealPeriodic d)
    (k : Fin d → ℤ) :
    realPeriodicFourierCoeff f (-k) = conj (realPeriodicFourierCoeff f k) := by
  let g : UnitAddTorus (Fin d) → ℂ := complexifyRealPeriodic f
  have hg : Integrable g (volume : Measure (UnitAddTorus (Fin d))) := by
    exact (complexifyContinuous f).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h := mFourierCoeff_realPart g hg k
  have hreal : (fun x => ((g x).re : ℂ)) = g := by
    funext x
    simp [g, complexifyRealPeriodic]
  rw [hreal] at h
  change realPeriodicFourierCoeff f k =
    (realPeriodicFourierCoeff f k + conj (realPeriodicFourierCoeff f (-k))) / 2 at h
  have hmul' : 2 * realPeriodicFourierCoeff f k =
      realPeriodicFourierCoeff f k + conj (realPeriodicFourierCoeff f (-k)) := by
    calc
      2 * realPeriodicFourierCoeff f k =
          2 * ((realPeriodicFourierCoeff f k +
            conj (realPeriodicFourierCoeff f (-k))) / 2) := by
              exact congrArg (fun z : ℂ => 2 * z) h
      _ = _ := by field_simp
  have hsub : realPeriodicFourierCoeff f k =
      conj (realPeriodicFourierCoeff f (-k)) := by
    calc
      realPeriodicFourierCoeff f k =
          (2 * realPeriodicFourierCoeff f k) - realPeriodicFourierCoeff f k := by ring
      _ = conj (realPeriodicFourierCoeff f (-k)) := by rw [hmul']; ring
  have hconj := congrArg conj hsub
  simpa using hconj.symm

private theorem tensorMultiplier_neg {d : ℕ} (s : Fin d → ℕ)
    (k : Fin d → ℤ) : tensorMultiplier s (-k) = tensorMultiplier s k := by
  unfold tensorMultiplier
  apply Finset.prod_congr rfl
  intro i hi
  simp [SmoothResolution.scalarBlock, SmoothResolution.cutoff_even, neg_div]

/-- A real-valued masked realization. Taking the real part is intentional:
the sum of all blocks is the complexification of the original real function. -/
def maskedBlockRealization {d : ℕ} (S : Set (Fin d → ℕ)) (f : RealPeriodic d)
    (_r : ℝ) (_hr : 1/2 < _r) (_hf : NikolskyUnitBall 2 _r f) : RealPeriodic d := by
  classical
  let u := maskedBlockSeries S f
  exact ⟨fun x => (u x).re, Complex.continuous_re.comp u.continuous⟩

/-- The real masked realization has exactly the selected scalar-multiplier
Fourier coefficients. The real-part symmetrization disappears because the
dyadic multipliers are even and the source is real-valued. -/
theorem maskedBlockRealization_fourierCoefficient {d : ℕ} {r : ℝ}
    (hr : 1/2 < r) (f : RealPeriodic d) (hf : NikolskyUnitBall 2 r f)
    (S : Set (Fin d → ℕ)) (k : Fin d → ℤ) :
    realPeriodicFourierCoeff (maskedBlockRealization S f r hr hf) k =
      ∑' s : Fin d → ℕ,
        if s ∈ S then (tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k
        else 0 := by
  classical
  let g := maskedBlockSeries S f
  have hg : Integrable g (volume : Measure (UnitAddTorus (Fin d))) :=
    g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hreal := mFourierCoeff_realPart g hg k
  have hneg := maskedBlockSeries_fourierCoefficient hr f hf S (-k)
  have hcoefNeg :
      (∑' s : Fin d → ℕ,
          if s ∈ S then (tensorMultiplier s (-k) : ℂ) * realPeriodicFourierCoeff f (-k)
          else 0) =
        conj (∑' s : Fin d → ℕ,
          if s ∈ S then (tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k
          else 0) := by
    have hterm : ∀ s : Fin d → ℕ,
        (if s ∈ S then (tensorMultiplier s (-k) : ℂ) * realPeriodicFourierCoeff f (-k)
          else 0) = conj (if s ∈ S then
            (tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k else 0) := by
      intro s
      by_cases hs : s ∈ S
      · simp [hs, tensorMultiplier_neg, realPeriodicFourierCoeff_neg]
      · simp [hs]
    rw [show (fun s : Fin d → ℕ =>
        if s ∈ S then (tensorMultiplier s (-k) : ℂ) * realPeriodicFourierCoeff f (-k)
          else 0) =
        fun s => conj (if s ∈ S then
          (tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k else 0) by
          funext s; exact hterm s]
    have hcoeffSummable : Summable (fun s : Fin d → ℕ =>
        if s ∈ S then (tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k
        else 0) := by
      have hcoeffHasSum := (fourierCoefficientCLM k).hasSum
        (maskedBlockSeries_summable hr f hf S).hasSum
      have hraw : Summable (fun s : Fin d → ℕ =>
          mFourierCoeff (⇑(if s ∈ S then block s f else 0)) k) := by
        simpa only [fourierCoefficientCLM_apply] using hcoeffHasSum.summable
      refine hraw.congr ?_
      intro s
      by_cases hs : s ∈ S
      · simp [hs, block_coefficient]
      · simp [hs, UnitAddTorus.mFourierCoeff]
    simpa only [Complex.conjCLE_apply] using
      (Complex.conjCLE.map_tsum (f := fun s : Fin d → ℕ =>
        if s ∈ S then (tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k
        else 0)).symm
  rw [realPeriodicFourierCoeff]
  change mFourierCoeff (fun x => ((g x).re : ℂ)) k = _
  rw [hreal]
  rw [maskedBlockSeries_fourierCoefficient hr f hf S k, hneg, hcoefNeg]
  simp

/-- For the fixed smooth resolution, analyzing a masked realization gives
the finite sum of neighboring cross-blocks of the original input. -/
theorem smoothBlock_maskedRealization_eq_closeRow_sum {d : ℕ} {r : ℝ}
    (hr : 1/2 < r) (f : RealPeriodic d) (hf : NikolskyUnitBall 2 r f)
    (S : Set (Fin d → ℕ)) (t : Fin d → ℕ) :
    admissibleBlock smoothResolutionCutoff t (maskedBlockRealization S f r hr hf) =
      ∑ s ∈ closeRow t,
        if s ∈ S then
          admissibleCrossBlock smoothResolutionCutoff smoothResolutionCutoff t s f
        else 0 := by
  classical
  let φ : AdmissibleCutoff := smoothResolutionCutoff
  have hscalar (n : ℕ) (ξ : ℝ) :
      AlignmentPeriodicAdmissibleCutoff.scalarBlock φ n ξ =
        SmoothResolution.scalarBlock n ξ := by
    rfl
  have hsymbol (s : Fin d → ℕ) (k : Fin d → ℤ) :
      admissibleCrossTensorSymbol φ φ t s k =
        (tensorMultiplier t k : ℂ) * (tensorMultiplier s k : ℂ) := by
    unfold admissibleCrossTensorSymbol
    calc
      (∏ i, ((AlignmentPeriodicAdmissibleCutoff.scalarBlock φ (t i) (k i : ℝ) : ℂ) *
          (AlignmentPeriodicAdmissibleCutoff.scalarBlock φ (s i) (k i : ℝ) : ℂ))) =
          ∏ i, ((SmoothResolution.scalarBlock (t i) (k i : ℝ) : ℂ) *
            (SmoothResolution.scalarBlock (s i) (k i : ℝ) : ℂ)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [hscalar, hscalar]
      _ = (∏ i, (SmoothResolution.scalarBlock (t i) (k i : ℝ) : ℂ)) *
          ∏ i, (SmoothResolution.scalarBlock (s i) (k i : ℝ) : ℂ) :=
        Finset.prod_mul_distrib
      _ = (tensorMultiplier t k : ℂ) * (tensorMultiplier s k : ℂ) := by
        rw [← Complex.ofReal_prod (Finset.univ : Finset (Fin d)),
          ← Complex.ofReal_prod (Finset.univ : Finset (Fin d))]
        rfl
  have hbase (k : Fin d → ℤ) :
      (∏ i, (AlignmentPeriodicAdmissibleCutoff.scalarBlock φ (t i)
        (k i : ℝ) : ℂ)) =
        (tensorMultiplier t k : ℂ) := by
    calc
      (∏ i, (AlignmentPeriodicAdmissibleCutoff.scalarBlock φ (t i)
          (k i : ℝ) : ℂ)) =
          ∏ i, (SmoothResolution.scalarBlock (t i) (k i : ℝ) : ℂ) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact congrArg Complex.ofReal (hscalar (t i) (k i : ℝ))
      _ = (tensorMultiplier t k : ℂ) := by
        rw [← Complex.ofReal_prod (Finset.univ : Finset (Fin d))]
        rfl
  have hvanish : ∀ s ∉ closeRow t, ∀ k : Fin d → ℤ,
      (if s ∈ S then
        ((tensorMultiplier t k : ℂ) * (tensorMultiplier s k : ℂ)) *
          realPeriodicFourierCoeff f k else 0) = 0 := by
    intro s hs k
    by_cases hS : s ∈ S
    · rw [if_pos hS]
      have hnot : ¬ closeIndices t s := by
        intro hclose
        exact hs ((closeRow_spec t s).2 hclose)
      obtain ⟨i, hi⟩ := not_forall.mp hnot
      rcases not_and_or.mp hi with hleft | hright
      · have hgap : s i + 2 < t i := by omega
        have hz := admissibleCrossBlock_eq_zero_of_far_lower φ φ t s i hgap f
        have hc := congrArg (fun u : C(UnitAddTorus (Fin d), ℂ) =>
          mFourierCoeff u k) hz
        rw [admissibleCrossBlock_coefficient] at hc
        have hc' : admissibleCrossTensorSymbol φ φ t s k *
            realPeriodicFourierCoeff f k = 0 := by
          have hcz := hc
          have hzero : mFourierCoeff
              (0 : UnitAddTorus (Fin d) → ℂ) k = 0 := by
            simp [UnitAddTorus.mFourierCoeff]
          exact hcz.trans (by simpa using hzero)
        calc
          ((tensorMultiplier t k : ℂ) * (tensorMultiplier s k : ℂ)) *
              realPeriodicFourierCoeff f k =
            admissibleCrossTensorSymbol φ φ t s k * realPeriodicFourierCoeff f k := by
              rw [hsymbol s k]
          _ = 0 := hc'
      · have hgap : t i + 2 < s i := by omega
        have hz := admissibleCrossBlock_eq_zero_of_far_lower φ φ s t i hgap f
        have hc := congrArg (fun u : C(UnitAddTorus (Fin d), ℂ) =>
          mFourierCoeff u k) hz
        rw [admissibleCrossBlock_coefficient] at hc
        have hc' : admissibleCrossTensorSymbol φ φ s t k *
            realPeriodicFourierCoeff f k = 0 := by
          have hcz := hc
          have hzero : mFourierCoeff
              (0 : UnitAddTorus (Fin d) → ℂ) k = 0 := by
            simp [UnitAddTorus.mFourierCoeff]
          exact hcz.trans (by simpa using hzero)
        have hsym : admissibleCrossTensorSymbol φ φ s t k =
            admissibleCrossTensorSymbol φ φ t s k := by
          unfold admissibleCrossTensorSymbol
          apply Finset.prod_congr rfl
          intro j hj
          ring
        calc
          ((tensorMultiplier t k : ℂ) * (tensorMultiplier s k : ℂ)) *
              realPeriodicFourierCoeff f k =
            admissibleCrossTensorSymbol φ φ s t k * realPeriodicFourierCoeff f k := by
              exact congrArg (fun z : ℂ => z * realPeriodicFourierCoeff f k)
                ((hsymbol s k).symm.trans hsym.symm)
          _ = 0 := hc'
    · simp [hS]
  have hcoeff (k : Fin d → ℤ) :
      mFourierCoeff
          (admissibleBlock φ t (maskedBlockRealization S f r hr hf)) k =
        mFourierCoeff
          (⇑(∑ s ∈ closeRow t,
            if s ∈ S then admissibleCrossBlock φ φ t s f else 0)) k := by
    let a : (Fin d → ℕ) → ℂ := fun s =>
      if s ∈ S then (tensorMultiplier s k : ℂ) * realPeriodicFourierCoeff f k else 0
    have ha : Summable a := by
      have hcoeffHasSum := (fourierCoefficientCLM k).hasSum
        (maskedBlockSeries_summable hr f hf S).hasSum
      have hraw : Summable (fun s : Fin d → ℕ =>
          mFourierCoeff (⇑(if s ∈ S then block s f else 0)) k) := by
        simpa only [fourierCoefficientCLM_apply] using hcoeffHasSum.summable
      refine hraw.congr ?_
      intro s
      by_cases hs : s ∈ S
      · simp [a, hs, block_coefficient]
      · simp [a, hs, UnitAddTorus.mFourierCoeff]
    calc
      _ = (tensorMultiplier t k : ℂ) * ∑' s, a s := by
        rw [admissibleBlock_coefficient, hbase, maskedBlockRealization_fourierCoefficient]
      _ = ∑' s, (tensorMultiplier t k : ℂ) * a s := by
        rw [tsum_mul_left]
      _ = ∑ s ∈ closeRow t, (tensorMultiplier t k : ℂ) * a s := by
        exact tsum_eq_sum (f := fun s => (tensorMultiplier t k : ℂ) * a s)
          (L := SummationFilter.unconditional (Fin d → ℕ)) (s := closeRow t)
          (fun s hs => by
            by_cases hS : s ∈ S
            · calc
                (tensorMultiplier t k : ℂ) * a s =
                    ((tensorMultiplier t k : ℂ) * (tensorMultiplier s k : ℂ)) *
                      realPeriodicFourierCoeff f k := by
                        simp only [a, if_pos hS]
                        ring
                _ = 0 := by
                  have hz := hvanish s hs k
                  rw [if_pos hS] at hz
                  exact hz
            · simp [a, hS])
      _ = mFourierCoeff
          (⇑(∑ s ∈ closeRow t,
            if s ∈ S then admissibleCrossBlock φ φ t s f else 0)) k := by
        symm
        rw [← fourierCoefficientCLM_apply k
          (∑ s ∈ closeRow t,
            if s ∈ S then admissibleCrossBlock φ φ t s f else 0)]
        rw [map_sum]
        simp_rw [fourierCoefficientCLM_apply]
        apply Finset.sum_congr rfl
        intro s hs
        by_cases hS : s ∈ S
        · simp only [if_pos hS]
          rw [admissibleCrossBlock_coefficient, hsymbol s k]
          simp only [a, if_pos hS]
          ring
        · simp [a, hS, UnitAddTorus.mFourierCoeff]
  have hLp :
      (admissibleBlock φ t (maskedBlockRealization S f r hr hf)).toLp 2 volume ℂ =
        (∑ s ∈ closeRow t,
          if s ∈ S then admissibleCrossBlock φ φ t s f else 0).toLp 2 volume ℂ := by
    apply mFourierBasis.repr.injective
    ext k
    simp only [mFourierBasis_repr, mFourierCoeff_toLp]
    simpa only [ContinuousMap.coe_sum] using hcoeff k
  have heq := ContinuousMap.toLp_injective volume hLp
  simpa [φ] using heq

private theorem dyadic_weight_close_le {d : ℕ} (r : ℝ) (hr : 0 ≤ r)
    (s t : Fin d → ℕ) (hst : closeIndices s t) :
    (2:ℝ) ^ (r * ∑ i, (s i : ℝ)) ≤
      (2:ℝ) ^ (2 * r * d) * (2:ℝ) ^ (r * ∑ i, (t i : ℝ)) := by
  have hsum : (∑ i, (s i : ℝ)) ≤ (∑ i, (t i : ℝ)) + 2 * d := by
    calc
      (∑ i, (s i : ℝ)) ≤ ∑ i, ((t i : ℝ) + 2) := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast (hst i).1
      _ = (∑ i, (t i : ℝ)) + 2 * d := by
        simp [Finset.sum_add_distrib]
        ring
  have hexp : r * (∑ i, (s i : ℝ)) ≤
      r * (∑ i, (t i : ℝ)) + 2 * r * d := by nlinarith
  calc
    (2:ℝ) ^ (r * ∑ i, (s i : ℝ)) ≤
        (2:ℝ) ^ (r * (∑ i, (t i : ℝ)) + 2 * r * d) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    _ = (2:ℝ) ^ (2 * r * d) * (2:ℝ) ^ (r * ∑ i, (t i : ℝ)) := by
      rw [Real.rpow_add (by norm_num : 0 < (2:ℝ))]
      ring_nf

/-- Weighted block control for a real masked realization. Each output block
is bounded by the finite neighbor sum of the selected input cross-blocks. -/
theorem maskedWeightedBlockNorm_le_closeRow_sum {d : ℕ} {r : ℝ}
    (hr : 1/2 < r) (hrr : 0 ≤ r) (f : RealPeriodic d)
    (hf : NikolskyUnitBall 2 r f) (S : Set (Fin d → ℕ)) (t : Fin d → ℕ)
    (L : ℝ) (hL : 0 ≤ L)
    (hKernel : ∀ s : Fin d → ℕ,
      (∫ x : UnitAddTorus (Fin d), ‖(admissibleBlockKernel smoothResolutionCutoff s) x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d) :
      AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r t
          (maskedBlockRealization S f r hr hf) ≤
        ∑ s ∈ closeRow t,
          if s ∈ S then ENNReal.ofReal (L ^ d * (2:ℝ) ^ (2 * r * d)) *
            AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r s f else 0 := by
  classical
  let φ : AdmissibleCutoff := smoothResolutionCutoff
  have hvolume : (volume : Measure (UnitAddTorus (Fin d))) =
      Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle) := by
    change Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle) = _
    rfl
  let C : ℝ := L ^ d * (2:ℝ) ^ (2 * r * d)
  have hC : 0 ≤ C := by positivity
  have htriangle :
      eLpNorm (admissibleBlock φ t (maskedBlockRealization S f r hr hf)) 2
        (volume : Measure (UnitAddTorus (Fin d))) ≤
        ∑ s ∈ closeRow t,
          if s ∈ S then
            eLpNorm (admissibleCrossBlock φ φ t s f) 2
              (volume : Measure (UnitAddTorus (Fin d))) else 0 := by
    have htri := MeasureTheory.eLpNorm_sum_le
      (μ := (volume : Measure (UnitAddTorus (Fin d))))
      (p := (2 : ℝ≥0∞))
      (f := fun s => fun x : UnitAddTorus (Fin d) =>
        if s ∈ S then admissibleCrossBlock φ φ t s f x else 0)
      (s := closeRow t) (by norm_num : 1 ≤ (2 : ℝ≥0∞))
    have hfun : (∑ s ∈ closeRow t,
        fun x : UnitAddTorus (Fin d) =>
          if s ∈ S then admissibleCrossBlock φ φ t s f x else 0) =
        (fun x => ∑ s ∈ closeRow t,
          if s ∈ S then admissibleCrossBlock φ φ t s f x else 0) := by
      funext x
      simp
    have htri' : eLpNorm (fun x : UnitAddTorus (Fin d) =>
        ∑ s ∈ closeRow t,
          if s ∈ S then admissibleCrossBlock φ φ t s f x else 0) 2
        (volume : Measure (UnitAddTorus (Fin d))) ≤
        ∑ s ∈ closeRow t,
          eLpNorm (fun x : UnitAddTorus (Fin d) =>
            if s ∈ S then admissibleCrossBlock φ φ t s f x else 0) 2
              (volume : Measure (UnitAddTorus (Fin d))) := by
      rw [← hfun]
      exact htri
    have hleft : admissibleBlock φ t (maskedBlockRealization S f r hr hf) =
        ∑ s ∈ closeRow t,
          if s ∈ S then admissibleCrossBlock φ φ t s f else 0 := by
      simpa [φ] using smoothBlock_maskedRealization_eq_closeRow_sum hr f hf S t
    rw [hleft]
    have hfun' : (∑ s ∈ closeRow t,
        if s ∈ S then admissibleCrossBlock φ φ t s f else 0) =
        (fun x : UnitAddTorus (Fin d) => ∑ s ∈ closeRow t,
          if s ∈ S then admissibleCrossBlock φ φ t s f x else 0) := by
      ext x
      change (ContinuousMap.evalCLM ℂ x)
          (∑ s ∈ closeRow t,
            if s ∈ S then admissibleCrossBlock φ φ t s f else 0) = _
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro s hs
      by_cases hS : s ∈ S <;> simp [hS]
    rw [hfun']
    calc
      _ ≤ ∑ s ∈ closeRow t,
          eLpNorm (fun x : UnitAddTorus (Fin d) =>
            if s ∈ S then admissibleCrossBlock φ φ t s f x else 0) 2
              (volume : Measure (UnitAddTorus (Fin d))) := htri'
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        by_cases hS : s ∈ S <;> simp [hS]
  have hweighted :
      ENNReal.ofReal ((2:ℝ) ^ (r * ∑ i, (t i : ℝ))) *
        eLpNorm (admissibleBlock φ t (maskedBlockRealization S f r hr hf)) 2
          (volume : Measure (UnitAddTorus (Fin d))) ≤
        ∑ s ∈ closeRow t,
          if s ∈ S then ENNReal.ofReal C *
            weightedBlockNorm φ 2 r s f else 0 := by
    calc
      _ ≤ ENNReal.ofReal ((2:ℝ) ^ (r * ∑ i, (t i : ℝ))) *
          ∑ s ∈ closeRow t,
            if s ∈ S then eLpNorm (admissibleCrossBlock φ φ t s f) 2
              (volume : Measure (UnitAddTorus (Fin d))) else 0 :=
        mul_le_mul_of_nonneg_left htriangle bot_le
      _ = ∑ s ∈ closeRow t,
          ENNReal.ofReal ((2:ℝ) ^ (r * ∑ i, (t i : ℝ))) *
            (if s ∈ S then eLpNorm (admissibleCrossBlock φ φ t s f) 2
              (volume : Measure (UnitAddTorus (Fin d))) else 0) := by
        rw [Finset.mul_sum]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro s hs
        by_cases hS : s ∈ S
        · simp only [if_pos hS]
          have hclose : closeIndices t s := (closeRow_spec t s).1 hs
          have hw := dyadic_weight_close_le r hrr t s hclose
          have hreal : (2:ℝ)^(r*∑ i,(t i:ℝ)) * L^d ≤
              C * (2:ℝ)^(r*∑ i,(s i:ℝ)) := by
            dsimp [C]
            calc
              _ ≤ ((2:ℝ)^(2*r*d) * (2:ℝ)^(r*∑ i,(s i:ℝ))) * L^d :=
                mul_le_mul_of_nonneg_right hw (by positivity)
              _ = _ := by ring
          have hcross :=
            admissibleCrossBlock_eLpNorm_le_of_kernel_bound_ennreal
              φ φ t s f (2 : ℝ≥0∞) (by norm_num) L hL hKernel
          have hcross' : eLpNorm (admissibleCrossBlock φ φ t s f) 2
              (volume : Measure (UnitAddTorus (Fin d))) ≤
              ENNReal.ofReal (L ^ d) * eLpNorm (admissibleBlock φ s f) 2
                (volume : Measure (UnitAddTorus (Fin d))) := by
            have hcrossPi :
                eLpNorm (admissibleCrossBlock φ φ t s f) 2
                    (Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) ≤
                  ENNReal.ofReal (L ^ d) * eLpNorm (admissibleBlock φ s f) 2
                    (Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) := by
              simpa only [BrownianSharp.unitAddTorus_volume_eq_productHaar d] using hcross
            simpa only [hvolume] using hcrossPi
          unfold AlignmentPeriodicCutoffClasses.weightedBlockNorm
          calc
            _ ≤ ENNReal.ofReal ((2:ℝ)^(r*∑ i,(t i:ℝ)) * L^d) *
                eLpNorm (admissibleBlock φ s f) 2
                  (volume : Measure (UnitAddTorus (Fin d))) := by
              calc
                _ ≤ ENNReal.ofReal ((2:ℝ)^(r*∑ i,(t i:ℝ))) *
                    (ENNReal.ofReal (L^d) *
                      eLpNorm (admissibleBlock φ s f) 2
                        (volume : Measure (UnitAddTorus (Fin d)))) :=
                  mul_le_mul_of_nonneg_left hcross' bot_le
                _ = _ := by
                  calc
                    _ = (ENNReal.ofReal ((2:ℝ)^(r*∑ i,(t i:ℝ))) *
                        ENNReal.ofReal (L^d)) *
                          eLpNorm (admissibleBlock φ s f) 2
                            (volume : Measure (UnitAddTorus (Fin d))) := by ac_rfl
                    _ = _ := by
                      rw [← ENNReal.ofReal_mul (by positivity :
                        0 ≤ (2:ℝ)^(r*∑ i,(t i:ℝ)))]
            _ ≤ ENNReal.ofReal C *
                (ENNReal.ofReal ((2:ℝ)^(r*∑ i,(s i:ℝ))) *
                  eLpNorm (admissibleBlock φ s f) 2
                    (volume : Measure (UnitAddTorus (Fin d)))) := by
              have hcoef := ENNReal.ofReal_le_ofReal hreal
              calc
                _ = ENNReal.ofReal ((2:ℝ)^(r*∑ i,(t i:ℝ)) * L^d) *
                    eLpNorm (admissibleBlock φ s f) 2
                      (volume : Measure (UnitAddTorus (Fin d))) := rfl
                _ ≤ _ := by
                  calc
                    _ ≤ ENNReal.ofReal (C * (2:ℝ)^(r*∑ i,(s i:ℝ))) *
                        eLpNorm (admissibleBlock φ s f) 2
                          (volume : Measure (UnitAddTorus (Fin d))) :=
                      mul_le_mul_of_nonneg_right hcoef bot_le
                    _ = ENNReal.ofReal C *
                        (ENNReal.ofReal ((2:ℝ)^(r*∑ i,(s i:ℝ))) *
                          eLpNorm (admissibleBlock φ s f) 2
                            (volume : Measure (UnitAddTorus (Fin d)))) := by
                      rw [ENNReal.ofReal_mul hC]
                      ac_rfl
          rw [hvolume, BrownianSharp.unitAddTorus_volume_eq_productHaar d]
        · simp [hS]
  unfold AlignmentPeriodicCutoffClasses.weightedBlockNorm
  simpa [C, φ, hvolume, BrownianSharp.unitAddTorus_volume_eq_productHaar d,
    continuousMap_eLpNorm_coe, SmoothResolution.weightedBlockNorm] using hweighted

/-- Global finite-overlap form of the masked block estimate. The estimate is
stated with an actual selected input sequence, ready for the ℓ²/ℓ∞ endpoint
summation argument. -/
theorem maskedWeightedBlockNorm_le_tsum {d : ℕ} {r : ℝ}
    (hr : 1/2 < r) (hrr : 0 ≤ r) (f : RealPeriodic d)
    (hf : NikolskyUnitBall 2 r f) (S : Set (Fin d → ℕ))
    (L : ℝ) (hL : 0 ≤ L)
    (hKernel : ∀ s : Fin d → ℕ,
      (∫ x : UnitAddTorus (Fin d), ‖(admissibleBlockKernel smoothResolutionCutoff s) x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d)
    (t : Fin d → ℕ) :
    AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r t
        (maskedBlockRealization S f r hr hf) ≤
      ENNReal.ofReal (L ^ d * (2:ℝ)^(2*r*d)) *
        ∑' s : Fin d → ℕ,
          if closeIndices t s then
            if s ∈ S then AlignmentPeriodicCutoffClasses.weightedBlockNorm
              smoothResolutionCutoff 2 r s f else 0
          else 0 := by
  classical
  have hlocal := maskedWeightedBlockNorm_le_closeRow_sum hr hrr f hf S t L hL hKernel
  have htsum : (∑' s : Fin d → ℕ,
      if closeIndices t s then
        if s ∈ S then AlignmentPeriodicCutoffClasses.weightedBlockNorm
          smoothResolutionCutoff 2 r s f else 0 else 0) =
      ∑ s ∈ closeRow t,
        if s ∈ S then AlignmentPeriodicCutoffClasses.weightedBlockNorm
          smoothResolutionCutoff 2 r s f else 0 := by
    calc
      _ = ∑ s ∈ closeRow t,
          (if closeIndices t s then
            if s ∈ S then AlignmentPeriodicCutoffClasses.weightedBlockNorm
              smoothResolutionCutoff 2 r s f else 0 else 0) :=
        tsum_eq_sum (f := fun s : Fin d → ℕ =>
          if closeIndices t s then
            if s ∈ S then AlignmentPeriodicCutoffClasses.weightedBlockNorm
              smoothResolutionCutoff 2 r s f else 0 else 0)
          (L := SummationFilter.unconditional (Fin d → ℕ)) (s := closeRow t)
          (fun s hs => by
            exact if_neg (fun hclose => hs ((closeRow_spec t s).2 hclose)))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro s hs
        simp [(closeRow_spec t s).1 hs]
  calc
    _ ≤ ∑ s ∈ closeRow t,
        if s ∈ S then ENNReal.ofReal (L ^ d * (2:ℝ)^(2*r*d)) *
          AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r s f else 0 := hlocal
    _ = ENNReal.ofReal (L ^ d * (2:ℝ)^(2*r*d)) *
        ∑' s : Fin d → ℕ,
          if closeIndices t s then
            if s ∈ S then AlignmentPeriodicCutoffClasses.weightedBlockNorm
              smoothResolutionCutoff 2 r s f else 0 else 0 := by
      calc
        _ = ∑ s ∈ closeRow t,
            ENNReal.ofReal (L ^ d * (2:ℝ)^(2*r*d)) *
              (if s ∈ S then AlignmentPeriodicCutoffClasses.weightedBlockNorm
                smoothResolutionCutoff 2 r s f else 0) := by
          apply Finset.sum_congr rfl
          intro s hs
          by_cases hS : s ∈ S <;> simp [hS]
        _ = ENNReal.ofReal (L ^ d * (2:ℝ)^(2*r*d)) *
            ∑ s ∈ closeRow t,
              if s ∈ S then AlignmentPeriodicCutoffClasses.weightedBlockNorm
                smoothResolutionCutoff 2 r s f else 0 := by rw [Finset.mul_sum]
        _ = _ := by rw [← htsum]

private theorem closeRow_card_bound {d : ℕ} (t : Fin d → ℕ) :
    (closeRow t).card ≤ 5 ^ d := by
  classical
  let B := Fintype.piFinset (fun i : Fin d => Finset.Icc (t i - 2) (t i + 2))
  have hsub : closeRow t ⊆ B := by
    intro s hs
    have hclose := (closeRow_spec t s).1 hs
    apply Fintype.mem_piFinset.mpr
    intro i
    simp only [B, Finset.mem_Icc]
    have hi := hclose i
    exact ⟨by omega, by omega⟩
  calc
    (closeRow t).card ≤ B.card := Finset.card_le_card hsub
    _ = ∏ i : Fin d, (Finset.Icc (t i - 2) (t i + 2)).card := by
      simp [B, Fintype.card_piFinset]
    _ ≤ ∏ _i : Fin d, 5 := by
      apply Finset.prod_le_prod
      · intro i hi
        rw [Nat.card_Icc]
        omega
    _ = 5 ^ d := by simp

private theorem closeCol_card_bound {d : ℕ} (t : Fin d → ℕ) :
    (closeCol t).card ≤ 5 ^ d := by
  classical
  let B := Fintype.piFinset (fun i : Fin d => Finset.Icc (t i - 2) (t i + 2))
  have hsub : closeCol t ⊆ B := by
    intro s hs
    have hclose := (closeCol_spec s t).1 hs
    apply Fintype.mem_piFinset.mpr
    intro i
    simp only [B, Finset.mem_Icc]
    have hi := hclose i
    exact ⟨by omega, by omega⟩
  calc
    (closeCol t).card ≤ B.card := Finset.card_le_card hsub
    _ = ∏ i : Fin d, (Finset.Icc (t i - 2) (t i + 2)).card := by
      simp [B, Fintype.card_piFinset]
    _ ≤ ∏ _i : Fin d, 5 := by
      apply Finset.prod_le_prod
      · intro i hi
        rw [Nat.card_Icc]
        omega
    _ = 5 ^ d := by simp

/-- Actual Besov-energy estimate for a masked reconstruction. This is the
finite-overlap step that turns selected coefficient blocks into the two
endpoint balls used by the paper's K-method decomposition. -/
theorem maskedBesovEnergy_le_selectedEnergy {d : ℕ} {r : ℝ}
    (hr : 1/2 < r) (hrr : 0 ≤ r) (f : RealPeriodic d)
    (hf : NikolskyUnitBall 2 r f) (S : Set (Fin d → ℕ))
    (L : ℝ) (hL : 0 ≤ L)
    (hKernel : ∀ s : Fin d → ℕ,
      (∫ x : UnitAddTorus (Fin d), ‖(admissibleBlockKernel smoothResolutionCutoff s) x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d)
    (theta : ℝ≥0∞) (htheta : theta ≠ ⊤) (hone : 1 ≤ theta.toReal)
    (E : ℝ≥0∞)
    (hselected : (∑' s : Fin d → ℕ,
      if s ∈ S then
        (AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff
          2 r s f) ^ theta.toReal else 0) ≤ E) :
    (∑' t : Fin d → ℕ,
      (AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r t
        (maskedBlockRealization S f r hr hf)) ^ theta.toReal) ≤
      (ENNReal.ofReal (L ^ d * (2:ℝ)^(2*r*d)) * (5 ^ d : ℝ≥0∞)) ^ theta.toReal * E := by
  classical
  let A : ℝ≥0∞ := ENNReal.ofReal (L ^ d * (2:ℝ)^(2*r*d))
  let N : ℕ := 5 ^ d
  have hN : 0 < N := by dsimp [N]; positivity
  have hrow : ∀ t : Fin d → ℕ, (closeRow t).card ≤ N := by
    intro t
    exact closeRow_card_bound t
  have hcol : ∀ s : Fin d → ℕ, (closeCol s).card ≤ N := by
    intro s
    exact closeCol_card_bound s
  let out : (Fin d → ℕ) → ℝ≥0∞ := fun t =>
    AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r t
      (maskedBlockRealization S f r hr hf)
  let inp : (Fin d → ℕ) → ℝ≥0∞ := fun s =>
    AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r s f
  let selected : (Fin d → ℕ) → ℝ≥0∞ := fun s => if s ∈ S then inp s else 0
  have hpoint : ∀ t, out t ≤ A * ∑' s : Fin d → ℕ,
      if closeIndices t s then selected s else 0 := by
    intro t
    simpa [out, inp, selected, A] using
      maskedWeightedBlockNorm_le_tsum hr hrr f hf S L hL hKernel t
  have hsum := BrownianSharp.AlignmentCountableFiniteOverlapRpow.countable_overlap_rpow_tsum_le
    (fun t s => closeIndices t s)
    (fun t : Fin d → ℕ => closeRow t) (fun s : Fin d → ℕ => closeCol s)
    closeRow_spec closeCol_spec
    A N hN theta.toReal hone hrow hcol out
      (fun s => selected s) hpoint
  have hselected' : (∑' s : Fin d → ℕ, selected s ^ theta.toReal) ≤ E := by
    have hp : 0 < theta.toReal := lt_of_lt_of_le (by norm_num) hone
    simpa [selected, inp, ENNReal.zero_rpow_of_pos hp] using hselected
  calc
    _ = ∑' t : Fin d → ℕ, out t ^ theta.toReal := by rfl
    _ ≤ (A * (N : ℝ≥0∞)) ^ theta.toReal *
          ∑' s : Fin d → ℕ, selected s ^ theta.toReal := hsum
    _ ≤ (A * (N : ℝ≥0∞)) ^ theta.toReal * E := by
      exact mul_le_mul_of_nonneg_left hselected' (by positivity)
    _ = _ := by simp [A, N]

/-- Supremum-endpoint version of masked finite-overlap control. -/
theorem maskedWeightedBlockNorm_le_selectedSup {d : ℕ} {r : ℝ}
    (hr : 1/2 < r) (hrr : 0 ≤ r) (f : RealPeriodic d)
    (hf : NikolskyUnitBall 2 r f) (S : Set (Fin d → ℕ))
    (L : ℝ) (hL : 0 ≤ L)
    (hKernel : ∀ s : Fin d → ℕ,
      (∫ x : UnitAddTorus (Fin d), ‖(admissibleBlockKernel smoothResolutionCutoff s) x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d)
    (B : ℝ≥0∞)
    (hselected : ∀ s, s ∈ S →
      AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r s f ≤ B)
    (t : Fin d → ℕ) :
    AlignmentPeriodicCutoffClasses.weightedBlockNorm smoothResolutionCutoff 2 r t
        (maskedBlockRealization S f r hr hf) ≤
      ENNReal.ofReal (L ^ d * (2:ℝ)^(2*r*d)) * (5 ^ d : ℝ≥0∞) * B := by
  classical
  let A : ℝ≥0∞ := ENNReal.ofReal (L ^ d * (2:ℝ)^(2*r*d))
  have hpoint := maskedWeightedBlockNorm_le_tsum hr hrr f hf S L hL hKernel t
  have hsum : (∑' s : Fin d → ℕ,
      if closeIndices t s then
        if s ∈ S then AlignmentPeriodicCutoffClasses.weightedBlockNorm
          smoothResolutionCutoff 2 r s f else 0 else 0) ≤ (5 ^ d : ℝ≥0∞) * B := by
    rw [tsum_eq_sum (f := fun s : Fin d → ℕ =>
      if closeIndices t s then
        if s ∈ S then AlignmentPeriodicCutoffClasses.weightedBlockNorm
          smoothResolutionCutoff 2 r s f else 0 else 0)
      (L := SummationFilter.unconditional (Fin d → ℕ)) (s := closeRow t)
      (fun s hs => if_neg (fun hclose => hs ((closeRow_spec t s).2 hclose)))]
    calc
      _ ≤ ∑ s ∈ closeRow t, B := by
        apply Finset.sum_le_sum
        intro s hs
        by_cases hS : s ∈ S <;> simp only [if_pos ((closeRow_spec t s).1 hs), hS]
        · exact hselected s hS
        · simp
      _ = (closeRow t).card * B := by simp
      _ ≤ (5 ^ d : ℝ≥0∞) * B := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast closeRow_card_bound t) bot_le
  calc
    _ ≤ A * (∑' s : Fin d → ℕ,
        if closeIndices t s then
          if s ∈ S then AlignmentPeriodicCutoffClasses.weightedBlockNorm
            smoothResolutionCutoff 2 r s f else 0 else 0) := by
      simpa [A] using hpoint
    _ ≤ A * ((5 ^ d : ℝ≥0∞) * B) := mul_le_mul_of_nonneg_left hsum bot_le
    _ = _ := by simp [A, mul_assoc]

/-- Complementary masked subseries reconstruct the input function exactly. -/
theorem complementary_maskedBlockRealizations_add {d : ℕ} {r : ℝ}
    (hr : 1/2 < r) (f : RealPeriodic d) (hf : NikolskyUnitBall 2 r f)
    (S : Set (Fin d → ℕ)) :
    maskedBlockRealization S f r hr hf +
      maskedBlockRealization Sᶜ f r hr hf = f := by
  classical
  have hfull := nikolsky_two_blocks_hasSum r hr f hf
  have hsplit : (fun s : Fin d → ℕ => if s ∈ S then block s f else 0) +
      (fun s : Fin d → ℕ => if s ∈ Sᶜ then block s f else 0) =
      fun s => block s f := by
    funext s
    by_cases hs : s ∈ S <;> simp [hs]
  have hadd := HasSum.add
    (maskedBlockSeries_summable hr f hf S).hasSum
    (maskedBlockSeries_summable hr f hf Sᶜ).hasSum
  have hcombined : HasSum (fun s : Fin d → ℕ => block s f)
      (maskedBlockSeries S f + maskedBlockSeries Sᶜ f) := by
    exact HasSum.congr_fun hadd (fun s => by
      simpa using (congrFun hsplit s).symm)
  have hseries : maskedBlockSeries S f + maskedBlockSeries Sᶜ f =
      complexifyContinuous f := by
    exact hcombined.unique hfull
  ext x
  have h := congrArg (fun g : C(UnitAddTorus (Fin d), ℂ) => g x) hseries
  change (maskedBlockSeries S f x).re +
      (maskedBlockSeries Sᶜ f x).re = f x
  have hre := congrArg Complex.re h
  simpa [Complex.add_re, complexifyContinuous] using hre

end BrownianSharp.AlignmentPaperBesovMaskedSynthesis
