import BrownianSharp.AlignmentPaperSignedKernelOperator
import BrownianSharp.External.WeakCZ.BadPieceL1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperSignedKernelBadSeries

open BrownianSharp.AlignmentPaperSignedKernelOperator
open BrownianSharp.External.WeakCZ

local instance circleMeasureSpace_badSeries : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance circleProbability_badSeries : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The pointwise sum of the mean-zero pieces on a countable disjoint
measurable family. -/
def badPieceSeries {I : Type*} [Countable I]
    (μ : Measure UnitAddCircle) (E : I → Set UnitAddCircle)
    (f : UnitAddCircle → ℂ) (x : UnitAddCircle) : ℂ :=
  ∑' i, badPiece μ (E i) f x

/-- The good part associated with the preceding bad-piece series. -/
def goodPart {I : Type*} [Countable I]
    (μ : Measure UnitAddCircle) (E : I → Set UnitAddCircle)
    (f : UnitAddCircle → ℂ) (x : UnitAddCircle) : ℂ :=
  f x - badPieceSeries μ E f x

theorem badPieceSeries_aestronglyMeasurable
    {I : Type*} [Countable I] (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (E : I → Set UnitAddCircle) (f : UnitAddCircle → ℂ)
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hf : Integrable f μ) :
    AEStronglyMeasurable (badPieceSeries μ E f) μ := by
  apply AEStronglyMeasurable.tsum
  intro i
  exact (integrable_badPiece μ (E i) f (hE i) hf).aestronglyMeasurable

theorem badPieceSeries_lintegral_enorm_le
    {I : Type*} [Countable I] (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (E : I → Set UnitAddCircle) (f : UnitAddCircle → ℂ)
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hf : Integrable f μ) :
    ∫⁻ x, ‖badPieceSeries μ E f x‖ₑ ∂μ ≤ 2 * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  have hnormMeas : ∀ i, AEMeasurable (fun x => ‖badPiece μ (E i) f x‖ₑ) μ := by
    intro i
    exact (integrable_badPiece μ (E i) f (hE i) hf).aestronglyMeasurable.enorm
  calc
    _ ≤ ∫⁻ x, ∑' i, ‖badPiece μ (E i) f x‖ₑ ∂μ := by
      apply lintegral_mono
      intro x
      exact enorm_tsum_le_tsum_enorm
    _ = ∑' i, ∫⁻ x, ‖badPiece μ (E i) f x‖ₑ ∂μ := lintegral_tsum hnormMeas
    _ ≤ 2 * ∫⁻ x, ‖f x‖ₑ ∂μ :=
      tsum_lintegral_enorm_badPiece_le μ E f hE hdisj hf

theorem badPieceSeries_integrable
    {I : Type*} [Countable I] (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (E : I → Set UnitAddCircle) (f : UnitAddCircle → ℂ)
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hf : Integrable f μ) : Integrable (badPieceSeries μ E f) μ := by
  have hsm := badPieceSeries_aestronglyMeasurable μ E f hE hdisj hf
  refine ⟨hsm, ?_⟩
  change (∫⁻ x, ‖badPieceSeries μ E f x‖ₑ ∂μ) < ⊤
  calc
    _ ≤ 2 * ∫⁻ x, ‖f x‖ₑ ∂μ := badPieceSeries_lintegral_enorm_le μ E f hE hdisj hf
    _ < ⊤ := by
      have hfinite : HasFiniteIntegral f μ := hf.2
      change (∫⁻ x, ‖f x‖ₑ ∂μ) < ⊤ at hfinite
      exact ENNReal.mul_lt_top (by norm_num) hfinite

lemma goodPart_integrable
    {I : Type*} [Countable I] (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (E : I → Set UnitAddCircle) (f : UnitAddCircle → ℂ)
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hf : Integrable f μ) : Integrable (goodPart μ E f) μ := by
  exact hf.sub (badPieceSeries_integrable μ E f hE hdisj hf)

lemma goodPart_aestronglyMeasurable
    {I : Type*} [Countable I] (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (E : I → Set UnitAddCircle) (f : UnitAddCircle → ℂ)
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hf : Integrable f μ) : AEStronglyMeasurable (goodPart μ E f) μ := by
  exact (goodPart_integrable μ E f hE hdisj hf).aestronglyMeasurable

lemma goodPart_lintegral_enorm_le_three
    {I : Type*} [Countable I] (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (E : I → Set UnitAddCircle) (f : UnitAddCircle → ℂ)
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hf : Integrable f μ) :
    ∫⁻ x, ‖goodPart μ E f x‖ₑ ∂μ ≤ 3 * ∫⁻ x, ‖f x‖ₑ ∂μ := by
  have hfMeas := hf.aestronglyMeasurable.enorm
  calc
    _ ≤ ∫⁻ x, ‖f x‖ₑ + ‖badPieceSeries μ E f x‖ₑ ∂μ := by
      apply lintegral_mono
      intro x
      exact enorm_sub_le
    _ = ∫⁻ x, ‖f x‖ₑ ∂μ +
        ∫⁻ x, ‖badPieceSeries μ E f x‖ₑ ∂μ :=
      lintegral_add_left' hfMeas _
    _ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ + 2 * ∫⁻ x, ‖f x‖ₑ ∂μ :=
      add_le_add_right (badPieceSeries_lintegral_enorm_le μ E f hE hdisj hf) _
    _ = 3 * ∫⁻ x, ‖f x‖ₑ ∂μ := by ring

private theorem finite_kernel_lintegral_badPiece_sum_ne_top
    {I : Type*} [Countable I] (μ : Measure UnitAddCircle) [IsFiniteMeasure μ]
    (E : I → Set UnitAddCircle) (f : UnitAddCircle → ℂ)
    (hE : ∀ i, MeasurableSet (E i)) (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hf : Integrable f μ) (N : ℕ) (ε : Fin (N+1) → ℝ)
    (x : UnitAddCircle) :
    ∑' i, ∫⁻ y, ‖circleSignedKernel N ε (x-y) * badPiece μ (E i) f y‖ₑ ∂μ ≠ ⊤ := by
  rcases circleSignedKernel_bdd N ε with ⟨M,hM⟩
  let B := max M 0
  have hB : 0 ≤ B := le_max_right _ _
  have hK (y : UnitAddCircle) : ‖circleSignedKernel N ε (x-y)‖ ≤ B := by
    exact (hM ⟨x-y,rfl⟩).trans (le_max_left _ _)
  have hpieces := tsum_lintegral_enorm_badPiece_le μ E f hE hdisj hf
  have hmul : ∀ i, ∫⁻ y, ‖circleSignedKernel N ε (x-y) * badPiece μ (E i) f y‖ₑ ∂μ ≤
      ENNReal.ofReal B * ∫⁻ y, ‖badPiece μ (E i) f y‖ₑ ∂μ := by
    intro i
    calc
      _ ≤ ∫⁻ y, ENNReal.ofReal B * ‖badPiece μ (E i) f y‖ₑ ∂μ := by
        apply lintegral_mono
        intro y
        change ‖circleSignedKernel N ε (x-y) * badPiece μ (E i) f y‖ₑ ≤ _
        calc
          _ = ‖circleSignedKernel N ε (x-y)‖ₑ *
                ‖badPiece μ (E i) f y‖ₑ := enorm_mul _ _
          _ = ENNReal.ofReal ‖circleSignedKernel N ε (x-y)‖ *
                ‖badPiece μ (E i) f y‖ₑ := by
              rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq, coe_nnnorm]
          _ ≤ ENNReal.ofReal B * ‖badPiece μ (E i) f y‖ₑ := by
              gcongr
              exact hK y
      _ = ENNReal.ofReal B * ∫⁻ y, ‖badPiece μ (E i) f y‖ₑ ∂μ := by
        rw [lintegral_const_mul' _ _ (ENNReal.ofReal_ne_top)]
  have hle : ∑' i, ∫⁻ y, ‖circleSignedKernel N ε (x-y) * badPiece μ (E i) f y‖ₑ ∂μ ≤
      ENNReal.ofReal B * (2 * ∫⁻ x, ‖f x‖ₑ ∂μ) := by
    calc
      _ ≤ ∑' i, ENNReal.ofReal B * ∫⁻ y, ‖badPiece μ (E i) f y‖ₑ ∂μ :=
        ENNReal.tsum_le_tsum hmul
      _ = ENNReal.ofReal B * (∑' i, ∫⁻ y, ‖badPiece μ (E i) f y‖ₑ ∂μ) := by
        rw [ENNReal.tsum_mul_left]
      _ ≤ _ := by gcongr
  have hsource : (∫⁻ x, ‖f x‖ₑ ∂μ) ≠ ⊤ := by
    have hfinite : HasFiniteIntegral f μ := hf.2
    change (∫⁻ x, ‖f x‖ₑ ∂μ) < ⊤ at hfinite
    exact ne_of_lt hfinite
  have htwosource : (2 : ℝ≥0∞) * ∫⁻ x, ‖f x‖ₑ ∂μ ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) hsource
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top htwosource) hle

/-- Applying the finite signed Circle convolution to a disjoint bad-piece
series commutes with its countable sum. The kernel constant may depend on the
finite depth; no estimate uniform in depth is used here. -/
theorem circleSignedConvolutionOperator_badPieceSeries
    {I : Type*} [Countable I] (E : I → Set UnitAddCircle)
    (f : UnitAddCircle → ℂ) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hf : Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (N : ℕ) (ε : Fin (N+1) → ℝ) (x : UnitAddCircle) :
    circleSignedConvolutionOperator N ε (badPieceSeries
      (AddCircle.haarAddCircle : Measure UnitAddCircle) E f) x =
      ∑' i, circleSignedConvolutionOperator N ε
        (badPiece (AddCircle.haarAddCircle : Measure UnitAddCircle) (E i) f) x := by
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  have hbi (i : I) : Integrable (badPiece μ (E i) f) μ :=
    integrable_badPiece μ (E i) f (hE i) hf
  have hFint (i : I) : Integrable (fun y : UnitAddCircle =>
      circleSignedKernel N ε (x-y) * badPiece μ (E i) f y) μ := by
    exact circleSignedConvolutionOperator_integrand_integrable N ε (hbi i) x
  have hFsum := finite_kernel_lintegral_badPiece_sum_ne_top μ E f hE hdisj hf N ε x
  have hpoint (y : UnitAddCircle) :
      circleSignedKernel N ε (x-y) * badPieceSeries μ E f y =
        ∑' i, circleSignedKernel N ε (x-y) * badPiece μ (E i) f y := by
    rw [badPieceSeries, ← tsum_mul_left]
  rw [circleSignedConvolutionOperator]
  rw [show (fun y : UnitAddCircle => circleSignedKernel N ε (x-y) *
      badPieceSeries μ E f y) = fun y => ∑' i,
        circleSignedKernel N ε (x-y) * badPiece μ (E i) f y by
          funext y
          exact hpoint y]
  rw [integral_tsum (fun i => (hFint i).aestronglyMeasurable) hFsum]
  apply tsum_congr
  intro i
  rfl

/-- Exact bad/good operator decomposition for the actual finite signed
smooth-resolution Circle convolution. -/
theorem circleSignedConvolutionOperator_good_bad_decomposition
    {I : Type*} [Countable I] (E : I → Set UnitAddCircle)
    (f : UnitAddCircle → ℂ) (hE : ∀ i, MeasurableSet (E i))
    (hdisj : Pairwise fun i j => Disjoint (E i) (E j))
    (hf : Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (N : ℕ) (ε : Fin (N+1) → ℝ) :
    circleSignedConvolutionOperator N ε f =
      circleSignedConvolutionOperator N ε (goodPart
        (AddCircle.haarAddCircle : Measure UnitAddCircle) E f) +
      fun x => ∑' i, circleSignedConvolutionOperator N ε
        (badPiece (AddCircle.haarAddCircle : Measure UnitAddCircle) (E i) f) x := by
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  let bsum := badPieceSeries μ E f
  let g := goodPart μ E f
  have hb : Integrable bsum μ := badPieceSeries_integrable μ E f hE hdisj hf
  have hg : Integrable g μ := goodPart_integrable μ E f hE hdisj hf
  have hlin := circleSignedConvolutionOperator_badPieceSeries E f hE hdisj hf N ε
  funext x
  have hadd := circleSignedConvolutionOperator_add_eq N ε hg hb
  have hdecomp : g + bsum = f := by
    funext y
    simp [g, goodPart, bsum, badPieceSeries, sub_add_cancel]
  calc
    circleSignedConvolutionOperator N ε f x =
        circleSignedConvolutionOperator N ε (g + bsum) x := by rw [hdecomp]
    _ = circleSignedConvolutionOperator N ε g x +
        circleSignedConvolutionOperator N ε bsum x := congrFun hadd x
    _ = circleSignedConvolutionOperator N ε g x +
        ∑' i, circleSignedConvolutionOperator N ε
          (badPiece (AddCircle.haarAddCircle : Measure UnitAddCircle) (E i) f) x := by
        rw [hlin x]

end BrownianSharp.AlignmentPaperSignedKernelBadSeries
