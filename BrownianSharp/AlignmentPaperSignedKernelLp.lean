import BrownianSharp.External.WeakCZ.CircleBadSeries
import BrownianSharp.AlignmentPaperSignedKernelSquareLp

/-! Unconditional signed-kernel Lp and smooth square-function bounds. The
weak-(1,1) input is the compiled actual Circle Calderón–Zygmund endpoint;
callers provide only the ordinary range and sign hypotheses.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperSignedKernelLp

open BrownianSharp.AlignmentPaperSignedKernelOperator
open BrownianSharp.AlignmentPaperSignedKernelSquareLp
open BrownianSharp.External.WeakCZ

/-- The fixed weak-(1,1) constant supplied by the actual Circle CZ proof. -/
noncomputable def uniformSignedKernelWeakConstant : ℝ :=
  Classical.choose exists_circle_signed_convolution_weak_one

theorem uniformSignedKernelWeakConstant_nonneg :
    0 ≤ uniformSignedKernelWeakConstant :=
  (Classical.choose_spec exists_circle_signed_convolution_weak_one).1

/-- Actual weak-(1,1) estimate, uniform over all finite depths and signs. -/
theorem circleSignedConvolutionOperator_weak_one
    (N : ℕ) (ε : Fin (N+1) → ℝ) (hε : ∀ s, |ε s| ≤ 1)
    (f : UnitAddCircle → ℂ)
    (hf : Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle))
    {t : ℝ} (ht : 0 < t) :
    (AddCircle.haarAddCircle : Measure UnitAddCircle)
      {y | t < ‖circleSignedConvolutionOperator N ε f y‖} ≤
      ENNReal.ofReal (uniformSignedKernelWeakConstant/t) *
        ∫⁻ x, ENNReal.ofReal (‖f x‖)
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  exact (Classical.choose_spec exists_circle_signed_convolution_weak_one).2
    N ε hε f hf t ht

/-- Unconditional signed convolution Lp bound for every `1 < p < 2`. Its
constant is uniform in finite kernel depth, coefficient signs, and input. -/
theorem circleSignedConvolutionOperator_lintegral_lp_le
    (N : ℕ) (ε : Fin (N+1) → ℝ) (hε : ∀ s, |ε s| ≤ 1)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : Lp ℂ (ENNReal.ofReal p)
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    ∫⁻ y : UnitAddCircle,
      ENNReal.ofReal (‖circleSignedConvolutionOperator N ε f y‖^p)
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) ≤
      ENNReal.ofReal ((2:ℝ)^p *
        (p*uniformSignedKernelWeakConstant/(p-1)+p/(2-p))) *
      ∫⁻ x : UnitAddCircle, ENNReal.ofReal (‖f x‖^p)
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  exact circleSignedConvolutionOperator_lintegral_lp_le_of_weak_one
    N ε hε uniformSignedKernelWeakConstant_nonneg hp1 hp2
    (fun g hg t ht => circleSignedConvolutionOperator_weak_one N ε hε g hg ht) f

/-- Unconditional Hilbert-valued smooth square-function Lp bound. -/
theorem circleSmoothSquareFunction_vector_lintegral_lp_le
    (N m : ℕ) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (u : Fin m → Lp ℂ (ENNReal.ofReal p)
      (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    ∫⁻ x : UnitAddCircle, ENNReal.ofReal
      ((∑ i : Fin m, ∑ s : Fin (N+1),
        ‖circleSmoothBlockConvolution s.val (u i) x‖^2)^(p/2))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) ≤
      ENNReal.ofReal ((24*(2:ℝ)^(p/2))^2 *
        (2^p*(p*uniformSignedKernelWeakConstant/(p-1)+p/(2-p)))) *
      ∫⁻ x : UnitAddCircle, ENNReal.ofReal
        ((∑ i : Fin m, ‖u i x‖^2)^(p/2))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  have hweak : ∀ (ε : Fin (N+1) → ℝ), (∀ s, |ε s| ≤ 1) →
      ∀ g, Integrable g (AddCircle.haarAddCircle : Measure UnitAddCircle) →
        ∀ t > 0,
          (AddCircle.haarAddCircle : Measure UnitAddCircle)
            {y | t < ‖circleSignedConvolutionOperator N ε g y‖} ≤
          ENNReal.ofReal (uniformSignedKernelWeakConstant/t) *
            ∫⁻ x, ENNReal.ofReal (‖g x‖)
              ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    intro ε hε g hg t ht
    exact circleSignedConvolutionOperator_weak_one N ε hε g hg ht
  exact circleSmoothSquareFunction_vector_lintegral_lp_le_of_weak_one
    N m uniformSignedKernelWeakConstant_nonneg hp1 hp2 hweak u

end BrownianSharp.AlignmentPaperSignedKernelLp
