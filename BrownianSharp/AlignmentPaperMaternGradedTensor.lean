import BrownianSharp.AlignmentPaperMaternSpectralFiltration
import BrownianSharp.AlignmentMaternTensorFeature
import BrownianSharp.AlignmentSigmaFiniteL2Tensor
import BrownianSharp.AlignmentNestedProjectionGrades

/-! Tensor frames for the actual Matérn spectral feature. The only analytic
input left open here is the scalar projection residual for the normalized
axis; all tensorization identities are proved for the concrete product L². -/

noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperMaternGradedTensor

open BrownianSharp.AlignmentPaperMaternSpectralFiltration
open BrownianSharp.AlignmentPaperMaternSpectralApproximation
open BrownianSharp.AlignmentMaternTensorFeature
open BrownianSharp.AlignmentMaternContinuousFeature
open BrownianSharp.AlignmentMaternSpectralFeature
open BrownianSharp.AlignmentMaternScalarFeature
open BrownianSharp.AlignmentSigmaFiniteL2Tensor
open BrownianSharp.AlignmentNestedProjectionGrades

abbrev TensorL2 {d : ℕ} (κ : Fin d → ℝ) (h : ℝ) := SpectralProductL2 κ h

def axisFiltration {d : ℕ} (κ : Fin d → ℝ) (h : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    ∀ i : Fin d, ℕ → Submodule ℝ (SpectralAxisL2 (κ i) h) := by
  intro i N
  exact cumulativeLevelSpace (κ i) h q N (hκ i) hh

def tensorGradedFrame {d M : ℕ} (κ : Fin d → ℝ) (h : ℝ) (q : ℕ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (a : ∀ i : Fin d,
      GradedFrameIndex (axisFiltration κ h q hκ hh i) M) : TensorL2 κ h := by
  letI (i : Fin d) : IsFiniteMeasure (spectralMeasure (κ i) h) :=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  exact productVector (fun i => gradedFrame (axisFiltration κ h q hκ hh i)
    (fun N => cumulativeLevelSpace_finiteDimensional (κ i) h q N (hκ i) hh) M (a i))

theorem tensorGradedFrame_orthonormal {d M : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (q : ℕ) (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    Orthonormal ℝ (tensorGradedFrame κ h q hκ hh (M := M)) := by
  classical
  letI (i : Fin d) : IsFiniteMeasure (spectralMeasure (κ i) h) :=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  apply productVector_orthonormal
  intro i
  exact cumulativeGradedFrame_orthonormal (κ i) h q M (hκ i) hh

theorem maternSheetFeature_inner_tensorGradedFrame {d M : ℕ}
    (κ : Fin d → ℝ) (h : ℝ) (q : ℕ) (hκ : ∀ i, 0 < κ i)
    (hh : 0 < h) (t : BrownianCubeAnchor d)
    (a : ∀ i : Fin d,
      GradedFrameIndex (axisFiltration κ h q hκ hh i) M) :
    ⟪maternSheetFeature κ h hκ hh t, tensorGradedFrame κ h q hκ hh a⟫ =
      ∏ i : Fin d,
        ⟪normalizedAxis (κ i) h (t.val i) (hκ i) hh,
          gradedFrame (axisFiltration κ h q hκ hh i)
            (fun N => cumulativeLevelSpace_finiteDimensional (κ i) h q N (hκ i) hh)
            M (a i)⟫ := by
  letI (i : Fin d) : IsFiniteMeasure (spectralMeasure (κ i) h) :=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  change ⟪productVector _ , productVector _⟫ = _
  rw [productVector_inner]

end BrownianSharp.AlignmentPaperMaternGradedTensor
