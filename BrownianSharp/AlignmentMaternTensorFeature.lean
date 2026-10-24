import BrownianSharp.AlignmentMaternContinuousFeature
import BrownianSharp.AlignmentSigmaFiniteL2Tensor
import BrownianSharp.AlignmentFractionalTensorOperator

/-! The actual unit-variance stationary tensor Matérn covariance as a
continuous feature in the real product spectral L2 space. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentMaternTensorFeature
open AlignmentMaternSpectralFeature AlignmentMaternScalarFeature
open AlignmentMaternContinuousFeature

abbrev SpectralProductL2 {d : ℕ} (κ : Fin d → ℝ) (h : ℝ) :=
  Lp ℝ 2 (Measure.pi (fun i => spectralMeasure (κ i) h))

def maternSheetFeature {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    C(BrownianCubeAnchor d, SpectralProductL2 κ h) := by
  letI (i : Fin d) : IsFiniteMeasure (spectralMeasure (κ i) h) :=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  exact {
    toFun := fun t => AlignmentSigmaFiniteL2Tensor.tensorContinuous
      (fun i => normalizedAxis (κ i) h (t.val i) (hκ i) hh)
    continuous_toFun := AlignmentSigmaFiniteL2Tensor.tensorContinuous.cont.comp
      (continuous_pi fun i => (normalizedAxis_continuous (κ i) h (hκ i) hh).comp
        ((continuous_apply i).comp continuous_subtype_val))
  }

def maternSheetCovariance {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h)
    (s t : BrownianCubeAnchor d) : ℝ :=
  ∏ i, normalizedCovariance (κ i) h (s.val i) (t.val i) (hκ i) hh

theorem maternSheetFeature_gram {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (s t : BrownianCubeAnchor d) :
    inner ℝ (maternSheetFeature κ h hκ hh s) (maternSheetFeature κ h hκ hh t) =
      maternSheetCovariance κ h hκ hh s t := by
  letI (i : Fin d) : IsFiniteMeasure (spectralMeasure (κ i) h) :=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  change inner ℝ (AlignmentSigmaFiniteL2Tensor.productVector _)
    (AlignmentSigmaFiniteL2Tensor.productVector _) = _
  rw [AlignmentSigmaFiniteL2Tensor.productVector_inner]
  apply Finset.prod_congr rfl
  intro i hi
  exact normalizedAxis_inner (κ i) h _ _ (hκ i) hh

theorem maternSheetFeature_norm {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (t : BrownianCubeAnchor d) :
    ‖maternSheetFeature κ h hκ hh t‖ = 1 := by
  letI (i : Fin d) : IsFiniteMeasure (spectralMeasure (κ i) h) :=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  change ‖AlignmentSigmaFiniteL2Tensor.productVector _‖ = _
  rw [AlignmentSigmaFiniteL2Tensor.productVector_norm]
  simp only [normalizedAxis_norm, Finset.prod_const_one]

theorem maternSheetCovariance_diagonal {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (t : BrownianCubeAnchor d) :
    maternSheetCovariance κ h hκ hh t t = 1 := by
  rw [← maternSheetFeature_gram, real_inner_self_eq_norm_sq,
    maternSheetFeature_norm, one_pow]

end BrownianSharp.AlignmentMaternTensorFeature
