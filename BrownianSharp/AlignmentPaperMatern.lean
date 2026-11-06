import BrownianSharp.AlignmentMaternTensorFeature
import BrownianSharp.AlignmentMaternComplexFeature
import BrownianSharp.AlignmentMaternComplexWindow
import BrownianSharp.AlignmentMaternWindowWeight
import BrownianSharp.AlignmentPeriodicFeatureEntropy
import BrownianSharp.AlignmentPeriodicScaledClassTransfer

/-!
A covariance and entropy-lower-bound step for tensor Matérn features.

This records how positive coordinate amplitudes `c i` scale the covariance
represented by the normalized tensor feature. Here `c i` multiplies the
normalized axis covariance; it is not a raw spectral-density parameter. The
feature Gram identities and a periodic Sobolev source argument prove a sharp
entropy lower bound for the canonical feature ball, including positive raw
spectral amplitudes. This module does not identify the Cameron–Martin space
of an arbitrary Gaussian field or prove matching entropy/width upper bounds
or the full two-sided small-deviation rate.
-/

noncomputable section

open HaarQuarter
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperMatern

open BrownianSharp.AlignmentMaternTensorFeature
open BrownianSharp.AlignmentMaternSpectralFeature
open BrownianSharp.AlignmentMaternScalarFeature
open BrownianSharp.AlignmentMaternContinuousFeature
open BrownianSharp.AlignmentMaternSpectralWeights
open BrownianSharp.AlignmentMaternComplexFeature
open BrownianSharp.AlignmentMaternComplexWindow
open BrownianSharp.AlignmentMaternWindowWeight
open BrownianSharp.AlignmentFractionalSheetRKHS
open BrownianSharp.AlignmentPeriodicFeatureEntropy
open BrownianSharp.AlignmentPeriodicScaledClassTransfer

/-- The scalar Matérn spectral mass cancels the normalization in the
unit-variance axis covariance. -/
theorem spectralMass_mul_normalizedCovariance (κ h s t : ℝ)
    (hκ : 0 < κ) (hh : 0 < h) :
    spectralMass κ h * normalizedCovariance κ h s t hκ hh =
      stationaryCovariance κ h s t := by
  rw [normalizedCovariance, ← scalarFeature_norm_sq κ h 0 hκ hh]
  have hN := scalarFeature_norm_pos κ h 0 hκ hh
  field_simp [ne_of_gt hN]

/-- The real feature with the actual positive one-dimensional spectral
amplitudes `c i` and densities `c i * (κᵢ²+ξ²)^(-h-1/2)`. Its covariance is
the product of the corresponding unnormalized stationary Matérn covariances.
This identifies the spectral-amplitude scaling at the feature-Gram level;
the Gaussian-law/Cameron–Martin and rate transfers remain separate. -/
def maternSheetFeatureWithSpectralAmplitude {d : ℕ}
    (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h) :
    C(BrownianCubeAnchor d, SpectralProductL2 κ h) := by
  let P : ℝ := ∏ i, c i * spectralMass (κ i) h
  have hP : 0 < P := Finset.prod_pos fun i hi =>
    mul_pos (hc i) (spectralMass_pos (κ i) h (hκ i) hh)
  exact Real.sqrt P • maternSheetFeature κ h hκ hh

/-- The spectral-amplitude-scaled tensor feature has exactly the covariance
kernel specified by the coordinate spectral densities, up to the shared
Fourier convention already used in `stationaryCovariance`. -/
theorem maternSheetFeatureWithSpectralAmplitude_gram {d : ℕ}
    (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h)
    (s t : BrownianCubeAnchor d) :
    inner ℝ (maternSheetFeatureWithSpectralAmplitude κ c h hκ hc hh s)
      (maternSheetFeatureWithSpectralAmplitude κ c h hκ hc hh t) =
        ∏ i, c i * stationaryCovariance (κ i) h (s.val i) (t.val i) := by
  let P : ℝ := ∏ i, c i * spectralMass (κ i) h
  have hP : 0 < P := Finset.prod_pos fun i hi =>
    mul_pos (hc i) (spectralMass_pos (κ i) h (hκ i) hh)
  have hroot : Real.sqrt P * Real.sqrt P = P := by
    rw [← pow_two, Real.sq_sqrt hP.le]
  calc
    inner ℝ (maternSheetFeatureWithSpectralAmplitude κ c h hκ hc hh s)
        (maternSheetFeatureWithSpectralAmplitude κ c h hκ hc hh t) =
      Real.sqrt P * Real.sqrt P *
        inner ℝ (maternSheetFeature κ h hκ hh s)
          (maternSheetFeature κ h hκ hh t) := by
            simp [maternSheetFeatureWithSpectralAmplitude, P,
              real_inner_smul_left, real_inner_smul_right, mul_assoc]
    _ = P * maternSheetCovariance κ h hκ hh s t := by
          rw [hroot, maternSheetFeature_gram]
    _ = ∏ i, c i * stationaryCovariance (κ i) h (s.val i) (t.val i) := by
          change P * (∏ i, normalizedCovariance (κ i) h
            (s.val i) (t.val i) (hκ i) hh) = _
          rw [← Finset.prod_mul_distrib]
          apply Finset.prod_congr rfl
          intro i hi
          rw [mul_assoc, spectralMass_mul_normalizedCovariance (κ i) h
            (s.val i) (t.val i) (hκ i) hh]

/-- The periodic Sobolev source construction and positive fixed window give
the sharp entropy lower rate for the normalized Matérn feature ball. This is
only the lower entropy direction; the Gaussian-field identification and the
matching width/entropy upper bounds and small-deviation conclusion are separate
results. -/
theorem maternSheetFeature_entropy_lower {d : ℕ}
    (hd : 2 ≤ d) (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    ∃ cE : ℝ, 0 < cE ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal
        (cE * logarithmicIndexRate (h + 1/2)
          ((h + 1/2) * (d - 1 : ℕ) + 1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          (featureOperator (maternSheetFeature κ h hκ hh) ''
            Metric.closedBall (0 : SpectralProductL2 κ h) 1) := by
  let r : ℝ := h + 1/2
  obtain ⟨A, hA, hEmbed⟩ :=
    matern_periodic_sobolev_source_embedding κ h hκ hh
  let c : ℝ := ((1/4 : ℝ) * (2/Real.pi)) ^ d
  have hc : 0 < c := by dsimp [c]; positivity
  have hw : ∀ t, c ≤ ‖cubeWindowWeight d (1/4) t‖ := by
    simpa [c] using (fixedCubeWindowWeight_lower d).2
  have hr : 1/2 < r := by dsimp [r]; linarith
  obtain ⟨cE, hcE, k₀, hk₀, hRate⟩ :=
    feature_entropy_lower_of_periodic_embedding hd r hr
      (complexSheetFeature κ h hκ hh) (cubeWindowWeight d (1/4))
      c A hc hA hw hEmbed
  refine ⟨cE, hcE, k₀, hk₀, ?_⟩
  intro k hk
  rw [← complexSheetFeature_ball_eq_real κ h hκ hh]
  simpa [r] using hRate k hk

/-- The feature ball for the raw Matérn product spectral densities has the
same sharp entropy lower order. The scale depends on the positive spectral
amplitudes and masses, as expected; only the asymptotic exponent is uniform. -/
theorem maternSheetRawSpectralFeature_entropy_lower {d : ℕ}
    (hd : 2 ≤ d) (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h) :
    ∃ cE : ℝ, 0 < cE ∧ ∃ k₀ : ℕ, 2 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      ENNReal.ofReal
        (cE * logarithmicIndexRate (h + 1/2)
          ((h + 1/2) * (d - 1 : ℕ) + 1/2) k) ≤
        HaarQuarter.TheoremD.entropyNumber k
          (featureOperator
            (maternSheetFeatureWithSpectralAmplitude κ c h hκ hc hh) ''
            Metric.closedBall (0 : SpectralProductL2 κ h) 1) := by
  let r : ℝ := h + 1/2
  let P : ℝ := ∏ i, c i * spectralMass (κ i) h
  let a : ℝ := Real.sqrt P
  have hP : 0 < P := Finset.prod_pos fun i hi =>
    mul_pos (hc i) (spectralMass_pos (κ i) h (hκ i) hh)
  have ha : 0 < a := Real.sqrt_pos.2 hP
  obtain ⟨cN, hcN, k₀, hk₀, hN⟩ :=
    maternSheetFeature_entropy_lower hd κ h hκ hh
  have hscale :
      (fun f : C(BrownianCubeAnchor d, ℝ) => a • f) ''
          (featureOperator (maternSheetFeature κ h hκ hh) ''
            Metric.closedBall (0 : SpectralProductL2 κ h) 1) ⊆
        featureOperator
          (maternSheetFeatureWithSpectralAmplitude κ c h hκ hc hh) ''
            Metric.closedBall (0 : SpectralProductL2 κ h) 1 := by
    rintro y ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    refine ⟨z, hz, ?_⟩
    have hmap :
        featureOperator (maternSheetFeatureWithSpectralAmplitude κ c h hκ hc hh) z =
          a • featureOperator (maternSheetFeature κ h hκ hh) z := by
      ext t
      simp [featureOperator_apply, maternSheetFeatureWithSpectralAmplitude,
        a, P, real_inner_smul_left]
    exact hmap
  refine ⟨a * cN, mul_pos ha hcN, k₀, hk₀, ?_⟩
  intro k hk
  have hrate : 0 ≤ logarithmicIndexRate r
      (r * (d - 1 : ℕ) + 1/2) k := by
    unfold logarithmicIndexRate
    have hkR : (1 : ℝ) < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
    have hlog : 0 < Real.log (k : ℝ) := Real.log_pos hkR
    positivity
  have hbase : ENNReal.ofReal
      (cN * logarithmicIndexRate r (r * (d - 1 : ℕ) + 1/2) k) ≤
      HaarQuarter.TheoremD.entropyNumber k
        (featureOperator (maternSheetFeature κ h hκ hh) ''
          Metric.closedBall (0 : SpectralProductL2 κ h) 1) := by
    simpa [r] using hN k hk
  have hscaled := entropyNumber_ge_of_scaled_subset
    (featureOperator
      (maternSheetFeatureWithSpectralAmplitude κ c h hκ hc hh) ''
        Metric.closedBall (0 : SpectralProductL2 κ h) 1)
    (featureOperator (maternSheetFeature κ h hκ hh) ''
      Metric.closedBall (0 : SpectralProductL2 κ h) 1)
    a (cN * logarithmicIndexRate r (r * (d - 1 : ℕ) + 1/2) k)
    ha (mul_nonneg hcN.le hrate) hscale k hbase
  simpa [mul_assoc, r] using hscaled

end BrownianSharp.AlignmentPaperMatern
