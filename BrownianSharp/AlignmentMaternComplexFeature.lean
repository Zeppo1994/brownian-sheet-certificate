import BrownianSharp.AlignmentMaternTensorFeature
import BrownianSharp.AlignmentFeatureGramTransfer
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Exponential

/-! Complex spectral features, viewed as a real Hilbert source. Integer
frequency windows are disjoint in this representation, simplifying the
periodic Sobolev embedding without changing the covariance kernel. -/
noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators ENNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentMaternComplexFeature
open AlignmentMaternSpectralFeature AlignmentMaternScalarFeature
open AlignmentMaternContinuousFeature AlignmentMaternTensorFeature

def complexPhase (t ξ : ℝ) : ℂ :=
  Complex.exp ((-(2*Real.pi*ξ*t):ℝ) * Complex.I)

theorem complexPhase_norm (t ξ : ℝ) : ‖complexPhase t ξ‖ = 1 := by
  simp [complexPhase, Complex.norm_exp]

theorem complexPhase_memLp (κ h t : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    MemLp (complexPhase t) 2 (spectralMeasure κ h) := by
  letI := spectralMeasure_isFinite κ h hκ hh
  apply MemLp.of_bound
    (show AEStronglyMeasurable (complexPhase t) (spectralMeasure κ h) from
      (show Measurable (complexPhase t) by unfold complexPhase; fun_prop).aestronglyMeasurable) 1
  filter_upwards with ξ
  rw [complexPhase_norm]

theorem complexPhase_conj_mul (s t ξ : ℝ) :
    star (complexPhase s ξ) * complexPhase t ξ =
      Complex.exp (((2*Real.pi*ξ*(s-t):ℝ):ℂ) * Complex.I) := by
  unfold complexPhase
  change (starRingEnd ℂ) (Complex.exp _) * Complex.exp _ = Complex.exp _
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem integral_complexPhase (κ h τ : ℝ) (hκ : 0 < κ) (hh : 0 < h) :
    ∫ ξ, Complex.exp (((2*Real.pi*ξ*τ:ℝ):ℂ)*Complex.I) ∂spectralMeasure κ h =
      (stationaryCovariance κ h τ 0 : ℂ) := by
  let μ := spectralMeasure κ h
  letI : IsFiniteMeasure μ := spectralMeasure_isFinite κ h hκ hh
  have hi : Integrable (fun ξ => Complex.exp (((2*Real.pi*ξ*τ:ℝ):ℂ)*Complex.I)) μ := by
    apply Integrable.of_bound
      (show AEStronglyMeasurable _ μ from
        (by fun_prop : Measurable (fun ξ : ℝ =>
          Complex.exp (((2*Real.pi*ξ*τ:ℝ):ℂ)*Complex.I))).aestronglyMeasurable) 1
    filter_upwards with ξ
    simp [Complex.norm_exp]
  apply Complex.ext
  · have hr := (integral_re hi).symm
    change (∫ ξ, Complex.exp (((2*Real.pi*ξ*τ:ℝ):ℂ)*Complex.I) ∂μ).re =
      ∫ ξ, (Complex.exp (((2*Real.pi*ξ*τ:ℝ):ℂ)*Complex.I)).re ∂μ at hr
    rw [hr]
    simp [stationaryCovariance, μ, Complex.exp_re]
  · have hr := (integral_im hi).symm
    change (∫ ξ, Complex.exp (((2*Real.pi*ξ*τ:ℝ):ℂ)*Complex.I) ∂μ).im =
      ∫ ξ, (Complex.exp (((2*Real.pi*ξ*τ:ℝ):ℂ)*Complex.I)).im ∂μ at hr
    rw [hr]
    simpa [μ, Complex.exp_im] using spectral_sine_integral_zero κ h τ hκ

abbrev ComplexProductL2 {d : ℕ} (κ : Fin d → ℝ) (h : ℝ) :=
  Lp ℂ 2 (Measure.pi (fun i => spectralMeasure (κ i) h))

def complexSheetPhase {d : ℕ} (t ξ : Fin d → ℝ) : ℂ :=
  ∏ i, complexPhase (t i) (ξ i)

theorem complexSheetPhase_norm {d : ℕ} (t ξ : Fin d → ℝ) :
    ‖complexSheetPhase t ξ‖ = 1 := by simp [complexSheetPhase, norm_prod, complexPhase_norm]

theorem complexSheetPhase_memLp {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (t : Fin d → ℝ) :
    MemLp (complexSheetPhase t) 2 (Measure.pi (fun i => spectralMeasure (κ i) h)) := by
  letI (i : Fin d) : IsFiniteMeasure (spectralMeasure (κ i) h) :=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  apply MemLp.of_bound
    (show AEStronglyMeasurable (complexSheetPhase t) _ from
      (show Measurable (complexSheetPhase t) by
        unfold complexSheetPhase complexPhase
        fun_prop).aestronglyMeasurable) 1
  filter_upwards with ξ
  rw [complexSheetPhase_norm]

def rawComplexSheetFeature {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (t : Fin d → ℝ) : ComplexProductL2 κ h :=
  (complexSheetPhase_memLp κ h hκ hh t).toLp (complexSheetPhase t)

theorem rawComplexSheetFeature_inner_complex {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (s t : Fin d → ℝ) :
    inner ℂ (rawComplexSheetFeature κ h hκ hh s)
      (rawComplexSheetFeature κ h hκ hh t) =
      ∏ i, (stationaryCovariance (κ i) h (s i) (t i) : ℂ) := by
  letI (i : Fin d) : IsFiniteMeasure (spectralMeasure (κ i) h) :=
    spectralMeasure_isFinite (κ i) h (hκ i) hh
  rw [L2.inner_def]
  have haeS := (complexSheetPhase_memLp κ h hκ hh s).coeFn_toLp
  have haeT := (complexSheetPhase_memLp κ h hκ hh t).coeFn_toLp
  calc
    _ = ∫ ξ, ∏ i, Complex.exp (((2*Real.pi*ξ i*(s i-t i):ℝ):ℂ)*Complex.I)
        ∂Measure.pi (fun i => spectralMeasure (κ i) h) := by
      apply integral_congr_ae
      filter_upwards [haeS,haeT] with ξ hs ht
      change inner ℂ ((rawComplexSheetFeature κ h hκ hh s) ξ)
        ((rawComplexSheetFeature κ h hκ hh t) ξ) = _
      change inner ℂ (((complexSheetPhase_memLp κ h hκ hh s).toLp _) ξ)
        (((complexSheetPhase_memLp κ h hκ hh t).toLp _) ξ) = _
      rw [hs,ht, RCLike.inner_apply']
      simp only [complexSheetPhase, map_prod]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      exact complexPhase_conj_mul (s i) (t i) (ξ i)
    _ = ∏ i, ∫ ξ, Complex.exp (((2*Real.pi*ξ*(s i-t i):ℝ):ℂ)*Complex.I)
        ∂spectralMeasure (κ i) h :=
      integral_fintype_prod_eq_prod (fun (i : Fin d) (ξ : ℝ) =>
        Complex.exp (((2*Real.pi*ξ*(s i-t i):ℝ):ℂ)*Complex.I))
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [integral_complexPhase (κ i) h (s i-t i) (hκ i) hh]
      simp [stationaryCovariance]


def complexFeatureScale {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) : ℝ :=
  ∏ i, ‖scalarFeature (κ i) h 0 (hκ i) hh‖⁻¹

theorem complexFeatureScale_pos {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    0 < complexFeatureScale κ h hκ hh :=
  Finset.prod_pos (fun i _ => inv_pos.mpr (scalarFeature_norm_pos (κ i) h 0 (hκ i) hh))

def normalizedComplexFeatureFun {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (t : BrownianCubeAnchor d) :
    ComplexProductL2 κ h :=
  complexFeatureScale κ h hκ hh • rawComplexSheetFeature κ h hκ hh t.val

theorem normalizedComplexFeatureFun_gram {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (s t : BrownianCubeAnchor d) :
    inner ℝ (normalizedComplexFeatureFun κ h hκ hh s)
      (normalizedComplexFeatureFun κ h hκ hh t) =
      maternSheetCovariance κ h hκ hh s t := by
  have hr : inner ℝ (rawComplexSheetFeature κ h hκ hh s.val)
      (rawComplexSheetFeature κ h hκ hh t.val) =
      ∏ i, stationaryCovariance (κ i) h (s.val i) (t.val i) := by
    have hi : inner ℝ (rawComplexSheetFeature κ h hκ hh s.val)
        (rawComplexSheetFeature κ h hκ hh t.val) =
        (inner ℂ (rawComplexSheetFeature κ h hκ hh s.val)
          (rawComplexSheetFeature κ h hκ hh t.val)).re := by
      rw [L2.inner_def,L2.inner_def]
      simpa only [Complex.inner,RCLike.inner_apply,RCLike.re_to_complex] using
        (integral_re (L2.integrable_inner (𝕜:=ℂ)
          (rawComplexSheetFeature κ h hκ hh s.val)
          (rawComplexSheetFeature κ h hκ hh t.val)))
    rw [hi,rawComplexSheetFeature_inner_complex]
    simp only [← Complex.ofReal_prod, Complex.ofReal_re]
  simp only [normalizedComplexFeatureFun, real_inner_smul_left, real_inner_smul_right, hr]
  simp only [maternSheetCovariance, normalizedCovariance, complexFeatureScale,
    Finset.prod_mul_distrib, Finset.prod_pow]
  ring

theorem normalizedComplexFeatureFun_norm {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (t : BrownianCubeAnchor d) :
    ‖normalizedComplexFeatureFun κ h hκ hh t‖ = 1 := by
  have he := normalizedComplexFeatureFun_gram κ h hκ hh t t
  rw [real_inner_self_eq_norm_sq,maternSheetCovariance_diagonal] at he
  nlinarith [norm_nonneg (normalizedComplexFeatureFun κ h hκ hh t)]

theorem normalizedComplexFeatureFun_norm_sub {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (s t : BrownianCubeAnchor d) :
    ‖normalizedComplexFeatureFun κ h hκ hh s-normalizedComplexFeatureFun κ h hκ hh t‖ =
      Real.sqrt (2-2*maternSheetCovariance κ h hκ hh s t) := by
  rw [← Real.sqrt_sq (norm_nonneg (_-_)),norm_sub_sq_real,
    normalizedComplexFeatureFun_norm,normalizedComplexFeatureFun_norm,
    normalizedComplexFeatureFun_gram]
  congr 1
  ring

theorem normalizedComplexFeatureFun_continuous {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    Continuous (normalizedComplexFeatureFun κ h hκ hh) := by
  rw [continuous_iff_continuous_dist]
  have hc : Continuous (fun p : BrownianCubeAnchor d × BrownianCubeAnchor d =>
      maternSheetCovariance κ h hκ hh p.1 p.2) := by
    simp_rw [← maternSheetFeature_gram]
    exact ((maternSheetFeature κ h hκ hh).continuous.comp continuous_fst).inner
      ((maternSheetFeature κ h hκ hh).continuous.comp continuous_snd)
  have hr : Continuous (fun p : BrownianCubeAnchor d × BrownianCubeAnchor d =>
      Real.sqrt (2-2*maternSheetCovariance κ h hκ hh p.1 p.2)) :=
    Real.continuous_sqrt.comp (continuous_const.sub (continuous_const.mul hc))
  simpa only [dist_eq_norm,normalizedComplexFeatureFun_norm_sub] using hr

def complexSheetFeature {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    C(BrownianCubeAnchor d,ComplexProductL2 κ h) :=
  ⟨normalizedComplexFeatureFun κ h hκ hh, normalizedComplexFeatureFun_continuous κ h hκ hh⟩

theorem complexSheetFeature_gram {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) (s t : BrownianCubeAnchor d) :
    inner ℝ (complexSheetFeature κ h hκ hh s) (complexSheetFeature κ h hκ hh t) =
      maternSheetCovariance κ h hκ hh s t :=
  normalizedComplexFeatureFun_gram κ h hκ hh s t

theorem complexSheetFeature_ball_eq_real {d : ℕ} (κ : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hh : 0 < h) :
    AlignmentFractionalSheetRKHS.featureOperator (complexSheetFeature κ h hκ hh) ''
      Metric.closedBall (0:ComplexProductL2 κ h) 1 =
    AlignmentFractionalSheetRKHS.featureOperator (maternSheetFeature κ h hκ hh) ''
      Metric.closedBall (0:SpectralProductL2 κ h) 1 := by
  apply AlignmentFeatureGramTransfer.feature_ball_eq_of_gram
  intro s t
  rw [maternSheetFeature_gram,complexSheetFeature_gram]

end BrownianSharp.AlignmentMaternComplexFeature
