import BrownianSharp.AlignmentPaperMaternGradedReverse
import BrownianSharp.AlignmentPaperMaternPathUpper

/-! Actual raw-spectral Matérn small balls. The upper logarithm uses the
proved scalar spectral residual, finite Gaussian grid probabilities and
continuous-path closure. This is an internal endpoint proof, not an assumed
general entropy-upper-to-small-ball-upper theorem. -/
noncomputable section
universe u
open MeasureTheory ProbabilityTheory HaarQuarter
namespace BrownianSharp.AlignmentPaperMaternSmallBallUpper

open BrownianSharp.AlignmentPaperMaternGradedReverse
open BrownianSharp.AlignmentPaperMaternFinal
open BrownianSharp.AlignmentPaperMaternPathUpper

/-- Uniform upper small-ball logarithm for the actual covariance specified by
the positive raw spectral densities. No scalar residual is a caller premise. -/
theorem maternRawSpectral_uniform_smallBall_upperLog {d : ℕ}
    (hd : 2 ≤ d) (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (F : Ω → C(BrownianCubeAnchor d,ℝ)) (hF : Measurable F)
        (hX : IsGaussianProcess (fun x ω => F ω x) P)
        (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
        (hcov : ∀ x y, cov[fun ω => F ω x, fun ω => F ω y; P] =
          rawMaternCovariance κ c h x y)
        (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        -Real.log (P.real {ω | ‖F ω‖ ≤ ε}) ≤
          C * BrownianSharp.Latest.smallBallRate h⁻¹ (d-1+(d:ℝ)/(2*h)) ε := by
  obtain ⟨A,D,hA,hD,hgrid⟩ :=
    rawMatern_grid_lower_bound (by omega : 0 < d) κ c h hκ hc hh
  have hg : KernelGridLower.{u} (rawMaternCovariance κ c h) (2*h) A D := by
    exact hgrid
  have hrate : 2/(2*h) = h⁻¹ := by field_simp
  simpa only [hrate] using
    path_upperLog_of_grid hd (rawMaternCovariance κ c h) (2*h) A D
      (by positivity) hA hD hg

/-- The exact two-sided raw-spectral Matérn small-ball order. Probability is
strictly positive, and both constants precede all realization quantifiers. -/
theorem maternRawSpectral_uniform_smallBall_twoSided {d : ℕ}
    (hd : 2 ≤ d) (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h) :
    ∃ cL CU ε₀ : ℝ, 0 < cL ∧ 0 < CU ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (F : Ω → C(BrownianCubeAnchor d,ℝ)) (hF : Measurable F)
        (hX : IsGaussianProcess (fun x ω => F ω x) P)
        (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
        (hcov : ∀ x y, cov[fun ω => F ω x, fun ω => F ω y; P] =
          rawMaternCovariance κ c h x y)
        (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        0 < P.real {ω | ‖F ω‖ ≤ ε} ∧
        cL * BrownianSharp.Latest.smallBallRate h⁻¹ (d-1+(d:ℝ)/(2*h)) ε ≤
          -Real.log (P.real {ω | ‖F ω‖ ≤ ε}) ∧
        -Real.log (P.real {ω | ‖F ω‖ ≤ ε}) ≤
          CU * BrownianSharp.Latest.smallBallRate h⁻¹ (d-1+(d:ℝ)/(2*h)) ε := by
  obtain ⟨cL,εL,hcL,hεL,hεLsmall,hlower⟩ :=
    maternRawSpectral_uniform_smallBall_lowerLog.{u} hd κ c h hκ hc hh
  obtain ⟨CU,εU,hCU,hεU,hεUsmall,hupper⟩ :=
    maternRawSpectral_uniform_smallBall_upperLog.{u} hd κ c h hκ hc hh
  refine ⟨cL,CU,min εL εU,hcL,hCU,lt_min hεL hεU,
    (min_le_left _ _).trans_lt hεLsmall,?_⟩
  intro Ω _ P _ F hF hX hmean hcov ε hε hsmall
  have hlo := hlower F hF hX hmean hcov ε hε (hsmall.trans (min_le_left _ _))
  have hup := hupper F hF hX hmean hcov ε hε (hsmall.trans (min_le_right _ _))
  exact ⟨hlo.1,hlo.2,hup⟩

/-- The small-deviation clause of manuscript Corollary 5.3, with raw spectral
amplitudes and arbitrary continuous centered Gaussian realizations. -/
def MaternRawSmallBallStatement : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (κ c : Fin d → ℝ) (h : ℝ)
    (_hκ : ∀ i, 0 < κ i) (_hc : ∀ i, 0 < c i) (_hh : 0 < h),
    ∃ cL CU ε₀ : ℝ, 0 < cL ∧ 0 < CU ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (F : Ω → C(BrownianCubeAnchor d,ℝ)) (hF : Measurable F)
        (hX : IsGaussianProcess (fun x ω => F ω x) P)
        (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
        (hcov : ∀ x y, cov[fun ω => F ω x, fun ω => F ω y; P] =
          rawMaternCovariance κ c h x y)
        (ε : ℝ), 0 < ε → ε ≤ ε₀ →
        0 < P.real {ω | ‖F ω‖ ≤ ε} ∧
        cL * BrownianSharp.Latest.smallBallRate h⁻¹ (d-1+(d:ℝ)/(2*h)) ε ≤
          -Real.log (P.real {ω | ‖F ω‖ ≤ ε}) ∧
        -Real.log (P.real {ω | ‖F ω‖ ≤ ε}) ≤
          CU * BrownianSharp.Latest.smallBallRate h⁻¹ (d-1+(d:ℝ)/(2*h)) ε

theorem maternRawSmallBall_certified : MaternRawSmallBallStatement.{u} := by
  intro d hd κ c h hκ hc hh
  exact maternRawSpectral_uniform_smallBall_twoSided hd κ c h hκ hc hh

end BrownianSharp.AlignmentPaperMaternSmallBallUpper
