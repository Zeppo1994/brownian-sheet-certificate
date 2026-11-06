import BrownianSharp.AlignmentPaperMaternUpper
import BrownianSharp.AlignmentOperatorNumbers
import BrownianSharp.AlignmentOperatorWidthIndexShift
import BrownianSharp.AlignmentPaperMaternSmallBall
import BrownianSharp.AlignmentPaperGaussianPathLaws

/-! Final strict-index Matérn width transfer. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace BrownianSharp.AlignmentPaperMaternFinal

open BrownianSharp.AlignmentPaperMaternUpper
open BrownianSharp.AlignmentOperatorNumbers
open BrownianSharp.AlignmentOperatorWidthIndexShift
open BrownianSharp.AlignmentWidthRates
open BrownianSharp.AlignmentPaperGaussianFeatureBridge
open BrownianSharp.AlignmentPaperGaussianPathLaws
open BrownianSharp.AlignmentPaperMaternSmallBall

def rawMaternCovariance {d : ℕ} (κ c : Fin d → ℝ) (h : ℝ)
    (x y : HaarQuarter.BrownianCubeAnchor d) : ℝ :=
  ∏ i, c i * BrownianSharp.AlignmentMaternSpectralFeature.stationaryCovariance
    (κ i) h (x.val i) (y.val i)

/-- The paper's strict-index operator Kolmogorov numbers have the sharp
two-sided rate for every intrinsic CM ball with the specified raw Matérn
covariance. Constants precede the realization quantifiers. -/
theorem maternRawSpectral_intrinsicCM_operator_width_two_sided {d : ℕ}
    (hd : 2 ≤ d) (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h) :
    ∃ cW CW : ℝ, 0 < cW ∧ 0 < CW ∧ ∃ k₀ : ℕ, 3 ≤ k₀ ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (X : HaarQuarter.BrownianCubeAnchor d → Ω → ℝ)
        (hX : ∀ x, MemLp (X x) 2 P)
        (hmean : ∀ x, ∫ ω, X x ω ∂P = 0)
        (hcov : ∀ x y,
          cov[X x, X y; P] =
            ∏ i, c i * BrownianSharp.AlignmentMaternSpectralFeature.stationaryCovariance
              (κ i) h (x.val i) (y.val i)),
        ∀ k : ℕ, k₀ ≤ k →
          ENNReal.ofReal (cW * logarithmicIndexRate (h+1/2)
            ((h+1/2)*(d-1:ℕ)+1/2) k) ≤
              operatorKolmogorovNumber (intrinsicGaussianCMUnitBall X hX) k ∧
          operatorKolmogorovNumber (intrinsicGaussianCMUnitBall X hX) k ≤
              ENNReal.ofReal (CW * logarithmicIndexRate (h+1/2)
                ((h+1/2)*(d-1:ℕ)+1/2) k) := by
  obtain ⟨c,C,hcW,hCW,k0,hk0,hwidth⟩ :=
    maternRawSpectral_intrinsicCM_width_two_sided hd κ c h hκ hc hh
  let r : ℝ := h+1/2
  let a : ℝ := r*(d-1:ℕ)+1/2
  let k₀ : ℕ := k0+1
  have hr : 0<r := by dsimp [r]; linarith
  have ha : 0≤a := by dsimp [a,r]; positivity
  have hk₀ : 3≤k₀ := by dsimp [k₀]; omega
  refine ⟨c*2^(-a), C*2^r, ?_, ?_, k₀,hk₀,?_⟩
  · exact mul_pos hcW (Real.rpow_pos_of_pos (by norm_num) _)
  · exact mul_pos hCW (Real.rpow_pos_of_pos (by norm_num) _)
  · intro Ω hΩ P hP X hX hmean hcov k hk
    have hK := hwidth X hX hmean hcov
    have hkprev : k0≤k-1 := by dsimp [k₀] at hk; omega
    have hbase := hK (k-1) hkprev
    have hrate := rate_succ_comparable hr ha (by omega : 3≤k)
    have hcscaled : c*2^(-a)*logarithmicIndexRate r a k ≤
        c*logarithmicIndexRate r a (k-1) := by
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hrate.1 hcW.le
    have hCscaled : C*logarithmicIndexRate r a (k-1) ≤
        C*2^r*logarithmicIndexRate r a k := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hrate.2 hCW.le
    have hidx : 1≤k := by omega
    rw [operatorKolmogorovNumber_eq_width_pred _ hidx]
    constructor
    · exact (ENNReal.ofReal_le_ofReal hcscaled).trans hbase.1
    · exact hbase.2.trans (ENNReal.ofReal_le_ofReal hCscaled)

/-- The small-ball probability upper bound (equivalently, the lower bound on
negative log probability) can be chosen uniformly over all centered
continuous Gaussian path laws with fixed raw Matérn covariance. This is the
entropy-lower direction; it makes no claim of the reverse small-ball bound. -/
theorem maternRawSpectral_uniform_smallBall_lowerLog {d : ℕ}
    (hd : 2 ≤ d) (κ c : Fin d → ℝ) (h : ℝ)
    (hκ : ∀ i, 0 < κ i) (hc : ∀ i, 0 < c i) (hh : 0 < h) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ε₀ < Real.exp (-1) ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
        (F : Ω → C(HaarQuarter.BrownianCubeAnchor d,ℝ))
        (hF : Measurable F)
        (hX : IsGaussianProcess (fun x ω => F ω x) P)
        (hmean : ∀ x, ∫ ω, F ω x ∂P = 0)
        (hcov : ∀ x y,
          cov[fun ω => F ω x, fun ω => F ω y; P] =
            rawMaternCovariance κ c h x y),
        ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
          0 < P.real {ω | ‖F ω‖ ≤ ε} ∧
          C * Latest.smallBallRate (h⁻¹) (d-1+(d:ℝ)/(2*h)) ε ≤
            -Real.log (P.real {ω | ‖F ω‖ ≤ ε}) := by
  let α := HaarQuarter.BrownianCubeAnchor d
  let Cker : α → α → ℝ := rawMaternCovariance κ c h
  let S : Set (Measure C(α,ℝ)) := {μ | IsCenteredPathLaw Cker μ}
  let B := {q : ℝ × ℝ // 0 < q.1 ∧ 0 < q.2 ∧ q.2 < Real.exp (-1)}
  have hB : Nonempty B := by
    refine ⟨⟨(1,Real.exp (-2)), ?_⟩⟩
    constructor
    · norm_num
    constructor
    · exact Real.exp_pos _
    · exact Real.exp_lt_exp.mpr (by norm_num)
  let prop : Measure C(α,ℝ) → B → Prop := fun μ q =>
    ∀ ε : ℝ, 0 < ε → ε ≤ q.1.2 →
      q.1.1 * Latest.smallBallRate (h⁻¹) (d-1+(d:ℝ)/(2*h)) ε ≤
        -Real.log (μ.real (Metric.closedBall (0 : C(α,ℝ)) ε))
  have huniq : ∀ μ ∈ S, ∀ ν ∈ S, μ = ν := by
    intro μ hμ ν hν
    exact centeredPathLaw_unique hμ hν
  have hexists : ∀ μ ∈ S, ∃ q : B, prop μ q := by
    intro μ hμ
    letI : IsProbabilityMeasure μ := hμ.1
    have hsmall := maternRawSpectral_actual_path_smallBall_lowerLog hd κ c h hκ hc hh
      (id : C(α,ℝ) → C(α,ℝ)) measurable_id hμ.2.1 hμ.2.2.1 hμ.2.2.2
    obtain ⟨C0,ε0,hC0,hε0,hε0lt,hbound⟩ := hsmall
    refine ⟨⟨(C0,ε0),⟨hC0,hε0,hε0lt⟩⟩,?_⟩
    intro ε hε hsmall
    have hb := hbound ε hε hsmall
    simpa using hb
  obtain ⟨q,hq⟩ := exists_uniform_of_unique_law S huniq prop hexists
  refine ⟨q.1.1,q.1.2,q.2.1,q.2.2.1,q.2.2.2,?_⟩
  intro Ω hΩ P hP F hF hX hmean hcov ε hε hsmall
  let μ := P.map F
  have hμ : μ ∈ S := by
    change IsCenteredPathLaw Cker (P.map F)
    exact isCenteredPathLaw_map F hF hX hmean Cker hcov
  have hqμ := hq μ hμ ε hε hsmall
  have hmapENN : μ (Metric.closedBall (0 : C(α,ℝ)) ε) =
      P {ω | ‖F ω‖ ≤ ε} := by
    rw [Measure.map_apply hF Metric.isClosed_closedBall.measurableSet]
    congr 1
  have hmapReal : μ.real (Metric.closedBall (0 : C(α,ℝ)) ε) =
      P.real {ω | ‖F ω‖ ≤ ε} := by
    simpa [Measure.real] using congrArg ENNReal.toReal hmapENN
  have hpositive := centered_path_closedBall_pos F hF hX hmean ε hε
  constructor
  · rw [← hmapReal]
    exact hpositive
  · simpa [hmapReal] using hqμ

end BrownianSharp.AlignmentPaperMaternFinal
