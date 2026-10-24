import BrownianSharp.AlignmentGaussianPacking
import BrownianSharp.AlignmentEndpointRateInverse
import BrownianSharp.AlignmentWidthRates

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace BrownianSharp.AlignmentGaussianEntropySmallBall
open BrownianSharp.AlignmentGaussianPacking

/-- The entropy-to-small-ball lower-log direction follows from explicit
Cameron--Martin ball translation bounds. No Gaussian law is assumed
implicitly: that analytic translation property is displayed as the input. -/
theorem smallBall_probability_upper_of_entropy_lower
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (K : Set X)
    (r a : ℝ) (hr : 1/2<r) (ha : 0≤a)
    (hEntropy : ∃c : ℝ,0<c ∧ ∃n₀ : ℕ,∀k,n₀≤k →
      ENNReal.ofReal (c*logarithmicIndexRate r a k) ≤
        HaarQuarter.TheoremD.entropyNumber k K)
    (hshift : ∀R : ℝ,0<R → ∀ε : ℝ,0<ε → ∀x∈K,
      ENNReal.ofReal (Real.exp (-(R^2)/2))*μ (Metric.closedBall 0 ε) ≤
        μ (Metric.closedBall (R • x) ε)) :
    ∃c ε₀ : ℝ,0<c ∧ 0<ε₀ ∧ ε₀<Real.exp (-1) ∧
      ∀ε : ℝ,0<ε → ε≤ε₀ →
        μ.real (Metric.closedBall 0 ε) ≤
          Real.exp (-c*Latest.smallBallRate (r-1/2)⁻¹ (a/(r-1/2)) ε) := by
  obtain ⟨c,hc,n₀,hE⟩ := hEntropy
  let s := r-1/2
  let c₀ := c*Real.sqrt (Real.log 2)/6
  let b₀ := Real.log 2/4
  have hs : 0<s := by dsimp [s]; linarith
  have hc₀ : 0<c₀ := by
    dsimp [c₀]
    exact div_pos (mul_pos hc (Real.sqrt_pos.mpr (Real.log_pos (by norm_num)))) (by norm_num)
  have hb₀ : 0<b₀ := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  obtain ⟨b,e₀,hb,he₀,hInv⟩ :=
    AlignmentEndpointRateInverse.exists_index_for_power_log_rate hs ha hc₀ (max 4 n₀)
  refine ⟨b₀*b,min e₀ (Real.exp (-2)),mul_pos hb₀ hb,lt_min he₀ (Real.exp_pos _),?_,?_⟩
  · exact (min_le_right _ _).trans_lt (Real.exp_lt_exp.mpr (by norm_num))
  · intro ε hε hε₀
    obtain ⟨k,hk,hkLower,hkRadius⟩ := hInv ε hε (hε₀.trans (min_le_left _ _))
    have hk4 : 4≤k := (le_max_left 4 n₀).trans ((le_max_right 2 (max 4 n₀)).trans hk)
    have hkn : n₀≤k := (le_max_right 4 n₀).trans ((le_max_right 2 (max 4 n₀)).trans hk)
    have hprob := smallBall_index_rate_of_entropy_lower μ K r a c hc k hk4 (hE k hkn) hshift
    have hmono : μ.real (Metric.closedBall 0 ε) ≤
        μ.real (Metric.closedBall 0 (c₀*(k:ℝ)^(-s)*(Real.log (k:ℝ))^a)) :=
      measureReal_mono (Metric.closedBall_subset_closedBall hkRadius) (measure_ne_top _ _)
    have hprob' : μ.real (Metric.closedBall 0 ε) ≤ Real.exp (-(b₀*(k:ℝ))) :=
      hmono.trans (by simpa only [c₀,s,b₀,neg_mul] using hprob)
    apply hprob'.trans
    apply Real.exp_le_exp.mpr
    have hscaled := mul_le_mul_of_nonneg_left hkLower hb₀.le
    change -(b₀*(k:ℝ)) ≤ -(b₀*b)*Latest.smallBallRate s⁻¹ (a/s) ε
    simp only [Latest.smallBallRate,one_div] at hscaled ⊢
    nlinarith only [hscaled]

theorem smallBall_lowerLog_of_entropy_lower
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (K : Set X)
    (r a : ℝ) (hr : 1/2<r) (ha : 0≤a)
    (hEntropy : ∃c : ℝ,0<c ∧ ∃n₀ : ℕ,∀k,n₀≤k →
      ENNReal.ofReal (c*logarithmicIndexRate r a k) ≤
        HaarQuarter.TheoremD.entropyNumber k K)
    (hshift : ∀R : ℝ,0<R → ∀ε : ℝ,0<ε → ∀x∈K,
      ENNReal.ofReal (Real.exp (-(R^2)/2))*μ (Metric.closedBall 0 ε) ≤
        μ (Metric.closedBall (R • x) ε))
    (hpositive : ∀ε : ℝ,0<ε → 0<μ.real (Metric.closedBall 0 ε)) :
    ∃c ε₀ : ℝ,0<c ∧ 0<ε₀ ∧ ε₀<Real.exp (-1) ∧
      ∀ε : ℝ,0<ε → ε≤ε₀ →
        c*Latest.smallBallRate (r-1/2)⁻¹ (a/(r-1/2)) ε ≤
          -Real.log (μ.real (Metric.closedBall 0 ε)) := by
  obtain ⟨c,ε₀,hc,hε₀,hε₀',hprob⟩ :=
    smallBall_probability_upper_of_entropy_lower μ K r a hr ha hEntropy hshift
  refine ⟨c,ε₀,hc,hε₀,hε₀',?_⟩
  intro ε hε hsmall
  have hlog := Real.log_le_log (hpositive ε hε) (hprob ε hε hsmall)
  rw [Real.log_exp] at hlog
  linarith


theorem operator_ball_shift_lower_of_source_shift
    {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]
    (μ : Measure X) (T : H→L[ℝ] X)
    (hshift : ∀g : H,∀ε : ℝ,0<ε →
      ENNReal.ofReal (Real.exp (-(‖g‖^2)/2))*μ (Metric.closedBall 0 ε) ≤
        μ (Metric.closedBall (T g) ε)) :
    ∀R : ℝ,0<R → ∀ε : ℝ,0<ε →
      ∀x∈T '' Metric.closedBall (0:H) 1,
      ENNReal.ofReal (Real.exp (-(R^2)/2))*μ (Metric.closedBall 0 ε) ≤
        μ (Metric.closedBall (R • x) ε) := by
  intro R hR ε hε x hx
  obtain ⟨g,hg,rfl⟩ := hx
  have hgn : ‖g‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hg
  have hRgn : ‖R • g‖≤R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hR]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hgn hR.le
  have hsq : ‖R • g‖^2≤R^2 := (sq_le_sq₀ (norm_nonneg _) hR.le).2 hRgn
  have hfactor : ENNReal.ofReal (Real.exp (-(R^2)/2)) ≤
      ENNReal.ofReal (Real.exp (-(‖R • g‖^2)/2)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
  exact (mul_le_mul hfactor le_rfl bot_le bot_le).trans
    (by simpa only [map_smul] using hshift (R • g) ε hε)


/-- The constants depend on the entropy class and its rate, uniformly over
all probability laws satisfying the displayed Cameron--Martin inequality. -/
theorem uniform_smallBall_probability_upper_of_entropy_lower
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MeasurableSpace X] [BorelSpace X] (K : Set X)
    (r a : ℝ) (hr : 1/2<r) (ha : 0≤a)
    (hEntropy : ∃c : ℝ,0<c ∧ ∃n₀ : ℕ,∀k,n₀≤k →
      ENNReal.ofReal (c*logarithmicIndexRate r a k) ≤
        HaarQuarter.TheoremD.entropyNumber k K) :
    ∃c ε₀ : ℝ,0<c ∧ 0<ε₀ ∧ ε₀<Real.exp (-1) ∧
      ∀(μ : Measure X),IsProbabilityMeasure μ →
        (∀R : ℝ,0<R → ∀ε : ℝ,0<ε → ∀x∈K,
          ENNReal.ofReal (Real.exp (-(R^2)/2))*μ (Metric.closedBall 0 ε) ≤
            μ (Metric.closedBall (R • x) ε)) →
        ∀ε : ℝ,0<ε → ε≤ε₀ →
          μ.real (Metric.closedBall 0 ε) ≤
            Real.exp (-c*Latest.smallBallRate (r-1/2)⁻¹ (a/(r-1/2)) ε) := by
  obtain ⟨c,hc,n₀,hE⟩ := hEntropy
  let s := r-1/2
  let c₀ := c*Real.sqrt (Real.log 2)/6
  let b₀ := Real.log 2/4
  have hs : 0<s := by dsimp [s]; linarith
  have hc₀ : 0<c₀ := by
    dsimp [c₀]
    exact div_pos (mul_pos hc (Real.sqrt_pos.mpr (Real.log_pos (by norm_num)))) (by norm_num)
  have hb₀ : 0<b₀ := div_pos (Real.log_pos (by norm_num)) (by norm_num)
  obtain ⟨b,e₀,hb,he₀,hInv⟩ :=
    AlignmentEndpointRateInverse.exists_index_for_power_log_rate hs ha hc₀ (max 4 n₀)
  refine ⟨b₀*b,min e₀ (Real.exp (-2)),mul_pos hb₀ hb,lt_min he₀ (Real.exp_pos _),?_,?_⟩
  · exact (min_le_right _ _).trans_lt (Real.exp_lt_exp.mpr (by norm_num))
  · intro μ hμ hshift ε hε hε₀
    letI := hμ
    obtain ⟨k,hk,hkLower,hkRadius⟩ := hInv ε hε (hε₀.trans (min_le_left _ _))
    have hk4 : 4≤k := (le_max_left 4 n₀).trans ((le_max_right 2 (max 4 n₀)).trans hk)
    have hkn : n₀≤k := (le_max_right 4 n₀).trans ((le_max_right 2 (max 4 n₀)).trans hk)
    have hprob := smallBall_index_rate_of_entropy_lower μ K r a c hc k hk4 (hE k hkn) hshift
    have hmono : μ.real (Metric.closedBall 0 ε) ≤
        μ.real (Metric.closedBall 0 (c₀*(k:ℝ)^(-s)*(Real.log (k:ℝ))^a)) :=
      measureReal_mono (Metric.closedBall_subset_closedBall hkRadius) (measure_ne_top _ _)
    have hprob' : μ.real (Metric.closedBall 0 ε) ≤ Real.exp (-(b₀*(k:ℝ))) :=
      hmono.trans (by simpa only [c₀,s,b₀,neg_mul] using hprob)
    apply hprob'.trans
    apply Real.exp_le_exp.mpr
    have hscaled := mul_le_mul_of_nonneg_left hkLower hb₀.le
    change -(b₀*(k:ℝ)) ≤ -(b₀*b)*Latest.smallBallRate s⁻¹ (a/s) ε
    simp only [Latest.smallBallRate,one_div] at hscaled ⊢
    nlinarith only [hscaled]

end BrownianSharp.AlignmentGaussianEntropySmallBall
