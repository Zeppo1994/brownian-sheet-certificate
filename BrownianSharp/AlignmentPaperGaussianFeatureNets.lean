import BrownianSharp.AlignmentPaperProbabilityNets
import BrownianSharp.AlignmentPaperMaternSmallBall

/-! Actual finite Cameron--Martin nets obtained from the proved Gaussian
shift inequality. This is the codebook packing ingredient for empirical
quantization; the path enlargement input is handled separately. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentPaperGaussianFeatureNets
open AlignmentCompactFeatureBall

/-- A true Gaussian path law gives a finite net of the dilated feature ball,
with the sharp exponential packing budget furnished by Cameron--Martin
translation. No entropy estimate for that ball is assumed. -/
theorem featurePathLaw_exists_net
    {α Ω H : Type*} [MetricSpace α] [CompactSpace α] [Nonempty α]
    [SecondCountableTopology α] [LocallyCompactSpace α]
    [MeasurableSpace Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : Ω → C(α,ℝ)) (hF : Measurable F)
    (hX : IsGaussianProcess (fun x ω => F ω x) P)
    (hmean : ∀ x, ∫ ω, F ω x ∂P=0)
    (K : C(α,H)) (a : α) (ha : K a ≠ 0)
    (hcov : ∀ x y, cov[fun ω => F ω x,fun ω => F ω y;P]=inner ℝ (K x) (K y))
    (R : ℝ) (hR : 0 < R) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ S : Set C(α,ℝ),
      S ⊆ (fun f : C(α,ℝ) => R • f) '' featureBall K ∧ S.Finite ∧
      Metric.IsCover (2*ε) ((fun f : C(α,ℝ) => R • f) '' featureBall K) S ∧
      (Nat.card S : ℝ)*
        (Real.exp (-(R^2)/2)*(P.map F).real (Metric.closedBall 0 (ε:ℝ))) ≤ 1 := by
  let μ := P.map F
  let KR := (fun f : C(α,ℝ) => R • f) '' featureBall K
  have hc : Continuous (fun f : C(α,ℝ) => R • f) := by fun_prop
  have hcompact : IsCompact KR := (featureBall_isCompact K).image hc
  apply AlignmentPaperProbabilityNets.exists_compact_net_of_ball_mass μ KR hcompact ε hε
  rintro center ⟨f,hf,rfl⟩
  have hs := AlignmentPaperMaternSmallBall.featurePathLaw_ball_shift_lower
    F hF hX hmean K a ha hcov R (ε:ℝ) hR hε f hf
  have hfin : ENNReal.ofReal (Real.exp (-(R^2)/2)) *
      (P.map F) (Metric.closedBall 0 (ε:ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (P.map F) _)
  have ht := (ENNReal.toReal_le_toReal hfin (measure_ne_top (P.map F) _)).2 hs
  change Real.exp (-(R^2)/2)*((P.map F) (Metric.closedBall 0 (ε:ℝ))).toReal ≤
    ((P.map F) (Metric.closedBall (R • f) (ε:ℝ))).toReal
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using ht

/-- The actual feature-ball embedding has its natural uniform bound. -/
theorem featureBall_norm_le {α H : Type*} [MetricSpace α] [CompactSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : C(α,H)) {f : C(α,ℝ)} (hf : f ∈ featureBall K) : ‖f‖ ≤ ‖K‖ := by
  obtain ⟨g,hg,rfl⟩ := hf
  apply (ContinuousMap.norm_le _ (norm_nonneg K)).2
  intro x
  change ‖inner ℝ g (K x)‖ ≤ ‖K‖
  calc
    _ ≤ ‖g‖*‖K x‖ := norm_inner_le_norm _ _
    _ ≤ 1*‖K‖ := mul_le_mul hg (K.norm_coe_le_norm x) (norm_nonneg _) (by norm_num)
    _ = ‖K‖ := one_mul _

/-- Net representatives in a dilated Cameron--Martin ball have a diameter
bound uniform over the actual finite codebook. -/
theorem scaled_featureBall_diameter_le {α H : Type*} [MetricSpace α] [CompactSpace α]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (K : C(α,H)) (R : ℝ) (hR : 0 ≤ R) {f g : C(α,ℝ)}
    (hf : f ∈ (fun h : C(α,ℝ) => R • h) '' featureBall K)
    (hg : g ∈ (fun h : C(α,ℝ) => R • h) '' featureBall K) :
    dist f g ≤ 2*R*‖K‖ := by
  obtain ⟨f,hf,rfl⟩ := hf
  obtain ⟨g,hg,rfl⟩ := hg
  rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hR]
  calc
    R*‖f-g‖ ≤ R*(‖f‖+‖g‖) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) hR
    _ ≤ R*(‖K‖+‖K‖) := mul_le_mul_of_nonneg_left
      (add_le_add (featureBall_norm_le K hf) (featureBall_norm_le K hg)) hR
    _ = 2*R*‖K‖ := by ring

/-- Explicit conversion of the probability packing budget into the
exponential codebook-size bound used in Gaussian quantization. -/
theorem cardinal_le_exp_of_shift_budget {N : ℕ} {a p φ : ℝ}
    (hp : 0 < p) (hbudget : (N:ℝ)*(Real.exp (-a)*p) ≤ 1)
    (hsmallball : -Real.log p ≤ φ) :
    (N:ℝ) ≤ Real.exp (a+φ) := by
  have heq : (Real.exp (-a)*p)*Real.exp (a-Real.log p)=1 := by
    rw [Real.exp_sub,Real.exp_log hp,Real.exp_neg]
    field_simp [hp.ne',Real.exp_ne_zero a]
  calc
    (N:ℝ) = ((N:ℝ)*(Real.exp (-a)*p))*Real.exp (a-Real.log p) := by
      rw [mul_assoc,heq,mul_one]
    _ ≤ 1*Real.exp (a-Real.log p) :=
      mul_le_mul_of_nonneg_right hbudget (Real.exp_pos _).le
    _ = Real.exp (a-Real.log p) := one_mul _
    _ ≤ Real.exp (a+φ) := Real.exp_le_exp.mpr (by linarith)

end BrownianSharp.AlignmentPaperGaussianFeatureNets
