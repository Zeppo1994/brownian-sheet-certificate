import BrownianSharp.BrownianHaarCovariance
import BrownianSharp.BrownianCriticalProjection

/-! The finite critical projection/residual independence theorem for actual
continuous tensor functions.  The only stochastic input is one jointly
Gaussian isonormal family indexed by the combined signal/residual coordinates;
the cross-covariance is proved from the deterministic Gram identities. -/

open MeasureTheory InnerProductSpace ProbabilityTheory
open scoped RealInnerProductSpace

namespace HaarQuarter

/-- A scalar coordinate of an isonormal Gaussian family has a finite second
moment.  The constant finite family exposes any requested integrand as one
coordinate of the jointly Gaussian map. -/
private theorem isonormal_eval_memLp_two
    {H Ω ι : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace Ω]
    {P : Measure Ω} (W : IsonormalGaussianFamily H Ω ι P) (f : H) :
    MemLp (fun ω => W.eval f ω) 2 P := by
  classical
  let i : ι := Classical.choice ‹Nonempty ι›
  have hX := (W.jointlyGaussian (fun _ : ι => f)).eval i
  have hmem := hX.memLp_two
  simpa using hmem

/-- Covariance isometry forces the stochastic-integral additivity relation
almost surely.  Finite second moments are derived from the jointly Gaussian
law; linearity itself follows from the covariance isometry and zero variance. -/
theorem isonormal_eval_add_ae
    {H Ω ι : Type*} [Fintype ι] [Nonempty ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    (W : IsonormalGaussianFamily H Ω ι P)
    (f g : H)
    :
    (fun ω => W.eval (f + g) ω) =ᵐ[P]
      (fun ω => W.eval f ω + W.eval g ω) := by
  let A : Ω → ℝ := fun ω => W.eval (f + g) ω
  let F : Ω → ℝ := fun ω => W.eval f ω
  let G : Ω → ℝ := fun ω => W.eval g ω
  let B : Ω → ℝ := F + G
  have hf := isonormal_eval_memLp_two W f
  have hg := isonormal_eval_memLp_two W g
  have hfg := isonormal_eval_memLp_two W (f + g)
  have hB : MemLp B 2 P := hf.add hg
  have hAA : ProbabilityTheory.covariance A A P = ⟪f + g, f + g⟫ := by
    exact W.covariance_eq_inner (f + g) (f + g)
  have hAB : ProbabilityTheory.covariance A B P =
      ⟪f + g, f⟫ + ⟪f + g, g⟫ := by
    have htmp := ProbabilityTheory.covariance_add_right hfg hf hg
    rw [W.covariance_eq_inner, W.covariance_eq_inner] at htmp
    change ProbabilityTheory.covariance
      (fun ω => W.eval (f + g) ω) (F + G) P = _
    simpa [F, G] using htmp
  have hBA : ProbabilityTheory.covariance B A P =
      ⟪f, f + g⟫ + ⟪g, f + g⟫ := by
    have htmp := ProbabilityTheory.covariance_add_left hf hg hfg
    rw [W.covariance_eq_inner, W.covariance_eq_inner] at htmp
    change ProbabilityTheory.covariance (F + G)
      (fun ω => W.eval (f + g) ω) P = _
    simpa [F, G] using htmp
  have hBB : ProbabilityTheory.covariance B B P =
      ⟪f, f⟫ + ⟪f, g⟫ + ⟪g, f⟫ + ⟪g, g⟫ := by
    have htmp := ProbabilityTheory.covariance_add_left hf hg hB
    rw [ProbabilityTheory.covariance_add_right hf hf hg,
      ProbabilityTheory.covariance_add_right hg hf hg] at htmp
    rw [W.covariance_eq_inner, W.covariance_eq_inner,
      W.covariance_eq_inner, W.covariance_eq_inner] at htmp
    simpa [B, F, G, Pi.add_apply, add_assoc, real_inner_self_eq_norm_sq] using htmp
  have hcov : ProbabilityTheory.covariance (A - B) (A - B) P = 0 := by
    rw [ProbabilityTheory.covariance_sub_sub hfg hB hfg hB, hAA, hAB, hBA, hBB]
    simp only [inner_add_left, inner_add_right]
    ring
  have hvar : ProbabilityTheory.variance (A - B) P = 0 := by
    rw [← ProbabilityTheory.covariance_self (hfg.sub hB).aemeasurable]
    exact hcov
  have hmeanA : ∫ ω, A ω ∂P = 0 := W.mean_zero (f + g)
  have hmeanB : ∫ ω, B ω ∂P = 0 := by
    have htmp := integral_add (hf.integrable (by norm_num)) (hg.integrable (by norm_num))
    rw [W.mean_zero f, W.mean_zero g] at htmp
    simpa [B, F, G, Pi.add_apply] using htmp
  have hmean : ∫ ω, (A - B) ω ∂P = 0 := by
    have htmp := integral_sub (hfg.integrable (by norm_num)) (hB.integrable (by norm_num))
    rw [hmeanA, hmeanB] at htmp
    simpa [A, B] using htmp
  have hAE := ProbabilityTheory.ae_eq_integral_of_variance_eq_zero
    (hfg.sub hB) hvar
  filter_upwards [hAE] with ω hω
  change A ω - B ω = ∫ x, (A - B) x ∂P at hω
  rw [hmean] at hω
  change A ω - B ω = 0 at hω
  dsimp [A, B] at hω
  linarith

/-- Covariance isometry also forces homogeneity almost surely. -/
theorem isonormal_eval_smul_ae
    {H Ω ι : Type*} [Fintype ι] [Nonempty ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    (W : IsonormalGaussianFamily H Ω ι P) (f : H) (c : ℝ)
    :
    (fun ω => W.eval (c • f) ω) =ᵐ[P]
      (fun ω => c * W.eval f ω) := by
  let A : Ω → ℝ := fun ω => W.eval (c • f) ω
  let F : Ω → ℝ := fun ω => W.eval f ω
  let B : Ω → ℝ := c • F
  have hf := isonormal_eval_memLp_two W f
  have hcf := isonormal_eval_memLp_two W (c • f)
  have hB : MemLp B 2 P := hf.const_smul c
  have hAA : ProbabilityTheory.covariance A A P = ⟪c • f, c • f⟫ :=
    W.covariance_eq_inner (c • f) (c • f)
  have hAB : ProbabilityTheory.covariance A B P =
      c * ⟪c • f, f⟫ := by
    change ProbabilityTheory.covariance A (c • F) P = _
    rw [ProbabilityTheory.covariance_smul_right c, W.covariance_eq_inner]
  have hBA : ProbabilityTheory.covariance B A P =
      c * ⟪f, c • f⟫ := by
    change ProbabilityTheory.covariance (c • F) A P = _
    rw [ProbabilityTheory.covariance_smul_left c, W.covariance_eq_inner]
  have hBB : ProbabilityTheory.covariance B B P =
      c ^ 2 * ⟪f, f⟫ := by
    change ProbabilityTheory.covariance (c • F) (c • F) P = _
    rw [ProbabilityTheory.covariance_smul_left c,
      ProbabilityTheory.covariance_smul_right c, W.covariance_eq_inner]
    ring
  have hcov : ProbabilityTheory.covariance (A - B) (A - B) P = 0 := by
    rw [ProbabilityTheory.covariance_sub_sub hcf hB hcf hB, hAA, hAB, hBA, hBB]
    simp only [inner_smul_left, inner_smul_right]
    ring
  have hvar : ProbabilityTheory.variance (A - B) P = 0 := by
    rw [← ProbabilityTheory.covariance_self (hcf.sub hB).aemeasurable]
    exact hcov
  have hmeanA : ∫ ω, A ω ∂P = 0 := W.mean_zero (c • f)
  have hmeanB : ∫ ω, B ω ∂P = 0 := by
    have htmp := integral_const_mul (μ := P) c (fun ω => W.eval f ω)
    rw [W.mean_zero f] at htmp
    simpa [B, F] using htmp
  have hmean : ∫ ω, (A - B) ω ∂P = 0 := by
    have htmp := integral_sub (hcf.integrable (by norm_num)) (hB.integrable (by norm_num))
    rw [hmeanA, hmeanB] at htmp
    simpa [A, B, F] using htmp
  have hAE := ProbabilityTheory.ae_eq_integral_of_variance_eq_zero
    (hcf.sub hB) hvar
  filter_upwards [hAE] with ω hω
  change A ω - B ω = ∫ x, (A - B) x ∂P at hω
  rw [hmean] at hω
  change A ω - B ω = 0 at hω
  dsimp [A, B, F] at hω
  linarith

end HaarQuarter
