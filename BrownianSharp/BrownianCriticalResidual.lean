import BrownianSharp.BrownianGaussianResidual
import BrownianSharp.BrownianTentCriticalGram

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

/-- The stochastic integral of a deterministic projection splits into its
orthogonal residual and projected coordinate almost surely. -/
theorem isonormal_eval_projection_decomposition_ae
    {H Ω ι : Type*} [Fintype ι] [Nonempty ι] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P]
    (W : IsonormalGaussianFamily H Ω ι P) (v e : H) (c : ℝ)
    :
    (fun ω => W.eval v ω) =ᵐ[P]
      (fun ω => W.eval (v - c • e) ω + c * W.eval e ω) := by
  have hadd := isonormal_eval_add_ae W (v - c • e) (c • e)
  have hsmul := isonormal_eval_smul_ae W e c
  filter_upwards [hadd, hsmul] with ω ha hs
  have hvec : (v - c • e) + c • e = v := sub_add_cancel v (c • e)
  simpa [hvec] using ha.trans (congrArg (fun x : ℝ =>
    W.eval (v - c • e) ω + x) hs)

private theorem criticalETensorLp_tentLp_inner_eq_integral {d : ℕ}
    (profileE cellsE profileT cellsT : Fin d → ℕ) :
    ⟪criticalDyadicETensorLp profileE cellsE,
      tensorIntegratedTentDyadicLp profileT cellsT⟫ =
      ∫ x : Fin d → ℝ,
        criticalDyadicETensor profileE cellsE x *
          tensorIntegratedTentDyadic profileT cellsT x ∂
            (Measure.pi fun _ : Fin d => volume) := by
  let a : Fin d → ℝ := fun i => integratedTentDyadicLeft (profileT i) (cellsT i)
  let b : Fin d → ℝ := fun i => integratedTentDyadicRight (profileT i) (cellsT i)
  let m : Fin d → ℝ := fun i => (a i + b i) / 2
  have hab : ∀ i, a i < b i := by
    intro i
    dsimp [a, b, integratedTentDyadicLeft, integratedTentDyadicRight]
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity
  have hmid : ∀ i, m i = (a i + b i) / 2 := by intro i; rfl
  change ⟪criticalDyadicETensorLp profileE cellsE,
    tensorIntegratedHaarTentLp a m b hab hmid⟫ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp
    (criticalDyadicETensor_memLp_two profileE cellsE),
    MemLp.coeFn_toLp (tensorIntegratedHaarTent_memLp_two a m b hab hmid)] with x he ht
  have htent : (tensorIntegratedHaarTent a m b x) =
      tensorIntegratedTentDyadic profileT cellsT x := by
    simp [tensorIntegratedHaarTent, tensorIntegratedTentDyadic,
      a, b, m, integratedTentDyadicLeft, integratedTentDyadicRight]
  simp only [criticalDyadicETensorLp, tensorIntegratedHaarTentLp]
  rw [he, ht]
  rw [RCLike.inner_apply]
  rw [htent]
  simp
  ring

noncomputable def brownianCriticalTentGramScale {d : ℕ}
    (profile cells : Fin d → ℕ) : ℝ :=
  ∏ i, ((realDyadicRight (profile i) (cells i) - realDyadicLeft (profile i) (cells i)) *
    Real.sqrt (realDyadicRight (profile i) (cells i) -
      realDyadicLeft (profile i) (cells i)) / 8)

private theorem brownianCriticalETensor_tentTensor_gram
    {d : ℕ} (profileE cellsE profileT cellsT : Fin d → ℕ)
    (hTotal : (∑ i, profileE i) = ∑ i, profileT i)
    (hPairDistinct : profileE ≠ profileT ∨ cellsE ≠ cellsT) :
    ⟪criticalDyadicETensorLp profileE cellsE,
      tensorIntegratedTentDyadicLp profileT cellsT⟫ = 0 := by
  rw [criticalETensorLp_tentLp_inner_eq_integral]
  have hzero : ∫ x : Fin d → ℝ,
      tensorIntegratedTentDyadic profileT cellsT x *
        criticalDyadicETensor profileE cellsE x ∂
          (Measure.pi fun _ : Fin d => volume) = 0 := by
    rcases hPairDistinct with hprof | hcell
    · exact brownianTentTensor_criticalETensor_inner_zero_of_equal_total_ne_profile
        profileT cellsT profileE cellsE hTotal.symm (Ne.symm hprof)
    · by_cases hprof : profileE = profileT
      · subst profileT
        exact brownianTentTensor_criticalETensor_inner_zero_of_same_profile_cell_mismatch
          profileE cellsT cellsE hcell.symm
      · exact brownianTentTensor_criticalETensor_inner_zero_of_equal_total_ne_profile
          profileT cellsT profileE cellsE hTotal.symm (Ne.symm hprof)
  calc
    ∫ x : Fin d → ℝ,
        criticalDyadicETensor profileE cellsE x *
          tensorIntegratedTentDyadic profileT cellsT x ∂
            (Measure.pi fun _ : Fin d => volume) =
        ∫ x : Fin d → ℝ,
          tensorIntegratedTentDyadic profileT cellsT x *
            criticalDyadicETensor profileE cellsE x ∂
              (Measure.pi fun _ : Fin d => volume) := by
                apply integral_congr_ae
                filter_upwards with x
                ring
    _ = 0 := hzero

/-- A finite family of actual critical tensor coefficients is independent of
the corresponding tent residuals after its exact diagonal projection is
removed.  Profiles share a common total depth and the profile/cell encoding
is injective. -/
theorem brownianCriticalTensor_projectionResidual_indepFun
    {d : ℕ} {Ω I : Type*} [Fintype I] [DecidableEq I] [MeasurableSpace Ω]
    {P : Measure Ω}
    (W : IsonormalGaussianFamily
      (Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) Ω (Sum I I) P)
    (profile cells : I → Fin d → ℕ) (T : ℕ)
    (hTotal : ∀ i, (∑ k, profile i k) = T)
    (hInjective : ∀ i j, profile i = profile j → cells i = cells j → i = j) :
    IndepFun
      (fun ω i => W.eval (criticalDyadicETensorLp (profile i) (cells i)) ω)
      (fun ω j => W.eval
        (tensorIntegratedTentDyadicLp (profile j) (cells j) -
          brownianCriticalTentGramScale (profile j) (cells j) •
            criticalDyadicETensorLp (profile j) (cells j)) ω) P := by
  apply isonormal_projectionResidual_indepFun W
    (fun i => criticalDyadicETensorLp (profile i) (cells i))
    (fun i => tensorIntegratedTentDyadicLp (profile i) (cells i))
    (fun i => brownianCriticalTentGramScale (profile i) (cells i))
  · intro i j
    by_cases hij : i = j
    · subst j
      simpa using criticalDyadicETensorLp_inner_self (profile i) (cells i)
    · have hne : profile i ≠ profile j ∨ cells i ≠ cells j := by
        by_contra h
        push_neg at h
        exact hij (hInjective i j h.1 h.2)
      rcases hne with hprofile | hcell
      · have hcoord : ∃ k, profile i k ≠ profile j k := by
          by_contra h
          push_neg at h
          exact hprofile (funext h)
        obtain ⟨k,hk⟩ := hcoord
        simpa [hij] using criticalDyadicETensorLp_inner_zero_of_coordinate_ne
          (profile i) (cells i) (profile j) (cells j) k (Or.inl hk)
      · have hcoord : ∃ k, cells i k ≠ cells j k := by
          by_contra h
          push_neg at h
          exact hcell (funext h)
        obtain ⟨k,hk⟩ := hcoord
        simpa [hij] using criticalDyadicETensorLp_inner_zero_of_coordinate_ne
          (profile i) (cells i) (profile j) (cells j) k (Or.inr hk)
  · intro i j
    by_cases hij : i = j
    · subst j
      rw [criticalETensorLp_tentLp_inner_eq_integral]
      have hswap : ∫ x : Fin d → ℝ,
          criticalDyadicETensor (profile i) (cells i) x *
            tensorIntegratedTentDyadic (profile i) (cells i) x ∂
              (Measure.pi fun _ : Fin d => volume) =
          ∫ x : Fin d → ℝ,
            tensorIntegratedTentDyadic (profile i) (cells i) x *
              criticalDyadicETensor (profile i) (cells i) x ∂
                (Measure.pi fun _ : Fin d => volume) := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      rw [hswap, brownianTentTensor_criticalETensor_diagonal]
      simp [brownianCriticalTentGramScale]
    · have hne : profile i ≠ profile j ∨ cells i ≠ cells j := by
        by_contra h
        push_neg at h
        exact hij (hInjective i j h.1 h.2)
      have hpairTotal : (∑ k, profile i k) = ∑ k, profile j k :=
        (hTotal i).trans (hTotal j).symm
      simpa [hij] using brownianCriticalETensor_tentTensor_gram
        (profile i) (cells i) (profile j) (cells j) hpairTotal hne

end HaarQuarter
