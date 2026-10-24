import BrownianSharp.AlignmentEndpointBrownianReverse
import BrownianSharp.AlignmentAuditHaarDilationBudget
import BrownianSharp.AlignmentGaussianReverseClosure

noncomputable section
open MeasureTheory ProbabilityTheory HaarQuarter
open scoped BigOperators RealInnerProductSpace ENNReal
namespace BrownianSharp.AlignmentGaussianBrownianReverse
open AlignmentEndpointBrownianReverse AlignmentEndpointGaussianHaarLaw
open AlignmentGaussianFiniteFeature AlignmentGaussianHaarProjection AlignmentGaussianChaining
open AlignmentExponentialDiagonalDilation AlignmentEndpointCubeGridLimit
open AlignmentExponentialReverseInversion AlignmentGaussianReverseClosure

/-- The finite-dimensional Gaussian confidence event transfers to the
original Brownian sheet on its actual dyadic grid. -/
theorem brownian_grid_mass_lower_of_scaled_field
    {d N M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (ρ : ℝ) (hρ : 0≤ρ)
    (hscaled : (1/2:ENNReal)≤productStandardGaussian (FiniteHaarIndex d M)
      {z | ‖finiteGaussianFeaturePath (scaledHaarFeaturePath (N:=N) (M:=M)) z‖≤ρ}) :
    ENNReal.ofReal (∏a : FiniteHaarIndex d M,gradeScale N (finiteHaarGrade a))*(1/2)≤
      P {ω | cubeGridMaximum M (B.path ω)≤ρ} := by
  classical
  let I := FiniteHaarIndex d M
  let S : Set (I→ℝ) := {z | ∀j : CubeDyadicGrid d M,|unscaledHaarGridRow z j|≤ρ}
  let D : (I→ℝ)→I→ℝ := fun z a=>gradeScale N (finiteHaarGrade a)*z a
  have hS : MeasurableSet S := by
    simp only [S,Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    apply measurableSet_le _ measurable_const
    unfold unscaledHaarGridRow
    fun_prop
  have hpos : ∀a : I,0<gradeScale N (finiteHaarGrade a) := by
    intro a
    unfold gradeScale
    split_ifs <;> positivity
  have hD := productGaussian_diagonal_dilation_preimage_ge
    (fun a : I=>gradeScale N (finiteHaarGrade a)) hpos
    (fun a=>gradeScale_le_one _ _) hS
  have hrow : ∀z : I→ℝ,∀j : CubeDyadicGrid d M,
      unscaledHaarGridRow (D z) j=
        finiteGaussianFeaturePath (scaledHaarFeaturePath (N:=N) (M:=M)) z (cubeDyadicAnchor j) := by
    intro z j
    rw [finiteGaussianFeaturePath_apply]
    unfold unscaledHaarGridRow
    apply Finset.sum_congr rfl
    intro a _
    rw [scaledHaarFeaturePath_apply,real_inner_comm]
    dsimp [D]
    ring
  have hsub : {z : I→ℝ |
      ‖finiteGaussianFeaturePath (scaledHaarFeaturePath (N:=N) (M:=M)) z‖≤ρ}⊆D ⁻¹' S := by
    intro z hz j
    rw [hrow]
    exact (ContinuousMap.norm_coe_le_norm _ _).trans hz
  have hmass : (1/2:ENNReal)≤productStandardGaussian I (D ⁻¹' S) :=
    hscaled.trans (measure_mono hsub)
  have hP : P {ω | cubeGridMaximum M (B.path ω)≤ρ}=productStandardGaussian I S := by
    have heq : {ω | cubeGridMaximum M (B.path ω)≤ρ}=
        {ω | ∀j : CubeDyadicGrid d M,|B.eval (cubeDyadicAnchor j) ω|≤ρ} := by
      ext ω
      simp only [cubeGridMaximum,pi_norm_le_iff_of_nonneg hρ,Real.norm_eq_abs,
        BrownianSheetOnCube.eval]
    rw [heq,brownian_grid_event_eq_product_gaussian B ρ]
  rw [hP]
  exact (mul_le_mul le_rfl hmass bot_le bot_le).trans hD

/-- The checked finite-dimensional Gaussian construction gives a lower
probability estimate for the actual full continuous Brownian sheet. -/
theorem brownian_dyadic_reverse_of_scaled_field_mass {d : ℕ} (hd : 2≤d)
    (A : ℝ) (hA : 0<A)
    (hscaled : ∀N M : ℕ,(1/2:ENNReal)≤productStandardGaussian (FiniteHaarIndex d M)
      {z | ‖finiteGaussianFeaturePath (scaledHaarFeaturePath (N:=N) (M:=M)) z‖≤
        radiusProfile d A N}) :
    ∃B : ℝ,0<B ∧
      ∀(Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : BrownianSheetOnCube d Ω P) (N : ℕ),
      Real.exp (-B*((2:ℝ)^N*((N+1:ℕ):ℝ)^(d-1)))≤
        P.real {ω | ‖X.path ω‖≤radiusProfile d A N} := by
  let C : ℝ := 2*Real.log 2*(d:ℝ)^(d-1)
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0<C := by
    dsimp [C]
    have hdR : 0<(d:ℝ) := by exact_mod_cast (by omega : 0<d)
    positivity
  refine ⟨C+Real.log 2,add_pos hC hl2,?_⟩
  intro Ω _ P _ X N
  let ρ := radiusProfile d A N
  let cost : ℝ := (2:ℝ)^N*((N+1:ℕ):ℝ)^(d-1)
  have hρ : 0<ρ := by dsimp [ρ,radiusProfile]; positivity
  have hgrid : ∀M : ℕ, ENNReal.ofReal (Real.exp (-C*cost))*(1/2)≤
      P {ω | cubeGridMaximum M (X.path ω)≤ρ} := by
    intro M
    have hdet : Real.exp (-C*cost)≤
        ∏a : FiniteHaarIndex d M,gradeScale N (finiteHaarGrade a) := by
      have hh := gradeScale_diagonal_product_exp_lower N d M (by omega)
      convert hh using 1 <;> congr 1 <;> dsimp [C,cost] <;> push_cast <;> ring
    have hh := brownian_grid_mass_lower_of_scaled_field X ρ hρ.le (hscaled N M)
    exact (mul_le_mul (ENNReal.ofReal_le_ofReal hdet) le_rfl bot_le bot_le).trans hh
  have hfull := cube_grid_mass_lower_to_uniform_mass_lower P X.path X.measurable_path
    ρ hρ.le (ENNReal.ofReal (Real.exp (-C*cost))*(1/2)) hgrid
  have hreal := ENNReal.toReal_mono (measure_ne_top P _) hfull
  norm_num only [ENNReal.toReal_mul,ENNReal.toReal_div,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)] at hreal
  norm_num at hreal
  have hcost : 1≤cost := by
    have hp : (1:ℝ)≤(2:ℝ)^N := one_le_pow₀ (by norm_num)
    have hs : (1:ℝ)≤((N+1:ℕ):ℝ) := by exact_mod_cast (by omega : 1≤N+1)
    have hq : (1:ℝ)≤((N+1:ℕ):ℝ)^(d-1) := one_le_pow₀ hs
    dsimp [cost]
    nlinarith [mul_le_mul_of_nonneg_left hq (show 0≤(2:ℝ)^N by positivity)]
  have habsorb : Real.exp (-(C+Real.log 2)*cost)≤Real.exp (-C*cost)/2 := by
    calc
      _≤Real.exp (-C*cost-Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hcost hl2.le]
      _=Real.exp (-C*cost)/2 := by
        rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<2)]
  exact habsorb.trans (by simpa only [div_eq_mul_inv,one_mul,neg_mul,Measure.real_def,ρ] using hreal)

/-- Constructive dyadic reverse bound, with constants chosen from dimension
alone before the probability space and Brownian-sheet realization. -/
theorem dyadic_brownian_reverse_certified : DyadicBrownianReverseStatement := by
  intro d hd
  obtain ⟨A,hA,hscaled⟩ := exists_scaledFiniteGaussianPath_half_mass hd
  obtain ⟨B,hB,hfull⟩ := brownian_dyadic_reverse_of_scaled_field_mass hd A hA (by
    intro N M
    simpa only [scaledFiniteGaussianPath] using hscaled N M)
  exact ⟨A,B,hA,hB,0,fun Ω _ P _ X N _=>hfull Ω P X N⟩

theorem brownian_upperLog_certified : BrownianUpperLogStatement :=
  brownian_upperLog_of_dyadic dyadic_brownian_reverse_certified

/-- The complete, literal two-sided Brownian-sheet clause in the latest
manuscript, proved for the actual continuous path law. -/
theorem latest_brownian_twoSided_certified : Latest.BrownianTwoSidedStatement :=
  latest_brownian_twoSided_of_dyadic dyadic_brownian_reverse_certified

end BrownianSharp.AlignmentGaussianBrownianReverse

