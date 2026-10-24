import BrownianSharp.AlignmentGaussianIntegratedSourceModel
import BrownianSharp.AlignmentExponentialDiagonalDilation
import BrownianSharp.AlignmentExponentialGaussianMaximum
import BrownianSharp.GaussianGridStatistics
import BrownianSharp.SheetProjection
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic

/-! Finite-grid confinement for an integrated Brownian sheet, by splitting its
actual finite-dimensional Gaussian law into selected source coordinates and an
independent orthogonal residual. The analytic inputs are only the scaled-main
half-mass and an explicit uniform bound on residual feature norms. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators RealInnerProductSpace ENNReal

namespace BrownianSharp.AlignmentGaussianIntegratedFiniteGridConfinement

open AlignmentGaussianIntegratedSourceModel
open AlignmentExponentialDiagonalDilation
open AlignmentExponentialGaussianMaximum
open GaussianProjection
open HaarQuarter

private def gridVector {J Ω : Type*} [Fintype J]
    (X : J → Ω → ℝ) (ω : Ω) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun j => X j ω)

/-- The actual integrated-sheet grid has a quantitative small-ball lower bound
once the scaled finite main field has half-mass and the orthogonal residual
has sufficiently small expected grid maximum. The determinant factor is the
volume cost of contracting the independent source coordinates. -/
theorem integratedGrid_confinement_of_main_half_mass
    {d : ℕ} {Ω I J : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype J] [Nonempty J]
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ)
    (e : I → CameronMartin.UnitCubeL2 d)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0)
    (x : J → BrownianCubeAnchor d) (a : I → ℝ) (ρ τ : ℝ)
    (hρ : 0 < ρ) (hτ : 0 ≤ τ)
    (ha : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1)
    (hscaled : (1/2:ENNReal) ≤ productStandardGaussian I
      {z | ∀ j, |∑ i, ⟪integerIntegratedKernelFeature m (x j), e i⟫ *
        (a i * z i)| ≤ ρ})
    (hres : ∀ j, ‖integerIntegratedKernelFeature m (x j) -
      projection e (integerIntegratedKernelFeature m (x j))‖ ≤ τ)
    (hbudget : 2 * τ * Real.sqrt (Real.log (2 * (Fintype.card J : ℝ) + 2)) ≤ ρ / 2) :
    ENNReal.ofReal (∏ i, a i) * ((1/2:ENNReal) * (1/2:ENNReal)) ≤
      P {ω | ∀ j, |BrownianSharp.AlignmentGaussianRates.integrateSheetPath
        m (B.path ω) (x j)| ≤ 2 * ρ} := by
  classical
  obtain ⟨W, hlaw, hindep, hmarg, hresIndep⟩ :=
    integratedGrid_law_eq_finiteSourceModel B m e he x
  let H := finiteSourceSpan (Sum.elim e (integerIntegratedKernelFeature m ∘ x))
  let Q : Measure H := stdGaussian H
  let eb : I → H := sourceFrameLift e (integerIntegratedKernelFeature m ∘ x)
  let vb : J → H := sourceFeatureLift e (integerIntegratedKernelFeature m ∘ x)
  let Z : H → I → ℝ := fun ω i => W.eval (eb i) ω
  let R : H → J → ℝ := fun ω j =>
    W.eval (vb j - projection eb (vb j)) ω
  let mainSet : Set (I → ℝ) := {z | ∀ j,
    |∑ i, ⟪integerIntegratedKernelFeature m (x j), e i⟫ * z i| ≤ ρ}
  let scaledSet : Set (I → ℝ) := {z | ∀ j,
    |∑ i, ⟪integerIntegratedKernelFeature m (x j), e i⟫ * (a i * z i)| ≤ ρ}
  let residualSet : Set (J → ℝ) := {z | ∀ j, |z j| ≤ ρ}
  let actualVec : Ω → EuclideanSpace ℝ J := gridVector (fun j ω =>
    BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) (x j))
  let modelVec : H → EuclideanSpace ℝ J := gridVector (fun j ω => W.eval (vb j) ω)
  let gridSet : Set (EuclideanSpace ℝ J) := {z | ∀ j, |z j| ≤ 2 * ρ}
  have he' : ∀ i j, ⟪eb i, eb j⟫ = if i = j then 1 else 0 := by
    intro i j
    exact he i j
  have hZmeas : Measurable Z := by
    apply measurable_pi_lambda
    intro i
    exact W.measurable_eval _
  have hRmeas : Measurable R := by
    apply measurable_pi_lambda
    intro j
    exact W.measurable_eval _
  have hmainMeas : MeasurableSet mainSet := by
    simp only [mainSet, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le (by fun_prop) (measurable_const)
  have hscaledMeas : MeasurableSet scaledSet := by
    simp only [scaledSet, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le (by fun_prop) (measurable_const)
  have hresMeas : MeasurableSet residualSet := by
    simp only [residualSet, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le (by fun_prop) (measurable_const)
  have hgridMeas : MeasurableSet gridSet := by
    simp only [gridSet, Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le (by fun_prop) (measurable_const)
  let D : (I → ℝ) → (I → ℝ) := fun z i => a i * z i
  have hDpre : D ⁻¹' mainSet = scaledSet := by
    ext z
    simp [D, mainSet, scaledSet]
  have hmainDilation := productGaussian_diagonal_dilation_preimage_ge
    a ha ha1 hmainMeas
  have hscaledMass : (1/2:ENNReal) ≤ productStandardGaussian I (D ⁻¹' mainSet) := by
    simpa only [hDpre] using hscaled
  have hmainMassProd : ENNReal.ofReal (∏ i, a i) * (1/2:ENNReal) ≤
      productStandardGaussian I mainSet := by
    calc
      ENNReal.ofReal (∏ i, a i) * (1/2:ENNReal) ≤
          ENNReal.ofReal (∏ i, a i) * productStandardGaussian I (D ⁻¹' mainSet) :=
        by simpa [mul_comm] using mul_le_mul_left hscaledMass (ENNReal.ofReal (∏ i, a i))
      _ ≤ productStandardGaussian I mainSet := hmainDilation
  have hZlaw : Q.map Z = productStandardGaussian I := by
    rw [hindep.map_fun_eq_pi_map (fun i => (W.measurable_eval (eb i)).aemeasurable)]
    change Measure.pi (fun i : I => Q.map (W.eval (eb i))) =
      Measure.pi (fun _ : I => gaussianReal 0 1)
    congr 1
    funext i
    exact hmarg i
  have hmainMass : ENNReal.ofReal (∏ i, a i) * (1/2:ENNReal) ≤ Q (Z ⁻¹' mainSet) := by
    calc
      _ ≤ productStandardGaussian I mainSet := hmainMassProd
      _ = Q (Z ⁻¹' mainSet) := by
        rw [← hZlaw, Measure.map_apply hZmeas hmainMeas]
  have hRlaw (j : J) : HasLaw (R · j)
      (gaussianReal 0 (‖integerIntegratedKernelFeature m (x j) -
        projection e (integerIntegratedKernelFeature m (x j))‖ ^ 2).toNNReal) Q := by
    let r : H := vb j - projection eb (vb j)
    let idx : Sum I J := Sum.inl (Classical.choice ‹Nonempty I›)
    have hcoord := W.coordinate_law (fun _ : Sum I J => r) idx
    have hrvec : (r : CameronMartin.UnitCubeL2 d) =
        integerIntegratedKernelFeature m (x j) -
          projection e (integerIntegratedKernelFeature m (x j)) := by
      apply Subtype.ext
      simp [r, vb, eb, sourceFeatureLift, sourceFrameLift, projection,
        real_inner_comm]
    have hnorm := congrArg norm hrvec
    have hinner : ⟪r, r⟫ =
        ‖integerIntegratedKernelFeature m (x j) -
          projection e (integerIntegratedKernelFeature m (x j))‖ ^ 2 := by
      calc
        ⟪r, r⟫ = ‖r‖ ^ 2 := real_inner_self_eq_norm_sq r
        _ = ‖(r : CameronMartin.UnitCubeL2 d)‖ ^ 2 := by rfl
        _ = _ := by rw [hrvec]
    refine ⟨(W.measurable_eval r).aemeasurable, ?_⟩
    change Q.map (fun ω => W.eval r ω) =
      gaussianReal 0 (‖integerIntegratedKernelFeature m (x j) -
        projection e (integerIntegratedKernelFeature m (x j))‖ ^ 2).toNNReal
    rw [← hinner]
    simpa [r] using hcoord
  have hvar : ∀ j, ((‖integerIntegratedKernelFeature m (x j) -
      projection e (integerIntegratedKernelFeature m (x j))‖ ^ 2).toNNReal : ℝ) ≤ τ ^ 2 := by
    intro j
    have h := hres j
    have hsquare : ‖integerIntegratedKernelFeature m (x j) -
        projection e (integerIntegratedKernelFeature m (x j))‖ ^ 2 ≤ τ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hτ).2 h
    have hnn := Real.toNNReal_le_toNNReal hsquare
    calc
      ↑(‖integerIntegratedKernelFeature m (x j) -
          projection e (integerIntegratedKernelFeature m (x j))‖ ^ 2).toNNReal ≤
          ↑(τ ^ 2).toNNReal := hnn
      _ = τ ^ 2 := Real.coe_toNNReal (τ ^ 2) (sq_nonneg τ)
  have hexpect := expected_max_le_sqrt_log (fun j ω => R ω j) hRlaw hτ hvar
  have hRint : Integrable (fun ω => ‖R ω‖) Q :=
    gaussian_max_abs_integrable (fun j ω => R ω j) hRlaw
  have hRnonneg : 0 ≤ᵐ[Q] fun ω => ‖R ω‖ := ae_of_all _ (fun _ => norm_nonneg _)
  have hRmarkov := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hRnonneg hRint ρ
  have hRbad : Q.real {ω | ρ ≤ ‖R ω‖} ≤ 1/2 := by
    have hdiv := div_le_div_of_nonneg_right
      (hRmarkov.trans (hexpect.trans hbudget)) hρ.le
    have hleft : (ρ * Q.real {ω | ρ ≤ ‖R ω‖}) / ρ =
        Q.real {ω | ρ ≤ ‖R ω‖} := by field_simp [ne_of_gt hρ]
    have hright : (ρ / 2) / ρ = 1 / 2 := by field_simp [ne_of_gt hρ]
    rw [hleft, hright] at hdiv
    exact hdiv
  have hRgoodReal : Q.real (R ⁻¹' residualSet) ≥ 1/2 := by
    have hRgood : R ⁻¹' residualSet = {ω | ‖R ω‖ ≤ ρ} := by
      ext ω
      simp only [residualSet, Set.mem_preimage, Set.mem_setOf_eq]
      rw [pi_norm_le_iff_of_nonneg hρ.le]
      simp [Real.norm_eq_abs]
    rw [hRgood]
    have hbadSub : {ω | ρ < ‖R ω‖} ⊆ {ω | ρ ≤ ‖R ω‖} := by
      intro ω hω
      change ρ < ‖R ω‖ at hω
      exact hω.le
    have hbad : Q.real {ω | ρ < ‖R ω‖} ≤ 1/2 :=
      (measureReal_mono hbadSub).trans hRbad
    have hleSet : MeasurableSet {ω : H | ‖R ω‖ ≤ ρ} :=
      measurableSet_le (measurable_norm.comp hRmeas) (measurable_const : Measurable fun _ : H => ρ)
    have hcomp := measureReal_add_measureReal_compl (μ := Q)
      (s := {ω : H | ‖R ω‖ ≤ ρ}) hleSet
    have huniv : Q.real Set.univ = 1 := by simp
    have hcomplSet : {ω : H | ‖R ω‖ ≤ ρ}ᶜ = {ω | ρ < ‖R ω‖} := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
    rw [hcomplSet] at hcomp
    rw [huniv] at hcomp
    linarith
  have hRgoodENN : (1/2:ENNReal) ≤ Q (R ⁻¹' residualSet) := by
    calc
      (1/2:ENNReal) = ENNReal.ofReal (1/2) := by
        calc
          (1/2:ENNReal) = ENNReal.ofReal 1 / ENNReal.ofReal 2 := by
            rw [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
          _ = ENNReal.ofReal (1/2:ℝ) := by
            rw [ENNReal.ofReal_div_of_pos (x := 1) (y := 2) (by norm_num)]
      _ ≤ ENNReal.ofReal (Q.real (R ⁻¹' residualSet)) := ENNReal.ofReal_le_ofReal hRgoodReal
      _ = Q (R ⁻¹' residualSet) := by
        rw [Measure.real_def]
        exact ENNReal.ofReal_toReal (measure_ne_top Q _)
  have hjoint := hresIndep.measure_inter_preimage_eq_mul
    mainSet residualSet hmainMeas hresMeas
  have hjointMass : ENNReal.ofReal (∏ i, a i) * ((1/2:ENNReal) * (1/2:ENNReal)) ≤
      Q (Z ⁻¹' mainSet ∩ R ⁻¹' residualSet) := by
    calc
      _ = (ENNReal.ofReal (∏ i, a i) * (1/2:ENNReal)) * (1/2:ENNReal) := by
        rw [mul_assoc]
      _ ≤ Q (Z ⁻¹' mainSet) * Q (R ⁻¹' residualSet) :=
        mul_le_mul hmainMass hRgoodENN (by positivity) (by positivity)
      _ = Q (Z ⁻¹' mainSet ∩ R ⁻¹' residualSet) := hjoint.symm
  letI : IsFiniteMeasure Q := inferInstance
  have hdecomp : ∀ j, (fun ω => W.eval (vb j) ω) =ᵐ[Q]
      (fun ω => (∑ i, ⟪eb i, vb j⟫ * W.eval (eb i) ω) + R ω j) := by
    intro j
    exact SheetProjection.eval_decomposition_ae W eb (vb j)
  have hdecompAll : ∀ᵐ ω ∂Q, ∀ j, W.eval (vb j) ω =
      (∑ i, ⟪eb i, vb j⟫ * W.eval (eb i) ω) + R ω j := by
    rw [ae_all_iff]
    intro j
    exact hdecomp j
  have hsubset : Z ⁻¹' mainSet ∩ R ⁻¹' residualSet ≤ᵐ[Q] modelVec ⁻¹' gridSet := by
    filter_upwards [hdecompAll] with ω hdec hω
    intro j
    have hmain : |∑ i, ⟪integerIntegratedKernelFeature m (x j), e i⟫ *
        W.eval (eb i) ω| ≤ ρ := by
      exact (hω.1 j)
    have hres : |R ω j| ≤ ρ := hω.2 j
    have hcoeff : ∀ i, ⟪eb i, vb j⟫ =
        ⟪integerIntegratedKernelFeature m (x j), e i⟫ := by
      intro i
      change ⟪(e i : CameronMartin.UnitCubeL2 d),
        (integerIntegratedKernelFeature m (x j) : CameronMartin.UnitCubeL2 d)⟫ =
          ⟪integerIntegratedKernelFeature m (x j), e i⟫
      exact real_inner_comm _ _
    have heq : (∑ i, ⟪eb i, vb j⟫ * W.eval (eb i) ω) =
        ∑ i, ⟪integerIntegratedKernelFeature m (x j), e i⟫ * W.eval (eb i) ω := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoeff i]
    have hval := hdec j
    rw [heq] at hval
    have hgrid : |W.eval (vb j) ω| ≤ 2 * ρ := by
      rw [hval]
      calc
          |(∑ i, ⟪integerIntegratedKernelFeature m (x j), e i⟫ *
            W.eval (eb i) ω) + R ω j| ≤
          |∑ i, ⟪integerIntegratedKernelFeature m (x j), e i⟫ * W.eval (eb i) ω| +
            |R ω j| := abs_add_le _ _
        _ ≤ ρ + ρ := add_le_add hmain hres
        _ = 2 * ρ := by ring
    simpa [modelVec, gridSet, gridVector] using hgrid
  have hmodelMass : ENNReal.ofReal (∏ i, a i) *
      ((1/2:ENNReal) * (1/2:ENNReal)) ≤ Q (modelVec ⁻¹' gridSet) :=
    hjointMass.trans (measure_mono_ae hsubset)
  have hPiActual : Measurable (fun ω j =>
      BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) (x j)) := by
    apply Measurable.of_eval
    intro j
    have hEval : Continuous (fun f : C(BrownianCubeAnchor d, ℝ) =>
        (BrownianSharp.AlignmentGaussianRates.integrateSheetPath m f) (x j)) := by
      have heval : Continuous (fun f : C(BrownianCubeAnchor d, ℝ) => f (x j)) := by
        exact ContinuousEval.continuous_eval.comp
          (continuous_id.prodMk continuous_const)
      exact heval.comp
        (BrownianSharp.AlignmentGaussianRates.integrateSheetPath_continuous m)
    exact hEval.measurable.comp B.measurable_path
  have hactualMeas : Measurable actualVec := by
    change Measurable (fun ω => (EuclideanSpace.equiv J ℝ).symm
      (fun j => BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) (x j)))
    exact (EuclideanSpace.equiv J ℝ).symm.continuous.measurable.comp hPiActual
  have hPiModel : Measurable (fun ω j => W.eval (vb j) ω) := by
    exact Measurable.of_eval (fun j => W.measurable_eval _)
  have hmodelMeas : Measurable modelVec := by
    change Measurable (fun ω => (EuclideanSpace.equiv J ℝ).symm
      (fun j => W.eval (vb j) ω))
    exact (EuclideanSpace.equiv J ℝ).symm.continuous.measurable.comp hPiModel
  have hLaw : Measure.map actualVec P = Measure.map modelVec Q := by
    convert hlaw using 1 <;> congr 1 <;> funext ω j <;> rfl
  have hprob : P (actualVec ⁻¹' gridSet) = Q (modelVec ⁻¹' gridSet) := by
    rw [← Measure.map_apply hactualMeas hgridMeas, hLaw,
      Measure.map_apply hmodelMeas hgridMeas]
  simpa [actualVec, gridSet, gridVector] using hmodelMass.trans_eq hprob.symm

end BrownianSharp.AlignmentGaussianIntegratedFiniteGridConfinement
