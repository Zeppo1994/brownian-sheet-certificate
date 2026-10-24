import BrownianSharp.AlignmentGaussianFiniteSourceModel
import BrownianSharp.AlignmentExponentialDiagonalDilation
import BrownianSharp.AlignmentExponentialGaussianMaximum
import BrownianSharp.GaussianGridStatistics
import BrownianSharp.SheetProjection
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Tactic

/-! Finite-grid confinement for any centered finite Gaussian feature field. The
finite-grid law is assumed to have the Gram covariance of vectors in a real
Hilbert space; selected orthonormal source coordinates split off an independent
residual. No process-specific covariance representation is assumed here. -/
noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators RealInnerProductSpace ENNReal

namespace BrownianSharp.AlignmentGaussianFiniteGridConfinement

open AlignmentGaussianFiniteSourceModel
open AlignmentExponentialDiagonalDilation
open AlignmentExponentialGaussianMaximum
open GaussianProjection
open HaarQuarter

private def gridVector {Ω J : Type*} [Fintype J]
    (X : Ω → J → ℝ) (ω : Ω) : EuclideanSpace ℝ J :=
  WithLp.toLp 2 (fun j => X ω j)

/-- A centered finite Gaussian feature field has a quantitative finite-grid
small-ball lower bound once the scaled projected field has half-mass and the
orthogonal residual has sufficiently small expected grid maximum. The law,
mean, and covariance hypotheses are explicit in the statement. -/
theorem finiteGrid_confinement_of_main_half_mass
    {Ω I J H : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [Nonempty I] [Fintype J] [Nonempty J]
    {P : Measure Ω} [IsProbabilityMeasure P]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Ω → J → ℝ) (e : I → H) (v : J → H)
    (hX : HasGaussianLaw (fun ω j => X ω j) P)
    (hmean : ∀ j, ∫ ω, X ω j ∂P = 0)
    (hcov : ∀ i j, covariance (fun ω => X ω i) (fun ω => X ω j) P = ⟪v i, v j⟫)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0)
    (a : I → ℝ) (ρ τ : ℝ) (hρ : 0 < ρ) (hτ : 0 ≤ τ)
    (ha : ∀ i, 0 < a i) (ha1 : ∀ i, a i ≤ 1)
    (hscaled : (1/2:ENNReal) ≤ productStandardGaussian I
      {z | ∀ j, |∑ i, ⟪v j, e i⟫ * (a i * z i)| ≤ ρ})
    (hres : ∀ j, ‖v j - projection e (v j)‖ ≤ τ)
    (hbudget : 2 * τ * Real.sqrt (Real.log (2 * (Fintype.card J : ℝ) + 2)) ≤ ρ / 2) :
    ENNReal.ofReal (∏ i, a i) * ((1/2:ENNReal) * (1/2:ENNReal)) ≤
      P {ω | ∀ j, |X ω j| ≤ 2 * ρ} := by
  classical
  obtain ⟨W, hlaw, hindep, hmarg, hresIndep⟩ :=
    exists_finiteFeatureSourceModel X e v hX hmean hcov he
  let S := finiteFeatureSpan (Sum.elim e v)
  let Q : Measure S := stdGaussian S
  let eb : I → S := fun i => ⟨e i, Submodule.subset_span ⟨Sum.inl i, rfl⟩⟩
  let vb : J → S := fun j => ⟨v j, Submodule.subset_span ⟨Sum.inr j, rfl⟩⟩
  let Z : S → I → ℝ := fun ω i => W.eval (eb i) ω
  let R : S → J → ℝ := fun ω j =>
    W.eval (vb j - projection eb (vb j)) ω
  let mainSet : Set (I → ℝ) := {z | ∀ j,
    |∑ i, ⟪v j, e i⟫ * z i| ≤ ρ}
  let scaledSet : Set (I → ℝ) := {z | ∀ j,
    |∑ i, ⟪v j, e i⟫ * (a i * z i)| ≤ ρ}
  let residualSet : Set (J → ℝ) := {z | ∀ j, |z j| ≤ ρ}
  let actualVec : Ω → EuclideanSpace ℝ J := gridVector X
  let modelVec : S → EuclideanSpace ℝ J := gridVector (fun ω j => W.eval (vb j) ω)
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
      (gaussianReal 0 (‖v j - projection e (v j)‖ ^ 2).toNNReal) Q := by
    let r : S := vb j - projection eb (vb j)
    let idx : Sum I J := Sum.inl (Classical.choice ‹Nonempty I›)
    have hcoord := W.coordinate_law (fun _ : Sum I J => r) idx
    have hproj : ((projection eb (vb j) : S) : H) = projection e (v j) := by
      simp [GaussianProjection.projection, eb, vb, real_inner_comm]
    have hrvec : (r : H) = v j - projection e (v j) := by
      change (vb j : H) - ((projection eb (vb j) : S) : H) = _
      rw [hproj]
    have hnorm : ⟪r, r⟫ = ‖v j - projection e (v j)‖ ^ 2 := by
      calc
        ⟪r, r⟫ = ‖r‖ ^ 2 := real_inner_self_eq_norm_sq r
        _ = ‖(r : H)‖ ^ 2 := by rfl
        _ = _ := by rw [hrvec]
    refine ⟨(W.measurable_eval r).aemeasurable, ?_⟩
    change Q.map (fun ω => W.eval r ω) =
      gaussianReal 0 (‖v j - projection e (v j)‖ ^ 2).toNNReal
    rw [← hnorm]
    simpa [r] using hcoord
  have hvar : ∀ j, ((‖v j -
      projection e (v j)‖ ^ 2).toNNReal : ℝ) ≤ τ ^ 2 := by
    intro j
    have h := hres j
    have hsquare : ‖v j -
        projection e (v j)‖ ^ 2 ≤ τ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hτ).2 h
    have hnn := Real.toNNReal_le_toNNReal hsquare
    calc
      ↑(‖v j -
          projection e (v j)‖ ^ 2).toNNReal ≤
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
    have hleSet : MeasurableSet {ω : S | ‖R ω‖ ≤ ρ} :=
      measurableSet_le (measurable_norm.comp hRmeas) (measurable_const : Measurable fun _ : S => ρ)
    have hcomp := measureReal_add_measureReal_compl (μ := Q)
      (s := {ω : S | ‖R ω‖ ≤ ρ}) hleSet
    have huniv : Q.real Set.univ = 1 := by simp
    have hcomplSet : {ω : S | ‖R ω‖ ≤ ρ}ᶜ = {ω | ρ < ‖R ω‖} := by
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
    have hmain : |∑ i, ⟪v j, e i⟫ *
        W.eval (eb i) ω| ≤ ρ := by
      exact (hω.1 j)
    have hres : |R ω j| ≤ ρ := hω.2 j
    have hcoeff : ∀ i, ⟪eb i, vb j⟫ =
        ⟪v j, e i⟫ := by
      intro i
      change ⟪(e i : H), (v j : H)⟫ = ⟪v j, e i⟫
      exact real_inner_comm _ _
    have heq : (∑ i, ⟪eb i, vb j⟫ * W.eval (eb i) ω) =
        ∑ i, ⟪v j, e i⟫ * W.eval (eb i) ω := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcoeff i]
    have hval := hdec j
    rw [heq] at hval
    have hgrid : |W.eval (vb j) ω| ≤ 2 * ρ := by
      rw [hval]
      calc
          |(∑ i, ⟪v j, e i⟫ *
            W.eval (eb i) ω) + R ω j| ≤
          |∑ i, ⟪v j, e i⟫ * W.eval (eb i) ω| +
            |R ω j| := abs_add_le _ _
        _ ≤ ρ + ρ := add_le_add hmain hres
        _ = 2 * ρ := by ring
    simpa [modelVec, gridSet, gridVector] using hgrid
  have hmodelMass : ENNReal.ofReal (∏ i, a i) *
      ((1/2:ENNReal) * (1/2:ENNReal)) ≤ Q (modelVec ⁻¹' gridSet) :=
    hjointMass.trans (measure_mono_ae hsubset)
  have hLaw : Measure.map actualVec P = Measure.map modelVec Q := by
    convert hlaw using 1 <;> congr 1 <;> funext ω j <;> rfl
  have hactualVecAE : AEMeasurable actualVec P := by
    change AEMeasurable ((EuclideanSpace.equiv J ℝ).symm ∘ (fun ω j => X ω j)) P
    exact ((EuclideanSpace.equiv J ℝ).symm.continuous.measurable.aemeasurable
      (μ := P.map (fun ω j => X ω j))).comp_aemeasurable hX.aemeasurable
  have hPiModel : Measurable (fun ω j => W.eval (vb j) ω) := by
    exact Measurable.of_eval (fun j => W.measurable_eval _)
  have hmodelMeas : Measurable modelVec := by
    change Measurable (fun ω => (EuclideanSpace.equiv J ℝ).symm
      (fun j => W.eval (vb j) ω))
    exact (EuclideanSpace.equiv J ℝ).symm.continuous.measurable.comp hPiModel
  have hprob : P (actualVec ⁻¹' gridSet) = Q (modelVec ⁻¹' gridSet) := by
    rw [← Measure.map_apply_of_aemeasurable hactualVecAE hgridMeas, hLaw,
      Measure.map_apply hmodelMeas hgridMeas]
  simpa [actualVec, gridSet, gridVector] using hmodelMass.trans_eq hprob.symm

end BrownianSharp.AlignmentGaussianFiniteGridConfinement
