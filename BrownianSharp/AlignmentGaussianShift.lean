import BrownianSharp.AlignmentGaussianBochner
import BrownianSharp.AlignmentAuditGaussianShift
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace
open HaarQuarter
open BrownianSharp.AlignmentGaussianBochner
open BrownianSharp.CameronMartin

namespace BrownianSharp.AlignmentGaussianShift

noncomputable section

/-! Finite evaluation events inherit the Cameron--Martin lower shift bound
from the actual isonormal feature realization. -/

private def featureSynthesis {H κ η : Type*} [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : κ → H) (f : η → H) (z : κ → ℝ) : η → ℝ :=
  fun j => ∑ i, ⟪b i, f j⟫ * z i

theorem isonormal_finite_feature_shift_lower
    {H Ω κ η : Type*} [Fintype κ] [Fintype η]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (W : IsonormalGaussianFamily H Ω κ P)
    (T : H →ₗᵢ[ℝ] Lp ℝ 2 P)
    (hWT : ∀ v, W.eval v =ᵐ[P] fun ω => T v ω)
    (b : κ → H) (hb : Orthonormal ℝ b) (f : η → H)
    (hf : ∀ j, f j = ∑ i, ⟪b i, f j⟫ • b i)
    (g : H) (ε : ℝ) :
    P {ω | ∀ j, |W.eval (f j) ω - ⟪f j, g⟫| ≤ ε} ≥
      ENNReal.ofReal (Real.exp (-‖g‖ ^ 2 / 2)) *
        P {ω | ∀ j, |W.eval (f j) ω| ≤ ε} := by
  classical
  let Z : Ω → κ → ℝ := fun ω i => W.eval (b i) ω
  let L : (κ → ℝ) → η → ℝ := featureSynthesis b f
  let h : κ → ℝ := fun i => ⟪b i, g⟫
  let A : Set (κ → ℝ) := {z | ∀ j, |L z j| ≤ ε}
  have horth : ∀ i j, i ≠ j → ⟪b i, b j⟫ = 0 := by
    intro i j hij
    exact hb.inner_eq_zero hij
  have hIndep₀ : iIndepFun (fun i ω => (1 : ℝ) * W.eval (b i) ω) P :=
    W.iIndepFun_of_orthogonal b (fun _ => 1) horth
  have hIndep : iIndepFun (fun i ω => W.eval (b i) ω) P := by
    simpa using hIndep₀
  have hZmeas : Measurable Z := by
    exact measurable_pi_iff.mpr (fun i => W.measurable_eval (b i))
  have hZlaw : P.map Z = BrownianSharp.productStandardGaussian κ := by
    have hindep := hIndep.map_fun_eq_pi_map
      (fun i => (W.measurable_eval (b i)).aemeasurable)
    rw [hindep]
    have hcoord (i : κ) : P.map (fun ω => W.eval (b i) ω) = gaussianReal 0 1 := by
      rw [W.coordinate_law]
      have hi : ⟪b i, b i⟫ = 1 := by
        rw [real_inner_self_eq_norm_sq, hb.norm_eq_one i]
        norm_num
      rw [hi]
      norm_num
    simpa [BrownianSharp.productStandardGaussian, hcoord] using hindep
  have hLmeas : Measurable L := by
    apply measurable_pi_iff.mpr
    intro j
    dsimp [L, featureSynthesis]
    change Measurable (fun z : κ → ℝ => ∑ i, ⟪b i, f j⟫ * z i)
    fun_prop
  have hAmeas : MeasurableSet A := by
    rw [show A = ⋂ j, {z | |L z j| ≤ ε} by
      ext z
      simp [A]]
    exact MeasurableSet.iInter fun j => by
      change MeasurableSet {z : κ → ℝ | |L z j| ≤ ε}
      exact isClosed_Iic.measurableSet.preimage
        (continuous_abs.measurable.comp ((measurable_pi_apply j).comp hLmeas))
  have hAsymm : ∀ z, z ∈ A ↔ -z ∈ A := by
    intro z
    simp only [A, Set.mem_setOf_eq]
    constructor <;> intro hz j
    · simpa [L, featureSynthesis, Pi.neg_apply, Finset.mul_sum] using hz j
    · simpa [L, featureSynthesis, Pi.neg_apply, Finset.mul_sum] using hz j
  have henergy : ∑ i, h i ^ 2 ≤ ‖g‖ ^ 2 := by
    simpa [h, real_inner_comm] using
      (hb.sum_inner_products_le (s := Finset.univ) g)
  have hshiftEval (j : η) (z : κ → ℝ) :
      L (z + h) j = L z j + ⟪f j, g⟫ := by
    have hp : ∑ i, ⟪b i, f j⟫ * h i = ⟪f j, g⟫ := by
      have hp0 := congrArg (fun v : H => ⟪v, g⟫) (hf j)
      simp only [sum_inner, real_inner_smul_left] at hp0
      simpa [h] using hp0.symm
    calc
      L (z + h) j = ∑ i, ⟪b i, f j⟫ * ((z + h) i) := rfl
      _ = (∑ i, ⟪b i, f j⟫ * z i) + (∑ i, ⟪b i, f j⟫ * h i) := by
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      _ = L z j + ⟪f j, g⟫ := by rw [hp]; rfl
  have hfeval : ∀ j, (fun ω => W.eval (f j) ω) =ᵐ[P] fun ω => L (Z ω) j := by
    intro j
    have hLp : T (f j) = ∑ i, ⟪b i, f j⟫ • T (b i) := by
      calc
        T (f j) = T (∑ i, ⟪b i, f j⟫ • b i) := congrArg T (hf j)
        _ = ∑ i, T (⟪b i, f j⟫ • b i) := map_sum T _ _
        _ = ∑ i, ⟪b i, f j⟫ • T (b i) := by simp [map_smul]
    have hLpAE := Lp.ext_iff.mp hLp
    have hcoords : (fun ω => T (f j) ω) =ᵐ[P] fun ω => L (Z ω) j := by
      have hsum := Lp.coeFn_finsetSum Finset.univ
        (fun i => ⟪b i, f j⟫ • T (b i))
      have hsmul := ae_all_iff.mpr
        (fun i => Lp.coeFn_smul (⟪b i, f j⟫) (T (b i)))
      have hall := ae_all_iff.mpr (fun i => hWT (b i))
      filter_upwards [hLpAE, hsum, hsmul, hall] with ω hω hsumω hsmulω hcoordsω
      have hsum' : (∑ i, ⟪b i, f j⟫ • T (b i)) ω =
          ∑ i, ⟪b i, f j⟫ * W.eval (b i) ω := by
        rw [hsumω]
        rw [Finset.sum_apply]
        change (∑ i, (⟪b i, f j⟫ • T (b i)) ω) = _
        apply Finset.sum_congr rfl
        intro i hi
        calc
          (⟪b i, f j⟫ • T (b i)) ω = ⟪b i, f j⟫ * T (b i) ω := by
            rw [hsmulω i]
            rfl
          _ = ⟪b i, f j⟫ * W.eval (b i) ω := by rw [← hcoordsω i]
      simpa [L, featureSynthesis, Z] using hω.trans hsum'
    exact (hWT (f j)).trans hcoords
  have hEcenter :
      {ω | ∀ j, |W.eval (f j) ω| ≤ ε} =ᵐ[P] Z ⁻¹' A := by
    have hall := ae_all_iff.mpr hfeval
    filter_upwards [hall] with ω heq
    simp only [Set.mem_setOf_eq, Set.mem_preimage, A]
    apply propext
    exact forall_congr' fun j => by rw [heq j]
  have hEshift :
      {ω | ∀ j, |W.eval (f j) ω - ⟪f j, g⟫| ≤ ε} =ᵐ[P]
        Z ⁻¹' ((fun z : κ → ℝ => z + h) '' A) := by
    have hall := ae_all_iff.mpr hfeval
    filter_upwards [hall] with ω heq
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_image]
    apply propext
    constructor
    · intro he
      refine ⟨Z ω - h, ?_, ?_⟩
      · intro j
        have hj := he j
        have hshift := hshiftEval j (Z ω - h)
        have hcancel : (Z ω - h) + h = Z ω := by ext i <;> simp
        rw [hcancel] at hshift
        have hL : L (Z ω - h) j = W.eval (f j) ω - ⟪f j, g⟫ := by
          have hh := hshift
          rw [← heq j] at hh
          linarith
        rw [hL]
        exact hj
      ext i
      simp
    · rintro ⟨z, hz, hzh⟩
      have hzj : ∀ j, |L z j| ≤ ε := hz
      have hZ : Z ω = z + h := hzh.symm
      intro j
      have heqj := heq j
      rw [heqj, hZ, hshiftEval]
      simpa using hzj j
  have hmass := BrownianSharp.AlignmentAuditGaussianShift.productGaussian_symmetric_translate_lower
    A hAmeas hAsymm h
  have hprobCenter :
      P {ω | ∀ j, |W.eval (f j) ω| ≤ ε} =
        BrownianSharp.productStandardGaussian κ A := by
    calc
      P {ω | ∀ j, |W.eval (f j) ω| ≤ ε} = P (Z ⁻¹' A) := measure_congr hEcenter
      _ = (P.map Z) A := (Measure.map_apply hZmeas hAmeas).symm
      _ = _ := congrArg (fun μ : Measure (κ → ℝ) => μ A) hZlaw
  have hprobShift :
      P {ω | ∀ j, |W.eval (f j) ω - ⟪f j, g⟫| ≤ ε} =
        BrownianSharp.productStandardGaussian κ ((fun z : κ → ℝ => z + h) '' A) := by
    have htrans : MeasurableSet ((fun z : κ → ℝ => z + h) '' A) :=
      (MeasurableEquiv.addRight h).measurableSet_image.mpr hAmeas
    calc
      P {ω | ∀ j, |W.eval (f j) ω - ⟪f j, g⟫| ≤ ε} =
          P (Z ⁻¹' ((fun z : κ → ℝ => z + h) '' A)) := measure_congr hEshift
      _ = (P.map Z) ((fun z : κ → ℝ => z + h) '' A) :=
        (Measure.map_apply hZmeas htrans).symm
      _ = _ := congrArg
        (fun μ : Measure (κ → ℝ) => μ ((fun z => z + h) '' A)) hZlaw
  have hexp :
      ENNReal.ofReal (Real.exp (-‖g‖ ^ 2 / 2)) ≤
        ENNReal.ofReal (Real.exp (-(∑ i, h i ^ 2) / 2)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [hprobShift, hprobCenter]
  calc
    BrownianSharp.productStandardGaussian κ ((fun z => z + h) '' A) ≥
        ENNReal.ofReal (Real.exp (-(∑ i, h i ^ 2) / 2)) *
          BrownianSharp.productStandardGaussian κ A := hmass
    _ ≥ ENNReal.ofReal (Real.exp (-‖g‖ ^ 2 / 2)) *
          BrownianSharp.productStandardGaussian κ A := by
      exact mul_le_mul_of_nonneg_right hexp (by positivity)

/-- The actual finite-grid shift inequality for an iterated integrated Brownian
sheet. The source is the genuine unit-cube Cameron--Martin function and the
deterministic shift is its actual tensor Riemann--Liouville image. -/
theorem integratedSheet_finiteGrid_shift_lower {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ)
    (g : CameronMartin.UnitCubeL2 d) (S : Finset (BrownianCubeAnchor d))
    (ε : ℝ) :
    P {ω | ∀ x ∈ S,
        |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x -
          BrownianSharp.Latest.fractionalIntegrationValue
            (fun i => (m i : ℝ) + 1) g x| ≤ ε} ≥
      ENNReal.ofReal (Real.exp (-‖g‖ ^ 2 / 2)) *
        P {ω | ∀ x ∈ S,
          |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x| ≤ ε} := by
  classical
  let I := {x : BrownianCubeAnchor d // x ∈ S}
  let f : I → brownianCubeBoxSpan d := fun x =>
    integratedFeatureField m x.1
  let V : Submodule ℝ (brownianCubeBoxSpan d) := Submodule.span ℝ (Set.range f)
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ (Set.finite_range f)
  let bV : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V := stdOrthonormalBasis ℝ V
  let b : Fin (Module.finrank ℝ V) → brownianCubeBoxSpan d := fun i => bV i
  have hb : Orthonormal ℝ b := by
    constructor
    · intro i
      change ‖bV i‖ = 1
      exact bV.orthonormal.1 i
    · intro i j hij
      change ⟪bV i, bV j⟫ = 0
      exact bV.orthonormal.2 hij
  have hf : ∀ j : I, f j = ∑ i, ⟪b i, f j⟫ • b i := by
    intro j
    let fV : V := ⟨f j, Submodule.subset_span (Set.mem_range_self j)⟩
    have hrepr := bV.sum_repr' fV
    apply Subtype.ext
    have hrepr' := congrArg (fun z : V => (z : brownianCubeBoxSpan d)) hrepr.symm
    have hbox : (f j : brownianCubeBoxSpan d) =
        ∑ i, ⟪(bV i : brownianCubeBoxSpan d), (f j : brownianCubeBoxSpan d)⟫ •
          (bV i : brownianCubeBoxSpan d) := by
      simpa [fV] using hrepr'
    exact congrArg (brownianCubeSpanEmbedding d) hbox
  obtain ⟨T, W, hT, hW⟩ := brownianSheetCube_exists_isonormal
    (ι := Fin (Module.finrank ℝ V)) B
  have hT_eval (z : BrownianCubeAnchor d) :
      brownianEvalToLp B z = T (featureVector z) := by
    rw [brownianEvalToLp_eq, ← hT z]
    apply congrArg T
    apply Subtype.ext
    rfl
  let X₀ : ContinuousIsonormalField P T := {
    path := B.path
    feature := ⟨featureVector, featureVector_continuous d⟩
    measurable_path := B.measurable_path
    eval_ae := by
      intro z
      have hmem : MemLp (B.eval z) 2 P := (B.eval_gaussian z).memLp_two
      have hrep : (fun ω => brownianEvalToLp B z ω) =ᵐ[P] B.eval z := by
        simpa [brownianEvalToLp] using hmem.coeFn_toLp
      have hclass : (fun ω => brownianEvalToLp B z ω) =ᵐ[P]
          fun ω => T (featureVector z) ω := by
        filter_upwards with ω
        exact congrArg (fun q : Lp ℝ 2 P => q ω) (hT_eval z)
      exact hrep.symm.trans hclass
    feature_norm_le_one := featureVector_norm_le_one
  }
  let X := integrateSheetIsonormalField m X₀
  have hpathAE (x : BrownianCubeAnchor d) :
      (fun ω => BrownianSharp.AlignmentGaussianRates.integrateSheetPath m
        (B.path ω) x) =ᵐ[P]
        fun ω => T (integratedFeatureField m x) ω := by
    have h := X.eval_ae x
    rw [integrateSheetIsonormalField_path] at h
    rw [integrateSheetIsonormalField_feature] at h
    simpa [X, X₀, integratedFeatureField, integrateSheetFeatureField] using h
  have hWT_feature (x : BrownianCubeAnchor d) :
      (fun ω => W.eval (integratedFeatureField m x) ω) =ᵐ[P]
        fun ω => T (integratedFeatureField m x) ω := hW _
  have hprocess (x : I) :
      (fun ω => BrownianSharp.AlignmentGaussianRates.integrateSheetPath m
        (B.path ω) x.1) =ᵐ[P]
        fun ω => W.eval (f x) ω := by
    exact (hpathAE x.1).trans (hWT_feature x.1).symm
  let source : CameronMartin.AmbientL2 d := CameronMartin.unitCubeZeroExtend g
  let pH : brownianCubeBoxSpan d :=
    (brownianCubeBoxSpan d).orthogonalProjectionOnto source
  let pV : V := V.orthogonalProjectionOnto pH
  have hpV (x : I) :
      ⟪f x, (pV : brownianCubeBoxSpan d)⟫ =
        BrownianSharp.Latest.fractionalIntegrationValue
          (fun i => (m i : ℝ) + 1) g x.1 := by
    have hprojV := V.inner_orthogonalProjectionOnto_eq_of_mem_left
      (⟨f x, Submodule.subset_span (Set.mem_range_self x)⟩ : V) pH
    have hprojH := (brownianCubeBoxSpan d).inner_orthogonalProjectionOnto_eq_of_mem_left
      (f x) source
    calc
      ⟪f x, (pV : brownianCubeBoxSpan d)⟫ = ⟪f x, pH⟫ := by
        change ⟪(⟨f x, Submodule.subset_span (Set.mem_range_self x)⟩ : V),
          V.orthogonalProjectionOnto pH⟫ = _
        exact hprojV
      _ = ⟪(f x : CameronMartin.AmbientL2 d), source⟫ := by
        change ⟪f x, pH⟫ = ⟪(f x : CameronMartin.AmbientL2 d), source⟫
        exact hprojH
      _ = ⟪brownianCubeSpanEmbedding d (f x), source⟫ := by rfl
      _ = BrownianSharp.Latest.fractionalIntegrationValue
          (fun i => (m i : ℝ) + 1) g x.1 := by
        change ⟪brownianCubeSpanEmbedding d (integratedFeatureField m x.1),
          unitCubeZeroExtendCLM d g⟫ = _
        exact integratedFeatureField_fractionalIntegrationValue m g x.1
  have hpVnorm : ‖(pV : brownianCubeBoxSpan d)‖ ≤ ‖g‖ := by
    calc
      ‖(pV : brownianCubeBoxSpan d)‖ = ‖pV‖ := rfl
      _ ≤ ‖pH‖ := V.norm_orthogonalProjectionOnto_apply_le pH
      _ ≤ ‖source‖ := (brownianCubeBoxSpan d).norm_orthogonalProjectionOnto_apply_le source
      _ = ‖g‖ := by
        change ‖CameronMartin.unitCubeZeroExtend g‖ = ‖g‖
        exact CameronMartin.unitCubeZeroExtend_norm g
  have hfinite := isonormal_finite_feature_shift_lower W T hW b hb f hf
    (pV : brownianCubeBoxSpan d) ε
  have hshiftedAE :
      {ω | ∀ x ∈ S,
          |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x -
            BrownianSharp.Latest.fractionalIntegrationValue
              (fun i => (m i : ℝ) + 1) g x| ≤ ε} =ᵐ[P]
        {ω | ∀ x : I,
          |W.eval (f x) ω - ⟪f x, (pV : brownianCubeBoxSpan d)⟫| ≤ ε} := by
    have hall := ae_all_iff.mpr (fun x : I => hprocess x)
    filter_upwards [hall] with ω hω
    apply propext
    constructor
    · intro hball x
      have hx := hball x.1 x.2
      change |W.eval (f x) ω - ⟪f x, (pV : brownianCubeBoxSpan d)⟫| ≤ ε
      rw [← hω x, hpV x]
      exact hx
    · intro hball x hx
      have hx' := hball ⟨x, hx⟩
      calc
        |(BrownianSharp.AlignmentGaussianRates.integrateSheetPath m
            (B.path ω)) x -
          BrownianSharp.Latest.fractionalIntegrationValue
            (fun i => (m i : ℝ) + 1) g x| =
            |W.eval (f ⟨x, hx⟩) ω - ⟪f ⟨x, hx⟩, (pV : brownianCubeBoxSpan d)⟫| := by
              rw [hω ⟨x, hx⟩, hpV ⟨x, hx⟩]
        _ ≤ ε := hx'
  have hcenterAE :
      {ω | ∀ x ∈ S,
          |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x| ≤ ε} =ᵐ[P]
        {ω | ∀ x : I, |W.eval (f x) ω| ≤ ε} := by
    have hall := ae_all_iff.mpr (fun x : I => hprocess x)
    filter_upwards [hall] with ω hω
    apply propext
    constructor
    · intro hball x
      change |W.eval (f x) ω| ≤ ε
      rw [← hω x]
      exact hball x.1 x.2
    · intro hball x hx
      have hx' := hball ⟨x, hx⟩
      calc
        |(BrownianSharp.AlignmentGaussianRates.integrateSheetPath m
            (B.path ω)) x| = |W.eval (f ⟨x, hx⟩) ω| := by
              rw [hω ⟨x, hx⟩]
        _ ≤ ε := hx'
  have hfinite' := hfinite
  have hnormExp : ENNReal.ofReal (Real.exp (-‖g‖ ^ 2 / 2)) ≤
      ENNReal.ofReal (Real.exp (-‖(pV : brownianCubeBoxSpan d)‖ ^ 2 / 2)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [hpVnorm, norm_nonneg (pV : brownianCubeBoxSpan d), norm_nonneg g]
  have hprobShiftEq :
      P {ω | ∀ x ∈ S,
          |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x -
            BrownianSharp.Latest.fractionalIntegrationValue
              (fun i => (m i : ℝ) + 1) g x| ≤ ε} =
        P {ω | ∀ x : I,
          |W.eval (f x) ω - ⟪f x, (pV : brownianCubeBoxSpan d)⟫| ≤ ε} :=
    measure_congr hshiftedAE
  have hprobCenterEq :
      P {ω | ∀ x ∈ S,
          |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x| ≤ ε} =
        P {ω | ∀ x : I, |W.eval (f x) ω| ≤ ε} := measure_congr hcenterAE
  rw [hprobShiftEq, hprobCenterEq]
  calc
    P {ω | ∀ x : I,
        |W.eval (f x) ω - ⟪f x, (pV : brownianCubeBoxSpan d)⟫| ≤ ε} ≥
      ENNReal.ofReal (Real.exp (-‖(pV : brownianCubeBoxSpan d)‖ ^ 2 / 2)) *
        P {ω | ∀ x : I, |W.eval (f x) ω| ≤ ε} := hfinite
    _ ≥ ENNReal.ofReal (Real.exp (-‖g‖ ^ 2 / 2)) *
        P {ω | ∀ x : I, |W.eval (f x) ω| ≤ ε} := by
      exact mul_le_mul_of_nonneg_right hnormExp (by positivity)

end

/-- The RL evaluation is linear in its source, inherited from the actual
bounded tensor Volterra operator. -/
theorem fractionalIntegrationValue_smul {d : ℕ} (a : Fin d → ℝ)
    (ha : ∀ i, 1/2 < a i) (c : ℝ) (g : CameronMartin.UnitCubeL2 d)
    (x : BrownianCubeAnchor d) :
    BrownianSharp.Latest.fractionalIntegrationValue a (c • g) x =
      c * BrownianSharp.Latest.fractionalIntegrationValue a g x := by
  rw [← BrownianSharp.AlignmentFractionalTensorOperator.fractionalTensorRL_apply a ha (c • g) x,
    ← BrownianSharp.AlignmentFractionalTensorOperator.fractionalTensorRL_apply a ha g x]
  change (BrownianSharp.AlignmentFractionalTensorOperator.fractionalTensorRL a ha (c • g)) x = _
  rw [map_smul]
  simp

/-- Finite-grid shift inequality for every radius multiple of a unit source.
The displayed center is exactly the scalar multiple of the actual RL image. -/
theorem integratedSheet_finiteGrid_shift_lower_scaled {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (B : BrownianSheetOnCube d Ω P) (m : Fin d → ℕ)
    (g : CameronMartin.UnitCubeL2 d) (hg : ‖g‖ ≤ 1)
    (S : Finset (BrownianCubeAnchor d)) (ε R : ℝ) (hR : 0 ≤ R) :
    P {ω | ∀ x ∈ S,
        |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x -
          R * BrownianSharp.Latest.fractionalIntegrationValue
            (fun i => (m i : ℝ) + 1) g x| ≤ ε} ≥
      ENNReal.ofReal (Real.exp (-R ^ 2 / 2)) *
        P {ω | ∀ x ∈ S,
          |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x| ≤ ε} := by
  have hnorm : ‖R • g‖ ≤ R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hR]
    simpa using mul_le_mul_of_nonneg_left hg hR
  have hbase := integratedSheet_finiteGrid_shift_lower B m (R • g) S ε
  have hfactor : ENNReal.ofReal (Real.exp (-R ^ 2 / 2)) ≤
      ENNReal.ofReal (Real.exp (-‖R • g‖ ^ 2 / 2)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    nlinarith [norm_nonneg (R • g), hnorm]
  have hcenter : ∀ x,
      BrownianSharp.Latest.fractionalIntegrationValue
        (fun i => (m i : ℝ) + 1) (R • g) x =
          R * BrownianSharp.Latest.fractionalIntegrationValue
            (fun i => (m i : ℝ) + 1) g x := by
    intro x
    exact fractionalIntegrationValue_smul _ (by intro i; nlinarith) R g x
  have hEq :
      {ω | ∀ x ∈ S,
        |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x -
          R * BrownianSharp.Latest.fractionalIntegrationValue
            (fun i => (m i : ℝ) + 1) g x| ≤ ε} =
      {ω | ∀ x ∈ S,
        |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x -
          BrownianSharp.Latest.fractionalIntegrationValue
            (fun i => (m i : ℝ) + 1) (R • g) x| ≤ ε} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    apply forall₂_congr
    intro x hx
    rw [hcenter]
  rw [hEq]
  calc
    P {ω | ∀ x ∈ S,
        |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x -
          BrownianSharp.Latest.fractionalIntegrationValue
            (fun i => (m i : ℝ) + 1) (R • g) x| ≤ ε} ≥
      ENNReal.ofReal (Real.exp (-‖R • g‖ ^ 2 / 2)) *
        P {ω | ∀ x ∈ S,
          |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x| ≤ ε} := hbase
    _ ≥ ENNReal.ofReal (Real.exp (-R ^ 2 / 2)) *
        P {ω | ∀ x ∈ S,
          |BrownianSharp.AlignmentGaussianRates.integrateSheetPath m (B.path ω) x| ≤ ε} :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)

end BrownianSharp.AlignmentGaussianShift
