import BrownianSharp.BrownianHaarCovariance
import BrownianSharp.GaussianProjection
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Tactic

/-! Generic finite Gaussian source model.  Unlike the integrated-sheet adapter,
this file is independent of any particular feature map or ambient source
space. -/

noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace HaarQuarter
open BrownianSharp.GaussianProjection
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentGaussianFiniteSourceModel

def finiteFeatureSpan {H κ : Type*} [Fintype κ]
    [AddCommGroup H] [Module ℝ H] (v : κ → H) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range v)

private instance finiteFeatureSpan_finiteDimensional {H κ : Type*} [Fintype κ]
    [AddCommGroup H] [Module ℝ H] (v : κ → H) :
    FiniteDimensional ℝ (finiteFeatureSpan v) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range v)

private instance finiteFeatureSpan_measurableSpace {H κ : Type*} [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (v : κ → H) :
    MeasurableSpace (finiteFeatureSpan v) := borel (finiteFeatureSpan v)

private instance finiteFeatureSpan_borelSpace {H κ : Type*} [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (v : κ → H) :
    BorelSpace (finiteFeatureSpan v) := ⟨rfl⟩

private def innerCoordinates {E κ : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fintype κ] (v : κ → E) : E →L[ℝ] (κ → ℝ) :=
  ContinuousLinearMap.pi fun i => innerSL ℝ (v i)

private def finiteFeatureIsonormal {H κ : Type*} [Fintype κ]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : κ → H) : IsonormalGaussianFamily (finiteFeatureSpan v)
      (finiteFeatureSpan v) κ (stdGaussian (finiteFeatureSpan v)) := by
  let S := finiteFeatureSpan v
  refine {
    eval := fun f ω => ⟪f, ω⟫
    jointlyGaussian := ?_
    measurable_eval := ?_
    mean_zero := ?_
    covariance_eq_inner := ?_ }
  · intro w
    let L : S →L[ℝ] (κ → ℝ) := innerCoordinates w
    have hbase : HasGaussianLaw id (stdGaussian S) :=
      ProbabilityTheory.IsGaussian.hasGaussianLaw_id
    have hmap := hbase.map L
    have heq : (fun ω i => ⟪w i, ω⟫) = L := by
      funext ω i
      rfl
    rw [heq]
    exact hmap
  · intro f
    exact (innerSL ℝ f).continuous.measurable
  · intro f
    let L : S →L[ℝ] ℝ := innerSL ℝ f
    have hidmem : MemLp (id : S → S) 2 (stdGaussian S) :=
      (ProbabilityTheory.IsGaussian.hasGaussianLaw_id
        (μ := stdGaussian S)).memLp_two
    have hid : Integrable (fun x : S => x) (stdGaussian S) :=
      hidmem.integrable (by norm_num)
    have h := L.integral_comp_comm hid
    rw [ProbabilityTheory.integral_id_stdGaussian] at h
    simpa [L] using h
  · intro f g
    have hid : MemLp (id : S → S) 2 (stdGaussian S) :=
      (ProbabilityTheory.IsGaussian.hasGaussianLaw_id
        (μ := stdGaussian S)).memLp_two
    have hcov := ProbabilityTheory.covarianceBilin_apply_eq_cov hid f g
    rw [ProbabilityTheory.covarianceBilin_stdGaussian] at hcov
    exact hcov.symm

private def piToEuclidean {J : Type*} [Fintype J] :
    (J → ℝ) →L[ℝ] EuclideanSpace ℝ J :=
  (EuclideanSpace.equiv J ℝ).symm.toContinuousLinearMap

def gridVector {Ω J : Type*} [Fintype J] (X : Ω → J → ℝ) (ω : Ω) :
    EuclideanSpace ℝ J := WithLp.toLp 2 (fun j => X ω j)

/-- A finite Gaussian coordinate family is realized on the finite span of its
source frame and feature vectors whenever its means vanish and its covariance
matrix is the Gram matrix of those features.  The source coordinates are
independent standard normals, and independent of each feature's orthogonal
residual. -/
theorem exists_finiteFeatureSourceModel
    {Ω I J H : Type*} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [Nonempty I] [Fintype J]
    {P : Measure Ω} [IsProbabilityMeasure P]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (X : Ω → J → ℝ) (e : I → H) (v : J → H)
    (hX : HasGaussianLaw (fun ω j => X ω j) P)
    (hmean : ∀ j, ∫ ω, X ω j ∂P = 0)
    (hcov : ∀ i j, covariance (fun ω => X ω i) (fun ω => X ω j) P = ⟪v i, v j⟫)
    (he : ∀ i j, ⟪e i, e j⟫ = if i = j then 1 else 0) :
    ∃ W : IsonormalGaussianFamily
      (finiteFeatureSpan (Sum.elim e v))
      (finiteFeatureSpan (Sum.elim e v)) (Sum I J)
      (stdGaussian (finiteFeatureSpan (Sum.elim e v))),
      Measure.map (gridVector X) P =
        Measure.map (gridVector (fun ω j => W.eval
          (⟨v j, Submodule.subset_span ⟨Sum.inr j, rfl⟩⟩ :
            finiteFeatureSpan (Sum.elim e v)) ω))
          (stdGaussian (finiteFeatureSpan (Sum.elim e v))) ∧
      iIndepFun (fun i ω => W.eval
        (⟨e i, Submodule.subset_span ⟨Sum.inl i, rfl⟩⟩ :
          finiteFeatureSpan (Sum.elim e v)) ω)
        (stdGaussian (finiteFeatureSpan (Sum.elim e v))) ∧
      (∀ i, (stdGaussian (finiteFeatureSpan (Sum.elim e v))).map
        (W.eval (⟨e i, Submodule.subset_span ⟨Sum.inl i, rfl⟩⟩ :
          finiteFeatureSpan (Sum.elim e v))) = gaussianReal 0 1) ∧
      IndepFun
        (fun ω i => W.eval
          (⟨e i, Submodule.subset_span ⟨Sum.inl i, rfl⟩⟩ :
            finiteFeatureSpan (Sum.elim e v)) ω)
        (fun ω j => W.eval
          ((⟨v j, Submodule.subset_span ⟨Sum.inr j, rfl⟩⟩ :
            finiteFeatureSpan (Sum.elim e v)) -
          projection
            (fun i => (⟨e i, Submodule.subset_span ⟨Sum.inl i, rfl⟩⟩ :
              finiteFeatureSpan (Sum.elim e v)))
            (⟨v j, Submodule.subset_span ⟨Sum.inr j, rfl⟩⟩ :
              finiteFeatureSpan (Sum.elim e v))) ω)
        (stdGaussian (finiteFeatureSpan (Sum.elim e v))) := by
  classical
  let S := finiteFeatureSpan (Sum.elim e v)
  let Q : Measure S := stdGaussian S
  let W := finiteFeatureIsonormal (Sum.elim e v)
  let eb : I → S := fun i =>
    ⟨e i, Submodule.subset_span ⟨Sum.inl i, rfl⟩⟩
  let vb : J → S := fun j =>
    ⟨v j, Submodule.subset_span ⟨Sum.inr j, rfl⟩⟩
  have heb : ∀ i j, ⟪eb i, eb j⟫ = if i = j then 1 else 0 := by
    intro i j
    exact he i j
  have hmodelPi : HasGaussianLaw (fun ω j => ⟪vb j, ω⟫) Q := by
    let L : S →L[ℝ] (J → ℝ) := innerCoordinates vb
    have hbase : HasGaussianLaw id (stdGaussian S) :=
      ProbabilityTheory.IsGaussian.hasGaussianLaw_id
    have h := hbase.map L
    change HasGaussianLaw (fun ω j => ⟪vb j, ω⟫) (stdGaussian S)
    exact h
  let μA := Measure.map (gridVector X) P
  let μM := Measure.map (gridVector (fun ω j => W.eval (vb j) ω)) Q
  have hactual : HasGaussianLaw (gridVector X) P := hX.map piToEuclidean
  have hmodel : HasGaussianLaw (gridVector (fun ω j => W.eval (vb j) ω)) Q :=
    hmodelPi.map piToEuclidean
  have hAis : IsGaussian μA := hactual.isGaussian_map
  have hMis : IsGaussian μM := hmodel.isGaussian_map
  have hAcoord : ∀ j, MemLp (fun ω => X ω j) 2 P := by
    intro j
    exact (hX.eval j).memLp_two
  have hMcoord : ∀ j, MemLp (fun ω => W.eval (vb j) ω) 2 Q := by
    intro j
    change MemLp (fun ω => ⟪vb j, ω⟫) 2 Q
    exact (hmodelPi.eval j).memLp_two
  have hIntA : Integrable (fun ω j => X ω j) P :=
    integrable_pi_iff.mpr (fun j => (hAcoord j).integrable (by norm_num))
  have hIntM : Integrable (fun ω j => W.eval (vb j) ω) Q :=
    integrable_pi_iff.mpr (fun j => (hMcoord j).integrable (by norm_num))
  have hIntEquivA : Integrable (fun ω => (EuclideanSpace.equiv J ℝ)
      (gridVector X ω)) P := by
    apply integrable_pi_iff.mpr
    intro j
    simpa [gridVector] using (hAcoord j).integrable (by norm_num)
  have hIntEquivM : Integrable (fun ω => (EuclideanSpace.equiv J ℝ)
      (gridVector (fun ω j => W.eval (vb j) ω) ω)) Q := by
    apply integrable_pi_iff.mpr
    intro j
    simpa [gridVector] using (hMcoord j).integrable (by norm_num)
  have hmeanA : ∫ z : EuclideanSpace ℝ J, z ∂μA = 0 := by
    apply (EuclideanSpace.equiv J ℝ).injective
    have hcomp := (EuclideanSpace.equiv J ℝ).toContinuousLinearMap.integral_comp_comm
      (IsGaussian.integrable_id (μ := μA))
    calc
      (EuclideanSpace.equiv J ℝ) (∫ z, z ∂μA) = ∫ z, (EuclideanSpace.equiv J ℝ) z ∂μA :=
        hcomp.symm
      _ = ∫ ω, (EuclideanSpace.equiv J ℝ) (gridVector X ω) ∂P :=
        MeasureTheory.integral_map hactual.aemeasurable (by fun_prop)
      _ = 0 := by
        ext j
        let q : (J → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
        have hproj := q.integral_comp_comm hIntEquivA
        calc
          (∫ ω, (EuclideanSpace.equiv J ℝ) (gridVector X ω) ∂P) j =
              q (∫ ω, (EuclideanSpace.equiv J ℝ) (gridVector X ω) ∂P) := rfl
          _ = ∫ ω, q ((EuclideanSpace.equiv J ℝ) (gridVector X ω)) ∂P := hproj.symm
          _ = ∫ ω, X ω j ∂P := by congr 1 <;> simp [q, gridVector]
          _ = 0 := hmean j
  have hmeanM : ∫ z : EuclideanSpace ℝ J, z ∂μM = 0 := by
    apply (EuclideanSpace.equiv J ℝ).injective
    have hcomp := (EuclideanSpace.equiv J ℝ).toContinuousLinearMap.integral_comp_comm
      (IsGaussian.integrable_id (μ := μM))
    calc
      (EuclideanSpace.equiv J ℝ) (∫ z, z ∂μM) = ∫ z, (EuclideanSpace.equiv J ℝ) z ∂μM :=
        hcomp.symm
      _ = ∫ ω, (EuclideanSpace.equiv J ℝ)
          (gridVector (fun ω j => W.eval (vb j) ω) ω) ∂Q :=
        MeasureTheory.integral_map hmodel.aemeasurable (by fun_prop)
      _ = 0 := by
        ext j
        let q : (J → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
        have hproj := q.integral_comp_comm hIntEquivM
        calc
          (∫ ω, (EuclideanSpace.equiv J ℝ)
              (gridVector (fun ω j => W.eval (vb j) ω) ω) ∂Q) j =
              q (∫ ω, (EuclideanSpace.equiv J ℝ)
                (gridVector (fun ω j => W.eval (vb j) ω) ω) ∂Q) := rfl
          _ = ∫ ω, q ((EuclideanSpace.equiv J ℝ)
              (gridVector (fun ω j => W.eval (vb j) ω) ω)) ∂Q := hproj.symm
          _ = ∫ ω, W.eval (vb j) ω ∂Q := by congr 1 <;> simp [q, gridVector]
          _ = 0 := W.mean_zero _
  have hmodelcov (i j : J) :
      covariance (fun ω => W.eval (vb i) ω) (fun ω => W.eval (vb j) ω) Q =
        ⟪v i, v j⟫ := by
    rw [W.covariance_eq_inner]
    rfl
  have hcovBilin : covarianceBilin μA = covarianceBilin μM := by
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun J ℝ).toBasis
      fun i j => ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply]
    change covarianceBilin (Measure.map (fun ω => WithLp.toLp 2 fun j => X ω j) P) _ _ =
      covarianceBilin (Measure.map
        (fun ω => WithLp.toLp 2 fun j => W.eval (vb j) ω) Q) _ _
    rw [covarianceBilin_apply_pi hAcoord, covarianceBilin_apply_pi hMcoord]
    simp_rw [hcov, hmodelcov]
  have hμeq : μA = μM :=
    IsGaussian.ext (by simpa using hmeanA.trans hmeanM.symm) hcovBilin
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · exact hμeq
  · exact coefficients_independent W eb vb heb
  · intro i
    exact coefficient_standard_normal W eb vb heb i
  · exact coefficients_residual_independent W eb vb heb

end BrownianSharp.AlignmentGaussianFiniteSourceModel
