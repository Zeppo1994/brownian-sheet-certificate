import BrownianSharp.AlignmentOrdinaryIntegrationLower
import BrownianSharp.AlignmentFractionalTensorOrthogonal
import BrownianSharp.AlignmentFractionalApproximationNumbers
import BrownianSharp.AlignmentOperatorKernelTrace
import BrownianSharp.LayerIndex
import BrownianSharp.PeriodicEntropy
import BrownianSharp.Interpolation
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 2000000
open MeasureTheory
open scoped BigOperators RealInnerProductSpace InnerProductSpace

namespace BrownianSharp.AlignmentOrdinaryTensorLower

open BrownianSharp
open BrownianSharp.AlignmentOrdinaryIntegrationLower
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentL2TensorProduct
open BrownianSharp.AlignmentOperatorKernelTrace
open BrownianSharp.CameronMartin
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalDensity
open BrownianSharp.AlignmentFractionalDensity
open HaarQuarter

def shiftedFrequency (r j : ℕ) : ℕ := 2^r + j

def layerFrequency {d n : ℕ} (a : LayerIndex d n) (i : Fin d) : ℕ :=
  shiftedFrequency (layerIndexDepth a i) (layerIndexCell a i)

def ordinaryTensorSource {d n : ℕ} (a : LayerIndex d n) : UnitCubeL2 d :=
  productToCube d (productVector (fun i => cosineSource (layerFrequency a i)))

def ordinaryTensorSourceFamily {d n : ℕ} : LayerIndex d n → UnitCubeL2 d :=
  ordinaryTensorSource

theorem shiftedFrequency_injective {r j s k : ℕ}
    (hj : j < 2^r) (hk : k < 2^s)
    (h : shiftedFrequency r j = shiftedFrequency s k) : r = s ∧ j = k := by
  dsimp [shiftedFrequency] at h
  have hpow_mono : ∀ {a b : ℕ}, a ≤ b → 2^a ≤ 2^b := by
    intro a b hab
    exact Nat.pow_le_pow_right (by omega) hab
  by_cases hrs : r < s
  · have hsmall : 2^r+j < 2^(r+1) := by
      calc
        2^r+j < 2^r+2^r := Nat.add_lt_add_left hj _
        _ = 2^(r+1) := by rw [pow_succ]; omega
    have hbig : 2^(r+1) ≤ 2^s := hpow_mono (by omega)
    omega
  · by_cases hrs' : s < r
    · have hsmall : 2^s+k < 2^(s+1) := by
        calc
          2^s+k < 2^s+2^s := Nat.add_lt_add_left hk _
          _ = 2^(s+1) := by rw [pow_succ]; omega
      have hbig : 2^(s+1) ≤ 2^r := hpow_mono (by omega)
      omega
    · have : r=s := by omega
      subst s
      have : j = k := by omega
      exact ⟨rfl, this⟩

theorem layerFrequency_injective {d n : ℕ} :
    Function.Injective (fun a : LayerIndex d n => layerFrequency a) := by
  intro a b hab
  have hp (i : Fin d) :
      (layerIndexDepth a i, layerIndexCell a i) =
        (layerIndexDepth b i, layerIndexCell b i) :=
    Prod.ext (shiftedFrequency_injective (layerIndexCell_lt a i)
      (layerIndexCell_lt b i) (congrFun hab i)).1
      (shiftedFrequency_injective (layerIndexCell_lt a i)
        (layerIndexCell_lt b i) (congrFun hab i)).2
  have hdepth : layerIndexDepth a = layerIndexDepth b := by
    funext i
    exact congrArg Prod.fst (hp i)
  have hcell : layerIndexCell a = layerIndexCell b := by
    funext i
    exact congrArg Prod.snd (hp i)
  cases a with
  | mk ra ca =>
    cases b with
    | mk rb cb =>
      simp only [layerIndexDepth, layerIndexCell] at hdepth hcell
      have hra : ra.1 = rb.1 := by
        apply Finsupp.ext
        intro i
        exact congrFun hdepth i
      have hra' : ra = rb := Subtype.ext hra
      subst rb
      have hc : ca = cb := by
        funext i
        apply Fin.ext
        exact congrFun hcell i
      subst cb
      rfl

theorem ordinaryTensorSource_inner {d n : ℕ} (a b : LayerIndex d n) :
    ⟪ordinaryTensorSource a, ordinaryTensorSource b⟫ =
      ∏ i : Fin d, ⟪cosineSource (layerFrequency a i),
        cosineSource (layerFrequency b i)⟫ := by
  classical
  let va : Fin d → UnitL2 := fun i => cosineSource (layerFrequency a i)
  let vb : Fin d → UnitL2 := fun i => cosineSource (layerFrequency b i)
  have haeA : productToCube d (productVector va) =ᵐ[
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet d)] (fun u => ∏ i, va i (u i)) := by
    have hp := productVector_ae va
    have hp' : productVector va =ᵐ[
        (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
          (CameronMartin.unitCubeSet d)] (fun u => ∏ i, va i (u i)) := by
      simpa only [AlignmentFractionalTensor.unitCube_measure_eq_pi] using hp
    exact (productToCube_ae (productVector va)).trans hp'
  have haeB : productToCube d (productVector vb) =ᵐ[
      (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet d)] (fun u => ∏ i, vb i (u i)) := by
    have hp := productVector_ae vb
    have hp' : productVector vb =ᵐ[
        (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
          (CameronMartin.unitCubeSet d)] (fun u => ∏ i, vb i (u i)) := by
      simpa only [AlignmentFractionalTensor.unitCube_measure_eq_pi] using hp
    exact (productToCube_ae (productVector vb)).trans hp'
  rw [L2.inner_def]
  simp_rw [Real.inner_apply]
  change (∫ u, ordinaryTensorSource a u * ordinaryTensorSource b u
      ∂((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet d))) = _
  calc
    _ = ∫ u, (∏ i : Fin d, va i (u i)) * (∏ i : Fin d, vb i (u i))
          ∂((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
            (CameronMartin.unitCubeSet d)) := by
      apply integral_congr_ae
      filter_upwards [haeA, haeB] with u hu hv
      dsimp [ordinaryTensorSource]
      rw [hu, hv]
    _ = ∫ u, ∏ i : Fin d, va i (u i) * vb i (u i)
          ∂Measure.pi (fun _ : Fin d => volume.restrict (Set.Icc (0:ℝ) 1)) := by
      have heq : (fun u : Fin d → ℝ =>
          (∏ i : Fin d, va i (u i)) * (∏ i : Fin d, vb i (u i))) =
          fun u => ∏ i : Fin d, va i (u i) * vb i (u i) := by
        funext u
        rw [← Finset.prod_mul_distrib]
      rw [heq, AlignmentFractionalTensor.unitCube_measure_eq_pi]
    _ = ∏ i : Fin d, ∫ u, va i u * vb i u
          ∂volume.restrict (Set.Icc (0:ℝ) 1) :=
      integral_fintype_prod_eq_prod (fun i u => va i u * vb i u)
    _ = ∏ i : Fin d, ⟪va i, vb i⟫ := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with u
      rw [Real.inner_apply]

theorem ordinaryTensorSource_orthonormal {d n : ℕ} :
    Orthonormal ℝ (ordinaryTensorSourceFamily (d:=d) (n:=n)) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  change ⟪ordinaryTensorSource a, ordinaryTensorSource b⟫ = _
  rw [ordinaryTensorSource_inner]
  have hcos := cosineSource_orthonormal
  have hcoord (i : Fin d) :
      ⟪cosineSource (layerFrequency a i), cosineSource (layerFrequency b i)⟫ =
        if layerFrequency a i = layerFrequency b i then 1 else 0 :=
    (orthonormal_iff_ite.mp hcos) _ _
  simp_rw [hcoord]
  by_cases hab : a=b
  · subst b
    simp
  · rw [if_neg hab]
    obtain ⟨i, hi⟩ : ∃ i : Fin d, layerFrequency a i ≠ layerFrequency b i := by
      by_contra hn
      push_neg at hn
      apply hab
      exact layerFrequency_injective (funext hn)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

def unitPiAnchor {d : ℕ} (x : Fin d → UnitInterval) :
    BrownianCubeAnchor d :=
  ⟨fun i => (x i).val, fun i => (x i).property⟩

theorem unitPiAnchor_continuous {d : ℕ} :
    Continuous (unitPiAnchor (d:=d)) := by
  change Continuous (fun x : Fin d → UnitInterval =>
    (⟨fun i => (x i).val, fun i => (x i).property⟩ : BrownianCubeAnchor d))
  exact (continuous_pi fun i =>
    (continuous_subtype_val : Continuous (fun x : UnitInterval => (x : ℝ))).comp
      (continuous_apply i)).subtype_mk _

def unitPiAnchorMap {d : ℕ} :
    C((Fin d → UnitInterval), BrownianCubeAnchor d) :=
  ⟨unitPiAnchor, unitPiAnchor_continuous⟩

def productTargetMeasure (d : ℕ) : Measure (Fin d → UnitInterval) :=
  Measure.pi (fun _ : Fin d => unitTargetMeasure)

instance productTargetMeasure_probability (d : ℕ) :
    IsProbabilityMeasure (productTargetMeasure d) := by
  dsimp [productTargetMeasure]
  infer_instance

theorem unitTarget_inner (f g : C(UnitInterval, ℝ)) :
    (∫ x, f x * g x ∂unitTargetMeasure) =
      ⟪profileToL2 f, profileToL2 g⟫_ℝ := by
  rw [unitTargetMeasure, integral_map clipUnit_continuous.aemeasurable]
  · rw [unitSourceProbability]
    change (∫ x in Set.Icc (0:ℝ) 1, f (clipUnit x) * g (clipUnit x) ∂volume) = _
    exact (BrownianSharp.AlignmentOrdinaryIntegrationLower.profileToL2_inner f g).symm
  · exact (f.continuous.mul g.continuous).aestronglyMeasurable

def ordinaryTensorEvaluationOperator {d n : ℕ} :
    UnitCubeL2 d →L[ℝ] C((Fin d → UnitInterval), ℝ) :=
  (ContinuousMap.compCLM ℝ ℝ (unitPiAnchorMap (d:=d))).comp
    (fractionalTensorRL (fun _ : Fin d => 1) (by intro i; norm_num))

theorem ordinaryTensorEvaluationOperator_apply {d n : ℕ}
    (g : UnitCubeL2 d) (x : Fin d → UnitInterval) :
    ordinaryTensorEvaluationOperator (d:=d) (n:=n) g x =
      fractionalTensorRL (fun _ : Fin d => 1) (by intro i; norm_num) g
        (unitPiAnchor x) := rfl

def tensorSineProfile {d n : ℕ} (a : LayerIndex d n) :
    C((Fin d → UnitInterval), ℝ) where
  toFun x := ∏ i : Fin d, sineProfile (layerFrequency a i) (x i)
  continuous_toFun := by
    apply continuous_finset_prod
    intro i hi
    exact (sineProfile (layerFrequency a i)).continuous.comp (continuous_apply i)

def tensorSineLp {d n : ℕ} (a : LayerIndex d n) :
    Lp ℝ 2 (productTargetMeasure d) :=
  ContinuousMap.toLp 2 (productTargetMeasure d) ℝ (tensorSineProfile a)

theorem tensorSineLp_orthonormal {d n : ℕ} :
    Orthonormal ℝ (tensorSineLp (d:=d) (n:=n)) := by
  classical
  rw [orthonormal_iff_ite]
  intro a b
  rw [L2.inner_def]
  simp_rw [Real.inner_apply]
  have hAEa : tensorSineLp a =ᵐ[productTargetMeasure d] tensorSineProfile a := by
    dsimp [tensorSineLp]
    exact ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℝ)
      (μ:=productTargetMeasure d) (tensorSineProfile a)
  have hAEb : tensorSineLp b =ᵐ[productTargetMeasure d] tensorSineProfile b := by
    dsimp [tensorSineLp]
    exact ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℝ)
      (μ:=productTargetMeasure d) (tensorSineProfile b)
  change (∫ x, tensorSineLp (d:=d) (n:=n) a x *
      tensorSineLp (d:=d) (n:=n) b x ∂(productTargetMeasure d)) = _
  calc
    _ = ∫ x, tensorSineProfile a x * tensorSineProfile b x
          ∂productTargetMeasure d := by
      apply integral_congr_ae
      filter_upwards [hAEa, hAEb] with x ha hb
      rw [ha, hb]
    _ = ∏ i : Fin d, ∫ x, sineProfile (layerFrequency a i) x *
          sineProfile (layerFrequency b i) x ∂unitTargetMeasure := by
      have hfun : (fun x : Fin d → UnitInterval =>
          (∏ i : Fin d, sineProfile (layerFrequency a i) (x i)) *
            ∏ i : Fin d, sineProfile (layerFrequency b i) (x i)) =
          fun x => ∏ i : Fin d,
            sineProfile (layerFrequency a i) (x i) *
              sineProfile (layerFrequency b i) (x i) := by
        funext x
        rw [← Finset.prod_mul_distrib]
      change (∫ x : Fin d → UnitInterval,
          (∏ i : Fin d, sineProfile (layerFrequency a i) (x i)) *
            ∏ i : Fin d, sineProfile (layerFrequency b i) (x i)
          ∂(productTargetMeasure d)) = _
      rw [hfun, productTargetMeasure]
      exact integral_fintype_prod_eq_prod (fun i x =>
        sineProfile (layerFrequency a i) x * sineProfile (layerFrequency b i) x)
    _ = _ := by
      have hscalar (i : Fin d) :
        (∫ x, sineProfile (layerFrequency a i) x * sineProfile (layerFrequency b i) x
          ∂unitTargetMeasure) =
        if layerFrequency a i = layerFrequency b i then 1 else 0 := by
        have horth := (orthonormal_iff_ite.mp sineSource_orthonormal)
          (layerFrequency a i) (layerFrequency b i)
        exact (unitTarget_inner (sineProfile (layerFrequency a i))
          (sineProfile (layerFrequency b i))).trans horth
      have hprod :
          (∏ i : Fin d, ∫ x, sineProfile (layerFrequency a i) x *
            sineProfile (layerFrequency b i) x ∂unitTargetMeasure) =
          ∏ i : Fin d, if layerFrequency a i = layerFrequency b i then 1 else 0 := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hscalar i
      rw [hprod]
      by_cases hab : a=b
      · subst b
        simp
      · have hneq : ∃ i, layerFrequency a i ≠ layerFrequency b i := by
          by_contra hn
          push_neg at hn
          apply hab
          exact layerFrequency_injective (funext hn)
        obtain ⟨i, hi⟩ := hneq
        have hz :
            (∏ i : Fin d, if layerFrequency a i = layerFrequency b i then (1:ℝ) else 0) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
        simpa [hab] using hz

def tensorFrequencyScale {d n : ℕ} (a : LayerIndex d n) : ℝ :=
  ∏ i : Fin d, (halfFrequency (layerFrequency a i))⁻¹

theorem ordinaryTensorEvaluationOperator_source {d n : ℕ}
    (a : LayerIndex d n) (x : Fin d → UnitInterval) :
    ordinaryTensorEvaluationOperator (d:=d) (n:=n) (ordinaryTensorSource a) x =
      tensorFrequencyScale a * tensorSineProfile a x := by
  rw [ordinaryTensorEvaluationOperator_apply]
  change fractionalTensorRL (fun _ : Fin d => 1) (by intro i; norm_num)
    (productToCube d (productVector (fun i => cosineSource (layerFrequency a i))))
    (unitPiAnchor x) = _
  rw [fractionalTensorRL_product]
  simp_rw [fractionalRL_one_cosine]
  dsimp [tensorFrequencyScale, tensorSineProfile]
  rw [Finset.prod_mul_distrib]
  congr 1

def ordinaryTensorOutput (d n : ℕ) :
    UnitCubeL2 d →L[ℝ] Lp ℝ 2 (productTargetMeasure d) :=
  (ContinuousMap.toLp 2 (productTargetMeasure d) ℝ).comp
    (ordinaryTensorEvaluationOperator (d:=d) (n:=n))

theorem ordinaryTensorOutput_source {d n : ℕ}
    (a : LayerIndex d n) :
    ordinaryTensorOutput d n (ordinaryTensorSource a) =
      tensorFrequencyScale a • tensorSineLp a := by
  change ContinuousMap.toLp 2 (productTargetMeasure d) ℝ
    (ordinaryTensorEvaluationOperator (d:=d) (n:=n) (ordinaryTensorSource a)) = _
  have hfun : ordinaryTensorEvaluationOperator (d:=d) (n:=n)
      (ordinaryTensorSource a) = tensorFrequencyScale a • tensorSineProfile a := by
    ext x
    exact ordinaryTensorEvaluationOperator_source a x
  rw [hfun]
  simp [tensorSineLp]

def ordinaryTensorSubspace (d n : ℕ) : Submodule ℝ (UnitCubeL2 d) :=
  Submodule.span ℝ (Set.range (ordinaryTensorSourceFamily (d:=d) (n:=n)))

theorem ordinaryTensorSubspace_finiteDimensional {d n : ℕ} :
    FiniteDimensional ℝ (ordinaryTensorSubspace d n) := by
  classical
  let b : OrthonormalBasis (Finset.univ : Finset (LayerIndex d n)) ℝ
      (Submodule.span ℝ (Finset.univ.image (ordinaryTensorSourceFamily (d:=d) (n:=n)) :
        Set (UnitCubeL2 d))) :=
    OrthonormalBasis.span (ordinaryTensorSource_orthonormal (d:=d) (n:=n)) Finset.univ
  have hs : ordinaryTensorSubspace d n =
      Submodule.span ℝ (Finset.univ.image
        (ordinaryTensorSourceFamily (d:=d) (n:=n)) : Set (UnitCubeL2 d)) := by
    unfold ordinaryTensorSubspace
    congr 1
    ext x
    simp
  rw [hs]
  exact Module.Finite.of_basis b.toBasis

theorem ordinaryTensorSubspace_finrank {d n : ℕ} :
    Module.finrank ℝ (ordinaryTensorSubspace d n) = Fintype.card (LayerIndex d n) := by
  classical
  let b : OrthonormalBasis (Finset.univ : Finset (LayerIndex d n)) ℝ
      (Submodule.span ℝ (Finset.univ.image (ordinaryTensorSourceFamily (d:=d) (n:=n)) :
        Set (UnitCubeL2 d))) :=
    OrthonormalBasis.span (ordinaryTensorSource_orthonormal (d:=d) (n:=n)) Finset.univ
  have hs : ordinaryTensorSubspace d n =
      Submodule.span ℝ (Finset.univ.image
        (ordinaryTensorSourceFamily (d:=d) (n:=n)) : Set (UnitCubeL2 d)) := by
    unfold ordinaryTensorSubspace
    congr 1
    ext x
    simp
  rw [hs, Module.finrank_eq_card_basis b.toBasis]
  simp

def tensorSineSubfamily {d n : ℕ} :
    (↥(Finset.univ : Finset (LayerIndex d n))) → Lp ℝ 2 (productTargetMeasure d) :=
  fun i => tensorSineLp i.1

theorem tensorSineSubfamily_orthonormal {d n : ℕ} :
    Orthonormal ℝ (tensorSineSubfamily (d:=d) (n:=n)) :=
  tensorSineLp_orthonormal.comp
    (fun i : ↥(Finset.univ : Finset (LayerIndex d n)) => i.1)
    Subtype.val_injective

def ordinaryTensorSourceSubfamily {d n : ℕ} :
    (↥(Finset.univ : Finset (LayerIndex d n))) → UnitCubeL2 d :=
  fun i => ordinaryTensorSourceFamily (d:=d) (n:=n) i.1

theorem ordinaryTensorSourceSubfamily_orthonormal {d n : ℕ} :
    Orthonormal ℝ (ordinaryTensorSourceSubfamily (d:=d) (n:=n)) :=
  ordinaryTensorSource_orthonormal.comp
    (fun i : ↥(Finset.univ : Finset (LayerIndex d n)) => i.1)
    Subtype.val_injective

theorem ordinaryTensorSubspace_eq_span_subfamily {d n : ℕ} :
    ordinaryTensorSubspace d n =
      Submodule.span ℝ (Set.range (ordinaryTensorSourceSubfamily (d:=d) (n:=n))) := by
  unfold ordinaryTensorSubspace ordinaryTensorSourceSubfamily
  congr 1
  ext x
  simp

theorem tensorFrequencyScale_pos {d n : ℕ} (a : LayerIndex d n) :
    0 < tensorFrequencyScale a := by
  dsimp [tensorFrequencyScale]
  apply Finset.prod_pos
  intro i hi
  apply inv_pos.mpr
  dsimp [halfFrequency]
  positivity

theorem tensorFrequencyScale_sq_le_output_energy {d n : ℕ}
    (a : LayerIndex d n) :
    tensorFrequencyScale a ^ 2 ≤
      ∫ x, (ordinaryTensorEvaluationOperator (d:=d) (n:=n)
        (ordinaryTensorSource a) x)^2 ∂productTargetMeasure d := by
  have hprofile :
      (∫ x, (tensorSineProfile a x)^2 ∂productTargetMeasure d) = 1 := by
    have hfun : (fun x : Fin d → UnitInterval =>
        (∏ j : Fin d, sineProfile (layerFrequency a j) (x j))^2) =
        fun x => ∏ j : Fin d, (sineProfile (layerFrequency a j) (x j))^2 := by
      funext x
      rw [Finset.prod_pow]
    change (∫ x : Fin d → UnitInterval,
      (∏ j : Fin d, sineProfile (layerFrequency a j) (x j))^2
      ∂productTargetMeasure d) = 1
    rw [hfun, productTargetMeasure]
    rw [integral_fintype_prod_eq_prod (fun j x =>
      (sineProfile (layerFrequency a j) x)^2)]
    have hscalar (j : Fin d) :
        (∫ x, (sineProfile (layerFrequency a j) x)^2 ∂unitTargetMeasure) = 1 := by
      rw [integral_unitTargetMeasure]
      have hn := sineSource_orthonormal.norm_eq_one (layerFrequency a j)
      rw [hn]
      norm_num
    simp_rw [hscalar]
    simp
  calc
    tensorFrequencyScale a ^ 2 =
        ∫ x, (tensorFrequencyScale a * tensorSineProfile a x)^2
          ∂productTargetMeasure d := by
      have hfun : (fun x => (tensorFrequencyScale a * tensorSineProfile a x)^2) =
          fun x => tensorFrequencyScale a ^ 2 * (tensorSineProfile a x)^2 := by
        funext x
        ring
      rw [hfun, integral_const_mul, hprofile]
      ring
    _ = ∫ x, (ordinaryTensorEvaluationOperator (d:=d) (n:=n)
          (ordinaryTensorSource a) x)^2 ∂productTargetMeasure d := by
      apply integral_congr_ae
      filter_upwards with x
      rw [ordinaryTensorEvaluationOperator_source]
    _ ≤ _ := le_rfl

def tensorSigma (d n : ℕ) : ℝ :=
  ((3 * Real.pi)^d * (2:ℝ)^n)⁻¹

private theorem real_prod_le_of_nonneg {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hfg : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    apply mul_le_mul
    · exact hfg i (Finset.mem_insert_self i s)
    · exact ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
    · exact Finset.prod_nonneg (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    · have hgi := hfg i (Finset.mem_insert_self i s)
      have hfi := hf i (Finset.mem_insert_self i s)
      linarith

theorem halfFrequency_shifted_le (r j : ℕ) (hj : j < 2^r) :
    halfFrequency (shiftedFrequency r j) ≤ 3 * Real.pi * (2:ℝ)^r := by
  have hpowcast : ((2^r : ℕ):ℝ) = (2:ℝ)^r := by norm_cast
  have hjcast : (j:ℝ) < (2:ℝ)^r := by exact_mod_cast hj
  have hone : 1 ≤ (2:ℝ)^r := one_le_pow₀ (by norm_num)
  dsimp [halfFrequency, shiftedFrequency]
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] at *
  nlinarith [Real.pi_pos]

theorem tensorFrequencyScale_lower (d n : ℕ) (a : LayerIndex d n) :
    tensorSigma d n ≤ tensorFrequencyScale a := by
  have hfactor (i : Fin d) :
      halfFrequency (layerFrequency a i) ≤
        3 * Real.pi * (2:ℝ)^(layerIndexDepth a i) := by
    exact halfFrequency_shifted_le _ _ (layerIndexCell_lt a i)
  have hfreqprod :
      (∏ i : Fin d, halfFrequency (layerFrequency a i)) ≤
        (3 * Real.pi)^d * (2:ℝ)^n := by
    calc
      _ ≤ ∏ i : Fin d, 3 * Real.pi * (2:ℝ)^(layerIndexDepth a i) :=
        real_prod_le_of_nonneg Finset.univ _ _
          (fun i hi => by dsimp [halfFrequency]; positivity) (fun i hi => hfactor i)
      _ = (3 * Real.pi)^d * (2:ℝ)^n := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow_eq_pow_sum]
        have hsum : ∑ i : Fin d, layerIndexDepth a i = n := by
          have h := layerIndexDepth_grade a
          simpa [layerIndexDepth, Finsupp.sum_fintype] using h
        simp [hsum]
  have hpositive : 0 < ∏ i : Fin d, halfFrequency (layerFrequency a i) := by
    apply Finset.prod_pos
    intro i hi
    dsimp [halfFrequency]
    positivity
  have hinv := one_div_le_one_div_of_le hpositive hfreqprod
  simpa [tensorSigma, tensorFrequencyScale, one_div, Finset.prod_inv_distrib] using hinv

theorem ordinaryTensorSubspace_L2energy_lower {d n : ℕ}
    (v : ordinaryTensorSubspace d n) (hv : ‖(v : UnitCubeL2 d)‖ = 1) :
    tensorSigma d n ^ 2 ≤
      ∫ x, (ordinaryTensorEvaluationOperator (d:=d) (n:=n)
        (v : UnitCubeL2 d) x)^2 ∂productTargetMeasure d := by
  classical
  let b : OrthonormalBasis (Finset.univ : Finset (LayerIndex d n)) ℝ
      (Submodule.span ℝ (Finset.univ.image
        (ordinaryTensorSourceFamily (d:=d) (n:=n)) : Set (UnitCubeL2 d))) :=
    OrthonormalBasis.span (ordinaryTensorSource_orthonormal
      (d:=d) (n:=n)) Finset.univ
  have hs : ordinaryTensorSubspace d n =
      Submodule.span ℝ (Finset.univ.image
        (ordinaryTensorSourceFamily (d:=d) (n:=n)) : Set (UnitCubeL2 d)) := by
    unfold ordinaryTensorSubspace
    congr 1
    ext x
    simp
  have hv' : (v : UnitCubeL2 d) ∈
      Submodule.span ℝ (Finset.univ.image
        (ordinaryTensorSourceFamily (d:=d) (n:=n)) : Set (UnitCubeL2 d)) := by
    rw [← hs]
    exact v.2
  let c : (↥Finset.univ) → ℝ := b.toBasis.repr ⟨(v : UnitCubeL2 d), hv'⟩
  have hrepr : (v : UnitCubeL2 d) =
      ∑ i : ↥Finset.univ, c i • ordinaryTensorSourceFamily (d:=d) (n:=n) i.1 := by
    have hh := congrArg Subtype.val (b.toBasis.sum_repr ⟨(v : UnitCubeL2 d), hv'⟩)
    simpa [c, b, OrthonormalBasis.span_apply] using hh.symm
  have hsource : ‖(v : UnitCubeL2 d)‖^2 =
      ∑ i : ↥Finset.univ, (c i)^2 := by
    rw [hrepr]
    exact orthonormal_sum_norm_sq
      (fun i : ↥Finset.univ => ordinaryTensorSourceFamily (d:=d) (n:=n) i.1)
      (ordinaryTensorSource_orthonormal.comp (fun i : ↥Finset.univ => i.1)
        Subtype.val_injective) c
  let out := ordinaryTensorOutput d n
  have hout : out (v : UnitCubeL2 d) =
      ∑ i : ↥Finset.univ,
        (c i * tensorFrequencyScale i.1) • tensorSineLp (i.1) := by
    rw [hrepr]
    dsimp [out]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_smul]
    change c i • ordinaryTensorOutput d n (ordinaryTensorSource i.1) = _
    rw [ordinaryTensorOutput_source]
    rw [smul_smul]
  have houtnorm : ‖out (v : UnitCubeL2 d)‖^2 =
      ∑ i : ↥Finset.univ, (c i * tensorFrequencyScale i.1)^2 := by
    rw [hout]
    exact orthonormal_sum_norm_sq
      (fun i : ↥Finset.univ => tensorSineLp (i.1))
      (tensorSineLp_orthonormal.comp (fun i : ↥Finset.univ => i.1)
        Subtype.val_injective)
      (fun i => c i * tensorFrequencyScale i.1)
  have hterm (i : ↥Finset.univ) :
      tensorSigma d n ^ 2 * (c i)^2 ≤
        (c i * tensorFrequencyScale i.1)^2 := by
    have hsigma : 0 ≤ tensorSigma d n := by
      dsimp [tensorSigma]
      positivity
    have hscale := tensorFrequencyScale_lower d n i.1
    have hscale0 := (tensorFrequencyScale_pos i.1).le
    have hsq : tensorSigma d n ^ 2 ≤ tensorFrequencyScale i.1 ^ 2 := by
      nlinarith
    calc
      tensorSigma d n ^ 2 * (c i)^2 ≤
          tensorFrequencyScale i.1 ^ 2 * (c i)^2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg (c i))
      _ = (c i * tensorFrequencyScale i.1)^2 := by ring
  have hsum : tensorSigma d n ^ 2 *
      (∑ i : ↥Finset.univ, (c i)^2) ≤
        ∑ i : ↥Finset.univ, (c i * tensorFrequencyScale i.1)^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => hterm i
  have hsourceone : (∑ i : ↥Finset.univ, (c i)^2) = 1 := by
    rw [← hsource, hv]
    norm_num
  have houtenergy : ‖out (v : UnitCubeL2 d)‖^2 =
      ∫ x, (ordinaryTensorEvaluationOperator (d:=d) (n:=n)
        (v : UnitCubeL2 d) x)^2 ∂productTargetMeasure d := by
    change ‖ContinuousMap.toLp 2 (productTargetMeasure d) ℝ
      (ordinaryTensorEvaluationOperator (d:=d) (n:=n) (v : UnitCubeL2 d))‖^2 = _
    rw [BrownianSharp.AlignmentFractionalTensor.realLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℝ)
      (μ:=productTargetMeasure d) (ordinaryTensorEvaluationOperator
        (d:=d) (n:=n) (v : UnitCubeL2 d))] with x hx
    rw [hx]
  calc
    tensorSigma d n ^ 2 = tensorSigma d n ^ 2 *
        (∑ i : ↥Finset.univ, (c i)^2) := by rw [hsourceone]; ring
    _ ≤ ∑ i : ↥Finset.univ, (c i * tensorFrequencyScale i.1)^2 := hsum
    _ = ‖out (v : UnitCubeL2 d)‖^2 := houtnorm.symm
    _ = ∫ x, (ordinaryTensorEvaluationOperator (d:=d) (n:=n)
        (v : UnitCubeL2 d) x)^2 ∂productTargetMeasure d := houtenergy

/-- The product probability measure on unit-interval coordinates, pushed to
the manuscript's actual compact cube anchor. -/
def ordinaryCubeMeasure (d : ℕ) : Measure (BrownianCubeAnchor d) :=
  Measure.map (unitPiAnchor (d:=d)) (productTargetMeasure d)

instance ordinaryCubeMeasure_probability (d : ℕ) :
    IsProbabilityMeasure (ordinaryCubeMeasure d) := by
  dsimp [ordinaryCubeMeasure]
  infer_instance

theorem ordinaryTensor_actual_subspace_energy_lower {d n : ℕ}
    (v : ordinaryTensorSubspace d n) (hv : ‖(v : UnitCubeL2 d)‖ = 1) :
    tensorSigma d n ^ 2 ≤
      ∫ t, (fractionalTensorRL (fun _ : Fin d => 1)
        (by intro i; norm_num) (v : UnitCubeL2 d) t)^2 ∂ordinaryCubeMeasure d := by
  have hp := ordinaryTensorSubspace_L2energy_lower v hv
  let T := fractionalTensorRL (fun _ : Fin d => 1)
    (by intro i; norm_num) (v : UnitCubeL2 d)
  change tensorSigma d n ^ 2 ≤ ∫ t, (T t)^2 ∂ordinaryCubeMeasure d
  have hmap : ∫ t, (T t)^2 ∂ordinaryCubeMeasure d =
      ∫ x, (T (unitPiAnchor x))^2 ∂productTargetMeasure d := by
    rw [ordinaryCubeMeasure]
    exact integral_map (φ:=unitPiAnchor (d:=d)) (μ:=productTargetMeasure d)
      (f:=fun t => (T t)^2) (unitPiAnchor_continuous (d:=d)).aemeasurable
      (T.continuous.pow 2).aestronglyMeasurable
  rw [hmap]
  simpa [T, ordinaryTensorEvaluationOperator_apply, unitPiAnchorMap] using hp

/-- A tensor hyperbolic layer of ordinary integration has a uniform lower
singular scale. The trace argument turns its dimension into a strict-rank
approximation-number lower bound for the actual RL operator. -/
theorem ordinaryTensor_approximationNumber_lower_layer {d n k : ℕ}
    (hk : 1 ≤ k) (hkD : k ≤ Fintype.card (LayerIndex d n)) :
    ENNReal.ofReal (tensorSigma d n *
      Real.sqrt (((Fintype.card (LayerIndex d n) - (k-1):ℕ):ℝ))) ≤
      BrownianSharp.AlignmentFractionalApproximationNumbers.approximationNumber
        (fractionalTensorRL (fun _ : Fin d => 1) (by intro i; norm_num)) k := by
  letI := ordinaryTensorSubspace_finiteDimensional (d:=d) (n:=n)
  apply approximationNumber_lower_of_subspace_trace
    (μ:=ordinaryCubeMeasure d)
    (T:=fractionalTensorRL (fun _ : Fin d => 1) (by intro i; norm_num))
    (V:=ordinaryTensorSubspace d n)
  · exact ordinaryTensorSubspace_finrank
  · exact hk
  · exact hkD
  · dsimp [tensorSigma]
    positivity
  · intro v hv
    exact ordinaryTensor_actual_subspace_energy_lower v hv

noncomputable def ordinaryTensorLowerRateConstant (d : ℕ) : ℝ :=
  1 / ((3 * Real.pi)^d * (8 * (d:ℝ)^2) *
    (Nat.factorial (d-1):ℝ) * (nativeLogScaleLower d)^(d-1))

theorem ordinaryTensorLowerRateConstant_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < ordinaryTensorLowerRateConstant d := by
  unfold ordinaryTensorLowerRateConstant
  apply one_div_pos.mpr
  have hdR : 0 < (d:ℝ) := by exact_mod_cast (by omega : 0<d)
  have hscale : 0 < nativeLogScaleLower d := nativeLogScaleLower_pos hd
  positivity

/-- All-index tensor lower rate for ordinary integration. -/
theorem ordinaryTensor_approximationNumber_lower {d k : ℕ}
    (hd : 2 ≤ d) (hk : 2 ≤ k) :
    ENNReal.ofReal (ordinaryTensorLowerRateConstant d *
      (Real.log (k:ℝ))^(d-1) / Real.sqrt (k:ℝ)) ≤
      BrownianSharp.AlignmentFractionalApproximationNumbers.approximationNumber
        (fractionalTensorRL (fun _ : Fin d => 1) (by intro i; norm_num)) k := by
  let q := nativeEntropyCrossing d (2*k) (by omega)
  let n := 2*q
  let D := Fintype.card (LayerIndex d n)
  have hqbr := nativeEntropyCrossing_bracket hd (by omega : 2 ≤ 2*k)
  have hqpos : 0 < q := by simpa [q] using hqbr.1
  have hq : 0 < (q:ℝ) := by exact_mod_cast hqpos
  have hDidentity : (D:ℝ) = nativeDimension d n := by
    dsimp [D,n]
    rw [layerIndex_card d (2*q) (by omega : 0<d)]
    simp [nativeDimension, hyperbolicCount]
  have hDlow : 2*(k:ℝ) ≤ (D:ℝ) := by
    rw [hDidentity]
    change 2*(k:ℝ) ≤ nativeDimension d (2*q)
    simpa [q] using hqbr.2.2.1
  have hDhigh : (D:ℝ) ≤ 8*(d:ℝ)^2*(k:ℝ) := by
    rw [hDidentity]
    have hh : nativeDimension d (2*q) ≤
        4*(d:ℝ)^2*(2*(k:ℝ)) := by
      simpa [q] using hqbr.2.2.2
    nlinarith
  have hDlowNat : 2*k ≤ D := by exact_mod_cast hDlow
  have hkD : k ≤ D := by
    have : (k:ℝ) ≤ (D:ℝ) := by linarith
    exact_mod_cast this
  have hlayer := ordinaryTensor_approximationNumber_lower_layer
    (d:=d) (n:=n) (k:=k) (by omega) hkD
  have hgap : k ≤ D-(k-1) := by omega
  have hsqrtdiff : Real.sqrt (k:ℝ) ≤
      Real.sqrt (((D-(k-1):ℕ):ℝ)) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hgap
  have hlogscale := (nativeEntropyCrossing_log_bounds hd (by omega : 2 ≤ 2*k)).1
  have hlogk : Real.log (k:ℝ) ≤ nativeLogScaleLower d * (q:ℝ) := by
    have hmono : Real.log (k:ℝ) ≤ Real.log ((2*k:ℕ):ℝ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast (show k ≤ 2*k by omega)
    have hlogscale' : Real.log ((2*k:ℕ):ℝ) ≤
        nativeLogScaleLower d * (q:ℝ) := by
      simpa [q, nativeLogScaleLower] using hlogscale
    exact hmono.trans hlogscale'
  have hlognonneg : 0 ≤ Real.log (k:ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ k by omega)
  have hlogpow : (Real.log (k:ℝ))^(d-1) ≤
      (nativeLogScaleLower d)^(d-1) * (q:ℝ)^(d-1) := by
    calc
      (Real.log (k:ℝ))^(d-1) ≤
          (nativeLogScaleLower d * (q:ℝ))^(d-1) :=
        pow_le_pow_left₀ hlognonneg hlogk (d-1)
      _ = _ := by rw [mul_pow]
  have hpoly := nativeDimension_polynomial_lower hd hqpos
  have hpolyD : (1/(Nat.factorial (d-1):ℝ)) *
      (2:ℝ)^n * (q:ℝ)^(d-1) ≤ (D:ℝ) := by
    have h := hpoly
    rw [hDidentity]
    simpa [n, Real.rpow_natCast] using h
  have hfact : 0 < (Nat.factorial (d-1):ℝ) := by positivity
  have hprod : (2:ℝ)^n * (q:ℝ)^(d-1) ≤
      (8*(d:ℝ)^2*(k:ℝ)) * (Nat.factorial (d-1):ℝ) := by
    have h := mul_le_mul_of_nonneg_left hpolyD (le_of_lt hfact)
    have hfactor : (Nat.factorial (d-1):ℝ) *
        ((1/(Nat.factorial (d-1):ℝ))*(2:ℝ)^n*(q:ℝ)^(d-1)) =
        (2:ℝ)^n*(q:ℝ)^(d-1) := by field_simp
    rw [hfactor] at h
    calc
      (2:ℝ)^n*(q:ℝ)^(d-1) ≤ (Nat.factorial (d-1):ℝ)*(D:ℝ) := h
      _ ≤ (Nat.factorial (d-1):ℝ) * (8*(d:ℝ)^2*(k:ℝ)) :=
        mul_le_mul_of_nonneg_left hDhigh (le_of_lt hfact)
      _ = _ := by ring
  have hdenpos : 0 < 8*(d:ℝ)^2*(k:ℝ)*(Nat.factorial (d-1):ℝ) := by positivity
  have hdyadic : (q:ℝ)^(d-1) /
      (8*(d:ℝ)^2*(k:ℝ)*(Nat.factorial (d-1):ℝ)) ≤ ((2:ℝ)^n)⁻¹ := by
    apply (div_le_iff₀ hdenpos).2
    have hpw : 0 < (2:ℝ)^n := by positivity
    have hprod' : (q:ℝ)^(d-1) * (2:ℝ)^n ≤
        8*(d:ℝ)^2*(k:ℝ)*(Nat.factorial (d-1):ℝ) := by
      calc
        _ = (2:ℝ)^n * (q:ℝ)^(d-1) := by ring
        _ ≤ _ := hprod
    have hdiv := (le_div_iff₀ hpw).2 hprod'
    convert hdiv using 1 <;> field_simp <;> ring
  have hbase : (q:ℝ)^(d-1) /
      (((3*Real.pi)^d)*(8*(d:ℝ)^2*(k:ℝ)*(Nat.factorial (d-1):ℝ))) ≤
        tensorSigma d n := by
    have hA : 0 < (3*Real.pi)^d := by positivity
    have h := div_le_div_of_nonneg_right hdyadic hA.le
    calc
      _ = ((q:ℝ)^(d-1) /
        (8*(d:ℝ)^2*(k:ℝ)*(Nat.factorial (d-1):ℝ))) / (3*Real.pi)^d := by
          field_simp <;> ring
      _ ≤ (((2:ℝ)^n)⁻¹) / (3*Real.pi)^d := h
      _ = tensorSigma d n := by
          dsimp [tensorSigma]
          field_simp
  have hlogq : (Real.log (k:ℝ))^(d-1) /
      (nativeLogScaleLower d)^(d-1) ≤ (q:ℝ)^(d-1) := by
    have hS := nativeLogScaleLower_pos hd
    apply (div_le_iff₀ (pow_pos hS (d-1))).2
    simpa [mul_comm] using hlogpow
  have hrootpos : 0 < Real.sqrt (k:ℝ) := Real.sqrt_pos.2 (by positivity)
  have htarget :
      ordinaryTensorLowerRateConstant d *
        (Real.log (k:ℝ))^(d-1) / Real.sqrt (k:ℝ) ≤
      tensorSigma d n * Real.sqrt (((D-(k-1):ℕ):ℝ)) := by
    let B : ℝ := (3*Real.pi)^d * (8*(d:ℝ)^2*(Nat.factorial (d-1):ℝ))
    have hB : 0 < B := by dsimp [B]; positivity
    have hbase' : (q:ℝ)^(d-1) / (B*(k:ℝ)) ≤ tensorSigma d n := by
      have heq : B*(k:ℝ) =
          (3*Real.pi)^d * (8*(d:ℝ)^2*(k:ℝ)*(Nat.factorial (d-1):ℝ)) := by
        dsimp [B]
        ring
      simpa [heq] using hbase
    have hroot_sq : Real.sqrt (k:ℝ)^2 = (k:ℝ) :=
      Real.sq_sqrt (by positivity)
    have hcoef : 0 ≤ (q:ℝ)^(d-1) / (B*(k:ℝ)) := by positivity
    have hbaseMul := mul_le_mul_of_nonneg_right hbase'
      (Real.sqrt_nonneg (((D-(k-1):ℕ):ℝ)))
    have htarget_to_q :
        ordinaryTensorLowerRateConstant d *
          (Real.log (k:ℝ))^(d-1) / Real.sqrt (k:ℝ) ≤
        ((q:ℝ)^(d-1) / (B*(k:ℝ))) * Real.sqrt (k:ℝ) := by
      have hlog := div_le_div_of_nonneg_right hlogq (le_of_lt hB)
      have hroot := div_le_div_of_nonneg_right hlog (Real.sqrt_nonneg (k:ℝ))
      have hconst : ordinaryTensorLowerRateConstant d *
          (Real.log (k:ℝ))^(d-1) / Real.sqrt (k:ℝ) =
          ((Real.log (k:ℝ))^(d-1) /
            (nativeLogScaleLower d)^(d-1) / B) / Real.sqrt (k:ℝ) := by
        unfold ordinaryTensorLowerRateConstant
        dsimp [B]
        field_simp [ne_of_gt (pow_pos (by positivity : 0 < (3*Real.pi)^d) _),
          ne_of_gt hrootpos,
          ne_of_gt (pow_pos (nativeLogScaleLower_pos hd) (d-1)),
          ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos _))]
        <;> ring
      rw [hconst]
      calc
        _ ≤ ((q:ℝ)^(d-1) / B) / Real.sqrt (k:ℝ) := by
              simpa [div_div] using hroot
        _ = ((q:ℝ)^(d-1) / (B*(k:ℝ))) * Real.sqrt (k:ℝ) := by
              field_simp [ne_of_gt hB, ne_of_gt hrootpos]
              nlinarith [hroot_sq]
    have hq_to_target :
        ((q:ℝ)^(d-1) / (B*(k:ℝ))) * Real.sqrt (k:ℝ) ≤
          tensorSigma d n * Real.sqrt (((D-(k-1):ℕ):ℝ)) := by
      have hfactor :
          ((q:ℝ)^(d-1) / (B*(k:ℝ))) * Real.sqrt (k:ℝ) ≤
          ((q:ℝ)^(d-1) / (B*(k:ℝ))) *
            Real.sqrt (((D-(k-1):ℕ):ℝ)) :=
        mul_le_mul_of_nonneg_left hsqrtdiff hcoef
      exact hfactor.trans hbaseMul
    exact htarget_to_q.trans hq_to_target
  have hlayerReal : ENNReal.ofReal (tensorSigma d n *
      Real.sqrt (((D-(k-1):ℕ):ℝ))) ≤
      BrownianSharp.AlignmentFractionalApproximationNumbers.approximationNumber
        (fractionalTensorRL (fun _ : Fin d => 1) (by intro i; norm_num)) k := by
    simpa [n,D] using hlayer
  exact (ENNReal.ofReal_le_ofReal htarget).trans hlayerReal

end BrownianSharp.AlignmentOrdinaryTensorLower
