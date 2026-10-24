import BrownianSharp.GaussianHeatSpatial
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Trace form of the finite-dimensional Gaussian heat equation

The time derivative formula is already available in `GaussianHeatTime`.  This
module supplies the coordinate integration-by-parts bridge to the spatial
trace for a constant plus a compactly supported smooth perturbation.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology BigOperators

namespace BrownianSharp

set_option maxHeartbeats 1000000 in
private theorem compactSupport_line_restriction {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : (κ → ℝ) → ℝ) (hp : HasCompactSupport p)
    (x w : κ → ℝ) (i : κ) (a : ℝ) (ha : 0 < a) :
    HasCompactSupport (fun s : ℝ => p (x + a • (w + s • Pi.single i 1))) := by
  classical
  obtain ⟨R₀, hR₀⟩ := hp.isCompact.isBounded.subset_closedBall (0 : κ → ℝ)
  let R := max R₀ 0
  have hR : tsupport p ⊆ Metric.closedBall (0 : κ → ℝ) R := by
    exact hR₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc)
  let K := (R + |x i + a * w i|) / a
  have hRnonneg : 0 ≤ R := le_max_right _ _
  intro s hs
  let y : κ → ℝ := x + a • (w + s • Pi.single i 1)
  have hne : p y ≠ 0 := by
    simpa only [y, Function.mem_support] using hs
  have hy : y ∈ tsupport p := subset_closure hne
  have hynorm : ‖y‖ ≤ R := by
    have := hR hy
    simpa [Metric.mem_closedBall, dist_eq_norm] using this
  have hcoord : |x i + a * (w i + s)| ≤ R := by
    have hnormcoordNN : ‖y i‖₊ ≤ ‖y‖₊ := by
      change ‖y i‖₊ ≤ Finset.univ.sup (fun j : κ => ‖y j‖₊)
      exact Finset.le_sup (s := (Finset.univ : Finset κ))
        (f := fun j : κ => ‖y j‖₊) (Finset.mem_univ i)
    have hnormcoord : ‖y i‖ ≤ ‖y‖ := by exact_mod_cast hnormcoordNN
    have hcoord0 := hnormcoord.trans hynorm
    convert hcoord0 using 1 <;> simp [Real.norm_eq_abs, y, Pi.single_apply, smul_eq_mul] <;> ring
  have hcoord' : |(x i + a * w i) + a * s| ≤ R := by
    convert hcoord using 1 <;> ring
  have hmul : |a * s| ≤ R + |x i + a * w i| := by
    calc
      |a * s| = |((x i + a * w i) + a * s) - (x i + a * w i)| := by congr 1 <;> ring
      _ ≤ |(x i + a * w i) + a * s| + |x i + a * w i| := abs_sub _ _
      _ ≤ R + |x i + a * w i| := add_le_add hcoord' (le_refl _)
  have hsabs : |s| ≤ K := by
    dsimp [K]
    rw [abs_mul, abs_of_pos ha] at hmul
    exact (le_div_iff₀ ha).2 (by simpa only [mul_comm] using hmul)
  have hsupper : s ≤ K := (abs_le.mp hsabs).2
  have hslower : -K ≤ s := (abs_le.mp hsabs).1
  exact ⟨hslower, hsupper⟩

private noncomputable def coordinateSplitEquiv {κ : Type*} [Fintype κ]
    [DecidableEq κ] (i : κ) :
    (({j : κ // j ≠ i} → ℝ) × ℝ) ≃ᵐ (κ → ℝ) := by
  let e₁ := MeasurableEquiv.piOptionEquivProd (fun _ : Option {j : κ // j ≠ i} => ℝ)
  let e₂ := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) (Equiv.optionSubtypeNe i)
  exact e₁.symm.trans e₂

private theorem measurePreserving_coordinateSplit {κ : Type*} [Fintype κ]
    [DecidableEq κ] (i : κ) :
    MeasurePreserving (coordinateSplitEquiv i)
      ((Measure.pi fun _ : {j : κ // j ≠ i} => gaussianReal 0 1).prod
        (gaussianReal 0 1)) (productStandardGaussian κ) := by
  let e₁ := MeasurableEquiv.piOptionEquivProd (fun _ : Option {j : κ // j ≠ i} => ℝ)
  let e₂ := MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) (Equiv.optionSubtypeNe i)
  have h₁ : MeasurePreserving e₁.symm
      ((Measure.pi fun _ : {j : κ // j ≠ i} => gaussianReal 0 1).prod
        (gaussianReal 0 1))
      (Measure.pi fun _ : Option {j : κ // j ≠ i} => gaussianReal 0 1) := by
    refine ⟨e₁.symm.measurable, ?_⟩
    exact Measure.pi_map_piOptionEquivProd (fun _ : Option {j : κ // j ≠ i} =>
      gaussianReal 0 1)
  have h₂ : MeasurePreserving e₂
      (Measure.pi fun _ : Option {j : κ // j ≠ i} => gaussianReal 0 1)
      (productStandardGaussian κ) := by
    simpa [productStandardGaussian] using
      (measurePreserving_piCongrLeft
        (fun _ : κ => gaussianReal 0 1) (Equiv.optionSubtypeNe i))
  convert h₂.comp h₁ using 1 <;> rfl

private theorem coordinateSplitEquiv_apply_self {κ : Type*} [Fintype κ]
    [DecidableEq κ] (i : κ) (w : {j : κ // j ≠ i} → ℝ) (s : ℝ) :
    coordinateSplitEquiv i (w, s) i = s := by
  simp [coordinateSplitEquiv, MeasurableEquiv.piOptionEquivProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply,
    MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
    MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.prodCongr]

private theorem coordinateSplitEquiv_apply_ne {κ : Type*} [Fintype κ]
    [DecidableEq κ] (i j : κ) (hji : j ≠ i)
    (w : {j : κ // j ≠ i} → ℝ) (s : ℝ) :
    coordinateSplitEquiv i (w, s) j = w ⟨j, hji⟩ := by
  simp [coordinateSplitEquiv, MeasurableEquiv.piOptionEquivProd,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply,
    MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
    MeasurableEquiv.piUnique, Equiv.piUnique, MeasurableEquiv.prodCongr, hji]

private noncomputable def coordinateBase {κ : Type*} [Fintype κ]
    [DecidableEq κ] (i : κ) (w : {j : κ // j ≠ i} → ℝ) : κ → ℝ :=
  coordinateSplitEquiv i (w, 0)

private theorem coordinateSplitEquiv_eq_base_add_single {κ : Type*} [Fintype κ]
    [DecidableEq κ] (i : κ) (w : {j : κ // j ≠ i} → ℝ) (s : ℝ) :
    coordinateSplitEquiv i (w, s) = coordinateBase i w + s • Pi.single i 1 := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [coordinateBase, coordinateSplitEquiv_apply_self]
  · simp [coordinateBase, coordinateSplitEquiv_apply_ne, hji]

private noncomputable def gaussianAffineHomeomorph {κ : Type*} [Fintype κ]
    (x : κ → ℝ) (a : ℝ) (ha : a ≠ 0) : (κ → ℝ) ≃ₜ (κ → ℝ) :=
  (Homeomorph.smulOfNeZero a ha).trans (Homeomorph.vaddConst x)

private theorem gaussianAffineHomeomorph_apply {κ : Type*} [Fintype κ]
    (x z : κ → ℝ) (a : ℝ) (ha : a ≠ 0) :
    gaussianAffineHomeomorph x a ha z = x + a • z := by
  simp [gaussianAffineHomeomorph, Homeomorph.smulOfNeZero, Homeomorph.vaddConst,
    vadd_eq_add]
  abel
/-- Coordinatewise Gaussian integration by parts for a compactly supported `C¹`
function on a finite product. -/
theorem integral_coordinate_mul_eq_integral_fderiv
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : (κ → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    (i : κ) :
    (∫ z, z i * f z ∂productStandardGaussian κ) =
      ∫ z, fderiv ℝ f z (Pi.single i 1) ∂productStandardGaussian κ := by
  classical
  let μRest := Measure.pi fun _ : {j : κ // j ≠ i} => gaussianReal 0 1
  let μPair := μRest.prod (gaussianReal 0 1)
  have hmap : (fun u : (({j : κ // j ≠ i} → ℝ) × ℝ) => coordinateSplitEquiv i u) =
      fun u j => if h : j = i then u.2 else u.1 ⟨j, h⟩ := by
    funext u j
    rcases u with ⟨w, s⟩
    by_cases hji : j = i
    · subst j
      simp [coordinateSplitEquiv_apply_self]
    · simp [coordinateSplitEquiv_apply_ne, hji]
  let splitInv : (κ → ℝ) → (({j : κ // j ≠ i} → ℝ) × ℝ) :=
    fun z => (fun j => z j, z i)
  have hleftInv (z : κ → ℝ) : coordinateSplitEquiv i (splitInv z) = z := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [splitInv, coordinateSplitEquiv_apply_self]
    · simp [splitInv, coordinateSplitEquiv_apply_ne, hji]
  have hsymm : (fun z => (coordinateSplitEquiv i).symm z) = splitInv := by
    funext z
    apply (coordinateSplitEquiv i).injective
    calc
      coordinateSplitEquiv i ((coordinateSplitEquiv i).symm z) = z :=
        (coordinateSplitEquiv i).apply_symm_apply z
      _ = coordinateSplitEquiv i (splitInv z) := (hleftInv z).symm
  have hecont : Continuous (fun u => coordinateSplitEquiv i u) := by
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      have hfun : (fun u : (({j : κ // j ≠ i} → ℝ) × ℝ) =>
          coordinateSplitEquiv i u i) = fun u => u.2 := by
        funext u
        exact coordinateSplitEquiv_apply_self i u.1 u.2
      rw [hfun]
      exact continuous_snd
    · have hfun : (fun u => coordinateSplitEquiv i u j) =
          fun u => u.1 ⟨j, hji⟩ := by
        funext u
        exact coordinateSplitEquiv_apply_ne i j hji u.1 u.2
      rw [hfun]
      exact (continuous_apply (⟨j, hji⟩ : {j : κ // j ≠ i})).comp continuous_fst
  have heinvcont : Continuous (fun y => (coordinateSplitEquiv i).symm y) := by
    rw [hsymm]
    have hfirst : Continuous (fun z : κ → ℝ =>
        fun j : {j : κ // j ≠ i} => z j.1) := by
      apply continuous_pi
      intro j
      exact continuous_apply j.1
    exact hfirst.prodMk (continuous_apply i)
  let H : Homeomorph (({j : κ // j ≠ i} → ℝ) × ℝ) (κ → ℝ) :=
    { toEquiv := (coordinateSplitEquiv i).toEquiv
      continuous_toFun := hecont
      continuous_invFun := heinvcont }
  have hfcComp : HasCompactSupport (fun u => f (coordinateSplitEquiv i u)) := by
    exact hfc.comp_isClosedEmbedding H.isClosedEmbedding
  have hfCompC : Continuous (fun u => f (coordinateSplitEquiv i u)) := hf.continuous.comp hecont
  have hleftC : Continuous (fun u : ({j : κ // j ≠ i} → ℝ) × ℝ => u.2 * f (coordinateSplitEquiv i u)) := by
    fun_prop
  have hleftCompact : HasCompactSupport (fun u : ({j : κ // j ≠ i} → ℝ) × ℝ =>
      u.2 * f (coordinateSplitEquiv i u)) := hfcComp.mul_left
  have hleftInt : Integrable (fun u : ({j : κ // j ≠ i} → ℝ) × ℝ =>
      u.2 * f (coordinateSplitEquiv i u)) μPair := hleftC.integrable_of_hasCompactSupport hleftCompact
  let df : (κ → ℝ) → ℝ := fun y => fderiv ℝ f y (Pi.single i (1 : ℝ))
  have hdfc : HasCompactSupport df := HasCompactSupport.fderiv_apply (𝕜 := ℝ) hfc (Pi.single i (1 : ℝ) : κ → ℝ)
  have hdfC : Continuous df := by
    exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdfCompC : Continuous (fun u => df (coordinateSplitEquiv i u)) := hdfC.comp hecont
  have hdfCompCompact : HasCompactSupport (fun u => df (coordinateSplitEquiv i u)) := by
    exact hdfc.comp_isClosedEmbedding H.isClosedEmbedding
  have hdfInt : Integrable (fun u : ({j : κ // j ≠ i} → ℝ) × ℝ => df (coordinateSplitEquiv i u)) μPair :=
    hdfCompC.integrable_of_hasCompactSupport hdfCompCompact
  have hchangeL :
      (∫ z, z i * f z ∂productStandardGaussian κ) =
        ∫ u, u.2 * f (coordinateSplitEquiv i u) ∂μPair := by
    rw [← (measurePreserving_coordinateSplit i).integral_comp'
      (fun z : κ → ℝ => z i * f z)]
    apply integral_congr_ae
    filter_upwards [] with u
    rcases u with ⟨w, s⟩
    simp [coordinateSplitEquiv_apply_self]
  have hchangeR :
      (∫ z, df z ∂productStandardGaussian κ) =
        ∫ u, df (coordinateSplitEquiv i u) ∂μPair := by
    rw [← (measurePreserving_coordinateSplit i).integral_comp' df]
  rw [hchangeL, hchangeR, integral_prod _ hleftInt, integral_prod _ hdfInt]
  apply integral_congr_ae
  filter_upwards [] with w
  let b := coordinateBase i w
  let v : κ → ℝ := Pi.single i 1
  have hb : (fun s : ℝ => coordinateSplitEquiv i (w, s)) =
      fun s => b + s • v := by
    funext s
    exact coordinateSplitEquiv_eq_base_add_single i w s
  have hfiberC : ContDiff ℝ 1 (fun s : ℝ => f (b + s • v)) := by
    exact hf.comp (by fun_prop)
  have hfiberCompact : HasCompactSupport (fun s : ℝ => f (b + s • v)) := by
    have h := compactSupport_line_restriction f hfc (0 : κ → ℝ) b i 1 (by norm_num)
    simpa [v, smul_eq_mul] using h
  have hline : ∀ s : ℝ, HasDerivAt (fun r : ℝ => f (b + r • v))
      (df (b + s • v)) s := by
    intro s
    have hmap : HasDerivAt (fun r : ℝ => b + r • v) v s := by
      simpa using ((hasDerivAt_id s).smul_const v).const_add b
    have hcomp := (hf.differentiable one_ne_zero _).hasFDerivAt.comp s hmap
    change HasDerivAt (fun r : ℝ => f (b + r • v)) (df (b + s • v)) s
    convert hcomp.hasDerivAt using 1
    · rfl
    · simp [df, v, ContinuousLinearMap.comp_apply]
  have hscalar := integral_id_mul_gaussian_eq_integral_deriv_gaussian
    hfiberC hfiberCompact
  calc
    (∫ s, s * f (coordinateSplitEquiv i (w, s)) ∂gaussianReal 0 1) =
        ∫ s, s * f (b + s • v) ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [← congrFun hb s]
    _ = ∫ s, deriv (fun r : ℝ => f (b + r • v)) s ∂gaussianReal 0 1 := hscalar
    _ = ∫ s, df (b + s • v) ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards [] with s
      exact (hline s).deriv
    _ = ∫ s, df (coordinateSplitEquiv i (w, s)) ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [← congrFun hb s]

set_option maxHeartbeats 1000000 in
/-- The finite-product Gaussian heat derivative is one half the averaged
coordinate trace of the Hessian. -/
theorem hasDerivAt_gaussianHeat_trace_of_contDiff_compactSupport
    {κ : Type*} [Fintype κ] [DecidableEq κ] (p : (κ → ℝ) → ℝ)
    (hp : ContDiff ℝ 2 p) (hpc : HasCompactSupport p)
    (x : κ → ℝ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s => gaussianHeat p s x)
      ((1 / 2) * ∑ i, ∫ z, fderiv ℝ
        (fun y => fderiv ℝ p y (Pi.single i (1 : ℝ)))
        (x + Real.sqrt t • z) (Pi.single i 1) ∂productStandardGaussian κ) t := by
  classical
  let a := Real.sqrt t
  have ha : 0 < a := Real.sqrt_pos.mpr ht
  have ha0 : a ≠ 0 := ha.ne'
  let μ := productStandardGaussian κ
  let T : (κ → ℝ) → (κ → ℝ) := fun z => x + a • z
  have hT : T = gaussianAffineHomeomorph x a ha0 := by
    funext z
    exact (gaussianAffineHomeomorph_apply x z a ha0).symm
  let evec (i : κ) : κ → ℝ := Pi.single i (1 : ℝ)
  let Di (i : κ) : (κ → ℝ) → ℝ := fun y => fderiv ℝ p y (evec i)
  let gi (i : κ) : (κ → ℝ) → ℝ := fun z => Di i (T z)
  have hDiC (i : κ) : ContDiff ℝ 1 (Di i) := by
    have h := hp.contDiff_fderiv_apply (m := 1) (n := 2) (by norm_num)
    have hm : ContDiff ℝ 1 (fun y : κ → ℝ => (y, evec i)) := by fun_prop
    change ContDiff ℝ 1 (fun y => (fderiv ℝ p y) (evec i))
    exact h.comp hm
  have hDiCompact (i : κ) : HasCompactSupport (Di i) :=
    HasCompactSupport.fderiv_apply (𝕜 := ℝ) hpc (evec i)
  have hgiC (i : κ) : ContDiff ℝ 1 (gi i) := by
    change ContDiff ℝ 1 (Di i ∘ T)
    exact (hDiC i).comp (by fun_prop)
  have hgiCompact (i : κ) : HasCompactSupport (gi i) := by
    change HasCompactSupport (Di i ∘ T)
    rw [hT]
    exact (hDiCompact i).comp_isClosedEmbedding
      (gaussianAffineHomeomorph x a ha0).isClosedEmbedding
  have htermInt (i : κ) : Integrable (fun z => z i * gi i z) μ := by
    have hcompact : HasCompactSupport (fun z => z i * gi i z) :=
      (hgiCompact i).mul_left
    have hcontinuous : Continuous (fun z : κ → ℝ => z i * gi i z) := by fun_prop
    exact hcontinuous.integrable_of_hasCompactSupport hcompact
  have hsumInt : Integrable (fun z : κ → ℝ => ∑ i, z i * gi i z) μ :=
    integrable_finset_sum (Finset.univ) (fun i hi => htermInt i)
  have htime := hasDerivAt_gaussianHeat_time_of_contDiff_compactSupport
    p hp hpc x t ht
  have hvector (z : κ → ℝ) : z = ∑ i, z i • evec i := by
    ext j
    simp [evec, Pi.single_apply, Finset.sum_ite_eq']
  have hpoint (z : κ → ℝ) :
      fderiv ℝ p (T z) ((2 * a)⁻¹ • z) =
        (2 * a)⁻¹ * ∑ i, z i * gi i z := by
    let L := fderiv ℝ p (T z)
    have hlin : L z = ∑ i, z i * L (evec i) := by
      calc
        L z = L (∑ i, z i • evec i) := congrArg L (hvector z)
        _ = ∑ i, z i * L (evec i) := by simp [map_sum, map_smul, smul_eq_mul]
    change L ((2 * a)⁻¹ • z) = (2 * a)⁻¹ * ∑ i, z i * gi i z
    rw [map_smul, hlin]
    simp [L, gi, Di, evec, mul_comm]
  have htimeIntegral :
      (∫ z, fderiv ℝ p (x + a • z) ((2 * a)⁻¹ • z) ∂μ) =
        (2 * a)⁻¹ * ∑ i, ∫ z, z i * gi i z ∂μ := by
    calc
      _ = ∫ z, (2 * a)⁻¹ * (∑ i, z i * gi i z) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact hpoint z
      _ = (2 * a)⁻¹ * ∫ z, ∑ i, z i * gi i z ∂μ := integral_const_mul _ _
      _ = (2 * a)⁻¹ * ∑ i, ∫ z, z i * gi i z ∂μ := by
        rw [integral_finset_sum Finset.univ (fun i hi => htermInt i)]
  have htrace (i : κ) :
      (∫ z, z i * gi i z ∂μ) = a * ∫ z, fderiv ℝ (Di i) (T z) (evec i) ∂μ := by
    have hchain (z : κ → ℝ) :
        fderiv ℝ (gi i) z (evec i) = a * fderiv ℝ (Di i) (T z) (evec i) := by
      change fderiv ℝ (Di i ∘ T) z (evec i) = _
      rw [fderiv_comp (f := T) (x := z) (g := Di i)
        ((hDiC i).differentiable (by norm_num) (T z)) (by fun_prop)]
      have hTf : fderiv ℝ T z = a • ContinuousLinearMap.id ℝ (κ → ℝ) := by
        have hlin : HasFDerivAt (fun y : κ → ℝ => a • y)
            (a • ContinuousLinearMap.id ℝ (κ → ℝ)) z := by
          have hlin0 := (a • ContinuousLinearMap.id ℝ (κ → ℝ)).hasFDerivAt (x := z)
          convert hlin0 using 1
          ext y
          simp [ContinuousLinearMap.smul_apply]
        have hTderiv : HasFDerivAt T
            (a • ContinuousLinearMap.id ℝ (κ → ℝ)) z := by
          convert hlin.const_add x using 1 <;> simp [T]
        exact hTderiv.fderiv
      rw [hTf]
      simp [ContinuousLinearMap.comp_apply, evec]
    calc
      _ = ∫ z, fderiv ℝ (gi i) z (evec i) ∂μ :=
        integral_coordinate_mul_eq_integral_fderiv (gi i) (hgiC i)
          (hgiCompact i) i
      _ = ∫ z, a * fderiv ℝ (Di i) (T z) (evec i) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with z
        exact hchain z
      _ = a * ∫ z, fderiv ℝ (Di i) (T z) (evec i) ∂μ := integral_const_mul _ _
  have hsumtrace :
      (2 * a)⁻¹ * ∑ i, ∫ z, z i * gi i z ∂μ =
        (1 / 2) * ∑ i, ∫ z, fderiv ℝ (Di i) (T z) (evec i) ∂μ := by
    calc
      _ = ∑ i, (2 * a)⁻¹ * ∫ z, z i * gi i z ∂μ := by rw [Finset.mul_sum]
      _ = ∑ i, (1 / 2) * ∫ z, fderiv ℝ (Di i) (T z) (evec i) ∂μ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [htrace i]
        field_simp [ha0]
      _ = _ := by rw [Finset.mul_sum]
  have hderivEq :
      (∫ z, fderiv ℝ p (x + a • z) ((2 * a)⁻¹ • z) ∂μ) =
        (1 / 2) * ∑ i, ∫ z, fderiv ℝ (Di i) (T z) (evec i) ∂μ :=
    htimeIntegral.trans hsumtrace
  simpa [gaussianHeat, μ, a, Di, evec, T] using htime.congr_deriv hderivEq

end BrownianSharp
