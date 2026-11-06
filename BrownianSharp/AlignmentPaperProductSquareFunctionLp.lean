import BrownianSharp.AlignmentPaperSignedKernelSquareLp
import BrownianSharp.AlignmentPaperSignedKernelLp
import BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel
import Mathlib.Analysis.Convolution
import Mathlib.Tactic

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace BrownianSharp.AlignmentPaperProductSquareFunctionLp

open BrownianSharp.AlignmentPaperSignedKernelOperator
open BrownianSharp.AlignmentPaperSignedKernelSquareLp
open BrownianSharp.AlignmentPaperSignedKernelLp
open BrownianSharp.AlignmentPeriodicAdmissibleCutoff
open BrownianSharp.AlignmentPeriodicAdmissibleCutoffTensorKernel
open BrownianSharp.Torus
open UnitAddTorus

local instance productSquareMeasureSpace : ∀ d, MeasureSpace (UnitAddTorus (Fin d)) :=
  fun d => ⟨Measure.pi fun _ : Fin d => AddCircle.haarAddCircle⟩
local instance productSquareProbability : ∀ d,
    IsProbabilityMeasure (volume : Measure (UnitAddTorus (Fin d))) := by
  intro d
  change IsProbabilityMeasure
    (Measure.pi fun _ : Fin d => (AddCircle.haarAddCircle : Measure UnitAddCircle))
  infer_instance

/-- Split the first coordinate from the remaining coordinates of a finite
torus, in the measure-theoretic form used by the tensor iteration. -/
def productTorusSplit (d : ℕ) :
    MeasurableEquiv (UnitAddTorus (Fin (d+1)))
      (UnitAddCircle × UnitAddTorus (Fin d)) :=
  MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d+1) => UnitAddCircle) 0

theorem productTorusSplit_measurePreserving (d : ℕ) :
    MeasurePreserving (productTorusSplit d)
      (Measure.pi fun _ : Fin (d+1) => AddCircle.haarAddCircle)
      ((AddCircle.haarAddCircle).prod
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) := by
  exact MeasureTheory.measurePreserving_piFinSuccAbove
    (fun _ : Fin (d+1) => (AddCircle.haarAddCircle : Measure UnitAddCircle))
    (0 : Fin (d+1))

/-- The same coordinate split is a homeomorphism for the product topology. -/
def productTorusSplitHomeomorph (d : ℕ) :
    Homeomorph (UnitAddTorus (Fin (d+1)))
      (UnitAddCircle × UnitAddTorus (Fin d)) where
  toEquiv := (productTorusSplit d).toEquiv
  continuous_toFun := by
    change Continuous (fun x : UnitAddTorus (Fin (d+1)) =>
      (x 0, fun i : Fin d => x (Fin.succAbove 0 i)))
    exact (continuous_apply 0).prodMk
      (continuous_pi fun i => continuous_apply (Fin.succAbove 0 i))
  continuous_invFun := by
    apply continuous_pi
    intro i
    by_cases hi : i = 0
    · subst i
      simp [productTorusSplit]
      exact continuous_fst
    · obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hi
      rw [← hj]
      change Continuous (fun a : UnitAddCircle × UnitAddTorus (Fin d) => a.2 j)
      exact (continuous_apply j).comp continuous_snd

/-- Fubini for the first-coordinate splitting of the product circle. -/
theorem integral_productTorusSplit_eq_iterated {d : ℕ}
    (f : UnitAddTorus (Fin (d+1)) → ℂ)
    (hf : Integrable f (Measure.pi fun _ : Fin (d+1) => AddCircle.haarAddCircle)) :
    (∫ x, f x ∂(Measure.pi fun _ : Fin (d+1) => AddCircle.haarAddCircle)) =
      ∫ u : UnitAddCircle, ∫ v : UnitAddTorus (Fin d),
        f ((productTorusSplit d).symm (u,v))
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
          ∂(AddCircle.haarAddCircle) := by
  let e := productTorusSplit d
  let ν : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  have hMP := productTorusSplit_measurePreserving d
  have hcomp : Integrable (fun z : UnitAddCircle × UnitAddTorus (Fin d) =>
      f (e.symm z)) ((AddCircle.haarAddCircle).prod ν) :=
    hMP.symm.integrable_comp_of_integrable hf
  have hfmap : AEStronglyMeasurable f
      (Measure.map e.symm ((AddCircle.haarAddCircle).prod ν)) := by
    rw [hMP.symm.map_eq]
    exact hf.aestronglyMeasurable
  calc
    _ = ∫ z : UnitAddCircle × UnitAddTorus (Fin d),
        f (e.symm z) ∂((AddCircle.haarAddCircle).prod ν) := by
          rw [← hMP.symm.map_eq]
          exact integral_map e.symm.measurable.aemeasurable hfmap
    _ = ∫ u : UnitAddCircle, ∫ v : UnitAddTorus (Fin d),
        f (e.symm (u,v)) ∂ν ∂(AddCircle.haarAddCircle) :=
          integral_prod _ hcomp

/-- Tonelli/Fubini for nonnegative measurable functions under the product
torus split. -/
theorem lintegral_productTorusSplit_eq_iterated {d : ℕ}
    (F : UnitAddTorus (Fin (d+1)) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂(Measure.pi fun _ : Fin (d+1) => AddCircle.haarAddCircle)) =
      ∫⁻ u : UnitAddCircle, ∫⁻ v : UnitAddTorus (Fin d),
        F ((productTorusSplit d).symm (u,v))
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
          ∂(AddCircle.haarAddCircle) := by
  let e := productTorusSplit d
  let ν : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  let ρ := (AddCircle.haarAddCircle : Measure UnitAddCircle).prod ν
  have hMP := productTorusSplit_measurePreserving d
  have hcomp : Measurable (fun q : UnitAddCircle × UnitAddTorus (Fin d) =>
      F (e.symm q)) := hF.comp e.symm.measurable
  calc
    _ = ∫⁻ q : UnitAddCircle × UnitAddTorus (Fin d), F (e.symm q) ∂ρ := by
      symm
      exact hMP.symm.lintegral_comp hF
    _ = ∫⁻ u : UnitAddCircle, ∫⁻ v : UnitAddTorus (Fin d),
        F (e.symm (u,v)) ∂ν ∂(AddCircle.haarAddCircle) :=
      MeasureTheory.lintegral_prod _ hcomp.aemeasurable

/-- The same Tonelli formula with the tail coordinates integrated first. -/
theorem lintegral_productTorusSplit_eq_iterated_tail_first {d : ℕ}
    (F : UnitAddTorus (Fin (d+1)) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, F x ∂(Measure.pi fun _ : Fin (d+1) => AddCircle.haarAddCircle)) =
      ∫⁻ z : UnitAddTorus (Fin d), ∫⁻ u : UnitAddCircle,
        F ((productTorusSplit d).symm (u,z))
          ∂(AddCircle.haarAddCircle)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  let e := productTorusSplit d
  let ν : Measure (UnitAddTorus (Fin d)) :=
    Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
  let ρ := (AddCircle.haarAddCircle : Measure UnitAddCircle).prod ν
  have hMP := productTorusSplit_measurePreserving d
  have hcomp : Measurable (fun q : UnitAddCircle × UnitAddTorus (Fin d) =>
      F (e.symm q)) := hF.comp e.symm.measurable
  calc
    _ = ∫⁻ q : UnitAddCircle × UnitAddTorus (Fin d), F (e.symm q) ∂ρ := by
      symm
      exact hMP.symm.lintegral_comp hF
    _ = ∫⁻ z : UnitAddTorus (Fin d), ∫⁻ u : UnitAddCircle,
        F (e.symm (u,z)) ∂(AddCircle.haarAddCircle) ∂ν :=
      MeasureTheory.lintegral_prod_symm _ hcomp.aemeasurable

/-- Integrating a jointly continuous function over a compact finite-measure
space gives a continuous function of the remaining parameter. -/
theorem continuous_integral_parameter
    {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [CompactSpace X] [MeasurableSpace Y] [OpensMeasurableSpace Y] [CompactSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Y) [IsFiniteMeasureOnCompacts μ]
    (F : C(X × Y, E)) :
    Continuous (fun x : X => ∫ y, F (x,y) ∂μ) := by
  let G : C(Y, C(X,E)) := (F.comp ContinuousMap.prodSwap).curry
  have hG : Integrable G μ :=
    G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace G)
  let H : C(X,E) := ∫ y, G y ∂μ
  have hEq (x : X) : H x = ∫ y, F (x,y) ∂μ := by
    change (∫ y, G y ∂μ) x = ∫ y, F (x,y) ∂μ
    rw [ContinuousMap.integral_apply hG x]
    simp [G, ContinuousMap.curry_apply, ContinuousMap.comp_apply,
      ContinuousMap.prodSwap]
  exact H.continuous.congr hEq

/-- Actual product smooth block, written as convolution against the tensor
product of the one-dimensional smooth block kernels. -/
def productSmoothBlockConvolution {d : ℕ} (s : Fin d → ℕ)
    (f : UnitAddTorus (Fin d) → ℂ) (x : UnitAddTorus (Fin d)) : ℂ :=
  ∫ y : UnitAddTorus (Fin d),
    admissibleBlockKernel smoothResolutionCutoff s (x-y) * f y
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)

/-- One-coordinate smooth block acting on sections of a product function. -/
def sectionSmoothBlockConvolution {β : Type*} (s : ℕ)
    (g : UnitAddCircle × β → ℂ) (x : UnitAddCircle) (z : β) : ℂ :=
  ∫ y : UnitAddCircle,
    scalarBlockKernel smoothResolutionCutoff s (x-y) * g (y,z)
      ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)

/-- Hilbert-family version of the sectionwise coordinate estimate. It is the
dimension-free step needed when the remaining coordinates are indexed by
their finite dyadic scales. -/
theorem circleSmoothSquareFunction_family_sections_lintegral_lp_le_of_weak_one
    {β : Type*} [MeasurableSpace β] (ν : Measure β) [SFinite ν]
    (N m : ℕ) {Cw p : ℝ} (hCw : 0 ≤ Cw) (hp1 : 1 < p) (hp2 : p < 2)
    (hweak : ∀ (ε : Fin (N+1) → ℝ), (∀ s, |ε s| ≤ 1) →
      ∀ f, Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle) →
        ∀ t > 0,
          (AddCircle.haarAddCircle : Measure UnitAddCircle)
              {y | t < ‖circleSignedConvolutionOperator N ε f y‖} ≤
            ENNReal.ofReal (Cw/t) *
              ∫⁻ x, ENNReal.ofReal (‖f x‖)
                ∂(AddCircle.haarAddCircle : Measure UnitAddCircle))
    (g : Fin m → UnitAddCircle × β → ℂ)
    (hg : ∀ i, Measurable (g i))
    (hsections : ∀ i, ∀ᵐ z ∂ν,
      MemLp (fun x : UnitAddCircle => g i (x,z)) (ENNReal.ofReal p)
        (AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    ∫⁻ z : β, ∫⁻ x : UnitAddCircle,
      ENNReal.ofReal ((∑ i : Fin m, ∑ s : Fin (N+1),
        ‖sectionSmoothBlockConvolution s.val (g i) x z‖^2)^(p/2))
        ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) ∂ν ≤
      ENNReal.ofReal ((24*(2:ℝ)^(p/2))^2 *
        (2^p*(p*Cw/(p-1)+p/(2-p)))) *
      ∫⁻ z : β, ∫⁻ x : UnitAddCircle,
        ENNReal.ofReal ((∑ i : Fin m, ‖g i (x,z)‖^2)^(p/2))
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) ∂ν := by
  classical
  let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
  let H : UnitAddCircle × β → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((∑ i : Fin m, ∑ s : Fin (N+1),
      ‖sectionSmoothBlockConvolution s.val (g i) q.1 q.2‖^2)^(p/2))
  let F : UnitAddCircle × β → ℝ≥0∞ := fun q =>
    ENNReal.ofReal ((∑ i : Fin m, ‖g i q‖^2)^(p/2))
  have hconvMeas : ∀ i : Fin m, ∀ s : Fin (N+1),
      Measurable (fun q : UnitAddCircle × β =>
        sectionSmoothBlockConvolution s.val (g i) q.1 q.2) := by
    intro i s
    have hjoint : Measurable (fun r : (UnitAddCircle × β) × UnitAddCircle =>
        scalarBlockKernel smoothResolutionCutoff s.val (r.1.1-r.2) *
          g i (r.2,r.1.2)) := by fun_prop
    have hsm := hjoint.stronglyMeasurable.integral_prod_right'
      (ν := (AddCircle.haarAddCircle : Measure UnitAddCircle))
    simpa [sectionSmoothBlockConvolution, Function.uncurry] using hsm.measurable
  have hHmeas : Measurable H := by dsimp [H]; fun_prop
  have hFmeas : Measurable F := by dsimp [F]; fun_prop
  have hpoint : ∀ᵐ z ∂ν,
      (∫⁻ x : UnitAddCircle,
        ENNReal.ofReal ((∑ i : Fin m, ∑ s : Fin (N+1),
          ‖sectionSmoothBlockConvolution s.val (g i) x z‖^2)^(p/2)) ∂μ) ≤
        ENNReal.ofReal ((24*(2:ℝ)^(p/2))^2 *
          (2^p*(p*Cw/(p-1)+p/(2-p)))) *
          (∫⁻ x : UnitAddCircle,
            ENNReal.ofReal ((∑ i : Fin m, ‖g i (x,z)‖^2)^(p/2)) ∂μ) := by
    have hall : ∀ᵐ z ∂ν, ∀ i : Fin m,
        MemLp (fun x : UnitAddCircle => g i (x,z))
          (ENNReal.ofReal p) (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
      rw [ae_all_iff]
      exact hsections
    filter_upwards [hall] with z hz
    let v : Fin m → Lp ℂ (ENNReal.ofReal p) μ :=
      fun i => (hz i).toLp (fun x => g i (x,z))
    have hv : ∀ i, (v i : UnitAddCircle → ℂ) =ᵐ[μ] fun x => g i (x,z) := by
      intro i
      exact MemLp.coeFn_toLp (hz i)
    have hsf := circleSmoothSquareFunction_vector_lintegral_lp_le_of_weak_one
      N m hCw hp1 hp2
      (by
        intro ε hε f hf t ht
        exact hweak ε hε f hf t ht) v
    have hblock (i : Fin m) (s : Fin (N+1)) (x : UnitAddCircle) :
        circleSmoothBlockConvolution s.val (v i) x =
          sectionSmoothBlockConvolution s.val (g i) x z := by
      unfold circleSmoothBlockConvolution sectionSmoothBlockConvolution
      apply integral_congr_ae
      filter_upwards [hv i] with y hy
      rw [hy]
    have hleft : (∫⁻ x : UnitAddCircle,
        ENNReal.ofReal ((∑ i : Fin m, ∑ s : Fin (N+1),
          ‖sectionSmoothBlockConvolution s.val (g i) x z‖^2)^(p/2)) ∂μ) =
        ∫⁻ x, ENNReal.ofReal ((∑ i : Fin m, ∑ s : Fin (N+1),
          ‖circleSmoothBlockConvolution s.val (v i) x‖^2)^(p/2)) ∂μ := by
      apply lintegral_congr
      intro x
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro s hs
      rw [hblock i s x]
    have hright : (∫⁻ x : UnitAddCircle,
        ENNReal.ofReal ((∑ i : Fin m, ‖g i (x,z)‖^2)^(p/2)) ∂μ) =
        ∫⁻ x, ENNReal.ofReal ((∑ i : Fin m, ‖v i x‖^2)^(p/2)) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_all_iff.2 hv] with x hx
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      rw [hx i]
    rw [hleft, hright]
    simpa using hsf
  have hcalc :
      (∫⁻ z : β, ∫⁻ x : UnitAddCircle, H (x,z) ∂μ ∂ν) ≤
        ENNReal.ofReal ((24*(2:ℝ)^(p/2))^2 *
          (2^p*(p*Cw/(p-1)+p/(2-p)))) *
          (∫⁻ z : β, ∫⁻ x : UnitAddCircle, F (x,z) ∂μ ∂ν) := by
    calc
      _ ≤ ∫⁻ z, ENNReal.ofReal ((24*(2:ℝ)^(p/2))^2 *
          (2^p*(p*Cw/(p-1)+p/(2-p)))) *
          (∫⁻ x, F (x,z) ∂μ) ∂ν := by
            apply lintegral_mono_ae
            filter_upwards [hpoint] with z hz
            simpa [H, F] using hz
      _ = ENNReal.ofReal ((24*(2:ℝ)^(p/2))^2 *
          (2^p*(p*Cw/(p-1)+p/(2-p)))) *
          (∫⁻ z, ∫⁻ x, F (x,z) ∂μ ∂ν) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  simpa [H, F, μ] using hcalc

/-- The product kernel factorization used by coordinate iteration. -/
theorem productSmoothBlockKernel_eq_coordinateProduct {d : ℕ} (s : Fin d → ℕ) :
    admissibleBlockKernel smoothResolutionCutoff s =
      BrownianSharp.coordinateProductKernel
        (fun i : Fin d => scalarBlockKernel smoothResolutionCutoff (s i)) :=
  admissibleBlockKernel_eq_product smoothResolutionCutoff s

private lemma productSmoothBlockKernel_bdd {d : ℕ} (s : Fin d → ℕ) :
    BddAbove (Set.range fun y : UnitAddTorus (Fin d) =>
      ‖admissibleBlockKernel smoothResolutionCutoff s y‖) := by
  have hc : IsCompact
      ((fun y : UnitAddTorus (Fin d) =>
        ‖admissibleBlockKernel smoothResolutionCutoff s y‖) '' Set.univ) :=
    isCompact_univ.image (admissibleBlockKernel smoothResolutionCutoff s).continuous.norm
  rw [← Set.image_univ]
  exact hc.bddAbove

private lemma productSmoothBlockConvolution_integrand_integrable {d : ℕ}
    (s : Fin d → ℕ) {f : UnitAddTorus (Fin d) → ℂ}
    (hf : Integrable f (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
    (x : UnitAddTorus (Fin d)) :
    Integrable (fun y : UnitAddTorus (Fin d) =>
      admissibleBlockKernel smoothResolutionCutoff s (x-y) * f y)
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  rcases productSmoothBlockKernel_bdd s with ⟨M,hM⟩
  apply hf.bdd_mul (by fun_prop)
  filter_upwards with y
  exact hM ⟨x-y,rfl⟩

/-- Finite actual tensor smooth-block square function at depth `N`. -/
def productSmoothSquareFunction {d : ℕ} (N : ℕ)
    (f : UnitAddTorus (Fin d) → ℂ) (x : UnitAddTorus (Fin d)) : ℝ :=
  (∑ s : Fin d → Fin (N+1),
    ‖productSmoothBlockConvolution (fun i => (s i).val) f x‖^2)^(1/2)

/-- Iterated coordinate realization of a product smooth block. The first
coordinate is applied outside the recursively formed tail block. -/
def iteratedProductBlock :
    ∀ (d : ℕ), (Fin d → ℕ) → (UnitAddTorus (Fin d) → ℂ) →
      UnitAddTorus (Fin d) → ℂ
  | 0, _, f, x => f x
  | d+1, s, f, x =>
      let e := productTorusSplit d
      let q := e x
      ∫ y : UnitAddCircle,
        scalarBlockKernel smoothResolutionCutoff (s 0) (q.1-y) *
          iteratedProductBlock d (fun i => s i.succ)
            (fun z => f (e.symm (y,z))) q.2
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)

/-- The first-coordinate section action is exactly the recursive product block
with that coordinate inserted before the tail scales. -/
theorem iteratedProductBlock_succ_eq_sectionSmoothBlockConvolution
    {d : ℕ} (s₀ : ℕ) (st : Fin d → ℕ)
    (f : UnitAddTorus (Fin (d+1)) → ℂ)
    (x : UnitAddTorus (Fin (d+1))) :
    iteratedProductBlock (d+1) (Fin.cons s₀ st) f x =
      sectionSmoothBlockConvolution s₀
        (fun q : UnitAddCircle × UnitAddTorus (Fin d) =>
          iteratedProductBlock d st
            (fun z => f ((productTorusSplit d).symm (q.1,z))) q.2)
        (productTorusSplit d x).1 (productTorusSplit d x).2 := by
  simp [iteratedProductBlock, sectionSmoothBlockConvolution,
    Fin.cons]

/-- Reindex the tensor square sum by first scale and tail scale. -/
theorem iteratedProductBlock_succ_square_sum_eq_family
    {d N : ℕ} (f : UnitAddTorus (Fin (d+1)) → ℂ)
    (x : UnitAddTorus (Fin (d+1))) :
    (∑ t : (Fin (d+1) → Fin (N+1)),
      ‖iteratedProductBlock (d+1) (fun j => (t j).val) f x‖^2) =
      (∑ i : Fin (Fintype.card (Fin d → Fin (N+1))),
        ∑ s₀ : Fin (N+1),
          ‖sectionSmoothBlockConvolution s₀.val
            (fun q : UnitAddCircle × UnitAddTorus (Fin d) =>
              iteratedProductBlock d (fun j =>
                (((Fintype.equivFin (Fin d → Fin (N+1))).symm i) j).val)
                (fun z => f ((productTorusSplit d).symm (q.1,z))) q.2)
            (productTorusSplit d x).1 (productTorusSplit d x).2‖^2) := by
  classical
  let α := Fin d → Fin (N+1)
  let E : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let R : Fin (N+1) × α ≃ (Fin (d+1) → Fin (N+1)) :=
    Fin.consEquiv (fun _ : Fin (d+1) => Fin (N+1))
  let H : (Fin (d+1) → Fin (N+1)) → ℝ := fun t =>
    ‖iteratedProductBlock (d+1) (fun j => (t j).val) f x‖^2
  let J : Fin (Fintype.card α) → Fin (N+1) → ℝ := fun i s₀ =>
    ‖sectionSmoothBlockConvolution s₀.val
      (fun q : UnitAddCircle × UnitAddTorus (Fin d) =>
        iteratedProductBlock d (fun j => (E.symm i j).val)
          (fun z => f ((productTorusSplit d).symm (q.1,z))) q.2)
      (productTorusSplit d x).1 (productTorusSplit d x).2‖^2
  calc
    _ = ∑ q : Fin (N+1) × α, H (R q) :=
      (Equiv.sum_comp R H).symm
    _ = ∑ a : α, ∑ s₀ : Fin (N+1), H (R (s₀,a)) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ i : Fin (Fintype.card α), ∑ s₀ : Fin (N+1),
          H (R (s₀,E.symm i)) := by
      rw [← Equiv.sum_comp E.symm]
    _ = ∑ i : Fin (Fintype.card α), ∑ s₀ : Fin (N+1), J i s₀ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro s₀ hs
      change ‖iteratedProductBlock (d+1)
          (fun j => (R (s₀,E.symm i) j).val) f x‖^2 =
        ‖sectionSmoothBlockConvolution s₀.val
          (fun q : UnitAddCircle × UnitAddTorus (Fin d) =>
            iteratedProductBlock d (fun j => (E.symm i j).val)
              (fun z => f ((productTorusSplit d).symm (q.1,z))) q.2)
          (productTorusSplit d x).1 (productTorusSplit d x).2‖^2
      have hscale : (fun j => (R (s₀,E.symm i) j).val) =
          Fin.cons s₀.val (fun j => (E.symm i j).val) := by
        funext j
        refine Fin.cases ?_ ?_ j
        · change (Fin.cons (α := fun _ : Fin (d+1) => Fin (N+1))
            s₀ (E.symm i) 0).val = s₀.val
          simp [Fin.cons_zero]
        · intro j
          change (Fin.cons (α := fun _ : Fin (d+1) => Fin (N+1))
            s₀ (E.symm i) j.succ).val = (E.symm i j).val
          simp [Fin.cons_succ]
      have hblock := iteratedProductBlock_succ_eq_sectionSmoothBlockConvolution
        s₀.val (fun j => (E.symm i j).val) f x
      rw [hscale]
      exact congrArg (fun z : ℂ => ‖z‖^2) hblock
    _ = _ := by
      simp [H, J, α, E, Fintype.equivFin]

/-- Tail-scale square sums are unchanged when the tail scale family is
enumerated by `Fin (card ...)`. -/
theorem iteratedProductBlock_square_sum_eq_fin_family {d N : ℕ}
    (f : UnitAddTorus (Fin d) → ℂ) (x : UnitAddTorus (Fin d)) :
    (∑ i : Fin (Fintype.card (Fin d → Fin (N+1))),
      ‖iteratedProductBlock d
        (fun j => ((Fintype.equivFin (Fin d → Fin (N+1))).symm i j).val) f x‖^2) =
    (∑ s : Fin d → Fin (N+1),
      ‖iteratedProductBlock d (fun j => (s j).val) f x‖^2) := by
  classical
  let α := Fin d → Fin (N+1)
  let E : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  change (∑ i : Fin (Fintype.card α),
      ‖iteratedProductBlock d (fun j => (E.symm i j).val) f x‖^2) = _
  exact Equiv.sum_comp E.symm
    (fun s : α => ‖iteratedProductBlock d (fun j => (s j).val) f x‖^2)

/-- The p-moment integrand for the iterated tensor square function, written
without square roots. -/
def iteratedProductSquareMoment {d : ℕ} (N : ℕ) (p : ℝ)
    (f : UnitAddTorus (Fin d) → ℂ) (x : UnitAddTorus (Fin d)) : ℝ :=
  (∑ s : Fin d → Fin (N+1),
    ‖iteratedProductBlock d (fun i => (s i).val) f x‖^2)^(p/2)

/-- In zero coordinates the finite square function consists of the source
itself. -/
theorem iteratedProductSquareMoment_zero {p : ℝ}
    (f : UnitAddTorus (Fin 0) → ℂ) (x : UnitAddTorus (Fin 0)) :
    iteratedProductSquareMoment 0 p f x = ‖f x‖^p := by
  simp only [iteratedProductSquareMoment, iteratedProductBlock]
  simp
  rw [← Real.rpow_natCast (‖f x‖) 2]
  rw [← Real.rpow_mul (norm_nonneg (f x)) (↑(2:ℕ):ℝ) (p/2)]
  congr 1
  ring

/-- A continuous circle function belongs to every finite Lp space. -/
theorem circleContinuous_memLp (g : C(UnitAddCircle,ℂ)) (p : ℝ≥0∞) :
    MemLp g p (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  have hc : IsCompact ((fun x : UnitAddCircle => ‖g x‖) '' Set.univ) :=
    isCompact_univ.image g.continuous.norm
  rcases hc.bddAbove with ⟨M,hM⟩
  apply MemLp.of_bound g.continuous.aestronglyMeasurable M
  filter_upwards with x
  have hm : ‖g x‖ ∈ (fun x : UnitAddCircle => ‖g x‖) '' Set.univ :=
    ⟨x,Set.mem_univ x,rfl⟩
  exact hM hm

/-- Applying any finite sequence of coordinate blocks to a continuous source
preserves joint continuity in auxiliary parameters and the output point. -/
theorem iteratedProductBlock_continuous_param
    {β : Type*} [TopologicalSpace β] [CompactSpace β] :
    ∀ (d : ℕ) (s : Fin d → ℕ)
      (F : C(β × UnitAddTorus (Fin d), ℂ)),
      Continuous (fun q : β × UnitAddTorus (Fin d) =>
        iteratedProductBlock d s (fun z => F (q.1,z)) q.2) := by
  intro d
  induction d generalizing β with
  | zero =>
      intro s F
      simpa [iteratedProductBlock] using F.continuous
  | succ d ih =>
      intro s F
      let e := productTorusSplitHomeomorph d
      have he : Continuous fun x : UnitAddTorus (Fin (d+1)) => e x := e.continuous
      have hes : Continuous fun z : UnitAddCircle × UnitAddTorus (Fin d) => e.symm z :=
        e.symm.continuous
      let Ftail : C((β × UnitAddCircle) × UnitAddTorus (Fin d), ℂ) :=
        { toFun := fun q => F (q.1.1, e.symm (q.1.2,q.2))
          continuous_toFun := by fun_prop }
      have htail := ih (β := β × UnitAddCircle) (fun i => s i.succ) Ftail
      let G : C((β × UnitAddTorus (Fin (d+1))) × UnitAddCircle, ℂ) :=
        { toFun := fun q =>
            scalarBlockKernel smoothResolutionCutoff (s 0)
              ((e q.1.2).1-q.2) *
              iteratedProductBlock d (fun i => s i.succ)
                (fun z => F (q.1.1,e.symm (q.2,z))) (e q.1.2).2
          continuous_toFun := by
            have htail' : Continuous (fun q : (β × UnitAddCircle) ×
                UnitAddTorus (Fin d) =>
                iteratedProductBlock d (fun i => s i.succ)
                  (fun z => F (q.1.1,e.symm (q.1.2,z))) q.2) := by
              simpa [Ftail] using htail
            have hk : Continuous (fun q : (β × UnitAddTorus (Fin (d+1))) ×
                UnitAddCircle =>
                scalarBlockKernel smoothResolutionCutoff (s 0)
                  ((e q.1.2).1-q.2)) := by
              exact (scalarBlockKernel smoothResolutionCutoff (s 0)).continuous.comp
                (by fun_prop)
            have ht : Continuous (fun q : (β × UnitAddTorus (Fin (d+1))) ×
                UnitAddCircle =>
                iteratedProductBlock d (fun i => s i.succ)
                  (fun z => F (q.1.1,e.symm (q.2,z))) (e q.1.2).2) := by
              have hmap : Continuous (fun q : (β × UnitAddTorus (Fin (d+1))) ×
                  UnitAddCircle => ((q.1.1,q.2),(e q.1.2).2)) := by fun_prop
              have h := htail'.comp hmap
              change Continuous (fun q : (β × UnitAddTorus (Fin (d+1))) ×
                UnitAddCircle =>
                iteratedProductBlock d (fun i => s i.succ)
                  (fun z => F (q.1.1,e.symm (q.2,z))) (e q.1.2).2)
              exact h
            exact hk.mul ht }
      have hcont := continuous_integral_parameter
        (μ := (AddCircle.haarAddCircle : Measure UnitAddCircle)) G
      simpa [iteratedProductBlock, e, productTorusSplitHomeomorph,
        productTorusSplit, G] using hcont

/-- Tail block sources for the first-coordinate induction are jointly
continuous whenever the original source is continuous. -/
theorem iteratedTailFamily_continuous {d N : ℕ}
    (f : C(UnitAddTorus (Fin (d+1)),ℂ))
    (i : Fin (Fintype.card (Fin d → Fin (N+1)))) :
    Continuous (fun q : UnitAddCircle × UnitAddTorus (Fin d) =>
      iteratedProductBlock d
        (fun j => (((Fintype.equivFin (Fin d → Fin (N+1))).symm i) j).val)
        (fun z => f ((productTorusSplit d).symm (q.1,z))) q.2) := by
  let e := productTorusSplitHomeomorph d
  let F : C(UnitAddCircle × UnitAddTorus (Fin d),ℂ) :=
    { toFun := fun q => f (e.symm q)
      continuous_toFun := f.continuous.comp e.symm.continuous }
  have h := iteratedProductBlock_continuous_param d
    (fun j => (((Fintype.equivFin (Fin d → Fin (N+1))).symm i) j).val) F
  simpa [F, e, productTorusSplitHomeomorph, productTorusSplit] using h

/-- Every first-coordinate section of a continuous tail block is in Lp. -/
theorem iteratedTailFamily_sections_memLp {d N : ℕ} {p : ℝ≥0∞}
    (f : C(UnitAddTorus (Fin (d+1)),ℂ)) :
    ∀ i : Fin (Fintype.card (Fin d → Fin (N+1))),
      ∀ᵐ z : UnitAddTorus (Fin d)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle),
        MemLp (fun x : UnitAddCircle =>
          iteratedProductBlock d
            (fun j => (((Fintype.equivFin (Fin d → Fin (N+1))).symm i) j).val)
            (fun w => f ((productTorusSplit d).symm (x,w))) z)
          p (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
  intro i
  filter_upwards with z
  let g : C(UnitAddCircle,ℂ) :=
    { toFun := fun x => iteratedProductBlock d
        (fun j => (((Fintype.equivFin (Fin d → Fin (N+1))).symm i) j).val)
        (fun w => f ((productTorusSplit d).symm (x,w))) z
      continuous_toFun := by
        have h := iteratedTailFamily_continuous f i
        exact h.comp (continuous_id.prodMk continuous_const) }
  exact circleContinuous_memLp g p

/-- Measurability of the nonnegative square-function p-moment for continuous
sources. -/
theorem iteratedProductSquareMoment_measurable {d N : ℕ} {p : ℝ}
    (f : C(UnitAddTorus (Fin d),ℂ)) :
    Measurable (fun x => ENNReal.ofReal (iteratedProductSquareMoment N p f x)) := by
  classical
  let F : C(Unit × UnitAddTorus (Fin d),ℂ) :=
    { toFun := fun q => f q.2
      continuous_toFun := f.continuous.comp continuous_snd }
  have hblock (s : Fin d → Fin (N+1)) :
      Continuous (fun x : UnitAddTorus (Fin d) =>
        iteratedProductBlock d (fun i => (s i).val) f x) := by
    have h := iteratedProductBlock_continuous_param d
      (fun i => (s i).val) F
    have hmap : Continuous (fun x : UnitAddTorus (Fin d) => (Unit.unit,x)) :=
      continuous_const.prodMk continuous_id
    have h' := h.comp hmap
    convert h' using 1
    funext x
    simp [F]
  dsimp [iteratedProductSquareMoment]
  fun_prop

/-- Tensorization of the actual smooth-block square function for continuous
sources. The bound is uniform in the block depth; each coordinate contributes
the one-dimensional finite-family constant. -/
theorem iteratedProductSquareMoment_lintegral_le_of_weak_one
    (N : ℕ) {Cw p : ℝ} (hCw : 0 ≤ Cw) (hp1 : 1 < p) (hp2 : p < 2)
    (hweak : ∀ (ε : Fin (N+1) → ℝ), (∀ s, |ε s| ≤ 1) →
      ∀ f, Integrable f (AddCircle.haarAddCircle : Measure UnitAddCircle) →
        ∀ t > 0,
          (AddCircle.haarAddCircle : Measure UnitAddCircle)
              {y | t < ‖circleSignedConvolutionOperator N ε f y‖} ≤
            ENNReal.ofReal (Cw/t) *
              ∫⁻ x, ENNReal.ofReal (‖f x‖)
                ∂(AddCircle.haarAddCircle : Measure UnitAddCircle)) :
    ∀ (d : ℕ) (f : C(UnitAddTorus (Fin d),ℂ)),
      (∫⁻ x, ENNReal.ofReal (iteratedProductSquareMoment N p f x)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
        ENNReal.ofReal
          (((24*(2:ℝ)^(p/2))^2 *
            (2^p*(p*Cw/(p-1)+p/(2-p))))^d) *
          ∫⁻ x, ENNReal.ofReal (‖f x‖^p)
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  classical
  let K : ℝ := (24*(2:ℝ)^(p/2))^2 *
    (2^p*(p*Cw/(p-1)+p/(2-p)))
  have hp0 : 0 < p := by linarith
  have hpden1 : 0 < p-1 := by linarith
  have hpden2 : 0 < 2-p := by linarith
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  intro d
  induction d with
  | zero =>
      intro f
      have hpoint (x : UnitAddTorus (Fin 0)) :
          iteratedProductSquareMoment N p f x = ‖f x‖^p :=
        iteratedProductSquareMoment_zero f x
      have hEq :
          (∫⁻ x, ENNReal.ofReal (iteratedProductSquareMoment N p f x)
            ∂(Measure.pi fun _ : Fin 0 => AddCircle.haarAddCircle)) =
          ∫⁻ x, ENNReal.ofReal (‖f x‖^p)
            ∂(Measure.pi fun _ : Fin 0 => AddCircle.haarAddCircle) := by
        apply lintegral_congr
        intro x
        rw [hpoint x]
      rw [hEq]
      simp [K]
  | succ d ih =>
      intro f
      let α := Fin d → Fin (N+1)
      let E : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
      let μ : Measure UnitAddCircle := AddCircle.haarAddCircle
      let ν : Measure (UnitAddTorus (Fin d)) :=
        Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
      let g : Fin (Fintype.card α) → UnitAddCircle × UnitAddTorus (Fin d) → ℂ :=
        fun i q => iteratedProductBlock d (fun j => (E.symm i j).val)
          (fun z => f ((productTorusSplit d).symm (q.1,z))) q.2
      have hg : ∀ i, Measurable (g i) := by
        intro i
        exact (iteratedTailFamily_continuous f i).measurable
      have hsections :=
        iteratedTailFamily_sections_memLp (d := d) (N := N) (p := ENNReal.ofReal p) f
      have hcoord :=
        circleSmoothSquareFunction_family_sections_lintegral_lp_le_of_weak_one
          ν N (Fintype.card α) hCw hp1 hp2
          (by
            intro ε hε q hf t ht
            exact hweak ε hε q hf t ht) g hg hsections
      let Q : UnitAddTorus (Fin (d+1)) → ℝ≥0∞ := fun x =>
        ENNReal.ofReal (iteratedProductSquareMoment N p f x)
      have hQ : Measurable Q :=
        iteratedProductSquareMoment_measurable f
      have hleft :
          (∫⁻ z : UnitAddTorus (Fin d), ∫⁻ x : UnitAddCircle,
            ENNReal.ofReal ((∑ i : Fin (Fintype.card α),
              ∑ s : Fin (N+1),
                ‖sectionSmoothBlockConvolution s.val (g i) x z‖^2)^(p/2))
                ∂μ ∂ν) =
          ∫⁻ x : UnitAddTorus (Fin (d+1)), Q x
            ∂(Measure.pi fun _ : Fin (d+1) => AddCircle.haarAddCircle) := by
        calc
          _ = ∫⁻ z : UnitAddTorus (Fin d), ∫⁻ x : UnitAddCircle,
              Q ((productTorusSplit d).symm (x,z)) ∂μ ∂ν := by
                apply lintegral_congr
                intro z
                apply lintegral_congr
                intro x
                have hs := iteratedProductBlock_succ_square_sum_eq_family
                  (N := N) f ((productTorusSplit d).symm (x,z))
                change ENNReal.ofReal
                    ((∑ i : Fin (Fintype.card α), ∑ s : Fin (N+1),
                      ‖sectionSmoothBlockConvolution s.val (g i) x z‖^2)^(p/2)) =
                  ENNReal.ofReal
                    ((∑ t : Fin (d+1) → Fin (N+1),
                      ‖iteratedProductBlock (d+1) (fun j => (t j).val) f
                        ((productTorusSplit d).symm (x,z))‖^2)^(p/2))
                apply congrArg ENNReal.ofReal
                apply congrArg (fun r : ℝ => r^(p/2))
                simpa [g, E, α] using hs.symm
          _ = ∫⁻ x : UnitAddTorus (Fin (d+1)), Q x
                ∂(Measure.pi fun _ : Fin (d+1) => AddCircle.haarAddCircle) := by
              symm
              exact lintegral_productTorusSplit_eq_iterated_tail_first Q hQ
      let R : UnitAddCircle × UnitAddTorus (Fin d) → ℝ≥0∞ := fun q =>
        ENNReal.ofReal ((∑ i : Fin (Fintype.card α), ‖g i q‖^2)^(p/2))
      have hR : Measurable R := by
        dsimp [R]
        fun_prop
      have hsectionIH (x : UnitAddCircle) :
          (∫⁻ z : UnitAddTorus (Fin d), R (x,z) ∂ν) ≤
            ENNReal.ofReal (K^d) *
              ∫⁻ z : UnitAddTorus (Fin d),
                ENNReal.ofReal (‖f ((productTorusSplit d).symm (x,z))‖^p) ∂ν := by
        let e := productTorusSplitHomeomorph d
        let ft : C(UnitAddTorus (Fin d),ℂ) :=
          { toFun := fun z => f (e.symm (x,z))
            continuous_toFun := f.continuous.comp
              ((e.symm.continuous.comp (continuous_const.prodMk continuous_id))) }
        have hsum := iteratedProductBlock_square_sum_eq_fin_family (N := N) ft
        have hleft' :
            (∫⁻ z : UnitAddTorus (Fin d), R (x,z) ∂ν) =
              ∫⁻ z : UnitAddTorus (Fin d),
                ENNReal.ofReal (iteratedProductSquareMoment N p ft z) ∂ν := by
          apply lintegral_congr
          intro z
          have hp := hsum z
          simpa [R, g, ft, e, productTorusSplitHomeomorph,
            productTorusSplit, iteratedProductSquareMoment, E, α] using
            congrArg (fun r : ℝ => ENNReal.ofReal (r^(p/2))) hp
        rw [hleft']
        have hIH := ih ft
        simpa [ft, e, productTorusSplitHomeomorph, productTorusSplit] using hIH
      have hRprod :
          (∫⁻ z : UnitAddTorus (Fin d), ∫⁻ x : UnitAddCircle, R (x,z) ∂μ ∂ν) =
            ∫⁻ x : UnitAddCircle, ∫⁻ z : UnitAddTorus (Fin d), R (x,z) ∂ν ∂μ := by
        calc
          _ = ∫⁻ q : UnitAddCircle × UnitAddTorus (Fin d), R q ∂(μ.prod ν) :=
            (MeasureTheory.lintegral_prod_symm R hR.aemeasurable).symm
          _ = ∫⁻ x : UnitAddCircle, ∫⁻ z : UnitAddTorus (Fin d), R (x,z) ∂ν ∂μ :=
            MeasureTheory.lintegral_prod R hR.aemeasurable
      have hRle :
          (∫⁻ z : UnitAddTorus (Fin d), ∫⁻ x : UnitAddCircle, R (x,z) ∂μ ∂ν) ≤
            ENNReal.ofReal (K^d) *
              ∫⁻ x : UnitAddCircle, ∫⁻ z : UnitAddTorus (Fin d),
                ENNReal.ofReal (‖f ((productTorusSplit d).symm (x,z))‖^p) ∂ν ∂μ := by
        rw [hRprod]
        calc
          _ ≤ ∫⁻ x : UnitAddCircle,
                ENNReal.ofReal (K^d) *
                  (∫⁻ z : UnitAddTorus (Fin d),
                    ENNReal.ofReal (‖f ((productTorusSplit d).symm (x,z))‖^p) ∂ν) ∂μ := by
              apply lintegral_mono_ae
              filter_upwards with x
              exact hsectionIH x
          _ = _ := by
              rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      have hsource : Measurable (fun x : UnitAddTorus (Fin (d+1)) =>
          ENNReal.ofReal (‖f x‖^p)) := by fun_prop
      have hsourceSplit := lintegral_productTorusSplit_eq_iterated
        (fun x : UnitAddTorus (Fin (d+1)) => ENNReal.ofReal (‖f x‖^p)) hsource
      calc
        _ = ∫⁻ z : UnitAddTorus (Fin d), ∫⁻ x : UnitAddCircle,
              ENNReal.ofReal ((∑ i : Fin (Fintype.card α),
                ∑ s : Fin (N+1),
                  ‖sectionSmoothBlockConvolution s.val (g i) x z‖^2)^(p/2))
                  ∂μ ∂ν := hleft.symm
        _ ≤ ENNReal.ofReal K *
              (∫⁻ z : UnitAddTorus (Fin d), ∫⁻ x : UnitAddCircle,
                ENNReal.ofReal ((∑ i : Fin (Fintype.card α), ‖g i (x,z)‖^2)^(p/2))
                  ∂μ ∂ν) := hcoord
        _ ≤ ENNReal.ofReal K *
              (ENNReal.ofReal (K^d) *
                ∫⁻ x : UnitAddCircle, ∫⁻ z : UnitAddTorus (Fin d),
                  ENNReal.ofReal (‖f ((productTorusSplit d).symm (x,z))‖^p) ∂ν ∂μ) :=
            mul_le_mul_of_nonneg_left hRle zero_le 
        _ = ENNReal.ofReal (K^(d+1)) *
              ∫⁻ x : UnitAddTorus (Fin (d+1)),
                ENNReal.ofReal (‖f x‖^p)
                  ∂(Measure.pi fun _ : Fin (d+1) => AddCircle.haarAddCircle) := by
            calc
              ENNReal.ofReal K * (ENNReal.ofReal (K^d) *
                  (∫⁻ x : UnitAddCircle, ∫⁻ z : UnitAddTorus (Fin d),
                    ENNReal.ofReal (‖f ((productTorusSplit d).symm (x,z))‖^p) ∂ν ∂μ))
                  = ENNReal.ofReal (K * K^d) *
                    (∫⁻ x : UnitAddCircle, ∫⁻ z : UnitAddTorus (Fin d),
                      ENNReal.ofReal (‖f ((productTorusSplit d).symm (x,z))‖^p) ∂ν ∂μ) := by
                    rw [← mul_assoc, ← ENNReal.ofReal_mul hK]
              _ = ENNReal.ofReal (K^(d+1)) *
                    (∫⁻ x : UnitAddTorus (Fin (d+1)),
                      ENNReal.ofReal (‖f x‖^p)
                        ∂(Measure.pi fun _ : Fin (d+1) => AddCircle.haarAddCircle)) := by
                    congr 1
                    · congr 1
                      rw [pow_succ]
                      ring
                    · exact hsourceSplit.symm

/-- The direct tensor-kernel block satisfies the same first-coordinate
recursion as the iterated scalar blocks. -/
theorem productSmoothBlockConvolution_succ_eq_section
    {d : ℕ} (s₀ : ℕ) (st : Fin d → ℕ)
    (f : C(UnitAddTorus (Fin (d+1)),ℂ))
    (x : UnitAddTorus (Fin (d+1))) :
    productSmoothBlockConvolution (Fin.cons s₀ st) f x =
      sectionSmoothBlockConvolution s₀
        (fun q : UnitAddCircle × UnitAddTorus (Fin d) =>
          productSmoothBlockConvolution st
            (fun z => f ((productTorusSplit d).symm (q.1,z))) q.2)
        (productTorusSplit d x).1 (productTorusSplit d x).2 := by
  let e := productTorusSplit d
  let μ : Measure (UnitAddCircle × UnitAddTorus (Fin d)) :=
    (AddCircle.haarAddCircle : Measure UnitAddCircle).prod
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
  have hf : Integrable (fun y : UnitAddTorus (Fin (d+1)) =>
      admissibleBlockKernel smoothResolutionCutoff (Fin.cons s₀ st) (x-y) * f y)
      (Measure.pi fun _ : Fin (d+1) => AddCircle.haarAddCircle) :=
    productSmoothBlockConvolution_integrand_integrable (Fin.cons s₀ st)
      (f.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace f)) x
  rw [productSmoothBlockConvolution]
  rw [integral_productTorusSplit_eq_iterated
    (fun y => admissibleBlockKernel smoothResolutionCutoff (Fin.cons s₀ st) (x-y) * f y) hf]
  let xq := e x
  have hxq1 : xq.1 = x 0 := by simp [xq, e, productTorusSplit]
  have hxq2 : xq.2 = Fin.tail x := by
    ext i
    simp [xq, e, productTorusSplit, Fin.tail]
  have hkernel (y : UnitAddCircle) (z : UnitAddTorus (Fin d)) :
      admissibleBlockKernel smoothResolutionCutoff (Fin.cons s₀ st)
        (x-e.symm (y,z)) =
        scalarBlockKernel smoothResolutionCutoff s₀ (xq.1-y) *
          admissibleBlockKernel smoothResolutionCutoff st (xq.2-z) := by
    rw [admissibleBlockKernel_eq_product, admissibleBlockKernel_eq_product]
    simp only [admissibleBlockKernelProduct, BrownianSharp.coordinateProductKernel,
      ContinuousMap.coe_mk]
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hxq1, hxq2]
    have hzero : (x-e.symm (y,z)) 0 = x 0-y := by
      simp [e, productTorusSplit]
    rw [hzero]
    apply congrArg (fun r : ℂ =>
      scalarBlockKernel smoothResolutionCutoff s₀ (x 0-y) * r)
    apply Finset.prod_congr rfl
    intro i hi
    simp [e, productTorusSplit, Fin.tail]
  have htailInt (y : UnitAddCircle) : Integrable
      (fun z : UnitAddTorus (Fin d) =>
        admissibleBlockKernel smoothResolutionCutoff st (xq.2-z) *
          f (e.symm (y,z)))
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
    let eH := productTorusSplitHomeomorph d
    have hcont : Continuous (fun z : UnitAddTorus (Fin d) =>
        admissibleBlockKernel smoothResolutionCutoff st (xq.2-z) * f (e.symm (y,z))) := by
      have hparam : Continuous (fun z : UnitAddTorus (Fin d) => eH.symm (y,z)) :=
        eH.symm.continuous.comp (continuous_const.prodMk continuous_id)
      have heq : ∀ w : UnitAddTorus (Fin (d+1)), e w = eH w := by
        intro w
        simp [eH, e, productTorusSplitHomeomorph, productTorusSplit, Fin.tail]
      have hsame : ∀ z : UnitAddTorus (Fin d), e.symm (y,z) = eH.symm (y,z) := by
        intro z
        apply e.injective
        rw [e.apply_symm_apply]
        rw [heq]
        exact (eH.apply_symm_apply (y,z)).symm
      have hcont' : Continuous (fun z : UnitAddTorus (Fin d) =>
          admissibleBlockKernel smoothResolutionCutoff st (xq.2-z) *
            f (eH.symm (y,z))) :=
        ((admissibleBlockKernel smoothResolutionCutoff st).continuous.comp
          (continuous_const.sub continuous_id)).mul
          (f.continuous.comp hparam)
      exact hcont'.congr (fun z => by rw [hsame z])
    exact hcont.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ∫ y : UnitAddCircle, ∫ z : UnitAddTorus (Fin d),
          (scalarBlockKernel smoothResolutionCutoff s₀ (xq.1-y) *
            admissibleBlockKernel smoothResolutionCutoff st (xq.2-z)) *
            f (e.symm (y,z))
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
        apply integral_congr_ae
        filter_upwards with y
        apply integral_congr_ae
        filter_upwards with z
        rw [hkernel y z]
    _ = ∫ y : UnitAddCircle,
          scalarBlockKernel smoothResolutionCutoff s₀ (xq.1-y) *
            (∫ z : UnitAddTorus (Fin d),
              admissibleBlockKernel smoothResolutionCutoff st (xq.2-z) *
                f (e.symm (y,z))
              ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
          ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
        apply integral_congr_ae
        filter_upwards with y
        calc
          (∫ z : UnitAddTorus (Fin d),
              (scalarBlockKernel smoothResolutionCutoff s₀ (xq.1-y) *
                admissibleBlockKernel smoothResolutionCutoff st (xq.2-z)) *
                f (e.symm (y,z))
              ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
            = ∫ z : UnitAddTorus (Fin d),
                scalarBlockKernel smoothResolutionCutoff s₀ (xq.1-y) *
                  (admissibleBlockKernel smoothResolutionCutoff st (xq.2-z) *
                    f (e.symm (y,z)))
                ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
                  apply integral_congr_ae
                  filter_upwards with z
                  ring
          _ = scalarBlockKernel smoothResolutionCutoff s₀ (xq.1-y) *
                (∫ z : UnitAddTorus (Fin d),
                  admissibleBlockKernel smoothResolutionCutoff st (xq.2-z) *
                    f (e.symm (y,z))
                  ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) := by
                  rw [integral_const_mul]
    _ = _ := rfl

/-- The nested scalar convolutions are exactly the direct tensor-kernel
convolution used by the product-block API. -/
theorem iteratedProductBlock_eq_productSmoothBlockConvolution :
    ∀ (d : ℕ) (s : Fin d → ℕ)
      (f : C(UnitAddTorus (Fin d),ℂ)) (x : UnitAddTorus (Fin d)),
      iteratedProductBlock d s f x = productSmoothBlockConvolution s f x := by
  intro d
  induction d with
  | zero =>
      intro s f x
      change f x = ∫ y : UnitAddTorus (Fin 0),
        admissibleBlockKernel smoothResolutionCutoff s (x-y) * f y
        ∂(Measure.pi fun _ : Fin 0 => AddCircle.haarAddCircle)
      have hk (y : UnitAddTorus (Fin 0)) :
          admissibleBlockKernel smoothResolutionCutoff s (x-y) = 1 := by
        rw [admissibleBlockKernel_eq_product]
        simp [admissibleBlockKernelProduct, BrownianSharp.coordinateProductKernel]
      simp_rw [hk, one_mul]
      have hconst : (fun y : UnitAddTorus (Fin 0) => f y) = fun _ => f x := by
        funext y
        congr 1
        exact Subsingleton.elim _ _
      rw [hconst, integral_const]
      simp
  | succ d ih =>
      intro s f x
      let e := productTorusSplitHomeomorph d
      let st : Fin d → ℕ := fun i => s i.succ
      have hs : s = Fin.cons (s 0) st := by
        funext i
        exact Fin.cases (by simp [st]) (fun j => by simp [st]) i
      let ftail (y : UnitAddCircle) : C(UnitAddTorus (Fin d),ℂ) :=
        { toFun := fun z => f ((productTorusSplit d).symm (y,z))
          continuous_toFun := by
            have hmap : ∀ z : UnitAddTorus (Fin d),
                (productTorusSplit d).symm (y,z) = e.symm (y,z) := by
              intro z
              apply (productTorusSplit d).injective
              rw [(productTorusSplit d).apply_symm_apply]
              have hforward (w : UnitAddTorus (Fin (d+1))) :
                  productTorusSplit d w = e w := by
                simp [e, productTorusSplitHomeomorph, productTorusSplit]
              rw [hforward]
              exact e.apply_symm_apply (y,z)
            have hcont : Continuous (fun z : UnitAddTorus (Fin d) => e.symm (y,z)) :=
              e.symm.continuous.comp (continuous_const.prodMk continuous_id)
            exact (f.continuous.comp hcont).congr (fun z => by
              exact congrArg f (hmap z)) }
      rw [hs, iteratedProductBlock_succ_eq_sectionSmoothBlockConvolution
        (s₀ := s 0) (st := st) f x,
        productSmoothBlockConvolution_succ_eq_section
          (s₀ := s 0) (st := st) f x]
      unfold sectionSmoothBlockConvolution
      apply integral_congr_ae
      filter_upwards with y
      have htail := ih st (ftail y) ((productTorusSplit d x).2)
      simpa [ftail, e, st, productTorusSplitHomeomorph] using congrArg
        (fun z : ℂ => scalarBlockKernel smoothResolutionCutoff (s 0)
          ((productTorusSplit d x).1-y) * z) htail

/-- The explicit product-kernel square function has the same uniform Lp
moment estimate as the recursive coordinate realization. -/
theorem productSmoothSquareFunction_lintegral_lp_le
    (N d : ℕ) {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2)
    (f : C(UnitAddTorus (Fin d),ℂ)) :
    (∫⁻ x : UnitAddTorus (Fin d),
      ENNReal.ofReal ((∑ s : Fin d → Fin (N+1),
        ‖productSmoothBlockConvolution (fun i => (s i).val) f x‖^2)^(p/2))
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      ENNReal.ofReal (((24*(2:ℝ)^(p/2))^2 *
        (2^p*(p*uniformSignedKernelWeakConstant/(p-1)+p/(2-p))))^d) *
      ∫⁻ x : UnitAddTorus (Fin d), ENNReal.ofReal (‖f x‖^p)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  have hweak : ∀ (ε : Fin (N+1) → ℝ), (∀ s, |ε s| ≤ 1) →
      ∀ g, Integrable g (AddCircle.haarAddCircle : Measure UnitAddCircle) →
        ∀ t > 0,
          (AddCircle.haarAddCircle : Measure UnitAddCircle)
              {y | t < ‖circleSignedConvolutionOperator N ε g y‖} ≤
            ENNReal.ofReal (uniformSignedKernelWeakConstant/t) *
              ∫⁻ x, ENNReal.ofReal (‖g x‖)
                ∂(AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    intro ε hε g hg t ht
    exact circleSignedConvolutionOperator_weak_one N ε hε g hg ht
  have hiter := iteratedProductSquareMoment_lintegral_le_of_weak_one
    N uniformSignedKernelWeakConstant_nonneg hp1 hp2 hweak d f
  have hpoint (x : UnitAddTorus (Fin d)) :
      (∑ s : Fin d → Fin (N+1),
        ‖productSmoothBlockConvolution (fun i => (s i).val) f x‖^2)^(p/2) =
      iteratedProductSquareMoment N p f x := by
    unfold iteratedProductSquareMoment
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    exact congrArg (fun z : ℂ => ‖z‖^2)
      (iteratedProductBlock_eq_productSmoothBlockConvolution d
        (fun i => (s i).val) f x).symm
  calc
    (∫⁻ x : UnitAddTorus (Fin d),
        ENNReal.ofReal ((∑ s : Fin d → Fin (N+1),
          ‖productSmoothBlockConvolution (fun i => (s i).val) f x‖^2)^(p/2))
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle))
      = ∫⁻ x : UnitAddTorus (Fin d),
          ENNReal.ofReal (iteratedProductSquareMoment N p f x)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
            apply lintegral_congr
            intro x
            exact congrArg ENNReal.ofReal (hpoint x)
    _ ≤ _ := hiter

end BrownianSharp.AlignmentPaperProductSquareFunctionLp
