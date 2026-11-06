import BrownianSharp.BrownianCubeSpan
import BrownianSharp.BrownianSheetOnCube
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Tactic

/-!
# The anchored Cameron--Martin ball

The manuscript's set `K_d` is the image of `L²([0,1]^d)` under the anchored integration map.
This module defines that restricted-measure space and proves its image agrees with the ambient
`L²(ℝ^d)` zero-extension image. The ambient image is then identified with the closed
feature-span unit ball by orthogonal projection; no ambient injectivity is asserted.
-/

noncomputable section

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace

namespace BrownianSharp.CameronMartin

open HaarQuarter

/-- The ambient real `L²` space on `ℝ^d`, used as a zero-extension realization of cube data. -/
abbrev AmbientL2 (d : ℕ) :=
  Lp ℝ 2 (Measure.pi fun _ : Fin d => (volume : Measure ℝ))

private instance cubeSpanComplete (d : ℕ) : CompleteSpace (brownianCubeBoxSpan d) :=
  completeSpace_coe_iff_isComplete.mpr
    (Submodule.isClosed_topologicalClosure _).isComplete

/-- The actual anchored-box feature in the closed feature span. -/
def featureVector {d : ℕ} (x : BrownianCubeAnchor d) : brownianCubeBoxSpan d :=
  ⟨brownianSheetBoxIndicatorLp x.val, brownianCubeBoxIndicator_mem x⟩

theorem boxIndicator_continuousOn_nonneg {d : ℕ} :
    ContinuousOn (brownianSheetBoxIndicatorLp (d := d))
      {t : Fin d → ℝ | ∀ i, 0 ≤ t i} := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  let F : (Fin d → ℝ) → ℝ := fun s =>
    (∏ i, s i) + (∏ i, t i) - 2 * ∏ i, min (s i) (t i)
  have hcont : ContinuousAt F t := by
    dsimp [F]
    fun_prop
  obtain ⟨δ, hδ, hbound⟩ :=
    (Metric.continuousAt_iff.mp hcont) (ε ^ 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro s hs hdist
  have hspos : ∀ i, 0 ≤ s i := hs
  have htpos : ∀ i, 0 ≤ t i := ht
  have hnormsq :
      ‖brownianSheetBoxIndicatorLp s - brownianSheetBoxIndicatorLp t‖ ^ 2 = F s := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
      brownianSheetBoxIndicatorLp_inner s s hspos hspos,
      brownianSheetBoxIndicatorLp_inner s t hspos htpos,
      brownianSheetBoxIndicatorLp_inner t s htpos hspos,
      brownianSheetBoxIndicatorLp_inner t t htpos htpos]
    simp only [min_self]
    have hst : (∏ i, min (t i) (s i)) = ∏ i, min (s i) (t i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [min_comm]
    rw [hst]
    dsimp [F]
    ring
  have hFs : F s = ‖brownianSheetBoxIndicatorLp s -
      brownianSheetBoxIndicatorLp t‖ ^ 2 := hnormsq.symm
  have hFt : F t = 0 := by
    simp [F, min_self]
    ring
  have hsmall : |F s| < ε ^ 2 := by
    have := hbound hdist
    simpa [dist_eq_norm, hFt] using this
  rw [dist_eq_norm]
  have hn : 0 ≤ ‖brownianSheetBoxIndicatorLp s -
      brownianSheetBoxIndicatorLp t‖ := norm_nonneg _
  rw [← hnormsq, abs_of_nonneg (sq_nonneg _)] at hsmall
  nlinarith

theorem featureVector_continuous (d : ℕ) :
    Continuous (featureVector (d := d)) := by
  apply Continuous.subtype_mk
  exact boxIndicator_continuousOn_nonneg.comp_continuous continuous_subtype_val
    (fun x => fun i => (x.property i).1)

/-! The compactness and distance calculation used for the feature modulus. -/

theorem featureVector_norm_le_one {d : ℕ} (x : BrownianCubeAnchor d) :
    ‖featureVector x‖ ≤ 1 := by
  have hself : ‖featureVector x‖ ^ 2 = ∏ i, x.val i := by
    rw [← real_inner_self_eq_norm_sq]
    change ⟪brownianSheetBoxIndicatorLp x.val,
      brownianSheetBoxIndicatorLp x.val⟫ = _
    rw [brownianSheetBoxIndicatorLp_inner x.val x.val
      (fun i => (x.property i).1) (fun i => (x.property i).1)]
    simp
  have hprod : (∏ i, x.val i) ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => (x.property i).1)
      (fun i _ => (x.property i).2)
  nlinarith [norm_nonneg (featureVector x)]

/-- The finite-cube feature path in the actual closed box span. -/
def featurePath {d : ℕ} (g : brownianCubeBoxSpan d) :
    C(BrownianCubeAnchor d, ℝ) :=
  ⟨fun x => ⟪g, featureVector x⟫,
    continuous_const.inner (featureVector_continuous d)⟩

/-- The ambient-`L²` anchored integration map, represented by inner products with box indicators.
It only depends on the integrand on the unit cube because every feature indicator is supported
there. -/
def anchoredIntegrationPath {d : ℕ} (g : AmbientL2 d) :
    C(BrownianCubeAnchor d, ℝ) :=
  ⟨fun x => ⟪g, (featureVector x : AmbientL2 d)⟫,
    continuous_const.inner
      ((brownianCubeSpanEmbedding d).continuous.comp (featureVector_continuous d))⟩

/-- The ambient realization of the manuscript's set `K_d`, as an image of the `L²(ℝ^d)` unit
ball.  The exact equivalence to the restricted-measure `L²([0,1]^d)` model is a separate bridge. -/
def Kd (d : ℕ) : Set C(BrownianCubeAnchor d, ℝ) :=
  {f | ∃ g : AmbientL2 d, ‖g‖ ≤ 1 ∧ anchoredIntegrationPath g = f}

/-- The unit cube as a measurable subset of the ambient parameter space. -/
def unitCubeSet (d : ℕ) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun _ : Fin d => Set.Icc (0 : ℝ) 1)

theorem measurableSet_unitCubeSet (d : ℕ) : MeasurableSet (unitCubeSet d) := by
  exact MeasurableSet.univ_pi fun _ => measurableSet_Icc

/-- The manuscript's integrand Hilbert space, with Lebesgue measure restricted to the cube. -/
abbrev UnitCubeL2 (d : ℕ) :=
  Lp ℝ 2 ((Measure.pi fun _ : Fin d => (volume : Measure ℝ)).restrict (unitCubeSet d))

/-- Zero extension from the restricted cube to ambient Euclidean space. -/
noncomputable def unitCubeZeroExtend {d : ℕ} (g : UnitCubeL2 d) : AmbientL2 d :=
  MemLp.toLp ((unitCubeSet d).indicator (g : (Fin d → ℝ) → ℝ))
    ((memLp_indicator_iff_restrict (measurableSet_unitCubeSet d)).2 (Lp.memLp g))

theorem unitCubeZeroExtend_norm {d : ℕ} (g : UnitCubeL2 d) :
    ‖unitCubeZeroExtend g‖ = ‖g‖ := by
  rw [unitCubeZeroExtend, Lp.norm_toLp, Lp.norm_def,
    eLpNorm_indicator_eq_eLpNorm_restrict (measurableSet_unitCubeSet d)]

def unitCubeIntegrationPath {d : ℕ} (g : UnitCubeL2 d) :
    C(BrownianCubeAnchor d, ℝ) := anchoredIntegrationPath (unitCubeZeroExtend g)

def KdUnitCube (d : ℕ) : Set C(BrownianCubeAnchor d, ℝ) :=
  {f | ∃ g : UnitCubeL2 d, ‖g‖ ≤ 1 ∧ unitCubeIntegrationPath g = f}

private theorem unitCubeSet_mem_iff {d : ℕ} (z : Fin d → ℝ) :
    z ∈ unitCubeSet d ↔ ∀ i, z i ∈ Set.Icc (0 : ℝ) 1 := by
  change (∀ i ∈ Set.univ, z i ∈ Set.Icc (0 : ℝ) 1) ↔ _
  simp

private def anchoredBoxSet {d : ℕ} (x : BrownianCubeAnchor d) : Set (Fin d → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (0 : ℝ) (x.val i))

private theorem anchoredBoxSet_subset_unitCube {d : ℕ} (x : BrownianCubeAnchor d) :
    anchoredBoxSet x ⊆ unitCubeSet d := by
  intro z hz
  rw [unitCubeSet_mem_iff]
  intro i
  have hzi := (Set.mem_pi.mp hz) i (Set.mem_univ i)
  exact ⟨hzi.1, le_trans hzi.2 (x.property i).2⟩

private theorem boxIndicator_ae {d : ℕ} (x : BrownianCubeAnchor d) :
    (featureVector x : AmbientL2 d) =ᵐ[Measure.pi fun _ : Fin d => (volume : Measure ℝ)]
      (anchoredBoxSet x).indicator (fun _ => (1 : ℝ)) := by
  change (brownianSheetBoxIndicatorLp x.val : AmbientL2 d) =ᵐ[_] _
  rw [brownianSheetBoxIndicatorLp]
  exact indicatorConstLp_coeFn

private theorem zeroExtend_ae {d : ℕ} (g : UnitCubeL2 d) :
    (unitCubeZeroExtend g : AmbientL2 d) =ᵐ[Measure.pi fun _ : Fin d => (volume : Measure ℝ)]
      (unitCubeSet d).indicator (g : (Fin d → ℝ) → ℝ) := by
  exact (memLp_indicator_iff_restrict (measurableSet_unitCubeSet d)).2
    (Lp.memLp g) |>.coeFn_toLp

private theorem anchoredIntegrationPath_eq_restrict {d : ℕ} (g : AmbientL2 d)
    (x : BrownianCubeAnchor d) :
    anchoredIntegrationPath (unitCubeZeroExtend
      (MemLp.toLp (g : (Fin d → ℝ) → ℝ)
        ((Lp.memLp g).restrict (unitCubeSet d)))) x =
      anchoredIntegrationPath g x := by
  let gC : UnitCubeL2 d :=
    MemLp.toLp (g : (Fin d → ℝ) → ℝ) ((Lp.memLp g).restrict (unitCubeSet d))
  have hgC : (gC : (Fin d → ℝ) → ℝ) =ᵐ[
      (Measure.pi fun _ : Fin d => (volume : Measure ℝ)).restrict (unitCubeSet d)]
      (g : (Fin d → ℝ) → ℝ) := by
    exact ((Lp.memLp g).restrict (unitCubeSet d)).coeFn_toLp
  have hcube := measurableSet_unitCubeSet d
  have hdata : (unitCubeSet d).indicator (gC : (Fin d → ℝ) → ℝ) =ᵐ[
      Measure.pi fun _ : Fin d => (volume : Measure ℝ)]
      (unitCubeSet d).indicator (g : (Fin d → ℝ) → ℝ) := by
    filter_upwards [(ae_restrict_iff' hcube).1 hgC] with z hz
    by_cases h : z ∈ unitCubeSet d
    · simp [Set.indicator_of_mem, h, hz h]
    · simp [Set.indicator_apply, h]
  have hfeature := boxIndicator_ae x
  have hext := zeroExtend_ae gC
  change ⟪unitCubeZeroExtend gC, featureVector x⟫ = ⟪g, featureVector x⟫
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hext, hfeature, hdata] with z hext hfeature hdata
  rw [hext, hfeature, hdata]
  by_cases hz : z ∈ anchoredBoxSet x
  · have hcube : z ∈ unitCubeSet d := anchoredBoxSet_subset_unitCube x hz
    simp [Set.indicator_of_mem, hz, hcube]
  · simp [Set.indicator_apply, hz]

/-- The exact restricted-cube Cameron--Martin image from the manuscript. -/
theorem KdUnitCube_eq_Kd (d : ℕ) : KdUnitCube d = Kd d := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨unitCubeZeroExtend g, ?_, rfl⟩
    rw [unitCubeZeroExtend_norm]
    exact hg
  · rintro ⟨g, hg, rfl⟩
    let gC : UnitCubeL2 d :=
      MemLp.toLp (g : (Fin d → ℝ) → ℝ) ((Lp.memLp g).restrict (unitCubeSet d))
    have hgC : ‖gC‖ ≤ 1 := by
      rw [Lp.norm_toLp]
      calc
        ENNReal.toReal (eLpNorm (g : (Fin d → ℝ) → ℝ) 2
            ((Measure.pi fun _ : Fin d => (volume : Measure ℝ)).restrict (unitCubeSet d)))
            ≤ ENNReal.toReal (eLpNorm (g : (Fin d → ℝ) → ℝ) 2
              (Measure.pi fun _ : Fin d => (volume : Measure ℝ))) :=
                ENNReal.toReal_mono (Lp.memLp g).eLpNorm_ne_top
                  (eLpNorm_restrict_le _ _ _ _)
        _ = ‖g‖ := (Lp.norm_def g).symm
        _ ≤ 1 := hg
    refine ⟨gC, hgC, ?_⟩
    ext x
    exact anchoredIntegrationPath_eq_restrict g x

end BrownianSharp.CameronMartin
