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

/-- The weak-star representation of the anchored path associated to a continuous linear
functional on the ambient `L²` space. -/
def dualFeaturePath {d : ℕ} (φ : WeakDual ℝ (AmbientL2 d)) :
    C(BrownianCubeAnchor d, ℝ) :=
  ⟨fun x => φ ((brownianCubeSpanEmbedding d) (featureVector x)),
    (φ.toStrongDual).continuous.comp
      ((brownianCubeSpanEmbedding d).continuous.comp (featureVector_continuous d))⟩

def dualFeatureEvaluation {d : ℕ} (φ : WeakDual ℝ (AmbientL2 d)) :
    BrownianCubeAnchor d → ℝ :=
  fun x => φ ((brownianCubeSpanEmbedding d) (featureVector x))

/-- The standard weak-star dual unit ball, viewed through the canonical norm-preserving
identification of a Hilbert space with its continuous dual. -/
def dualUnitBall (d : ℕ) : Set (WeakDual ℝ (AmbientL2 d)) :=
  WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ (AmbientL2 d)) 1

/-- The feature-space image of the unit ball, matching the v10 entropy interface. -/
def anchoredFeatureBall (d : ℕ) : Set C(BrownianCubeAnchor d, ℝ) :=
  {f | ∃ g : brownianCubeBoxSpan d, ‖g‖ ≤ 1 ∧ featurePath g = f}

theorem anchoredIntegrationPath_projected {d : ℕ} (g : AmbientL2 d)
    (x : BrownianCubeAnchor d) :
    anchoredIntegrationPath g x =
      ⟪(brownianCubeBoxSpan d).orthogonalProjectionOnto g, featureVector x⟫ := by
  have hproj := (brownianCubeBoxSpan d).inner_orthogonalProjectionOnto_eq_of_mem_right
    (u := featureVector x) (v := g)
  change ⟪g, (featureVector x : AmbientL2 d)⟫ = _
  exact hproj.symm

theorem Kd_eq_anchoredFeatureBall (d : ℕ) : Kd d = anchoredFeatureBall d := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨(brownianCubeBoxSpan d).orthogonalProjectionOnto g, ?_, ?_⟩
    · exact (Submodule.norm_orthogonalProjectionOnto_apply_le
        (brownianCubeBoxSpan d) g).trans hg
    · ext x
      rw [anchoredIntegrationPath_projected]
      rfl
  · rintro ⟨g, hg, rfl⟩
    refine ⟨brownianCubeSpanEmbedding d g, ?_, ?_⟩
    · simpa using hg
    · ext x
      change ⟪brownianCubeSpanEmbedding d g,
        (brownianCubeSpanEmbedding d) (featureVector x)⟫ = _
      rfl

theorem Kd_eq_dualFeaturePath_image (d : ℕ) :
    Kd d = dualFeaturePath '' dualUnitBall d := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    let φ : WeakDual ℝ (AmbientL2 d) :=
      (InnerProductSpace.toDualMap ℝ (AmbientL2 d) g).toWeakDual
    have hφ : φ ∈ dualUnitBall d := by
      change (InnerProductSpace.toDualMap ℝ (AmbientL2 d) g).toWeakDual.toStrongDual ∈
        Metric.closedBall (0 : StrongDual ℝ (AmbientL2 d)) 1
      simpa [Metric.mem_closedBall, dist_eq_norm] using hg
    refine ⟨φ, hφ, ?_⟩
    ext x
    change ⟪g, (brownianCubeSpanEmbedding d) (featureVector x)⟫ =
      (InnerProductSpace.toDualMap ℝ (AmbientL2 d) g)
        ((brownianCubeSpanEmbedding d) (featureVector x))
    rw [InnerProductSpace.toDualMap_apply_apply]
  · rintro ⟨φ, hφ, rfl⟩
    let g : AmbientL2 d := (InnerProductSpace.toDual ℝ (AmbientL2 d)).symm φ.toStrongDual
    have hg : ‖g‖ ≤ 1 := by
      have hφ' : ‖φ.toStrongDual‖ ≤ 1 := by
        simpa [dualUnitBall, Metric.mem_closedBall, dist_eq_norm] using hφ
      simpa [g] using hφ'
    refine ⟨g, hg, ?_⟩
    ext x
    change ⟪g, (brownianCubeSpanEmbedding d) (featureVector x)⟫ = _
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
theorem Kd_neg {d : ℕ} {f : C(BrownianCubeAnchor d, ℝ)}
    (hf : f ∈ Kd d) : -f ∈ Kd d := by
  rcases hf with ⟨g, hg, rfl⟩
  refine ⟨-g, ?_, ?_⟩
  · simpa using hg
  · ext x
    simp [anchoredIntegrationPath, inner_neg_left]

theorem Kd_zero_mem (d : ℕ) : (0 : C(BrownianCubeAnchor d, ℝ)) ∈ Kd d := by
  refine ⟨0, by simp, ?_⟩
  ext x
  simp [anchoredIntegrationPath]

/-- The actual ambient `L²` image ball is compact in the uniform topology on the closed cube.
This is the Arzelà--Ascoli route used in the manuscript: Banach--Alaoglu gives pointwise
compactness of the weak-star dual image, while the compact feature parameterization gives a
common modulus of continuity. -/
theorem Kd_isCompact (d : ℕ) : IsCompact (Kd d) := by
  rw [Kd_eq_dualFeaturePath_image]
  let B := dualUnitBall d
  let S := dualFeaturePath '' B
  have hB : IsCompact B := by
    exact WeakDual.isCompact_closedBall (0 : StrongDual ℝ (AmbientL2 d)) 1
  have hEval : Continuous (fun φ : WeakDual ℝ (AmbientL2 d) =>
      dualFeatureEvaluation φ) := by
    apply continuous_pi
    intro x
    exact WeakDual.eval_continuous _
  have hpoint : IsCompact (ContinuousMap.toFun '' S) := by
    have himage : ContinuousMap.toFun '' S = dualFeatureEvaluation '' B := by
      ext f
      constructor
      · rintro ⟨u, ⟨φ, hφ, rfl⟩, rfl⟩
        exact ⟨φ, hφ, rfl⟩
      · rintro ⟨φ, hφ, rfl⟩
        exact ⟨dualFeaturePath φ, ⟨φ, hφ, rfl⟩, rfl⟩
    rw [himage]
    exact hB.image hEval
  have hfeature : Continuous (fun x : BrownianCubeAnchor d =>
      (brownianCubeSpanEmbedding d) (featureVector x)) :=
    (brownianCubeSpanEmbedding d).continuous.comp (featureVector_continuous d)
  have hfeatureOn : ContinuousOn (fun x : BrownianCubeAnchor d =>
      (brownianCubeSpanEmbedding d) (featureVector x)) Set.univ :=
    continuousOn_univ.mpr hfeature
  have huniform : UniformContinuousOn (fun x : BrownianCubeAnchor d =>
      (brownianCubeSpanEmbedding d) (featureVector x)) Set.univ :=
    isCompact_univ.uniformContinuousOn_of_continuous hfeatureOn
  have hS : Equicontinuous ((↑) : S → BrownianCubeAnchor d → ℝ) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hclose⟩ := (Metric.uniformContinuousOn_iff.mp huniform) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro y hy f
    rcases f.property with ⟨φ, hφ, hpath⟩
    have hnorm : ‖φ.toStrongDual‖ ≤ 1 := by
      simpa [B, dualUnitBall, Metric.mem_closedBall, dist_eq_norm] using hφ
    have hmap : φ ((brownianCubeSpanEmbedding d) (featureVector x)) -
        φ ((brownianCubeSpanEmbedding d) (featureVector y)) =
        φ.toStrongDual ((brownianCubeSpanEmbedding d) (featureVector x) -
          (brownianCubeSpanEmbedding d) (featureVector y)) := by
      simp
    calc
      dist (f.val x) (f.val y) =
          ‖φ ((brownianCubeSpanEmbedding d) (featureVector x)) -
            φ ((brownianCubeSpanEmbedding d) (featureVector y))‖ := by
              rw [← hpath]
              rfl
      _ = ‖φ.toStrongDual ((brownianCubeSpanEmbedding d) (featureVector x) -
            (brownianCubeSpanEmbedding d) (featureVector y))‖ := by rw [hmap]
      _ ≤ ‖φ.toStrongDual‖ *
          ‖(brownianCubeSpanEmbedding d) (featureVector x) -
            (brownianCubeSpanEmbedding d) (featureVector y)‖ :=
              (φ.toStrongDual).le_opNorm _
      _ ≤ ‖(brownianCubeSpanEmbedding d) (featureVector x) -
            (brownianCubeSpanEmbedding d) (featureVector y)‖ := by
              nlinarith [norm_nonneg ((brownianCubeSpanEmbedding d) (featureVector x) -
                (brownianCubeSpanEmbedding d) (featureVector y))]
      _ = dist ((brownianCubeSpanEmbedding d) (featureVector x))
            ((brownianCubeSpanEmbedding d) (featureVector y)) := (dist_eq_norm _ _).symm
      _ < ε := hclose x (by simp) y (by simp)
        (by simpa [dist_comm] using hy)
  have hcompactS : IsCompact S :=
    ArzelaAscoli.isCompact_of_equicontinuous S hpoint hS
  simpa [S, B] using hcompactS

end BrownianSharp.CameronMartin
