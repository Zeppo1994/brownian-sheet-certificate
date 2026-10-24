import BrownianSharp.AlignmentFractionalTensorOperator
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
open HaarQuarter
namespace BrownianSharp.AlignmentFractionalPadding
open AlignmentFractionalTensorOperator
open AlignmentFractionalTensor

abbrev intervalCubeMeasure (d : ℕ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ : Fin d => (volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1))

private abbrev finSplitEquiv (ν e : ℕ) : Fin ν ⊕ Fin e ≃ Fin (ν + e) :=
  finSumFinEquiv

private def splitCoordinateEquiv (ν e : ℕ) :
    (Fin (ν + e) → ℝ) ≃ᵐ ((Fin ν → ℝ) × (Fin e → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (ν + e) => ℝ)
    (finSplitEquiv ν e)).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin ν ⊕ Fin e => ℝ))

/-- Projection onto the first block of coordinates of a split cube. -/
def activeCoordinates (ν e : ℕ) : (Fin (ν + e) → ℝ) → (Fin ν → ℝ) :=
  fun u i => u (Fin.castAdd e i)

def inactiveCoordinates (ν e : ℕ) : (Fin (ν + e) → ℝ) → (Fin e → ℝ) :=
  fun u j => u (Fin.natAdd ν j)

/-- The coordinate split as a measure-preserving map of product cubes. -/
theorem activeCoordinates_measurePreserving (ν e : ℕ) :
    MeasurePreserving (activeCoordinates ν e) (intervalCubeMeasure (ν + e))
      (intervalCubeMeasure ν) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1)
  have hsplit : MeasurePreserving (splitCoordinateEquiv ν e)
      (intervalCubeMeasure (ν + e))
      ((intervalCubeMeasure ν).prod (intervalCubeMeasure e)) := by
    dsimp [splitCoordinateEquiv, intervalCubeMeasure, μ]
    exact (measurePreserving_sumPiEquivProdPi (fun _ : Fin ν ⊕ Fin e => μ)).comp
      (measurePreserving_piCongrLeft (fun _ : Fin (ν + e) => μ) (finSplitEquiv ν e)).symm
  have hprobI : IsProbabilityMeasure μ := by
    refine ⟨?_⟩
    simp [μ]
  haveI : IsProbabilityMeasure (intervalCubeMeasure e) := by
    dsimp [intervalCubeMeasure, μ]
    infer_instance
  have hfst : MeasurePreserving Prod.fst
      ((intervalCubeMeasure ν).prod (intervalCubeMeasure e)) (intervalCubeMeasure ν) :=
    measurePreserving_fst
  have hcomp := hfst.comp hsplit
  have hfun : Prod.fst ∘ splitCoordinateEquiv ν e = activeCoordinates ν e := by
    funext u i
    rfl
  rw [← hfun]
  exact hcomp

theorem splitCoordinates_measurePreserving (ν e : ℕ) :
    MeasurePreserving (splitCoordinateEquiv ν e) (intervalCubeMeasure (ν + e))
      ((intervalCubeMeasure ν).prod (intervalCubeMeasure e)) := by
  let μ : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1)
  dsimp [splitCoordinateEquiv, intervalCubeMeasure, μ]
  exact (measurePreserving_sumPiEquivProdPi (fun _ : Fin ν ⊕ Fin e => μ)).comp
    (measurePreserving_piCongrLeft (fun _ : Fin (ν + e) => μ) (finSplitEquiv ν e)).symm

@[simp] theorem splitCoordinateEquiv_fst (ν e : ℕ) (u : Fin (ν + e) → ℝ) :
    (splitCoordinateEquiv ν e u).1 = activeCoordinates ν e u := by
  funext i
  change (Equiv.piCongrLeft (fun _ : Fin (ν + e) => ℝ) (finSplitEquiv ν e)).symm
    u (Sum.inl i) = u (Fin.castAdd e i)
  rw [Equiv.piCongrLeft_symm_apply]
  congr 1

@[simp] theorem splitCoordinateEquiv_snd (ν e : ℕ) (u : Fin (ν + e) → ℝ) :
    (splitCoordinateEquiv ν e u).2 = inactiveCoordinates ν e u := by
  funext j
  change (Equiv.piCongrLeft (fun _ : Fin (ν + e) => ℝ) (finSplitEquiv ν e)).symm
    u (Sum.inr j) = u (Fin.natAdd ν j)
  rw [Equiv.piCongrLeft_symm_apply]
  congr 1

/-- Lift an active cube L² function to the larger cube by making it constant
in the inactive coordinates. -/
noncomputable def liftActiveSource (ν e : ℕ)
    (g : CameronMartin.UnitCubeL2 ν) : CameronMartin.UnitCubeL2 (ν + e) := by
  exact Lp.compMeasurePreserving (activeCoordinates ν e)
    (by simpa [CameronMartin.UnitCubeL2, intervalCubeMeasure, unitCube_measure_eq_pi]
      using activeCoordinates_measurePreserving ν e) g

theorem liftActiveSource_norm (ν e : ℕ) (g : CameronMartin.UnitCubeL2 ν) :
    ‖liftActiveSource ν e g‖ = ‖g‖ := by
  simp [liftActiveSource, CameronMartin.UnitCubeL2, intervalCubeMeasure,
    unitCube_measure_eq_pi]

/-- Put the active order `r` on the first block and arbitrary orders `b` on
the final block. -/
def paddedOrders {ν e : ℕ} (r : ℝ) (b : Fin e → ℝ) : Fin (ν + e) → ℝ :=
  fun i => (finSumFinEquiv.symm i).elim (fun _ => r) b

theorem paddedOrders_gt {ν e : ℕ} {r : ℝ} {b : Fin e → ℝ}
    (hr : 1/2 < r) (hb : ∀ j, 1/2 < b j) :
    ∀ i : Fin (ν + e), 1/2 < paddedOrders r b i := by
  intro i
  rcases h : finSumFinEquiv.symm i with j | j
  · simpa [paddedOrders, h] using hr
  · simpa [paddedOrders, h] using hb j

/-- Extend an active anchor by fixing every inactive coordinate at one. -/
def paddedAnchor {ν e : ℕ} (t : BrownianCubeAnchor ν) : BrownianCubeAnchor (ν + e) := by
  refine ⟨fun i => (finSumFinEquiv.symm i).elim (fun j => t.val j) (fun _ => 1), ?_⟩
  intro i
  rcases h : finSumFinEquiv.symm i with j | j
  · simpa [h] using t.property j
  · simp [h]

/-- The inactive block contributes its one-dimensional RL integral of the
constant source, evaluated at the right endpoint. -/
private def inactiveRightAnchor (e : ℕ) : BrownianCubeAnchor e :=
  ⟨fun _ => 1, fun _ => ⟨by norm_num, by norm_num⟩⟩

/-- The inactive coordinates contribute the actual RL integral of the unit
source at the right endpoint. This is the product of the normalized profiles
`t ↦ t^b / Γ(b+1)`. -/
def inactivePaddingFactor {e : ℕ} (b : Fin e → ℝ) : ℝ :=
  ∫ v, Latest.fractionalTensorKernel b (inactiveRightAnchor e) v
    ∂intervalCubeMeasure e

theorem paddedTensorKernel_factor {ν e : ℕ} (r : ℝ) (b : Fin e → ℝ)
    (t : BrownianCubeAnchor ν) (u : Fin (ν + e) → ℝ) :
    Latest.fractionalTensorKernel (paddedOrders r b) (paddedAnchor t) u =
      Latest.fractionalTensorKernel (fun _ : Fin ν => r) t (activeCoordinates ν e u) *
      Latest.fractionalTensorKernel b (inactiveRightAnchor e) (inactiveCoordinates ν e u) := by
  rw [Latest.fractionalTensorKernel, Fin.prod_univ_add,
    Latest.fractionalTensorKernel, Latest.fractionalTensorKernel]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [paddedOrders, paddedAnchor, activeCoordinates,
      finSumFinEquiv_symm_apply_castAdd] <;> rfl
  · apply Finset.prod_congr rfl
    intro j hj
    simp [paddedOrders, paddedAnchor, inactiveRightAnchor, inactiveCoordinates,
      finSumFinEquiv_symm_apply_natAdd] <;> rfl

/-- The scalar RL profile of the unit source is strictly positive at the
right endpoint; this also proves positivity of every inactive padding factor. -/
theorem inactivePaddingFactor_pos {e : ℕ} (b : Fin e → ℝ)
    (hb : ∀ j, 1/2 < b j) : 0 < inactivePaddingFactor b := by
  let μ : Measure ℝ := volume.restrict (Set.Icc (0:ℝ) 1)
  let f : ∀ i : Fin e, ℝ → ℝ := fun i u =>
    AlignmentFractionalL2.causalKernel (b i) 1 u
  have hfmem : ∀ i, MemLp (f i) 2 μ := by
    intro i
    simpa [f, μ] using AlignmentFractionalL2.causalKernel_memLp_unit
      (hb i) (by norm_num) (by norm_num)
  have hfactor : (fun u : Fin e → ℝ =>
      Latest.fractionalTensorKernel b (inactiveRightAnchor e) u) =
      (fun u => ∏ i, f i (u i)) := by
    funext u
    rfl
  rw [inactivePaddingFactor, intervalCubeMeasure, hfactor,
    integral_fintype_prod_eq_prod]
  apply Finset.prod_pos
  intro i hi
  have hnonneg : ∀ u, 0 ≤ f i u := by
    intro u
    by_cases hu : u < 1
    · simp [f, AlignmentFractionalL2.causalKernel, AlignmentFractionalKernel.kernel, hu]
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt (Real.Gamma_pos_of_pos (by linarith [hb i]))))
        (Real.rpow_nonneg (by linarith) _)
    · simp [f, AlignmentFractionalL2.causalKernel, hu]
  have hInt : Integrable (f i) μ := (hfmem i).integrable (by norm_num)
  have hsupport : Set.Ioo (0:ℝ) 1 ⊆ Function.support (f i) := by
    intro u hu
    change f i u ≠ 0
    have hu1 : u < 1 := hu.2
    change AlignmentFractionalL2.causalKernel (b i) 1 u ≠ 0
    rw [AlignmentFractionalL2.causalKernel, if_pos hu1,
      AlignmentFractionalKernel.kernel]
    apply ne_of_gt
    exact mul_pos (inv_pos.mpr (Real.Gamma_pos_of_pos (by linarith [hb i])))
      (Real.rpow_pos_of_pos (by linarith) _)
  have hmeasure : 0 < μ (Set.Ioo (0:ℝ) 1) := by
    change 0 < (volume.restrict (Set.Icc (0:ℝ) 1)) (Set.Ioo 0 1)
    rw [Measure.restrict_apply (measurableSet_Ioo)]
    have hsub : Set.Ioo (0:ℝ) 1 ⊆ Set.Icc 0 1 := by
      intro x hx
      exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
    rw [Set.inter_eq_left.mpr hsub]
    rw [Real.volume_Ioo]
    norm_num
  have hpos := (integral_pos_iff_support_of_nonneg (hnonneg) hInt).2
    (lt_of_lt_of_le hmeasure (measure_mono hsupport))
  exact hpos

/-- Padding by an inactive constant source factors the full RL value into the
active RL value and the fixed inactive profile. -/
theorem fractionalTensorRL_padding_apply {ν e : ℕ} (r : ℝ)
    (hr : 1/2 < r) (b : Fin e → ℝ) (hb : ∀ j, 1/2 < b j)
    (g : CameronMartin.UnitCubeL2 ν) (t : BrownianCubeAnchor ν) :
    fractionalTensorRL (paddedOrders (ν := ν) (e := e) r b)
      (paddedOrders_gt hr hb)
      (liftActiveSource ν e g) (paddedAnchor t) =
      fractionalTensorRL (fun _ : Fin ν => r) (fun _ => hr) g t *
        inactivePaddingFactor b := by
  rw [fractionalTensorRL_apply, fractionalTensorRL_apply]
  change (∫ u, Latest.fractionalTensorKernel (paddedOrders r b) (paddedAnchor t) u *
      (liftActiveSource ν e g) u
      ∂((Measure.pi (fun _ : Fin (ν + e) => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet (ν + e)))) =
    (∫ u, Latest.fractionalTensorKernel (fun _ : Fin ν => r) t u * g u
      ∂((Measure.pi (fun _ : Fin ν => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet ν))) * inactivePaddingFactor b
  let split := splitCoordinateEquiv ν e
  have hsource :
      (liftActiveSource ν e g : (Fin (ν + e) → ℝ) → ℝ) =ᵐ[
        ((Measure.pi (fun _ : Fin (ν + e) => (volume : Measure ℝ))).restrict
          (CameronMartin.unitCubeSet (ν + e)))]
        (fun u => g (activeCoordinates ν e u)) := by
    have hMP : MeasurePreserving (activeCoordinates ν e)
        ((Measure.pi (fun _ : Fin (ν + e) => (volume : Measure ℝ))).restrict
          (CameronMartin.unitCubeSet (ν + e)))
        ((Measure.pi (fun _ : Fin ν => (volume : Measure ℝ))).restrict
          (CameronMartin.unitCubeSet ν)) := by
      simpa [unitCube_measure_eq_pi] using activeCoordinates_measurePreserving ν e
    simpa [liftActiveSource, Function.comp_def] using
      (Lp.coeFn_compMeasurePreserving g hMP)
  have hsplit : MeasurePreserving (splitCoordinateEquiv ν e)
      ((Measure.pi (fun _ : Fin (ν + e) => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet (ν + e)))
      ((intervalCubeMeasure ν).prod (intervalCubeMeasure e)) := by
    rw [unitCube_measure_eq_pi]
    exact splitCoordinates_measurePreserving ν e
  let fActive : (Fin ν → ℝ) → ℝ := fun u =>
    Latest.fractionalTensorKernel (fun _ : Fin ν => r) t u * g u
  let fInactive : (Fin e → ℝ) → ℝ := fun v =>
    Latest.fractionalTensorKernel b (inactiveRightAnchor e) v
  let fPair : (Fin ν → ℝ) × (Fin e → ℝ) → ℝ :=
    fun p => fActive p.1 * fInactive p.2
  have hIntegrand :
      (fun u : Fin (ν + e) → ℝ =>
        Latest.fractionalTensorKernel (paddedOrders r b) (paddedAnchor t) u *
          (liftActiveSource ν e g) u) =ᵐ[((Measure.pi (fun _ : Fin (ν + e) => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet (ν + e)))]
      fun u => fPair (split u) := by
    filter_upwards [hsource] with u hu
    dsimp [fPair, fActive, fInactive, split]
    rw [paddedTensorKernel_factor]
    rw [hu]
    simp [fPair, fActive, fInactive, split, splitCoordinateEquiv_fst,
      splitCoordinateEquiv_snd, activeCoordinates, inactiveCoordinates] <;> ring
  calc
    _ = ∫ u, fPair (split u)
        ∂((Measure.pi (fun _ : Fin (ν + e) => (volume : Measure ℝ))).restrict
          (CameronMartin.unitCubeSet (ν + e))) := integral_congr_ae hIntegrand
    _ = ∫ p, fPair p ∂((intervalCubeMeasure ν).prod (intervalCubeMeasure e)) :=
      MeasurePreserving.integral_comp' hsplit fPair
    _ = (∫ u, fActive u ∂intervalCubeMeasure ν) *
        ∫ v, fInactive v ∂intervalCubeMeasure e := by
      dsimp [fPair]
      exact integral_prod_mul fActive fInactive
    _ = _ := by
      simp [fActive, fInactive, inactivePaddingFactor,
        fractionalTensorRL_apply, Latest.fractionalIntegrationValue,
        unitCube_measure_eq_pi]

/-- The inactive-face anchor map is continuous. -/
theorem paddedAnchor_continuous {ν e : ℕ} :
    Continuous (paddedAnchor (ν := ν) (e := e)) := by
  have hc : Continuous (fun t : BrownianCubeAnchor ν =>
      fun i : Fin (ν + e) => (finSumFinEquiv.symm i).elim
        (fun j => (t : Fin ν → ℝ) j) (fun _ => (1 : ℝ))) := by
    apply continuous_pi
    intro i
    rcases h : finSumFinEquiv.symm i with j | j
    · simpa [h, Function.comp_def] using (continuous_apply j).comp continuous_subtype_val
    · exact continuous_const
  exact hc.subtype_mk _

def paddedAnchorMap {ν e : ℕ} : C(BrownianCubeAnchor ν, BrownianCubeAnchor (ν + e)) :=
  ⟨paddedAnchor, paddedAnchor_continuous⟩

/-- Restrict a continuous function on the full anchor cube to the face where
all inactive coordinates equal one. -/
def paddedRestriction {ν e : ℕ} :
    C(BrownianCubeAnchor (ν + e), ℝ) →L[ℝ] C(BrownianCubeAnchor ν, ℝ) :=
  ContinuousMap.compCLM ℝ ℝ (paddedAnchorMap (ν := ν) (e := e))

@[simp] theorem paddedRestriction_apply {ν e : ℕ}
    (F : C(BrownianCubeAnchor (ν + e), ℝ)) (t : BrownianCubeAnchor ν) :
    paddedRestriction F t = F (paddedAnchor t) := rfl

theorem paddedRestriction_norm_le {ν e : ℕ}
    (F : C(BrownianCubeAnchor (ν + e), ℝ)) :
    ‖paddedRestriction F‖ ≤ ‖F‖ := by
  apply (ContinuousMap.norm_le (f := paddedRestriction F) (C := ‖F‖)
    (norm_nonneg _)).2
  intro t
  rw [paddedRestriction_apply]
  exact ContinuousMap.norm_coe_le_norm F (paddedAnchor t)

/-- The scaled active RL ball embeds into the restriction of the anisotropic
full-dimensional RL ball. This is the padding reduction needed to transfer
entropy lower bounds from the minimum-order coordinates. -/
theorem scaled_active_ball_subset_restricted_full_ball
    {ν e : ℕ} (r : ℝ) (hr : 1/2 < r) (b : Fin e → ℝ)
    (hb : ∀ j, 1/2 < b j) :
    Set.image (fun f : C(BrownianCubeAnchor ν, ℝ) => inactivePaddingFactor b • f)
      (Latest.fractionalIntegrationBall (fun _ : Fin ν => r)) ⊆
      paddedRestriction '' Latest.fractionalIntegrationBall (paddedOrders (ν := ν) (e := e) r b) := by
  intro f hf
  rcases (Set.mem_image _ _ _).mp hf with ⟨f₀, hf₀, rfl⟩
  rw [fractionalIntegrationBall_eq_operator_image (fun _ : Fin ν => r)
    (fun _ => hr)] at hf₀
  rcases (Set.mem_image _ _ _).mp hf₀ with ⟨g, hg, rfl⟩
  let G := fractionalTensorRL (paddedOrders (ν := ν) (e := e) r b)
    (paddedOrders_gt hr hb)
    (liftActiveSource ν e g)
  have hGball : G ∈ Latest.fractionalIntegrationBall (paddedOrders (ν := ν) (e := e) r b) := by
    rw [fractionalIntegrationBall_eq_operator_image (paddedOrders (ν := ν) (e := e) r b)
      (paddedOrders_gt hr hb)]
    exact Set.mem_image_of_mem _
      (show liftActiveSource ν e g ∈ {v : CameronMartin.UnitCubeL2 (ν + e) | ‖v‖ ≤ 1} from
        (liftActiveSource_norm ν e g).trans_le hg)
  refine ⟨G, hGball, ?_⟩
  ext t
  rw [paddedRestriction_apply,
    fractionalTensorRL_padding_apply (r := r) (hr := hr) (b := b) (hb := hb)
      (g := g) (t := t)]
  simp
  ring

end BrownianSharp.AlignmentFractionalPadding
