import BrownianSharp.AlignmentFractionalPadding
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Fintype.Sort

noncomputable section
open MeasureTheory HaarQuarter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
namespace BrownianSharp.AlignmentFractionalPaddingPermutation
open BrownianSharp.AlignmentFractionalPadding
open BrownianSharp.AlignmentFractionalTensorOperator
open BrownianSharp.AlignmentFractionalTensor

/-- Re-express a cube point in coordinates permuted by `e`: new coordinate `i`
reads old coordinate `e.symm i`. -/
def coordinateBackEquiv {d : ℕ} (e : Fin d ≃ Fin d) :
    (Fin d → ℝ) ≃ᵐ (Fin d → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin d => ℝ) e

def coordinateBack {d : ℕ} (e : Fin d ≃ Fin d) (x : Fin d → ℝ) : Fin d → ℝ :=
  coordinateBackEquiv e x

@[simp] theorem coordinateBackEquiv_apply {d : ℕ} (e : Fin d ≃ Fin d)
    (x : Fin d → ℝ) (i : Fin d) : coordinateBackEquiv e x i = x (e.symm i) := by
  simp [coordinateBackEquiv, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

@[simp] theorem coordinateBack_apply {d : ℕ} (e : Fin d ≃ Fin d)
    (x : Fin d → ℝ) (i : Fin d) : coordinateBack e x i = x (e.symm i) := by
  simp [coordinateBack, coordinateBackEquiv, MeasurableEquiv.coe_piCongrLeft,
    Equiv.piCongrLeft_apply]

def reindexAnchor {d : ℕ} (e : Fin d ≃ Fin d) (t : BrownianCubeAnchor d) :
    BrownianCubeAnchor d := by
  refine ⟨coordinateBack e t, ?_⟩
  intro i
  simpa only [coordinateBack_apply] using t.property (e.symm i)

def reindexAnchorMap {d : ℕ} (e : Fin d ≃ Fin d) :
    C(BrownianCubeAnchor d, BrownianCubeAnchor d) := by
  have hc : Continuous (fun t : BrownianCubeAnchor d => coordinateBack e t) := by
    exact continuous_pi fun i => by
      simpa [coordinateBack_apply, Function.comp_def] using
        (continuous_apply (e.symm i)).comp continuous_subtype_val
  exact ⟨reindexAnchor e, hc.subtype_mk _⟩

def reindexOrders {d : ℕ} (e : Fin d ≃ Fin d) (a : Fin d → ℝ) : Fin d → ℝ :=
  fun i => a (e i)

theorem reindexCoordinatesMP {d : ℕ} (e : Fin d ≃ Fin d) :
    MeasurePreserving (coordinateBackEquiv e)
      ((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet d))
      ((Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
        (CameronMartin.unitCubeSet d)) := by
  rw [unitCube_measure_eq_pi]
  exact measurePreserving_piCongrLeft (fun _ : Fin d =>
    (volume : Measure ℝ).restrict (Set.Icc (0:ℝ) 1)) e

noncomputable def reindexSource {d : ℕ} (e : Fin d ≃ Fin d)
    (g : CameronMartin.UnitCubeL2 d) : CameronMartin.UnitCubeL2 d :=
  Lp.compMeasurePreserving (coordinateBackEquiv e) (reindexCoordinatesMP e) g

theorem reindexSource_norm {d : ℕ} (e : Fin d ≃ Fin d)
    (g : CameronMartin.UnitCubeL2 d) : ‖reindexSource e g‖ = ‖g‖ := by
  simp [reindexSource]

@[simp] theorem fractionalTensorKernel_reindex {d : ℕ}
    (e : Fin d ≃ Fin d) (a : Fin d → ℝ) (t : BrownianCubeAnchor d)
    (u : Fin d → ℝ) :
    Latest.fractionalTensorKernel (reindexOrders e a) t u =
      Latest.fractionalTensorKernel a (reindexAnchor e t) (coordinateBack e u) := by
  unfold Latest.fractionalTensorKernel reindexOrders
  apply Fintype.prod_equiv e
  intro i
  simp [reindexAnchor, coordinateBack, coordinateBack_apply]

/-- Reindexing coordinates commutes with the actual bounded RL operator. -/
theorem fractionalTensorRL_reindex_apply {d : ℕ} (e : Fin d ≃ Fin d)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i)
    (g : CameronMartin.UnitCubeL2 d) (t : BrownianCubeAnchor d) :
    fractionalTensorRL (reindexOrders e a) (fun i => ha (e i))
      (reindexSource e g) t =
      fractionalTensorRL a ha g (reindexAnchor e t) := by
  rw [fractionalTensorRL_apply (a := reindexOrders e a)
      (ha := by simpa [reindexOrders] using fun i => ha (e i)),
    fractionalTensorRL_apply (a := a) (ha := ha)]
  unfold Latest.fractionalIntegrationValue
  let μd := (Measure.pi (fun _ : Fin d => (volume : Measure ℝ))).restrict
      (CameronMartin.unitCubeSet d)
  have hsource :
      (reindexSource e g : (Fin d → ℝ) → ℝ) =ᵐ[μd]
        (fun u => g (coordinateBack e u)) := by
    simpa [reindexSource, coordinateBack, coordinateBackEquiv, μd, Function.comp_def] using
      (Lp.coeFn_compMeasurePreserving g (reindexCoordinatesMP e))
  have hkernel : ∀ u, Latest.fractionalTensorKernel (reindexOrders e a) t u =
      Latest.fractionalTensorKernel a (reindexAnchor e t) (coordinateBack e u) :=
    fun u => fractionalTensorKernel_reindex e a t u
  calc
    _ = ∫ u, Latest.fractionalTensorKernel (reindexOrders e a) t u *
          g (coordinateBack e u) ∂μd := by
        apply integral_congr_ae
        filter_upwards [hsource] with u hu
        rw [hu]
    _ = ∫ u, Latest.fractionalTensorKernel a (reindexAnchor e t)
          (coordinateBack e u) * g (coordinateBack e u) ∂μd := by
        apply integral_congr_ae
        filter_upwards with u
        rw [hkernel]
    _ = ∫ u, Latest.fractionalTensorKernel a (reindexAnchor e t) u * g u ∂μd :=
      by simpa [μd, coordinateBack, coordinateBackEquiv] using
        (MeasurePreserving.integral_comp' (reindexCoordinatesMP e)
          (fun u => Latest.fractionalTensorKernel a (reindexAnchor e t) u * g u))


@[simp] theorem reindexAnchor_symm_left {d : ℕ} (e : Fin d ≃ Fin d)
    (t : BrownianCubeAnchor d) : reindexAnchor e.symm (reindexAnchor e t) = t := by
  apply Subtype.ext
  funext i
  simp [reindexAnchor, coordinateBack]

@[simp] theorem reindexAnchor_symm_right {d : ℕ} (e : Fin d ≃ Fin d)
    (t : BrownianCubeAnchor d) : reindexAnchor e (reindexAnchor e.symm t) = t := by
  apply Subtype.ext
  funext i
  simp [reindexAnchor, coordinateBack]

def reindexOutput {d : ℕ} (e : Fin d ≃ Fin d) :
    C(BrownianCubeAnchor d, ℝ) →L[ℝ] C(BrownianCubeAnchor d, ℝ) :=
  ContinuousMap.compCLM ℝ ℝ (reindexAnchorMap e)

@[simp] theorem reindexOutput_apply {d : ℕ} (e : Fin d ≃ Fin d)
    (F : C(BrownianCubeAnchor d, ℝ)) (t : BrownianCubeAnchor d) :
    reindexOutput e F t = F (reindexAnchor e t) := rfl

@[simp] theorem reindexOrders_symm {d : ℕ} (e : Fin d ≃ Fin d)
    (a : Fin d → ℝ) : reindexOrders e.symm (reindexOrders e a) = a := by
  funext i
  simp [reindexOrders]

/-- The image ball is equivariant under a permutation of coordinates. -/
theorem fractionalIntegrationBall_reindex {d : ℕ} (e : Fin d ≃ Fin d)
    (a : Fin d → ℝ) (ha : ∀ i, 1/2 < a i) :
    Latest.fractionalIntegrationBall (reindexOrders e a) =
      reindexOutput e '' Latest.fractionalIntegrationBall a := by
  rw [fractionalIntegrationBall_eq_operator_image (reindexOrders e a)
      (by simpa [reindexOrders] using fun i => ha (e i)),
    fractionalIntegrationBall_eq_operator_image a ha]
  ext F
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨fractionalTensorRL a ha (reindexSource e.symm g), ?_, ?_⟩
    · exact Set.mem_image_of_mem (fractionalTensorRL a ha)
        (show reindexSource e.symm g ∈ {v : CameronMartin.UnitCubeL2 d | ‖v‖ ≤ 1} by
          change ‖reindexSource e.symm g‖ ≤ 1
          rw [reindexSource_norm]
          exact hg)
    · ext t
      change fractionalTensorRL a ha (reindexSource e.symm g) (reindexAnchor e t) =
        fractionalTensorRL (reindexOrders e a) (fun i => ha (e i)) g t
      have h := fractionalTensorRL_reindex_apply (e := e.symm)
        (a := reindexOrders e a)
        (ha := by intro i; simpa [reindexOrders] using ha (e i))
        (g := g) (t := reindexAnchor e t)
      simpa [reindexOrders] using h
  · rintro ⟨F₀, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨reindexSource e g, ?_, ?_⟩
    · change ‖reindexSource e g‖ ≤ 1
      rw [reindexSource_norm]
      exact hg
    · ext t
      change fractionalTensorRL (reindexOrders e a) (fun i => ha (e i))
          (reindexSource e g) t =
        fractionalTensorRL a ha g (reindexAnchor e t)
      exact fractionalTensorRL_reindex_apply e a ha g t


/-- Indices attaining the minimum order. -/
def minimumIndexSet {d : ℕ} (a : Fin d → ℝ) (r : ℝ) : Finset (Fin d) :=
  Finset.univ.filter (fun i => a i = r)

/-- Permutation placing the minimum-order indices in the first coordinate
block. -/
def minimumCoordinatePermutation {ν e : ℕ} (a : Fin (ν + e) → ℝ) (r : ℝ)
    (hcard : (minimumIndexSet a r).card = ν) : Fin (ν + e) ≃ Fin (ν + e) := by
  let S := minimumIndexSet a r
  have hcompl : Sᶜ.card = e := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
    omega
  exact finSumFinEquiv.symm.trans (finSumEquivOfFinset hcard hcompl)

theorem minimumCoordinatePermutation_first {ν e : ℕ}
    (a : Fin (ν + e) → ℝ) (r : ℝ)
    (hcard : (minimumIndexSet a r).card = ν) (i : Fin ν) :
    a (minimumCoordinatePermutation a r hcard (Fin.castAdd e i)) = r := by
  have hmem : minimumCoordinatePermutation a r hcard (Fin.castAdd e i) ∈
      minimumIndexSet a r := by
    dsimp [minimumCoordinatePermutation]
    rw [finSumFinEquiv_symm_apply_castAdd, finSumEquivOfFinset_inl]
    exact Finset.orderEmbOfFin_mem _ _ _
  exact (Finset.mem_filter.mp hmem).2

/-- A minimum-multiplicity assumption therefore yields a permutation whose
first block consists exactly of the minimum-order coordinates. -/
theorem exists_minimumCoordinatePermutation {ν e : ℕ}
    (a : Fin (ν + e) → ℝ) (r : ℝ)
    (hm : Latest.minimumMultiplicity a r ν) :
    ∃ eperm : Fin (ν + e) ≃ Fin (ν + e),
      ∀ i : Fin ν, reindexOrders eperm a (Fin.castAdd e i) = r := by
  change (∀ i, r ≤ a i) ∧ (minimumIndexSet a r).card = ν at hm
  refine ⟨minimumCoordinatePermutation a r hm.2, ?_⟩
  intro i
  exact minimumCoordinatePermutation_first a r hm.2 i


/-- After the minimum coordinates are moved first, the order vector is exactly
of the padded form used by the RL face restriction. -/
theorem reindexOrders_eq_paddedOrders {ν e : ℕ}
    (a : Fin (ν + e) → ℝ) (r : ℝ)
    (hcard : (minimumIndexSet a r).card = ν) :
    reindexOrders (minimumCoordinatePermutation a r hcard) a =
      paddedOrders (ν := ν) (e := e) r
        (fun j => reindexOrders (minimumCoordinatePermutation a r hcard) a
          (Fin.natAdd ν j)) := by
  funext i
  let ep := minimumCoordinatePermutation a r hcard
  rcases hi : finSumFinEquiv.symm i with j | j
  · have hi' : i = Fin.castAdd e j := by
      have h := congrArg finSumFinEquiv hi
      simpa using h
    rw [hi']
    rw [paddedOrders, finSumFinEquiv_symm_apply_castAdd]
    exact minimumCoordinatePermutation_first a r hcard j
  · have hi' : i = Fin.natAdd ν j := by
      have h := congrArg finSumFinEquiv hi
      simpa using h
    rw [hi']
    simp [paddedOrders, reindexOrders, ep]


/-- Coordinate permutation for an arbitrary ambient dimension, with the first
`ν` coordinates mapped to the minimum-order indices. -/
theorem exists_minimumCoordinatePermutation_general {d ν : ℕ}
    (hν : ν ≤ d) (a : Fin d → ℝ) (r : ℝ)
    (hm : Latest.minimumMultiplicity a r ν) :
    ∃ eperm : Fin d ≃ Fin d,
      ∀ i : Fin ν, a (eperm (Equiv.cast (congrArg Fin
        (by omega : ν + (d - ν) = d)) (Fin.castAdd (d-ν) i))) = r := by
  classical
  change (∀ i, r ≤ a i) ∧ (minimumIndexSet a r).card = ν at hm
  let S := minimumIndexSet a r
  have hcompl : Sᶜ.card = d - ν := by
    rw [Finset.card_compl, Fintype.card_fin, hm.2]
  have hsum : ν + (d - ν) = d := by omega
  let ec : Fin (ν + (d-ν)) ≃ Fin d := Equiv.cast (congrArg Fin hsum)
  let es : Fin (ν + (d-ν)) ≃ Fin d :=
    finSumFinEquiv.symm.trans (finSumEquivOfFinset hm.2 hcompl)
  let eperm : Fin d ≃ Fin d := ec.symm.trans es
  refine ⟨eperm, ?_⟩
  intro i
  have hmem : eperm (ec (Fin.castAdd (d-ν) i)) ∈ S := by
    change (finSumFinEquiv.symm.trans (finSumEquivOfFinset hm.2 hcompl))
      (ec.symm (ec (Fin.castAdd (d-ν) i))) ∈ S
    rw [Equiv.symm_apply_apply, Equiv.trans_apply,
      finSumFinEquiv_symm_apply_castAdd, finSumEquivOfFinset_inl]
    exact Finset.orderEmbOfFin_mem S hm.2 i
  exact (Finset.mem_filter.mp hmem).2

end BrownianSharp.AlignmentFractionalPaddingPermutation
