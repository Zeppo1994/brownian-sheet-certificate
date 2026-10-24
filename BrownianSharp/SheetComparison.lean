import BrownianSharp.NativeProjection
import BrownianSharp.IndependentComparison

/-!
The original continuous sheet is compared with its actual native finite
Haar layer on any finite evaluation grid. Uniform confinement implies the
finite closed-cube event, so no process-level conditioning theorem is needed.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1600000

namespace BrownianSharp
open HaarQuarter

def nativeFinLayerMap {d n N M : ℕ} (e : Fin N ≃ LayerIndex d n)
    (t : Fin M → BrownianCubeAnchor d) :
    (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ) where
  toFun x j := ∑ i, ⟪nativeLayerVector (e i), nativeBoxVector (t j)⟫ * x i
  map_add' x y := by ext j; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by ext j; simp [Finset.mul_sum, mul_left_comm]

theorem nativeFinLayerMap_coordinates {d n N M : ℕ} {Ω : Type*}
    (e : Fin N ≃ LayerIndex d n) (t : Fin M → BrownianCubeAnchor d)
    (G : LayerIndex d n → Ω → ℝ) (ω : Ω) :
    nativeFinLayerMap e t (fun i => G (e i) ω) =
      fun j => nativeLayerEvaluation G (t j) ω := by
  ext j
  exact e.sum_comp (fun a => ⟪nativeLayerVector a, nativeBoxVector (t j)⟫ * G a ω)

/-- All complement modes remain in the independent residual. The comparison
is for the actual original sheet and the actual native coordinate layer. -/
theorem original_sheet_native_grid_comparison
    {d n M : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : 0 < d) (B : BrownianSheetOnCube d Ω P)
    (t : Fin M → BrownianCubeAnchor d) :
    ∃ G : LayerIndex d n → Ω → ℝ,
      (∀ a, Measurable (G a)) ∧ iIndepFun G P ∧
      (∀ a, P.map (G a) = gaussianReal 0 1) ∧
      ∀ ε : ℝ, 0 ≤ ε → P {ω | ‖B.path ω‖ ≤ ε} ≤
        P {ω | ‖fun j : Fin M => nativeLayerEvaluation G (t j) ω‖ ≤ ε} := by
  classical
  obtain ⟨G, hG, hIndep, hLaw, hResidual⟩ := original_sheet_native_layer hd B t
  refine ⟨G, hG, hIndep, hLaw, ?_⟩
  let N := Fintype.card (LayerIndex d n)
  let e : Fin N ≃ LayerIndex d n := (Fintype.equivFin (LayerIndex d n)).symm
  have hN : 0 < N := Fintype.card_pos_iff.mpr (nativeLayerIndex_nonempty d n hd)
  let X : Ω → (Fin N → ℝ) := fun ω i => G (e i) ω
  let Z : Ω → (Fin M → ℝ) :=
    fun ω j => B.eval (t j) ω - nativeLayerEvaluation G (t j) ω
  let A := nativeFinLayerMap e t
  have hX : Measurable X := by exact measurable_pi_lambda (fun i => hG (e i))
  have hZ : Measurable Z := by
    apply measurable_pi_lambda
    intro j
    exact (B.measurable_eval (t j)).sub (by unfold nativeLayerEvaluation; fun_prop)
  have hXI : iIndepFun (fun i : Fin N => G (e i)) P := hIndep.precomp e.injective
  have hXLaw : P.map X = Measure.pi (fun _ : Fin N => gaussianReal 0 1) := by
    change P.map (fun ω i => G (e i) ω) = _
    have hmap := hXI.map_fun_eq_pi_map (fun i => (hG (e i)).aemeasurable)
    simpa only [hLaw] using hmap
  have hXZ : IndepFun X Z P := by
    exact hResidual.comp
      (by fun_prop : Measurable (fun x : LayerIndex d n → ℝ => fun i : Fin N => x (e i)))
      measurable_id
  have hAX (ω : Ω) : A (X ω) = fun j => nativeLayerEvaluation G (t j) ω :=
    nativeFinLayerMap_coordinates e t G ω
  intro ε hε
  let C : Set (Fin M → ℝ) := Metric.closedBall 0 ε
  have hconv : Convex ℝ C := convex_closedBall _ _
  have hsymm : ∀ z, z ∈ C → -z ∈ C := by
    intro z hz
    simpa [C, Metric.mem_closedBall, dist_zero_right] using hz
  have hC : MeasurableSet C :=
    (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : Fin M → ℝ) ε)).measurableSet
  have hcomp := independent_standardGaussian_residual_comparison hN X Z hX hZ
    hXZ hXLaw C A hconv hsymm hC
  have hsum (ω : Ω) : A (X ω) + Z ω = fun j => B.eval (t j) ω := by
    rw [hAX]
    ext j
    dsimp [Z]
    ring
  have hleft : {ω | ‖B.path ω‖ ≤ ε} ⊆ {ω | A (X ω) + Z ω ∈ C} := by
    intro ω hω
    change A (X ω) + Z ω ∈ C
    rw [hsum ω]
    change ‖B.path ω‖ ≤ ε at hω
    change dist (fun j => B.eval (t j) ω) 0 ≤ ε
    rw [dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg hε).2
    intro j
    exact ((B.path ω).norm_coe_le_norm (t j)).trans hω
  calc
    _ ≤ P {ω | A (X ω) + Z ω ∈ C} := measure_mono hleft
    _ ≤ P {ω | A (X ω) ∈ C} := hcomp
    _ = _ := by
      apply congrArg P
      ext ω
      change A (X ω) ∈ C ↔ _
      rw [hAX ω]
      simp only [C, Metric.mem_closedBall, dist_zero_right, Set.mem_setOf_eq]

end BrownianSharp
