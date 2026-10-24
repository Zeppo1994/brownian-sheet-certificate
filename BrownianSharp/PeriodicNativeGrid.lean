import BrownianSharp.PeriodicCover
import BrownianSharp.SmoothLayer

/-! Exact identification of the periodized smooth native atoms with the
finite midpoint samples used in the covariance calculation. -/
noncomputable section
open scoped BigOperators
namespace BrownianSharp
open BrownianSharp.Torus

/-- The same native Haar rectangle addresses specify the smooth tensor atoms. -/
def periodicNativeAtomIndex {d n : ℕ} (a : LayerIndex d n) : PeriodicCover.AtomIndex d where
  depth := layerIndexDepth a
  cell := layerIndexCell a
  valid := layerIndexCell_lt a

def periodicNativeAtom {d n : ℕ} (a : LayerIndex d n) : RealPeriodic d :=
  PeriodicCover.periodizedDyadicAtom (periodicNativeAtomIndex a)

def periodicMidpoint {d n : ℕ} (q : MidpointGridIndex d n) : UnitAddTorus (Fin d) :=
  fun i => (midpointGridCoordinate n (q i) : UnitAddCircle)

theorem periodizedDyadicAtom1_unit_interval (s j : ℕ) (hj : j < 2 ^ s)
    (x : ℝ) (hx : x ∈ Set.Ico (0 : ℝ) 1) :
    PeriodicCover.periodizedDyadicAtom1 s j hj (x : UnitAddCircle) =
      smoothAtom ((2 : ℝ) ^ s * x - (j : ℝ)) := by
  change AddCircle.liftIco (1 : ℝ) 0
    (fun y => smoothAtom ((2 : ℝ) ^ s * y - (j : ℝ))) (x : UnitAddCircle) = _
  exact AddCircle.liftIco_zero_coe_apply hx

theorem periodicNativeAtom_midpoint_eq {d n : ℕ}
    (a : LayerIndex d n) (q : MidpointGridIndex d n) :
    periodicNativeAtom a (periodicMidpoint q) = smoothLayerAtom smoothAtom q a := by
  change (∏ i, PeriodicCover.periodizedDyadicAtom1
    (layerIndexDepth a i) (layerIndexCell a i) (layerIndexCell_lt a i)
      (midpointGridCoordinate n (q i) : UnitAddCircle)) = _
  unfold smoothLayerAtom
  apply Finset.prod_congr rfl
  intro i _
  exact periodizedDyadicAtom1_unit_interval _ _ _ _
    ⟨(midpointGridCoordinate_mem_Ioo n (q i)).1.le,
      (midpointGridCoordinate_mem_Ioo n (q i)).2⟩

/-- The finite Gaussian synthesis grid is literally the smooth-atom row
matrix. This connects the periodic covering and shell-variance routes. -/
theorem periodicNativeSynthesis_grid_eq {d n N M : ℕ}
    (e : Fin N ≃ LayerIndex d n) (q : Fin M → MidpointGridIndex d n)
    (x : Fin N → ℝ) (j : Fin M) :
    PeriodicCover.synthesisGridMap (fun i => periodicNativeAtom (e i))
      (fun j => periodicMidpoint (q j)) x j =
      ∑ a : LayerIndex d n, smoothLayerAtom smoothAtom (q j) a * x (e.symm a) := by
  change (∑ i : Fin N, x i • periodicNativeAtom (e i)) (periodicMidpoint (q j)) = _
  simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [periodicNativeAtom_midpoint_eq]
  exact Fintype.sum_equiv e _ _ (by intro i; simp [mul_comm])

end BrownianSharp
