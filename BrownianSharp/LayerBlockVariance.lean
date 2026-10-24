import BrownianSharp.AtomicTensorFactorization
import BrownianSharp.PeriodicNativeGrid

/-! Full native-layer block variance from the rectangular-shape bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.LayerBlockVariance

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.PeriodicCover
open BrownianSharp.AtomicTensorVariance
open BrownianSharp.AtomicTensorFactorization
open UnitAddTorus

/-- Variance envelope for all atoms in one native grade. The shape coordinate
is the genuine weak-composition index from `LayerIndex`. -/
def nativeLayerVarianceEnvelope (d n K : ℕ) (C : ℝ)
    (t : Fin d → ℕ) : ℝ :=
  ∑ r : Shape d n, ∏ i : Fin d,
    scalarVarianceEnvelope K C (r.1 i) (t i)

private theorem periodicNativeAtom_eq_shape (d n : ℕ)
    (a : LayerIndex d n) :
    periodicNativeAtom a = shapePeriodicAtom (layerIndexDepth a)
      (fun i => a.2 i) := by
  ext x
  simp [periodicNativeAtom, periodicNativeAtomIndex,
    AtomicTensorVariance.shapePeriodicAtom, PeriodicCover.periodizedDyadicAtom,
    PeriodicCover.AtomIndex, layerIndexDepth, layerIndexCell, dyadicShapeAtom,
    periodizedDyadicAtomDerivative1_zero_eq_existing]

/-- Actual native smooth atoms at grade n have precisely the variance bound
obtained by summing the rectangular-shape envelopes over the weak compositions
of n. This is the exact family used by `NativeProjection`. -/
theorem nativeLayer_block_variance_le (d n K : ℕ) (hK : 1 ≤ K)
    (C : ℝ) (hC : ∀ x : ℝ, |iteratedDeriv K smoothAtom x| ≤ C)
    (t : Fin d → ℕ) (x : UnitAddTorus (Fin d)) :
    (∑ a : LayerIndex d n,
      ‖block t (periodicNativeAtom a) x‖ ^ 2) ≤
      nativeLayerVarianceEnvelope d n K C t := by
  classical
  rw [Fintype.sum_sigma]
  dsimp [nativeLayerVarianceEnvelope]
  apply Finset.sum_le_sum
  intro r hr
  simpa [periodicNativeAtom_eq_shape, layerIndexDepth] using
    actual_shape_block_variance_product_bound d K hK C hC r.1
      t x


end BrownianSharp.LayerBlockVariance
