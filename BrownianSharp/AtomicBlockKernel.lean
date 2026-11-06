import BrownianSharp.AtomicBlockVariance
import Mathlib.Analysis.Fourier.AddCircleMulti

/-!
Finite multiplier kernels for the smooth resolution.  This file records the
exact convolution identity before the L² estimates are added.  In particular,
no asymptotic kernel bound is assumed or claimed here.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp.AtomicBlockKernel
open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open UnitAddTorus

private theorem mFourier_sub_mul {d : ℕ} (k : Fin d → ℤ)
    (x y : UnitAddTorus (Fin d)) :
    UnitAddTorus.mFourier k (x - y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier (-k) y := by
  classical
  have hcoord : ∀ i : Fin d,
      fourier (k i) ((x - y) i) = fourier (k i) (x i) * fourier (-k i) (y i) := by
    intro i
    simp [sub_eq_add_neg, fourier_apply, zsmul_add, AddCircle.toCircle_add]
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Finset.prod_mul_distrib]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  exact hcoord i

end BrownianSharp.AtomicBlockKernel
