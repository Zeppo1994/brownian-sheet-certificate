import BrownianSharp.AtomicTensorSynthesisLp
import BrownianSharp.TensorBlockKernelLp
import BrownianSharp.TorusComplexYoung
import BrownianSharp.InverseDerivativeProfileIdentity

/-! Lp synthesis and convolution bounds for coordinatewise derivatives of a
fixed tensor shape. These are the inputs for the inverse-multiplier refinement
of `FixedShapeBlockLp`. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.ScalarKernelL1
open UnitAddTorus

local instance fixedDerivativeFact : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance fixedDerivativeMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance fixedDerivativeAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance fixedDerivativeNegInvariant : Measure.IsNegInvariant (volume : Measure UnitAddCircle) := by
  infer_instance
local instance fixedDerivativeProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Continuous tensor synthesis using a specified derivative order in each
coordinate. -/
def fixedShapeDerivativeSynthesis {d : ℕ} (s k : Fin d → ℕ)
    (c : DyadicShapeCell d s → ℝ) : RealPeriodic d where
  toFun x := ∑ j : DyadicShapeCell d s,
    c j * dyadicShapeDerivativeAtom s k j x
  continuous_toFun := by
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (continuous_finsetProd Finset.univ fun i hi =>
      (periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt (k i)).continuous.comp
        (continuous_apply i))

/-- Coordinatewise derivative synthesis has a proved finite-p integral bound.
The factors separate derivative growth, atom support volume, and coefficient
size exactly. -/
theorem fixedShapeDerivativeSynthesis_rpow_integral_le {d : ℕ}
    (s k : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (p : ℝ) (hp : 0 < p) (C : Fin d → ℝ)
    (hC : ∀ i, 0 ≤ C i)
    (hderiv : ∀ i x, |iteratedDeriv (k i) smoothAtom x| ≤ C i) :
    (∫ x : UnitAddTorus (Fin d), |fixedShapeDerivativeSynthesis s k c x| ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∏ i : Fin d,
        (((2 : ℝ) ^ (s i))⁻¹ *
          (C i * (2 : ℝ) ^ (s i * k i)) ^ p)) *
        ∑ j : DyadicShapeCell d s, |c j| ^ p := by
  simpa [fixedShapeDerivativeSynthesis] using
    (dyadicShapeDerivativeLevel_rpow_integral_le s k c p hp C hC hderiv)

/-- A coordinatewise low/high kernel: low coordinates use the smooth block
kernel, while positive derivative orders use the actual inverse-derivative
kernel. -/
def fixedShapeMixedKernel {d : ℕ} (t k : Fin d → ℕ) :
    Fin d → C(UnitAddCircle, ℂ) := fun i =>
  if hk : k i = 0 then ScalarKernelL1.scalarBlockKernel (t i)
  else inverseMultiplierKernel (t i) (k i)

theorem fixedShapeMixedKernel_integral_le {d : ℕ}
    (t k : Fin d → ℕ) (L0 : ℝ) (hL0 : 0 ≤ L0)
    (hscalar : ∀ q : ℕ,
      (∫ x : UnitAddCircle,
        ‖ScalarKernelL1.scalarBlockKernel q x‖ ∂AddCircle.haarAddCircle) ≤ L0)
    (Linverse : Fin d → ℝ) (hLinverse : ∀ i, 0 ≤ Linverse i)
    (hhigh : ∀ i, k i ≠ 0 → 0 < t i ∧ Even (k i) ∧
      (∫ x : UnitAddCircle, ‖inverseMultiplierKernel (t i) (k i) x‖
        ∂AddCircle.haarAddCircle) ≤ Linverse i) :
    (∫ x : UnitAddTorus (Fin d),
      ‖coordinateProductKernel (fixedShapeMixedKernel t k) x‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      ∏ i : Fin d, if k i = 0 then L0 else Linverse i := by
  classical
  apply coordinateProductKernel_norm_integral_le
  · intro i
    split_ifs with hk
    · exact hL0
    · exact hLinverse i
  · intro i
    split_ifs with hk
    · simpa [fixedShapeMixedKernel, hk] using hscalar (t i)
    · simpa [fixedShapeMixedKernel, hk] using (hhigh i hk).2.2

/-- The exact torus Young bound for a fixed-shape mixed kernel acting on its
derivative synthesis. -/
theorem fixedShapeMixedConvolution_rpow_integral_le {d : ℕ}
    (t k : Fin d → ℕ) (c : DyadicShapeCell d t → ℝ)
    (p : ℝ) (hp : 1 ≤ p) :
    (∫ x : UnitAddTorus (Fin d),
      ‖∫ y : UnitAddTorus (Fin d),
        coordinateProductKernel (fixedShapeMixedKernel t k) y *
          ((fixedShapeDerivativeSynthesis t k c (x-y) : ℝ) : ℂ)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∫ y : UnitAddTorus (Fin d),
        ‖coordinateProductKernel (fixedShapeMixedKernel t k) y‖
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p *
      ∫ x : UnitAddTorus (Fin d),
        |fixedShapeDerivativeSynthesis t k c x| ^ p
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  let K := coordinateProductKernel (fixedShapeMixedKernel t k)
  let u : C(UnitAddTorus (Fin d), ℂ) :=
    ⟨fun x => (fixedShapeDerivativeSynthesis t k c x : ℂ),
      Complex.continuous_ofReal.comp (fixedShapeDerivativeSynthesis t k c).continuous⟩
  have hy := unitAddTorus_complex_convolution_rpow_le K u p hp
  calc
    _ = ∫ x : UnitAddTorus (Fin d),
        ‖∫ y : UnitAddTorus (Fin d), K y * u (x-y)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp [K, u, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ (∫ y : UnitAddTorus (Fin d), ‖K y‖
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p *
        ∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := hy
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      simp [u, Complex.norm_real, Real.norm_eq_abs]

end BrownianSharp
