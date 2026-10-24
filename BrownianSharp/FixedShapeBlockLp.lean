import BrownianSharp.TensorBlockKernelLp
import BrownianSharp.AtomicTensorSynthesisLp
import BrownianSharp.TorusComplexYoung
import BrownianSharp.InverseDerivativeProfileIdentity
import BrownianSharp.SmoothAtom

/-! A first operator estimate for a finite synthesis on one fixed tensor
shape. The multiplier block has a uniform Lp bound, and the synthesis input
has the exact cellwise Lp budget. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp

open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AtomicBlockKernel
open BrownianSharp.ScalarKernelL1
open UnitAddTorus

local instance fixedShapeBlockFact : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance fixedShapeBlockMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance fixedShapeBlockAddHaar : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance fixedShapeBlockNegInvariant : Measure.IsNegInvariant (volume : Measure UnitAddCircle) := by
  infer_instance
local instance fixedShapeBlockProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Real synthesis of a finite family of periodized smooth atoms at one fixed
rectangular shape. -/
def fixedShapeSynthesis {d : ℕ} (s : Fin d → ℕ)
    (c : DyadicShapeCell d s → ℝ) : RealPeriodic d where
  toFun x := ∑ j : DyadicShapeCell d s,
    c j * dyadicShapeDerivativeAtom s (fun _ => 0) j x
  continuous_toFun := by
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul (continuous_finsetProd Finset.univ fun i hi =>
      (periodizedDyadicAtomDerivative1 (s i) (j i).val (j i).isLt 0).continuous.comp
        (continuous_apply i))

/-- The actual finite-p integral bound for fixed-shape atom synthesis. -/
theorem fixedShapeSynthesis_rpow_integral_le {d : ℕ}
    (s : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ) (p : ℝ) (hp : 0 < p) :
    (∫ x : UnitAddTorus (Fin d), |fixedShapeSynthesis s c x| ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      (∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹) *
        ∑ j : DyadicShapeCell d s, |c j| ^ p := by
  simpa [fixedShapeSynthesis, dyadicShapeDerivativeAtom] using
    (dyadicShapeDerivativeLevel_rpow_integral_le s (fun _ => 0) c p hp
      (fun _ => 1) (by intro i; norm_num)
      (by intro i x; simpa using smoothAtom_abs_le_one x))

/-- Uniform finite-p control of the smooth Fourier block on any fixed-shape
finite synthesis. The bound keeps the exact product cell volume and coefficient
sum; high-coordinate decay is supplied in the derivative refinement. -/
theorem fixedShapeBlock_rpow_integral_le {d : ℕ}
    (s : Fin d → ℕ) (c : DyadicShapeCell d s → ℝ)
    (p : ℝ) (hp : 1 ≤ p) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t : Fin d → ℕ,
    (∫ x : UnitAddTorus (Fin d), ‖SmoothResolution.block t (fixedShapeSynthesis s c) x‖ ^ p
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      ((L ^ d) ^ p) *
        ((∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹) *
          ∑ j : DyadicShapeCell d s, |c j| ^ p) := by
  obtain ⟨L, hL, hscalar⟩ := exists_scalarBlockKernel_uniform_L1_bound
  refine ⟨L, hL, ?_⟩
  intro t
  let K : C(UnitAddTorus (Fin d), ℂ) := AtomicBlockKernel.kernel t
  let u : C(UnitAddTorus (Fin d), ℂ) :=
    ⟨fun x => (fixedShapeSynthesis s c x : ℂ), Complex.continuous_ofReal.comp (fixedShapeSynthesis s c).continuous⟩
  have hK : (∫ x : UnitAddTorus (Fin d), ‖K x‖
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤ L ^ d := by
    simpa [K] using tensorBlockKernel_norm_integral_le t L hL hscalar
  have hYoung := unitAddTorus_complex_convolution_rpow_le K u p hp
  have hconv (x : UnitAddTorus (Fin d)) :
      SmoothResolution.block t (fixedShapeSynthesis s c) x =
        ∫ y : UnitAddTorus (Fin d), K y * u (x-y)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
    rw [BrownianSharp.block_eq_kernel_integral]
    let μ : Measure (UnitAddTorus (Fin d)) :=
      Measure.pi fun _ : Fin d => AddCircle.haarAddCircle
    letI : Measure.IsAddLeftInvariant μ := inferInstance
    have hneg : MeasurePreserving (fun y : UnitAddTorus (Fin d) => -y) μ μ := by
      change MeasurePreserving (fun y : (Fin d → UnitAddCircle) => -y)
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)
      exact measurePreserving_pi
        (fun _ : Fin d => AddCircle.haarAddCircle)
        (fun _ : Fin d => AddCircle.haarAddCircle)
        (fun i : Fin d => Measure.measurePreserving_neg (AddCircle.haarAddCircle))
    have hadd : MeasurePreserving (fun y : UnitAddTorus (Fin d) => x + y) μ μ :=
      measurePreserving_add_left μ x
    have hmp : MeasurePreserving (fun y : UnitAddTorus (Fin d) => x-y) μ μ := by
      convert hadd.comp hneg using 1 <;> ext y <;> simp [sub_eq_add_neg]
    let g : UnitAddTorus (Fin d) → ℂ := fun y => K y * u (x-y)
    calc
      (∫ y : UnitAddTorus (Fin d), AtomicBlockKernel.kernel t (x-y) *
          (fixedShapeSynthesis s c y : ℂ)
            ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
          ∫ y : UnitAddTorus (Fin d), g (x-y) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with y
        simp [g, K, u, sub_sub_cancel]
      _ = ∫ y : UnitAddTorus (Fin d), g y ∂μ :=
        hmp.integral_comp (Homeomorph.subLeft x).measurableEmbedding g
      _ = ∫ y : UnitAddTorus (Fin d), K y * u (x-y)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
        rfl
  have hreal : (∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p ∂
      (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) =
      ∫ x : UnitAddTorus (Fin d), |fixedShapeSynthesis s c x| ^ p ∂
        (Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
    apply integral_congr_ae
    filter_upwards [] with x
    simp [u, Complex.norm_real, Real.norm_eq_abs]
  have hinput := fixedShapeSynthesis_rpow_integral_le s c p (by linarith)
  have hpL : (∫ x : UnitAddTorus (Fin d), ‖K x‖
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p ≤ (L ^ d) ^ p :=
    Real.rpow_le_rpow (integral_nonneg (fun x => norm_nonneg _)) hK
      (le_trans (by norm_num) hp)
  calc
    _ = ∫ x : UnitAddTorus (Fin d), ‖∫ y, K y * u (x-y)
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← hconv x]
    _ ≤ (∫ x : UnitAddTorus (Fin d), ‖K x‖
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ^ p *
        ∫ x : UnitAddTorus (Fin d), ‖u x‖ ^ p
          ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := hYoung
    _ ≤ (L ^ d) ^ p *
        ((∏ i : Fin d, ((2 : ℝ) ^ (s i))⁻¹) *
          ∑ j : DyadicShapeCell d s, |c j| ^ p) := by
      rw [hreal]
      exact mul_le_mul hpL hinput
        (integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg _) _))
        (Real.rpow_nonneg (by positivity : 0 ≤ L ^ d) p)

end BrownianSharp
