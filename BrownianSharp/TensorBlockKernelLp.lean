import BrownianSharp.AtomicBlockKernel
import BrownianSharp.ScalarBlockLp
import BrownianSharp.ComplexYoungConvolutionLp
import Mathlib.Analysis.Fourier.AddCircleMulti

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace BrownianSharp
open BrownianSharp.AtomicBlockKernel
open BrownianSharp.SmoothResolution
open BrownianSharp.ScalarKernelL1
open BrownianSharp.ScalarAtomVariance
open UnitAddTorus

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem prod_le_prod_nonneg_real {ι : Type*} (s : Finset ι)
    (f g : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i)
    (hle : ∀ i ∈ s, f i ≤ g i) : ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      exact mul_le_mul (hle i (Finset.mem_insert_self _ _))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
          (fun j hj => hle j (Finset.mem_insert_of_mem hj)))
        (Finset.prod_nonneg fun j hj => hf j (Finset.mem_insert_of_mem hj))
        (hg i (Finset.mem_insert_self _ _))

/-- The tensor product of the actual one-dimensional smooth block kernels. -/
def productScalarBlockKernel {d : ℕ} (s : Fin d → ℕ) :
    C(UnitAddTorus (Fin d), ℂ) :=
  ⟨fun x => ∏ i : Fin d, ScalarKernelL1.scalarBlockKernel (s i) (x i), by
    fun_prop⟩

/-- The finite multiplier kernel on the torus is the tensor product of the
actual scalar block kernels. -/
theorem tensorBlockKernel_eq_product {d : ℕ} (s : Fin d → ℕ) :
    AtomicBlockKernel.kernel s = productScalarBlockKernel s := by
  classical
  apply ContinuousMap.ext
  intro x
  simp only [AtomicBlockKernel.kernel, productScalarBlockKernel,
    ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    SmoothResolution.frequencyBox, ScalarKernelL1.scalarBlockKernel,
    ScalarKernelL1.polynomialKernel, ContinuousMap.coe_mk]
  simp only [tensorMultiplier, UnitAddTorus.mFourier, ContinuousMap.coe_mk]
  push_cast
  have hprod (k : Fin d → ℤ) :
      (∏ i : Fin d, (scalarBlock (s i) (k i : ℝ) : ℂ)) *
        (∏ i : Fin d, fourier (k i) (x i)) =
      ∏ i : Fin d,
        ((scalarBlock (s i) (k i : ℝ) : ℂ) * fourier (k i) (x i)) := by
    rw [Finset.prod_mul_distrib]
  simp_rw [hprod]
  have hbox (i : Fin d) :
      Finset.Icc (-((2 : ℤ) ^ (s i + 1))) ((2 : ℤ) ^ (s i + 1)) =
        scalarFrequencyBox (s i) := by rfl
  simp_rw [hbox]
  rw [(Finset.prod_univ_sum
    (fun i : Fin d => scalarFrequencyBox (s i))
    (fun i n => ((scalarBlock (s i) (n : ℝ) : ℂ) * fourier n (x i)))).symm]




/-- An arbitrary coordinate product kernel has exactly the product L1
budget. -/
def coordinateProductKernel {d : ℕ} (K : Fin d → C(UnitAddCircle, ℂ)) :
    C(UnitAddTorus (Fin d), ℂ) :=
  ⟨fun x => ∏ i : Fin d, K i (x i), by fun_prop⟩

theorem coordinateProductKernel_norm_integral_le {d : ℕ}
    (K : Fin d → C(UnitAddCircle, ℂ)) (B : Fin d → ℝ)
    (hB : ∀ i, 0 ≤ B i)
    (hK : ∀ i, (∫ y : UnitAddCircle, ‖K i y‖
      ∂AddCircle.haarAddCircle) ≤ B i) :
    (∫ x : UnitAddTorus (Fin d), ‖coordinateProductKernel K x‖
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      ∏ i : Fin d, B i := by
  change (∫ x : (i : Fin d) → UnitAddCircle,
      ‖∏ i : Fin d, K i (x i)‖
        ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) ≤ _
  have hprod :
      (∫ x : (i : Fin d) → UnitAddCircle,
        ‖∏ i : Fin d, K i (x i)‖
          ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) =
      ∏ i : Fin d, ∫ y : UnitAddCircle, ‖K i y‖ ∂AddCircle.haarAddCircle := by
    rw [show (fun x : (i : Fin d) → UnitAddCircle => ‖∏ i : Fin d, K i (x i)‖) =
      fun x => ∏ i : Fin d, ‖K i (x i)‖ by
        funext x
        simp [norm_prod]]
    exact MeasureTheory.integral_fintype_prod_eq_prod
      (fun i y => ‖K i y‖)
  rw [hprod]
  exact prod_le_prod_nonneg_real Finset.univ
    (fun i => ∫ y : UnitAddCircle, ‖K i y‖ ∂AddCircle.haarAddCircle)
    B
    (fun i hi => integral_nonneg (fun y => norm_nonneg _))
    (fun i hi => hB i)
    (fun i hi => hK i)

/-- The actual tensor block kernel has the product L1 bound inherited from
the one-dimensional scalar profile bound. -/
theorem tensorBlockKernel_norm_integral_le {d : ℕ} (s : Fin d → ℕ)
    (L : ℝ) (hL : 0 ≤ L)
    (hscalar : ∀ t : ℕ,
      (∫ x : UnitAddCircle, ‖ScalarKernelL1.scalarBlockKernel t x‖
        ∂AddCircle.haarAddCircle) ≤ L) :
    (∫ x : UnitAddTorus (Fin d), ‖AtomicBlockKernel.kernel s x‖
      ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle)) ≤
      L ^ d := by
  rw [tensorBlockKernel_eq_product]
  change (∫ x : (i : Fin d) → UnitAddCircle,
      ‖∏ i : Fin d, ScalarKernelL1.scalarBlockKernel (s i) (x i)‖
        ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) ≤ _
  have hprod :
      (∫ x : (i : Fin d) → UnitAddCircle,
        ‖∏ i : Fin d, ScalarKernelL1.scalarBlockKernel (s i) (x i)‖
          ∂Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)) =
      ∏ i : Fin d, ∫ y : UnitAddCircle,
        ‖ScalarKernelL1.scalarBlockKernel (s i) y‖ ∂AddCircle.haarAddCircle := by
    rw [show (fun x : (i : Fin d) → UnitAddCircle =>
      ‖∏ i : Fin d, ScalarKernelL1.scalarBlockKernel (s i) (x i)‖) =
      fun x => ∏ i : Fin d, ‖ScalarKernelL1.scalarBlockKernel (s i) (x i)‖ by
        funext x
        simp [norm_prod]]
    exact MeasureTheory.integral_fintype_prod_eq_prod
      (fun i y => ‖ScalarKernelL1.scalarBlockKernel (s i) y‖)
  rw [hprod]
  calc
    _ ≤ ∏ i : Fin d, L := by
      apply prod_le_prod_nonneg_real Finset.univ
      · intro i hi
        exact integral_nonneg (fun y => norm_nonneg _)
      · intro i hi
        exact hL
      · intro i hi
        exact hscalar (s i)
    _ = L ^ d := by simp

end BrownianSharp

namespace BrownianSharp

/-- The structural finite sum in the block identity is ordinary convolution
by the actual tensor multiplier kernel. -/
theorem block_eq_kernel_integral {d : ℕ} (s : Fin d → ℕ)
    (f : BrownianSharp.Torus.RealPeriodic d) (x : UnitAddTorus (Fin d)) :
    SmoothResolution.block s f x =
      ∫ y : UnitAddTorus (Fin d),
        AtomicBlockKernel.kernel s (x-y) * (f y : ℂ)
        ∂(Measure.pi fun _ : Fin d => AddCircle.haarAddCircle) := by
  rw [AtomicBlockKernel.block_eq_kernelSum_integral]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [AtomicBlockKernel.kernel]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply]
  rw [Finset.sum_mul]

end BrownianSharp
