import BrownianSharp.AtomicBlockKernel
import BrownianSharp.InverseDerivativeProfileIdentity
import BrownianSharp.YoungFejerMixtureLp
import BrownianSharp.YoungLp
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Tactic
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

end BrownianSharp

namespace BrownianSharp

end BrownianSharp
