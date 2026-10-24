import BrownianSharp.Anderson
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
Finite-dimensional Anderson comparison on the original probability space.
The residual may have any law, including singular or non-Gaussian laws;
independence and the exact standard coefficient-vector law are displayed.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace BrownianSharp

theorem standardGaussian_linear_shift_le_of_pos {N M : ℕ} (hN : 0 < N)
    (C : Set (Fin M → ℝ)) (A : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ))
    (shift : Fin M → ℝ) (hconv : Convex ℝ C)
    (hsymm : ∀ z, z ∈ C → -z ∈ C) (hC : MeasurableSet C) :
    (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) {x | A x + shift ∈ C} ≤
      (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) {x | A x ∈ C} := by
  cases N with
  | zero => omega
  | succ N => exact standardGaussian_linear_shift_le C A shift hconv hsymm hC

/-- Average the deterministic-shift comparison using the actual independent
joint law; no conditional-distribution assertion is left as an assumption. -/
theorem independent_standardGaussian_residual_comparison
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N M : ℕ} (hN : 0 < N)
    (G : Ω → (Fin N → ℝ)) (Z : Ω → (Fin M → ℝ))
    (hG : Measurable G) (hZ : Measurable Z) (hIndep : IndepFun G Z P)
    (hLaw : P.map G = Measure.pi (fun _ : Fin N => gaussianReal 0 1))
    (C : Set (Fin M → ℝ)) (A : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ))
    (hconv : Convex ℝ C) (hsymm : ∀ z, z ∈ C → -z ∈ C)
    (hC : MeasurableSet C) :
    P {ω | A (G ω) + Z ω ∈ C} ≤ P {ω | A (G ω) ∈ C} := by
  let E : Set ((Fin N → ℝ) × (Fin M → ℝ)) := {u | A u.1 + u.2 ∈ C}
  have hE : MeasurableSet E := hC.preimage (by fun_prop)
  have hzero : MeasurableSet {x : Fin N → ℝ | A x ∈ C} := hC.preimage (by fun_prop)
  have hprod : P {ω | A (G ω) + Z ω ∈ C} =
      ((P.map G).prod (P.map Z)) E := by
    rw [← hIndep.map_prod_eq_prod_map_map hG.aemeasurable hZ.aemeasurable,
      Measure.map_apply (hG.prodMk hZ) hE]
    rfl
  have hright : P {ω | A (G ω) ∈ C} =
      (Measure.pi (fun _ : Fin N => gaussianReal 0 1)) {x | A x ∈ C} := by
    rw [← hLaw, Measure.map_apply hG hzero]
    rfl
  rw [hprod, hright, hLaw, Measure.prod_apply_symm hE]
  calc
    _ ≤ ∫⁻ _z, (Measure.pi (fun _ : Fin N => gaussianReal 0 1))
        {x | A x ∈ C} ∂P.map Z := by
      apply lintegral_mono
      intro z
      exact standardGaussian_linear_shift_le_of_pos hN C A z hconv hsymm hC
    _ = _ := by simp [Measure.map_apply hZ MeasurableSet.univ]

end BrownianSharp
