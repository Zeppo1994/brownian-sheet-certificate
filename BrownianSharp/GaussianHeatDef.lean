import BrownianSharp.GaussianGridStatistics

/-!
# Finite-dimensional Gaussian heat averaging

The heat transform is kept in its own small interface module so analytic
support lemmas and the PDE development can import the same frozen definition.
-/

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace BrownianSharp

/-- Finite-dimensional Gaussian heat averaging. At time `t ≥ 0`, this is the
expectation of `q(x + √t Z)` for a standard product Gaussian vector `Z`. The
formula is defined for every real `t`; its heat-semigroup interpretation uses
nonnegative times. -/
noncomputable def gaussianHeat {κ : Type*} [Fintype κ]
    (q : (κ → ℝ) → ℝ) (t : ℝ) (x : κ → ℝ) : ℝ :=
  ∫ z, q (x + Real.sqrt t • z) ∂productStandardGaussian κ

/-- Gaussian heat averaging is the identity at time zero. -/
theorem gaussianHeat_zero {κ : Type*} [Fintype κ]
    (q : (κ → ℝ) → ℝ) (x : κ → ℝ) : gaussianHeat q 0 x = q x := by
  simp [gaussianHeat]

end BrownianSharp
