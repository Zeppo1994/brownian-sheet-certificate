import BrownianSharp.Concentration

/-!
# Ehrhard interface for finite-grid homogeneous convex statistics

This file isolates the geometric theorem still needed by the Brownian
concentration argument. It does not postulate Ehrhard as an axiom: the
conditional theorem below takes the classical set-level Ehrhard inequality as
an explicit argument and proves that it supplies the mass interpolation
premise used by the Paouris--Valettas reduction.
-/

namespace BrownianSharp.Concentration

open MeasureTheory ProbabilityTheory

/-- The affine Minkowski combination of two sets, written in witness form so
that no measurability assumptions are hidden in its definition. -/
def weightedMinkowski {E : Type*} [AddCommGroup E] [Module ℝ E]
    (a : ℝ) (A : Set E) (b : ℝ) (B : Set E) : Set E :=
  {z | ∃ x ∈ A, ∃ y ∈ B, z = a • x + b • y}

/-- Set-level finite-dimensional Ehrhard inequality in the quantile form needed
here. This is the remaining geometric theorem: in applications, `μ` is the
standard product Gaussian measure and `A`, `B` are convex sublevel sets. -/
def GaussianEhrhard (E : Type*) [MeasurableSpace E] [AddCommGroup E]
    [Module ℝ E] (μ : Measure E) : Prop :=
  ∀ A B : Set E, Convex ℝ A → Convex ℝ B →
    ∀ a b : ℝ, 0 < a → 0 < b → a + b = 1 →
      0 < μ.real A → μ.real A < 1 → 0 < μ.real B → μ.real B < 1 →
        standardGaussianCDF
            (a * standardGaussianQuantile (μ.real A) +
             b * standardGaussianQuantile (μ.real B)) ≤
          μ.real (weightedMinkowski a A b B)

end BrownianSharp.Concentration
