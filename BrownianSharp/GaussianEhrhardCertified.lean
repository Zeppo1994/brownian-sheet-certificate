import BrownianSharp.BorellRegularizedHeat
import BrownianSharp.NativeConditional

/-!
# Certified finite-product Gaussian Ehrhard inequality

This is the generic API used by the concentration argument. The heat-flow
proof, Gaussian trace identity, and regularized-set passage are imported from
their independently proved modules.
-/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace BrownianSharp

/-- The product-Gaussian Ehrhard inequality in each finite coordinate type.
Decidable equality is supplied locally rather than exposed to callers. -/
theorem finiteProductGaussianEhrhard_certified
    {κ : Type*} [Fintype κ] :
    Concentration.GaussianEhrhard (κ → ℝ) (productStandardGaussian κ) := by
  classical
  exact gaussianEhrhard_of_gaussianHeatTrace (κ := κ)

/-- Generic certified input satisfying the existing product-Gaussian property
used by the conditional Brownian concentration assembly. -/
theorem productGaussianEhrhard_certified : ProductGaussianEhrhard := by
  intro κ hκ
  letI := hκ
  exact finiteProductGaussianEhrhard_certified (κ := κ)

end BrownianSharp
