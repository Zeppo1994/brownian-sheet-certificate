import BrownianSharp.BorellRegularizedHeat
import BrownianSharp.NativeVarianceBound
import BrownianSharp.NativeStatisticProperties
import BrownianSharp.NativeScale
import BrownianSharp.EventualRates
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import BrownianSharp.Statement
import BrownianSharp.Interpolation

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

end BrownianSharp
