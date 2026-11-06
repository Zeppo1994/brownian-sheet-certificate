import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import BrownianSharp.GaussianDensity

/-!
# Finite-grid Gaussian statistics

A finite deterministic layer for the Brownian sharp-certificate project.  The coefficient vector
is arbitrary here (and can later be evaluated under a Gaussian law).  The normalized p-statistic
is the uniform average of the p-th powers of linear row evaluations; its p-root is represented by
a rescaled `PiLp` norm.  Thus convexity is deterministic and does not assume concentration.
-/

noncomputable section

open scoped BigOperators Topology
open MeasureTheory Filter ProbabilityTheory

namespace BrownianSharp

/-- A finite matrix acting on a coefficient vector by row evaluation. -/
def rowEvaluation {κ ι : Type*} [Fintype κ] [Fintype ι]
    (A : ι → κ → ℝ) : (κ → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun x i := ∑ k, A i k * x k
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' c x := by
    ext i
    simp [Finset.mul_sum, mul_left_comm]

end BrownianSharp
