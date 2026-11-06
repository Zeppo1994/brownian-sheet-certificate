import BrownianSharp.DKLLRankAllocation
import Mathlib.Tactic

/-! Numerical summation of a dyadic high-grade error profile. This is the
scalar endpoint needed after the finite-layer orthogonal approximation has
supplied the per-layer estimates. -/

open scoped BigOperators

namespace BrownianSharp.DKLLFiniteLayerRate

noncomputable section

def dyadicSquare (n : ℕ) : ℝ := ((2 : ℝ) ^ n)⁻¹ ^ 2

theorem dyadicSquare_nonneg (n : ℕ) : 0 ≤ dyadicSquare n := by
  unfold dyadicSquare
  positivity

end
end BrownianSharp.DKLLFiniteLayerRate
