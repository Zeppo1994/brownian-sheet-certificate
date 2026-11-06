import BrownianSharp.AlignmentFractionalTail

/-! Whole-line causal-profile interfaces for the fractional atom preimages.

These lemmas make explicit the zero extension used by the preimage
construction. They do not assert a Fourier multiplier formula. -/
noncomputable section

namespace BrownianSharp.AlignmentPaperFractionalFourier

open BrownianSharp.AlignmentFractionalTail
open BrownianSharp.AlignmentFractionalKernel
open scoped ContDiff

/-- On positive times the zero-extended causal profile is exactly the
Riemann--Liouville integral. -/
theorem causalRLProfile_eq_rlIntegral_of_pos {β : ℝ} (F : ℝ → ℝ) {t : ℝ}
    (ht : 0 < t) :
    causalRLProfile β F t = rlIntegral β F t := by
  simp [causalRLProfile, not_le.mpr ht]

end BrownianSharp.AlignmentPaperFractionalFourier
