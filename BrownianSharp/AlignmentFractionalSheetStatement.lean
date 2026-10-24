import BrownianSharp.AlignmentFractionalSheetLowerLog
import BrownianSharp.AlignmentGaussianActualFractionalUpperLog
import BrownianSharp.AlignmentLatestStatements
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace BrownianSharp.AlignmentFractionalSheetStatement

open BrownianSharp.AlignmentFractionalSheetLowerLog
open BrownianSharp.AlignmentGaussianActualFractionalUpperLog
open BrownianSharp.AlignmentGaussianRates
open BrownianSharp.Latest

/-- The latest two-sided logarithmic small-ball statement for actual
fractional Brownian sheets. The MvN filtration supplies the upper bound and
small-ball positivity; the RL feature-ball entropy lower bound supplies the
opposite inequality. -/
theorem latest_fractionalSheet_certified : Latest.FractionalSheetStatement := by
  intro d hd H hH h ν hν hmin
  obtain ⟨cU, εU, hcU, hεU, hεUsmall, hUpper⟩ :=
    fractionalSheet_upperLog_of_actualMvN_scalar_filtrations_any_dimension
      hd H hH h ν hν hmin
  obtain ⟨cL, εL, hcL, hεL, hεLsmall, hLower⟩ :=
    fractionalSheet_oneSided_lowerLog_of_positive (by omega) H hH hν h hmin
  let ε₀ := min εU εL
  refine ⟨cL, cU, ε₀, hcL, hcU, lt_min hεU hεL, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_right _ _) hεLsmall
  · intro Ω _ P _ B hBH ε hε hsmall
    have hsmallU : ε ≤ εU := le_trans hsmall (min_le_left _ _)
    have hsmallL : ε ≤ εL := le_trans hsmall (min_le_right _ _)
    have hu := hUpper Ω P B hBH ε hε hsmallU
    have hl := hLower Ω P B hBH ε hε hsmallL hu.1
    exact ⟨hl, hu.2⟩

end BrownianSharp.AlignmentFractionalSheetStatement
