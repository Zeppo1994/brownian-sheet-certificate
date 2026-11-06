import BrownianSharp.AlignmentPaperContinuumConfinement

/-! Numerical radius and grade selection for the literal continuum proof.
The final concrete shell estimate discharges the explicit variance input. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp.AlignmentPaperContinuumConfinementRates
open AlignmentPaperContinuumGoodRegion AlignmentPaperContinuumConfinement
open AlignmentPaperSpatialExponential

theorem gaussian_threeQuarter_quantile_pos :
    0<Concentration.standardGaussianQuantile (3/4) := by
  have hq := Concentration.standardGaussianCDF_standardGaussianQuantile
    (u:=(3/4:ℝ)) (by norm_num) (by norm_num)
  by_contra hn
  have hh := Concentration.standardGaussianCDF_strictMono.monotone (le_of_not_gt hn)
  rw [hq,Concentration.standardGaussianCDF_zero] at hh
  norm_num at hh

end BrownianSharp.AlignmentPaperContinuumConfinementRates
