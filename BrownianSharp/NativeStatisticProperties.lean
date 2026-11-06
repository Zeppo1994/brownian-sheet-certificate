import BrownianSharp.NativeGoodStatistics
import BrownianSharp.ActualConcentration

/-! All elementary side conditions for both concentration applications on the
actual native good-grid statistic. Ehrhard remains a displayed geometric input. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace BrownianSharp

theorem productStandardGaussian_coeff_memLp_two (κ : Type*) [Fintype κ] :
    MemLp (id : (κ → ℝ) → κ → ℝ) 2 (productStandardGaussian κ) := by
  apply MeasureTheory.memLp_pi_iff.mpr
  intro k
  exact (GaussianRows.coordinate_gaussian
    (fun (j : κ) (x : κ → ℝ) => x j)
    (fun j => measurable_pi_apply j)
    (fun j => productStandardGaussian_coordinate_law j) k).memLp_two

end BrownianSharp
