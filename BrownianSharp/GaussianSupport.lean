import BrownianSharp.GaussianDensity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! Full support of the actual product standard Gaussian measure. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp.GaussianDensity
variable {ι : Type*} [Fintype ι]

theorem density_pos (x : ι → ℝ) : 0 < density x :=
  Finset.prod_pos fun i _ => gaussianPDFReal_pos 0 1 (x i) one_ne_zero

theorem density_measurable : Measurable (density : (ι → ℝ) → ℝ) := by
  unfold density
  fun_prop

theorem volume_absolutelyContinuous_standardGaussian :
    (volume : Measure (ι → ℝ)) ≪ Measure.pi (fun _ : ι => gaussianReal 0 1) := by
  rw [standardGaussian_eq_withDensity]
  apply withDensity_absolutelyContinuous' density_measurable.ennreal_ofReal.aemeasurable
  exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (density_pos x)).ne'

theorem standardGaussian_open_pos {s : Set (ι → ℝ)} (hs : IsOpen s) (hne : s.Nonempty) :
    0 < (Measure.pi (fun _ : ι => gaussianReal 0 1)) s := by
  letI : Measure.IsOpenPosMeasure (Measure.pi (fun _ : ι => gaussianReal 0 1)) :=
    volume_absolutelyContinuous_standardGaussian.isOpenPosMeasure
  exact hs.measure_pos _ hne
end BrownianSharp.GaussianDensity
