import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! The actual finite product Gaussian density, independent of covariance rank
of any linear image used later. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace BrownianSharp.GaussianDensity
variable {ι : Type*} [Fintype ι]

noncomputable def density (x : ι → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

theorem density_nonneg (x : ι → ℝ) : 0 ≤ density x :=
  Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg 0 1 (x i)

theorem density_integrable : Integrable (density : (ι → ℝ) → ℝ) volume := by
  exact Integrable.fintype_prod fun _ => integrable_gaussianPDFReal 0 1

theorem standardGaussian_eq_withDensity :
    Measure.pi (fun _ : ι => gaussianReal 0 1) =
      volume.withDensity (fun x : ι → ℝ => ENNReal.ofReal (density x)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs)]
  have hInt : Integrable (density : (ι → ℝ) → ℝ)
      (volume.restrict (Set.univ.pi s)) := density_integrable.restrict
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ density_nonneg)]
  change ENNReal.ofReal (∫ x, ∏ i, gaussianPDFReal 0 1 (x i)
    ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict (Set.univ.pi s)) = _
  rw [Measure.restrict_pi_pi, integral_fintype_prod_eq_prod]
  calc
    _ = ∏ i, ENNReal.ofReal (∫ x in s i, gaussianPDFReal 0 1 x) :=
      ENNReal.ofReal_prod_of_nonneg (fun i _ =>
        integral_nonneg (fun x => gaussianPDFReal_nonneg 0 1 x))
    _ = _ := Finset.prod_congr rfl (fun i _ =>
      (gaussianReal_apply_eq_integral (0 : ℝ)
        (one_ne_zero : (1 : ℝ≥0) ≠ 0) (s i)).symm)

theorem standardGaussian_absolutelyContinuous :
    Measure.pi (fun _ : ι => gaussianReal 0 1) ≪ (volume : Measure (ι → ℝ)) := by
  rw [standardGaussian_eq_withDensity]
  exact withDensity_absolutelyContinuous _ _

end BrownianSharp.GaussianDensity
