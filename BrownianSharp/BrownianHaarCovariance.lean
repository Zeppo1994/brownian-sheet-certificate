import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import BrownianSharp.IntegratedHaarTent

/-! Finite-dimensional Gaussian consequences of an honest isonormal family.

The Brownian-sheet application supplies stochastic integrals `W f` and proves
the covariance identity from the sheet covariance.  This interface keeps the
joint Gaussian and covariance inputs explicit; it does not assume independent
Haar coefficients. -/

open MeasureTheory InnerProductSpace ProbabilityTheory
open scoped RealInnerProductSpace

namespace HaarQuarter

/-- A centered jointly Gaussian isonormal family on a real Hilbert space.
The finite-family Gaussian field is the definition of joint Gaussianity; the
separate covariance field is the isometry needed for the Brownian-sheet
application. -/
structure IsonormalGaussianFamily (H Ω ι : Type*) [Fintype ι]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [MeasurableSpace Ω] (P : Measure Ω) where
  eval : H → Ω → ℝ
  jointlyGaussian : (v : ι → H) →
    HasGaussianLaw (fun ω i => eval (v i) ω) P
  measurable_eval : ∀ f : H, Measurable (fun ω => eval f ω)
  mean_zero : ∀ f : H, ∫ ω, eval f ω ∂P = 0
  covariance_eq_inner : ∀ f g : H,
    cov[fun ω ↦ eval f ω, fun ω ↦ eval g ω; P] = ⟪f, g⟫

namespace IsonormalGaussianFamily

variable {H Ω ι : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace Ω]
  {P : Measure Ω} (W : IsonormalGaussianFamily H Ω ι P)

/-- Every stochastic integral has the centered Gaussian law with variance
equal to the squared Hilbert norm of its integrand. -/
theorem coordinate_law (v : ι → H) (i : ι) :
    P.map (fun ω => W.eval (v i) ω) =
      gaussianReal 0 (⟪v i, v i⟫).toNNReal := by
  have hjoint := W.jointlyGaussian v
  have hX := hjoint.eval i
  have hmean : (∫ ω, W.eval (v i) ω ∂P) = 0 := W.mean_zero (v i)
  have hvar : Var[fun ω => W.eval (v i) ω; P] = ⟪v i, v i⟫ := by
    rw [← covariance_self hX.aemeasurable, W.covariance_eq_inner]
  rw [hX.map_eq_gaussianReal, hmean, hvar]

/-- Orthogonal isonormal vectors give independent scaled Gaussian
coordinates.  We derive independence from the joint Gaussian law and the
covariance identity rather than assuming it. -/
theorem iIndepFun_of_orthogonal
    (v : ι → H) (c : ι → ℝ)
    (horth : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 0) :
    iIndepFun (fun i ω => c i * W.eval (v i) ω) P := by
  classical
  have hindep : iIndepFun (fun i ω => W.eval (v i) ω) P := by
    apply HasGaussianLaw.iIndepFun_of_covariance_eq_zero
      (W.jointlyGaussian v)
    intro i j hij
    rw [W.covariance_eq_inner, horth i j hij]
  have hscaled := hindep.comp (fun i x => c i * x)
    (fun _ => measurable_const.mul measurable_id)
  simpa [Function.comp_def] using hscaled

end IsonormalGaussianFamily

end HaarQuarter
