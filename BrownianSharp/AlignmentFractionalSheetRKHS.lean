import BrownianSharp.AlignmentFractionalTensorOperator
import BrownianSharp.AlignmentGaussianRates
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Feature-space comparison for fractional-sheet Cameron–Martin classes

A Gaussian covariance feature map `v : K → H` generates the operator
`g ↦ (x ↦ ⟪v x,g⟫)` and its Cameron–Martin image ball.  The theorem below
isolates the exact positive-time-factor argument used for fractional Brownian
sheets: an isometric copy of the RL source inside the covariance feature space,
whose feature operator agrees with `c` times RL, embeds the scaled RL image
ball in the true Gaussian feature image ball.  This is an operator/RKHS bridge;
it does not identify the RL process law with fractional Brownian motion.  The
source for the missing concrete model is Kühn–Linde, *Optimal Series
Representation of Fractional Brownian Sheets*,
https://users.fmi.uni-jena.de/~hicke/inst_stoch/Linde/SERREP5.pdf,
pp. 23–24, Proposition 7.2 and equations (7.3)–(7.9): for covariance
exponent `γ=2H`, their 1D feature source is `L²[0,1] ⊕ L²(−∞,0]` and
`Tγ=κγ(R_{(γ+1)/2} ⊕ Qγ)`.  Proposition 7.2 asserts that its feature Gram
kernel is the fBm covariance.  Tensorization and projection to the positive
source factor give `Tγ^d ∘ P = κ R_tensor` and (7.9), the scaled-image
inclusion formalized below.  The Gram identity and smoothing estimate for
`Qγ` are not proved in this module.
-/

noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory

namespace BrownianSharp.AlignmentFractionalSheetRKHS

open BrownianSharp.AlignmentFractionalKernel
open BrownianSharp.AlignmentFractionalL2
open BrownianSharp.AlignmentFractionalTranslation

/-- The unnormalized causal power used in the Mandelbrot–van Ness feature. -/
def mvNPower (p x : ℝ) : ℝ := if 0 < x then x ^ p else 0

/-- Full-line Mandelbrot–van Ness increment kernel, with exponent
`p=H−1/2`.  The difference is essential on negative source times; omitting it
would produce the RL covariance instead of the fBm covariance. -/
def mvNFullKernel (p t u : ℝ) : ℝ := mvNPower p (t-u) - mvNPower p (-u)

theorem mvNPower_scale {p t x : ℝ} (ht : 0 < t) :
    mvNPower p (t*x) = t ^ p * mvNPower p x := by
  by_cases hx : 0 < x
  · have htx : 0 < t*x := mul_pos ht hx
    rw [mvNPower, if_pos htx, mvNPower, if_pos hx, Real.mul_rpow ht.le hx.le]
  · have hx' : x ≤ 0 := le_of_not_gt hx
    have htx : t*x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le hx'
    simp [mvNPower, hx, htx]

/-- Homogeneity of the full MvN increment kernel.  This is the pointwise
identity needed for the generic Lebesgue-dilation lemma proving the exact
feature norm scaling. -/
theorem mvNFullKernel_scale {p t u : ℝ} (ht : 0 < t) :
    mvNFullKernel p t (t*u) = t ^ p * mvNFullKernel p 1 u := by
  rw [mvNFullKernel, mvNFullKernel, show t - t*u = t*(1-u) by ring,
    show -(t*u) = t*(-u) by ring, mvNPower_scale ht, mvNPower_scale ht]
  ring

/-- The continuous linear feature operator associated to a continuous Hilbert
feature field. Its evaluation kernel is the Gram kernel of the field. -/
def featureOperator {K H : Type*} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : C(K, H)) : H →L[ℝ] C(K, ℝ) := by
  let L : H →ₗ[ℝ] C(K, ℝ) :=
    { toFun := fun g => ⟨fun x => ⟪v x, g⟫, v.continuous.inner continuous_const⟩
      map_add' := by
        intro g h
        ext x
        simp [inner_add_right]
      map_smul' := by
        intro c g
        ext x
        simp [inner_smul_right] }
  exact L.mkContinuous ‖v‖ (by
    intro g
    apply (ContinuousMap.norm_le _ (by positivity : 0 ≤ ‖v‖ * ‖g‖)).2
    intro x
    exact (norm_inner_le_norm (v x) g).trans
      (mul_le_mul_of_nonneg_right (v.norm_coe_le_norm x) (norm_nonneg g)))

@[simp] theorem featureOperator_apply {K H : Type*} [TopologicalSpace K]
    [CompactSpace K] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : C(K, H)) (g : H) (x : K) :
    featureOperator v g x = ⟪v x, g⟫ := rfl

end BrownianSharp.AlignmentFractionalSheetRKHS
