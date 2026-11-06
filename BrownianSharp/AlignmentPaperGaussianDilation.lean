import BrownianSharp.GaussianEhrhardCertified
import BrownianSharp.AlignmentGaussianFiniteSourceModel
import BrownianSharp.AlignmentGaussianRates
import BrownianSharp.AlignmentPaperGaussianFeatureBridge
import Mathlib.Analysis.Convex.Basic
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic

noncomputable section
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace BrownianSharp.AlignmentPaperGaussianDilation

open BrownianSharp.Concentration
open BrownianSharp.AlignmentGaussianFiniteSourceModel

/-- Transfer the finite-dimensional Gaussian Ehrhard interpolation inequality
through a linear equivalence. This keeps the set-level argument explicit and
lets actual Gaussian vectors use the certified product-normal theorem. -/
theorem gaussianEhrhard_of_linearEquiv
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (μ : Measure E) (ν : Measure F)
    (e : E ≃ₗ[ℝ] F)
    (hemb : MeasurableEmbedding e)
    (hmap : μ.map e = ν)
    (hEhrhard : GaussianEhrhard E μ)
    : GaussianEhrhard F ν := by
  intro A B hA hB a b ha hb hab hμA0 hμA1 hμB0 hμB1
  let A' := e ⁻¹' A
  let B' := e ⁻¹' B
  have hA' : Convex ℝ A' := hA.linear_preimage e.toLinearMap
  have hB' : Convex ℝ B' := hB.linear_preimage e.toLinearMap
  have hAmap : ν.real A = μ.real A' := by
    change (ν A).toReal = (μ (e ⁻¹' A)).toReal
    rw [← hmap, hemb.map_apply]
  have hBmap : ν.real B = μ.real B' := by
    change (ν B).toReal = (μ (e ⁻¹' B)).toReal
    rw [← hmap, hemb.map_apply]
  have hwm : weightedMinkowski a A' b B' =
      e ⁻¹' weightedMinkowski a A b B := by
    ext z
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      refine ⟨e x, hx, e y, hy, ?_⟩
      simp [map_add, map_smul]
    · intro hz
      rcases hz with ⟨x, hx, y, hy, hxy⟩
      refine ⟨e.symm x, ?_, e.symm y, ?_, ?_⟩
      · simpa [A'] using hx
      · simpa [B'] using hy
      · apply e.injective
        simpa [map_add, map_smul] using hxy
  have hWMmap : ν.real (weightedMinkowski a A b B) =
      μ.real (weightedMinkowski a A' b B') := by
    change (ν (weightedMinkowski a A b B)).toReal =
      (μ (weightedMinkowski a A' b B')).toReal
    rw [← hmap, hemb.map_apply, hwm]
  have hμA'0 : 0 < μ.real A' := by rw [← hAmap]; exact hμA0
  have hμA'1 : μ.real A' < 1 := by rw [← hAmap]; exact hμA1
  have hμB'0 : 0 < μ.real B' := by rw [← hBmap]; exact hμB0
  have hμB'1 : μ.real B' < 1 := by rw [← hBmap]; exact hμB1
  have h := hEhrhard A' B' hA' hB' a b ha hb hab
    hμA'0 hμA'1 hμB'0 hμB'1
  rw [hAmap, hBmap, hWMmap]
  exact h

/-- The standard Gaussian on any finite-dimensional real inner-product space
satisfies the certified set-level Ehrhard inequality. -/
theorem stdGaussian_gaussianEhrhard
    {E ι : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (b : OrthonormalBasis ι ℝ E) :
    GaussianEhrhard E (stdGaussian E) := by
  let eCL : (ι → ℝ) ≃L[ℝ] E :=
    (EuclideanSpace.equiv ι ℝ).symm.trans b.repr.symm.toContinuousLinearEquiv
  let e : (ι → ℝ) ≃ₗ[ℝ] E := eCL.toLinearEquiv
  have heq : (fun x : ι → ℝ => e x) = fun x => ∑ i, x i • b i := by
    funext x
    change ((EuclideanSpace.basisFun ι ℝ).equiv b (Equiv.refl ι)
      ((EuclideanSpace.equiv ι ℝ).symm x)) = ∑ i, x i • b i
    rw [b.equiv_apply_euclideanSpace]
    simp
  have hmap : (productStandardGaussian ι).map e = stdGaussian E := by
    rw [show e = fun x : ι → ℝ => ∑ i, x i • b i from heq]
    simpa [productStandardGaussian] using
      (stdGaussian_eq_map_pi_orthonormalBasis b).symm
  have hemb : MeasurableEmbedding e := by
    convert eCL.toHomeomorph.toMeasurableEquiv.measurableEmbedding using 1 <;> rfl
  exact gaussianEhrhard_of_linearEquiv (productStandardGaussian ι)
    (stdGaussian E) e hemb hmap (finiteProductGaussianEhrhard_certified (κ := ι))

end BrownianSharp.AlignmentPaperGaussianDilation
