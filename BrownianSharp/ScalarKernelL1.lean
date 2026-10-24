import BrownianSharp.TheoremDFejerFourier
import BrownianSharp.ScalarBlockBessel

/-! L1 multiplier kernels from finite Fejer mixtures. The scalar smooth
resolution estimates will use this positive-kernel representation. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal NNReal
namespace BrownianSharp.ScalarKernelL1
open AddCircle HaarQuarter.TheoremD.FejerFourier

local instance : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

theorem fejer_continuous (N : ℕ) : Continuous (fejerFourierPolynomial N) := by
  unfold fejerFourierPolynomial
  fun_prop

theorem fejer_norm_eq_re (N : ℕ) (x : UnitAddCircle) :
    ‖fejerFourierPolynomial N x‖ = (fejerFourierPolynomial N x).re := by
  induction x using QuotientAddGroup.induction_on with
  | H t =>
    rw [fejerFourierPolynomial_eval_eq_real]
    simp only [Complex.norm_real, Complex.ofReal_re]
    apply abs_of_nonneg
    unfold realFejerKernel
    exact div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fejer_integral (N : ℕ) (hN : 0<N) :
    (∫ x : UnitAddCircle, fejerFourierPolynomial N x ∂AddCircle.haarAddCircle) = 1 := by
  have h := fejerFourierPolynomial_fourierCoeff_nat N 0 hN (by omega)
  simpa [fourierCoeff, fourier, hN.ne'] using h

theorem fejer_norm_integral (N : ℕ) (hN : 0<N) :
    (∫ x : UnitAddCircle, ‖fejerFourierPolynomial N x‖ ∂AddCircle.haarAddCircle) = 1 := by
  simp_rw [fejer_norm_eq_re]
  have hi : Integrable (fejerFourierPolynomial N) (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    (fejer_continuous N).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  change (∫ x : UnitAddCircle, RCLike.re (fejerFourierPolynomial N x) ∂AddCircle.haarAddCircle) = 1
  rw [integral_re hi, fejer_integral N hN]
  norm_num

/-- Fourier coefficients determine a continuous periodic function pointwise. -/
theorem continuous_eq_of_fourierCoeff_eq (f g : C(UnitAddCircle, ℂ))
    (h : ∀ n : ℤ, fourierCoeff f n = fourierCoeff g n) : f=g := by
  apply ContinuousMap.toLp_injective (p := (2:ℝ≥0∞)) (μ := AddCircle.haarAddCircle) (𝕜 := ℂ)
  apply (fourierBasis.repr).injective
  ext n
  rw [fourierBasis_repr, fourierBasis_repr, fourierCoeff_toLp, fourierCoeff_toLp]
  exact h n

/-- Positive normalized Fejer kernel as a continuous circle function. -/
def fejerKernel (N : ℕ) : C(UnitAddCircle, ℂ) := ⟨fejerFourierPolynomial N, fejer_continuous N⟩

/-- An actual finite signed Fejer mixture has L1 norm at most its coefficient
variation. -/
theorem fejer_mixture_norm_integral_le (S : Finset ℕ) (w : ℕ → ℂ)
    (hpos : ∀ N ∈ S, 0<N) :
    (∫ x : UnitAddCircle, ‖∑ N ∈ S, w N * fejerFourierPolynomial N x‖
      ∂AddCircle.haarAddCircle) ≤ ∑ N ∈ S, ‖w N‖ := by
  have hcont : Continuous (fun x : UnitAddCircle => ∑ N ∈ S, w N * fejerFourierPolynomial N x) := by
    exact continuous_finset_sum S fun N hN => continuous_const.mul (fejer_continuous N)
  have hint : Integrable (fun x : UnitAddCircle => ‖∑ N ∈ S, w N * fejerFourierPolynomial N x‖)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    hcont.norm.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hterms : ∀ N ∈ S, Integrable (fun x : UnitAddCircle => ‖w N‖ * ‖fejerFourierPolynomial N x‖)
      (AddCircle.haarAddCircle : Measure UnitAddCircle) := by
    intro N hN
    exact ((fejer_continuous N).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).const_mul _
  calc
    _ ≤ ∫ x : UnitAddCircle, ∑ N ∈ S, ‖w N‖ * ‖fejerFourierPolynomial N x‖
        ∂AddCircle.haarAddCircle := by
      apply integral_mono hint (integrable_finset_sum S hterms)
      intro x
      simpa only [norm_mul] using norm_sum_le S (fun N => w N * fejerFourierPolynomial N x)
    _ = ∑ N ∈ S, ‖w N‖ * (∫ x : UnitAddCircle, ‖fejerFourierPolynomial N x‖
        ∂AddCircle.haarAddCircle) := by
      rw [integral_finset_sum S hterms]
      apply Finset.sum_congr rfl
      intro N hN
      exact integral_const_mul _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro N hN
      rw [fejer_norm_integral N (hpos N hN), mul_one]

end BrownianSharp.ScalarKernelL1
