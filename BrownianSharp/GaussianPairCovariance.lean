import BrownianSharp.GaussianPairMoments
import Mathlib.Probability.Moments.Covariance

open MeasureTheory ProbabilityTheory

namespace BrownianSharp

/-- The normalized power-moment envelope is the actual covariance envelope
when the two row marginals are standard Gaussian and the displayed powers are
square-integrable. -/
theorem normalizedGaussianRows_actualCovariance_bound
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (G : ι → Ω → ℝ) (hG : ∀ i, Measurable (G i))
    (hLaw : ∀ i, P.map (G i) = gaussianReal 0 1)
    (hIndep : iIndepFun G P) (c d : ι → ℝ)
    (hc : ∑ i, c i ^ 2 = 1) (hd : ∑ i, d i ^ 2 = 1)
    (k : ℕ)
    (hLpC : MemLp (fun ω => GaussianRows.row G c ω ^ (2 * k)) 2 P)
    (hLpD : MemLp (fun ω => GaussianRows.row G d ω ^ (2 * k)) 2 P) :
    cov[fun ω => GaussianRows.row G c ω ^ (2 * k),
        fun ω => GaussianRows.row G d ω ^ (2 * k); P] /
        ((∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)) ^ 2) ≤
      ((4 * k : ℝ) * |∑ i, c i * d i|) ^ 2 *
        Real.exp ((4 * k : ℝ) * |∑ i, c i * d i|) := by
  let X : Ω → ℝ := GaussianRows.row G c
  let Y : Ω → ℝ := GaussianRows.row G d
  let M : ℝ := ∫ x : ℝ, x ^ (2 * k) ∂gaussianReal (0 : ℝ) (1 : NNReal)
  have hXm : Measurable X := by
    change Measurable (fun ω => ∑ i, c i * G i ω)
    exact Finset.measurable_fun_sum _ (fun i hi => measurable_const.mul (hG i))
  have hYm : Measurable Y := by
    change Measurable (fun ω => ∑ i, d i * G i ω)
    exact Finset.measurable_fun_sum _ (fun i hi => measurable_const.mul (hG i))
  have hXlaw : P.map X = gaussianReal 0 1 := by
    dsimp [X]
    rw [GaussianRows.row_law G hG hLaw hIndep c, hc]
    norm_num
  have hYlaw : P.map Y = gaussianReal 0 1 := by
    dsimp [Y]
    rw [GaussianRows.row_law G hG hLaw hIndep d, hd]
    norm_num
  have hXmoment : (∫ ω, X ω ^ (2 * k) ∂P) = M := by
    have hm := integral_map hXm.aemeasurable
      (f := fun x : ℝ => x ^ (2 * k)) (by rw [hXlaw]; fun_prop)
    simpa [M, hXlaw] using hm.symm
  have hYmoment : (∫ ω, Y ω ^ (2 * k) ∂P) = M := by
    have hm := integral_map hYm.aemeasurable
      (f := fun x : ℝ => x ^ (2 * k)) (by rw [hYlaw]; fun_prop)
    simpa [M, hYlaw] using hm.symm
  have hMpos : 0 < M := by
    dsimp [M]
    rw [standardGaussian_evenMoment]
    positivity
  have hbound := normalizedGaussianRows_evenPowerCovariance_bound_full
    G hG hLaw hIndep c d hc hd k
  rw [show (fun ω => GaussianRows.row G c ω ^ (2 * k)) =
      (fun ω => X ω ^ (2 * k)) by funext ω; rfl,
    show (fun ω => GaussianRows.row G d ω ^ (2 * k)) =
      (fun ω => Y ω ^ (2 * k)) by funext ω; rfl]
  rw [covariance_eq_sub hLpC hLpD, hXmoment, hYmoment]
  change (P[(fun ω => X ω ^ (2 * k)) * (fun ω => Y ω ^ (2 * k))] - M * M) / M ^ 2 ≤ _
  have hratio :
      (P[(fun ω => X ω ^ (2 * k)) * (fun ω => Y ω ^ (2 * k))] / M ^ 2) - 1 ≤
        ((4 * k : ℝ) * |∑ i, c i * d i|) ^ 2 *
          Real.exp ((4 * k : ℝ) * |∑ i, c i * d i|) := by
    simpa [X, Y, M] using hbound
  calc
    _ = (P[(fun ω => X ω ^ (2 * k)) * (fun ω => Y ω ^ (2 * k))] / M ^ 2) - 1 := by
      field_simp [ne_of_gt hMpos]
    _ ≤ _ := hratio

end BrownianSharp
