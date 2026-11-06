import BrownianSharp.AlignmentPaperLpJointDvp
import BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
import BrownianSharp.AlignmentPaperFiniteShapeEnergy

/-! Actual fixed-grid sample budgets for smooth hyperbolic grades. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace BrownianSharp.AlignmentPaperJointSamplingBudget
open BrownianSharp
open BrownianSharp.Torus
open BrownianSharp.SmoothResolution
open BrownianSharp.AlignmentPaperLpJointDvp
open BrownianSharp.AlignmentPaperLpDvpBlockCover
open BrownianSharp.AlignmentPaperLpDvpSampling
open BrownianSharp.AlignmentPaperLpGridOrthogonality
open BrownianSharp.AlignmentPaperLpOversampledGrid
open BrownianSharp.AlignmentPaperJointAdaptiveScalarSums
open BrownianSharp.AlignmentPaperFiniteShapeEnergy

def samplingConstant (d : ℕ) (p : ℝ) : ℝ :=
  2 * ((3:ℝ)^d)^(p-1) * (5:ℝ)^d * (2:ℝ)^(3*d)

theorem shapeSample_product_eq {d n : ℕ} (r : Shape d n) :
    (∏ i : Fin d, 5*((shapeBandwidth r i*4 : ℕ):ℝ)) =
      (5:ℝ)^d * (2:ℝ)^(n+3*d) := by
  have hc : Fintype.card (ShapeGrid r) = ∏ i : Fin d, shapeBandwidth r i*4 := by
    change Fintype.card (∀ i : Fin d, Fin (shapeBandwidth r i*4)) = _
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
  have hn := hc.symm.trans (shapeGrid_card_eq r)
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  exact_mod_cast hn

theorem smoothGrade_shape_grid_budget {d n : ℕ} (r : Shape d n)
    {p q : ℝ} (hpq : p.HolderConjugate q) (f : RealPeriodic d) :
    (∑ j : ShapeGrid r, ‖block r.1 f
      (oversampledTorusGridPoint (shapeBandwidth r) j)‖^p) ≤
      ((3:ℝ)^d)^(p-1) * (5:ℝ)^d * (2:ℝ)^(n+3*d) *
        (∫ x : UnitAddTorus (Fin d), ‖block r.1 f x‖^p ∂volume) := by
  have hgrid := torusFourierPolynomial_shifted_grid_lp_bound
    (fun i => shapeBandwidth r i*4)
    (by intro i; dsimp [shapeBandwidth]; positivity)
    (frequencyBox r.1)
    (fun k => (tensorMultiplier r.1 k : ℂ)*realPeriodicFourierCoeff f k)
    (by
      intro k hk i
      have hb := smoothBlock_bandlimited r f k hk i
      exact hb.trans (by omega)) hpq (block r.1 f)
  have heq (j : ShapeGrid r) :
      oversampledTorusGridPoint (shapeBandwidth r) j =
        AlignmentPaperLpDvpReproduction.midpointTorusGridPoint
          (fun i => shapeBandwidth r i*4) j := by
    funext i
    simp only [oversampledTorusGridPoint,
      AlignmentPaperLpDvpReproduction.midpointTorusGridPoint, oversampledGridCoordinate]
  simp_rw [heq]
  rw [shapeSample_product_eq r, AlignmentPaperTorusTranslation.torusMeasure_eq_volume] at hgrid
  simpa only [block, mul_assoc] using hgrid

theorem encodeSmoothGradeSamples_energy_budget {d n : ℕ}
    {p q : ℝ} (hpq : p.HolderConjugate q) (f : RealPeriodic d) :
    (∑ a : ShapeSampleIndex d n, |encodeSmoothGradeSamples f a|^p) ≤
      samplingConstant d p * (2:ℝ)^n *
        ∑ r : Shape d n,
          (∫ x : UnitAddTorus (Fin d), ‖block r.1 f x‖^p ∂volume) := by
  classical
  rw [Fintype.sum_sigma]
  have hp : 0 ≤ p := hpq.nonneg
  have hb (r : Shape d n) :
      (∑ a : ShapeGrid r × Bool,
        |encodeSmoothGradeSamples f ⟨r,a⟩|^p) ≤
        2 * ∑ j : ShapeGrid r, ‖block r.1 f
          (oversampledTorusGridPoint (shapeBandwidth r) j)‖^p := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    simp only [Fintype.sum_bool, encodeSmoothGradeSamples, Bool.false_eq_true, ↓reduceIte]
    have hRe := Real.rpow_le_rpow (abs_nonneg _)
      (Complex.abs_re_le_norm (block r.1 f (oversampledTorusGridPoint (shapeBandwidth r) j))) hp
    have hIm := Real.rpow_le_rpow (abs_nonneg _)
      (Complex.abs_im_le_norm (block r.1 f (oversampledTorusGridPoint (shapeBandwidth r) j))) hp
    linarith
  calc
    _ ≤ ∑ r : Shape d n, 2 *
        (((3:ℝ)^d)^(p-1)*(5:ℝ)^d*(2:ℝ)^(n+3*d)*
          ∫ x : UnitAddTorus (Fin d), ‖block r.1 f x‖^p ∂volume) := by
      apply Finset.sum_le_sum
      intro r _
      exact (hb r).trans (mul_le_mul_of_nonneg_left (smoothGrade_shape_grid_budget r hpq f) (by norm_num))
    _ = _ := by
      unfold samplingConstant
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      rw [pow_add]
      ring

theorem encodeSmoothGradeSamples_square_budget {d n : ℕ}
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp2 : p ≤ 2) (f : RealPeriodic d) :
    (∑ a : ShapeSampleIndex d n, |encodeSmoothGradeSamples f a|^p) ≤
      samplingConstant d p * (2:ℝ)^n *
        (Fintype.card (Shape d n):ℝ)^(1-p/2) *
        (∑ r : Shape d n,
          (∫ x : UnitAddTorus (Fin d), ‖block r.1 f x‖^p ∂volume)^(2/p))^(p/2) := by
  have hE (r : Shape d n) :
      0 ≤ ∫ x : UnitAddTorus (Fin d), ‖block r.1 f x‖^p ∂volume :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hfinite := sum_energy_le_card_square_budget _ hE hpq.pos hp2
  apply (encodeSmoothGradeSamples_energy_budget hpq f).trans
  have hc : 0 ≤ samplingConstant d p*(2:ℝ)^n := by unfold samplingConstant; positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hfinite hc
/-- The same budget on the actual finite Euclidean coordinates used by the
feature map. The source reindexing changes no sample or norm. -/
theorem encodeSmoothGradeSamples_fin_square_budget {d n : ℕ}
    {p q : ℝ} (hpq : p.HolderConjugate q) (hp2 : p ≤ 2) (f : RealPeriodic d) :
    (∑ i : Fin (JointSampleDimension d n),
      |encodeSmoothGradeSamples f ((jointSampleIndexEquivFin d n).symm i)|^p) ≤
      samplingConstant d p * (2:ℝ)^n *
        (Fintype.card (Shape d n):ℝ)^(1-p/2) *
        (∑ r : Shape d n,
          (∫ x : UnitAddTorus (Fin d), ‖block r.1 f x‖^p ∂volume)^(2/p))^(p/2) := by
  rw [Equiv.sum_comp (jointSampleIndexEquivFin d n).symm
    (fun a : ShapeSampleIndex d n => |encodeSmoothGradeSamples f a|^p)]
  exact encodeSmoothGradeSamples_square_budget hpq hp2 f

end BrownianSharp.AlignmentPaperJointSamplingBudget
