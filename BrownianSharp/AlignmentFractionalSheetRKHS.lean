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

abbrev PastSourceL2 := Lp ℝ 2 (volume.restrict (Set.Iic (0:ℝ)))

/-- The direct-sum feature source used in the Mandelbrot–van Ness model:
positive times on `[0,1]` and the independent past tail on `(-∞,0]`. -/
abbrev FractionalSheetFeatureSource :=
  WithLp 2 (UnitL2 × PastSourceL2)

/-- Isometric inclusion of the positive-time RL source as the first summand
of the full fractional Brownian feature space. -/
def positiveSourceEmbedding : UnitL2 →L[ℝ] FractionalSheetFeatureSource := by
  let L : UnitL2 →ₗ[ℝ] FractionalSheetFeatureSource :=
    { toFun := fun g => WithLp.toLp 2 (g, 0)
      map_add' := by
        intro f g
        simp [← WithLp.toLp_add]
      map_smul' := by
        intro c f
        simp [← WithLp.toLp_smul] }
  exact L.mkContinuous 1 (by
    intro g
    change ‖WithLp.toLp 2 (g, (0:PastSourceL2))‖ ≤ 1 * ‖g‖
    rw [WithLp.norm_toLp_fst]
    simp)

theorem positiveSourceEmbedding_norm (g : UnitL2) :
    ‖positiveSourceEmbedding g‖ = ‖g‖ := by
  change ‖WithLp.toLp 2 (g, (0:PastSourceL2))‖ = ‖g‖
  exact WithLp.norm_toLp_fst 2 UnitL2 PastSourceL2 g

theorem positiveSourceEmbedding_inner {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (g : UnitL2) (z : FractionalSheetFeatureSource) :
    ⟪positiveSourceEmbedding g, z⟫ = ⟪g, z.fst⟫ := by
  change ⟪WithLp.toLp 2 (g, (0:PastSourceL2)), z⟫ = _
  rw [WithLp.prod_inner_apply]
  simp

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

/-- For the direct-sum covariance feature, the positive-time projection is
exactly the scaled RL operator.  This packages the functional-analytic source
projection used in Kühn–Linde (2002), eqs. (7.3) and (7.9). -/
theorem directSum_featureOperator_eq_RL
    (α c : ℝ) (hα : 1/2 < α)
    (v : C(UnitInterval, FractionalSheetFeatureSource))
    (hpositive : ∀ (t : UnitInterval) (ht0 : 0 ≤ (t:ℝ)) (ht1 : (t:ℝ) ≤ 1),
      (WithLp.ofLp (v t)).1 = c • kernelVector α t.1 hα
        ht0 ht1)
    (g : UnitL2) :
    featureOperator v (positiveSourceEmbedding g) = c • fractionalRL α hα g := by
  ext t
  rw [featureOperator_apply]
  have ht01 : 0 ≤ (t:ℝ) ∧ (t:ℝ) ≤ 1 := by
    exact Set.mem_Icc.mp t.property
  calc
    ⟪v t, positiveSourceEmbedding g⟫ =
        ⟪positiveSourceEmbedding g, v t⟫ := real_inner_comm _ _
    _ = ⟪g, (WithLp.ofLp (v t)).1⟫ :=
      positiveSourceEmbedding_inner (E:=FractionalSheetFeatureSource) g (v t)
    _ = c * ⟪g, kernelVector α t.1 hα
        ht01.1 ht01.2⟫ := by
      rw [hpositive t ht01.1 ht01.2]
      rw [inner_smul_right]
    _ = c * fractionalRL α hα g t := by
      congr 1
      rw [real_inner_comm]
      change evaluationFunctional α t.1 hα
        ht01.1 ht01.2 g = _
      rw [fractionalRL_apply α hα g t.1 ht01.1 ht01.2]
      exact evaluationFunctional_apply α t.1 hα ht01.1 ht01.2 g

/-- The covariance kernel represented by a Hilbert feature field. -/
def gramCovariance {K H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (v : K → H) (x y : K) : ℝ :=
  ⟪v x, v y⟫

/-- A covariance kernel realized by a continuous Hilbert feature field.  For
fractional Brownian motion, constructing this record with the actual
covariance requires the Gram identity in Kühn–Linde (2002), Proposition 7.2,
pp. 23–24, equations (7.3)–(7.5); that identity is deliberately not assumed
as an instance or silently identified with the RL covariance. -/
structure CovarianceFeatureField {K H : Type*} [TopologicalSpace K]
    [CompactSpace K] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (cov : K → K → ℝ) where
  feature : C(K, H)
  gram_eq : ∀ x y, cov x y = gramCovariance feature x y

/-- If a feature model realizes the defining covariance kernel, then the
actual fractional sheet's finite evaluation covariance matrices are exactly
the feature Gram matrices. This is the process-specific handoff; the remaining
analytic input is constructing the model via the MvN/Kühn–Linde feature. -/
theorem fractionalSheet_covariance_eq_featureGram
    {d : ℕ} {Ω H : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [IsProbabilityMeasure P]
    (B : BrownianSharp.AlignmentGaussianRates.FractionalBrownianSheetOnCube d Ω P)
    (M : CovarianceFeatureField (H:=H)
      (fun x y => BrownianSharp.AlignmentGaussianRates.fractionalSheetCovariance
        B.H x y)) (x y : HaarQuarter.BrownianCubeAnchor d) :
    cov[fun ω => B.path ω x, fun ω => B.path ω y; P] =
      gramCovariance M.feature x y := by
  rw [B.covariance]
  exact M.gram_eq x y

theorem featureOperator_gramCovariance {K H : Type*} [TopologicalSpace K]
    [CompactSpace K] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : C(K, H)) (x y : K) :
    gramCovariance v x y = ⟪v x, v y⟫ := rfl

/-- Polarization turns the two Mandelbrot–van Ness identities (self-similar
feature norms and stationary-increment difference norms) into the exact
fractional Brownian covariance.  The kernel-specific scaling and translation
identities are separate analytic obligations. -/
theorem gram_of_scaled_stationary_increments
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (F : ℝ → E) (H c s t : ℝ)
    (hnorm_s : ‖F s‖ ^ 2 = c * s ^ (2 * H))
    (hnorm_t : ‖F t‖ ^ 2 = c * t ^ (2 * H))
    (hdiff : ‖F s - F t‖ ^ 2 = c * |s - t| ^ (2 * H)) :
    ⟪F s, F t⟫ = c *
      BrownianSharp.AlignmentGaussianRates.fractionalCoordinateCovariance H s t := by
  rw [BrownianSharp.AlignmentGaussianRates.fractionalCoordinateCovariance]
  have hpolar : ‖F s - F t‖ ^ 2 = ‖F s‖ ^ 2 + ‖F t‖ ^ 2 - 2 * ⟪F s, F t⟫ := by
    rw [norm_sub_sq_real]
    ring
  rw [hnorm_s, hnorm_t, hdiff] at hpolar
  nlinarith

/-- If a covariance feature space contains the RL source isometrically and
its feature operator restricts to `c` times the RL operator, then the scaled
RL image unit ball is contained in the true feature-space image unit ball.
This is the precise inclusion needed for the fractional-sheet small-ball lower
bound after the covariance feature identity is established. -/
theorem scaled_RL_image_subset_feature_image
    {K X H : Type*} [TopologicalSpace K] [CompactSpace K]
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (v : C(K, H)) (J : X →L[ℝ] H) (R : X →L[ℝ] C(K, ℝ))
    (c : ℝ) (hJ : ∀ x, ‖J x‖ = ‖x‖)
    (hfactor : ∀ x, featureOperator v (J x) = c • R x) :
    (fun f : C(K, ℝ) => c • f) ''
        (R '' {x : X | ‖x‖ ≤ 1}) ⊆
      featureOperator v '' {g : H | ‖g‖ ≤ 1} := by
  rintro f ⟨f₀, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨J x, ?_, ?_⟩
  · change ‖J x‖ ≤ 1
    change ‖x‖ ≤ 1 at hx
    rw [hJ x]
    exact hx
  · exact hfactor x

/-- Tensorized positive-source comparison.  Here `X` is the tensor RL source,
`J` is its isometric inclusion into the complete covariance feature space, and
`R` is the tensor RL operator.  The same proof applies at every tensor order;
the analytic content is constructing `model`, `J`, and `hfactor` from the
coordinate Gram identity and source-factor projection.  In Kühn–Linde (2002),
equations (7.6), (7.8), and (7.9), that source-factor identity is explicit. -/
theorem tensorized_scaled_RL_image_subset_feature_image
    {K X H : Type*} [TopologicalSpace K] [CompactSpace K]
      [NormedAddCommGroup X] [NormedSpace ℝ X]
      [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {cov : K → K → ℝ} (model : CovarianceFeatureField cov)
    (J : X →L[ℝ] H) (R : X →L[ℝ] C(K, ℝ)) (c : ℝ)
    (hJ : ∀ x, ‖J x‖ = ‖x‖)
    (hfactor : ∀ x, featureOperator model.feature (J x) = c • R x) :
    (fun f : C(K, ℝ) => c • f) ''
        (R '' {x : X | ‖x‖ ≤ 1}) ⊆
      featureOperator model.feature '' {g : H | ‖g‖ ≤ 1} :=
  scaled_RL_image_subset_feature_image model.feature J R c hJ hfactor

end BrownianSharp.AlignmentFractionalSheetRKHS
